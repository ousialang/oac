package io.ousia
package parser

import io.ousia.util.Parsing
import io.ousia.exceptions.SyntaxException

object Parser {

  def apply(tokens: Seq[Tokens.Token]): Seq[Statements.Statement] = {
    Parsing.splitBySemicolons(tokens) map {t => tokensToStatement(t)}
  }

  def tokensToStatement(tokens: Seq[Tokens.Token]): Statements.Statement = {
    if (tokens.isEmpty) {
      throw new SyntaxException("Empty statements are not allowed.")
    }
    val keyword = tokens(0) match {
      case x: Tokens.Identifier => x.s
      case _ => throw new SyntaxException("The statement doesn't start with an identifier.")
    }
    keyword match {
      case "package" => {
        // After the "package" keyword, odd indexed elements are the package
        // path and even indexed ones are separator periods.
        // Ex. package abc.xyz
        val paths = tokens.zipWithIndex filter {
          case (_, index) => index%2 == 1
        } map (_._1)
        val periods = tokens.tail.zipWithIndex filter {
          case (_, index) => index%2 == 1
        } map (_._1)
        periods foreach {
          _ match {
            case p: Tokens.Identifier => if (p.s != ".")
              throw new SyntaxException("unknwon symbol in statement")
            case _ => throw new SyntaxException("Unknown symbol in statement")
          }
        }
        if (periods.size == paths.size)
          throw new SyntaxException("The package names can't end in a period.")
        val identifierPaths = paths map {
          _ match {
            case p: Tokens.Identifier => p
            case _ => throw new SyntaxException("Invalid identifier")
          }
        }
        Statements.Package(identifierPaths)
      }
      case "val" => {
        val identifier = tokens(1) match {
          case i: Tokens.Identifier => i.s
          case _ => throw new SyntaxException("invalid constanct name")
        }
        if (tokens(2) != Tokens.Identifier("="))
          throw new SyntaxException("Expected = token")
        Statements.Val(identifier, Tokens.RoundBrackets(tokens take (3)))
      }
      case "function" => {
        val identifier = tokens(1) match {
          case i: Tokens.Identifier => i.s
          case _ => throw new SyntaxException("invalid constanct name")
        }
        if (tokens(2) != Tokens.Identifier("="))
          throw new SyntaxException("Expected = token")
        Statements.Val(identifier, Tokens.RoundBrackets(tokens take (3)))
      }
    }
  }
}
