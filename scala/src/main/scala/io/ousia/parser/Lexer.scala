package io.ousia
package parser

import scala.util.parsing.combinator.RegexParsers
import io.ousia.exceptions.SyntaxException

object Lexer extends RegexParsers {

  def apply(src: String): Seq[Tokens.Token] = {
    parse(ousia, src) match {
      case Success(matched, _) => matched
      case Failure(msg, _) => throw new SyntaxException("FAILED: " + msg)
      case Error(msg, _) => throw new SyntaxException("ERR: " + msg)
    }
  }

  def ousia: Parser[Seq[Tokens.Token]] = rep(term)

  def term: Parser[Tokens.Token] =
    (number | literal | identifier | symbolic | code | nested)

  def number: Parser[Tokens.Number] = ("0" | """[1-9]\d*""".r) ^^ {
    case x => Tokens.Number(x, 10)
  }

  def literal: Parser[Tokens.Literal] = "\"" ~> """[^\"]*""".r <~ "\"" ^^ {
    case x => Tokens.Literal(x)
  }

  def identifier: Parser[Tokens.Identifier] = """[a-zA-Z_]+""".r ^^ {
    case x => Tokens.Identifier(x)
  }

  def symbolic: Parser[Tokens.Identifier] = """[<>=;\.,]+""".r ^^ {
    case x => Tokens.Identifier(x)
  }

  def code: Parser[Tokens.BraceBrackets] = "{" ~> ousia <~ "}" ^^ {
    case x => Tokens.BraceBrackets(x)
  }

  def nested: Parser[Tokens.RoundBrackets] = "(" ~> ousia <~ ")" ^^ {
    case x => Tokens.RoundBrackets(x)
  }
}
