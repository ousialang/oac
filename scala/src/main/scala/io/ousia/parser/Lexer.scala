package ousia.parser

import scala.util.parsing.combinator.RegexParsers
import ousia.exceptions.SyntaxException
import Tokens._

object Lexer extends RegexParsers {

  def apply(src: String): Seq[Token] = {
    parse(ousia, src) match {
      case Success(matched, _) => matched
      case Failure(msg, _) => throw new SyntaxException("FAILED: " + msg)
      case Error(msg, _) => throw new SyntaxException("ERR: " + msg)
    }
  }

  def ousia: Parser[Seq[Token]] = rep(term)

  def comment: Parser[Comment] = inlineComment | multilineComment

  def inlineComment: Parser[Comment] = "//"

  def multilineComment: Parser[Comment] = "/*" <~ """.*?""".r ~> "*/"

  def term: Parser[Token] =
    (number | literal | identifier | symbolic | code | nested)

  def number: Parser[Number] = ("0" | """[1-9]\d*""".r) ^^ {
    case x => Tokens.Number(x, 10)
  }

  def literal: Parser[Literal] = "\"" ~> """[^\"]*""".r <~ "\"" ^^ {
    case x => Tokens.Literal(x)
  }

  def identifier: Parser[Identifier] = """[a-zA-Z_]+""".r ^^ {
    case x => Tokens.Identifier(x)
  }

  def symbolic: Parser[Identifier] = """[<>=;\.,]+""".r ^^ {
    case x => Tokens.Identifier(x)
  }

  def code: Parser[BraceBrackets] = "{" ~> ousia <~ "}" ^^ {
    case x => Tokens.BraceBrackets(x)
  }

  def nested: Parser[RoundBrackets] = "(" ~> ousia <~ ")" ^^ {
    case x => Tokens.RoundBrackets(x)
  }
}
