package org.ousia
package parser

import exceptions.SyntaxException
import fastparse.all._
import Tokens._

object Lexer {

  def apply(src: String): Parsed[Block] = ousia.parse(src)

  val ousia: P[Block] = P(
    whitespace.rep ~
    token.rep(sep=whitespace.rep(1)).map(Block(_)) ~
    whitespace.rep
  )

  val word: P[Identifier] = P(CharIn('a' to 'z', 'A' to 'Z', "_").rep(1).!.map(Identifier(_)))
  val operator: P[Operator] = P(CharIn("\\|/!%&?^*+@#.,-√<>≤≥≠~‹›=").rep(1).!.map(Operator(_)))

  val token: P[Token] = P((
    word |
    operator |
    string |
    number |
    parentheses |
    brackets |
    braces
  ))

  val whitespace = P(line | space)
  // Semicolon, LF, and CRLF
  val line = P("\u000D".? ~ "\u000A")
  // All Unicode characters in the "Zs" category
  val space = P(CharIn(
    " ",
    "\u00A0",
    "\u1680",
    '\u2000' to '\u200A',
    "\u202F",
    "\u205F",
    "\u3000"
  ))

  val string: P[RawString] = P("\"" ~ (AnyChar.rep | ("\\" ~ AnyChar)).!.map(RawString(_)) ~ "\"")
  val character: P[RawChar] = P("'" ~ AnyChar.!.map(RawChar(_)) ~ "'")

  val number: P[Number] = P((float | int | intBin | intOct | intHex).!.map(Number(_, 10)))
  val int = P(CharIn('0' to '9') ~ CharIn('1' to '9').rep(1))
  val intBin = P("0b" ~ CharIn('0' to '1').rep(1))
  val intOct = P("0o" ~ CharIn('0' to '7').rep(1))
  val intHex = P("0x" ~ CharIn('0' to '9', 'A' to 'F').rep(1))
  val float = P(int ~ "." ~ CharIn('0' to '9').rep(1))

  val parentheses: P[Block] = P("(" ~ ousia ~ ")")
  val brackets: P[Block] = P("[" ~ ousia ~ "]")
  val braces: P[Block] = P("{" ~ ousia ~ "}")
}
