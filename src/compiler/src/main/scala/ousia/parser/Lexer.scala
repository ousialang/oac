package org.ousia
package parser

import exceptions.SyntaxException
import fastparse.all._

object Lexer {

  def apply(src: String) {
    println(ousia.parse(src))
  }

  val ousia = P((word ~ " ".?).rep(1))
  val word = P((CharIn('a' to 'z') | CharIn('A' to 'Z') | "_").rep(1).!)
  val symbol = P(CharIn("\\|/!%&?^*+@#.,-<>≤≥≠~‹›").rep(1) | "==")

  val break = P(";" | "\n")

  val number = P(int | intBin | intOct | intHex | float)
  val int = P(CharIn('0' to '9').rep(1))
  val intBin = P("0b" ~ ("0" | "1").rep(1))
  val intOct = P("0o" ~ ("0" | "7").rep(1))
  val intHex = P("0x" ~ ("0" | "f").rep(1))
  val float = P(int~ "." ~ CharIn('0' to '9').rep(1))
}
