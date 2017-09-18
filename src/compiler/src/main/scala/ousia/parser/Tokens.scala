package org.ousia
package parser

object Tokens {
  trait Token
  case class Identifier(s: String) extends Token
  case class Number(s: String, base: Integer) extends Token
  case class Literal(s: String) extends Token
  case class RoundBrackets(seq: Seq[Token]) extends Token
  case class SquareBrackets(seq: Seq[Token]) extends Token
  case class BraceBrackets(seq: Seq[Token]) extends Token
}
