package io.ousia
package parser

object Tokens {

  trait Token
  trait NestedToken extends Token

  case class Identifier(s: String) extends Token
  case class Number(s: String, base: Integer) extends Token
  case class Literal(s: String) extends Token

  case class RoundBrackets(seq: Seq[Token]) extends NestedToken
  case class SquareBrackets(seq: Seq[Token]) extends NestedToken
  case class BraceBrackets(seq: Seq[Token]) extends NestedToken
}
