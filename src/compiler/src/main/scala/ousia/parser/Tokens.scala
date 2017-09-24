package org.ousia
package parser

object Tokens {
  trait Token
  case class Block(t: Seq[Token]) extends Token
  case class Operator(s: String) extends Token
  case class Identifier(s: String) extends Token
  case class Number(s: String, base: Int) extends Token
  case class RawString(s: String) extends Token
  case class RawChar(s: String) extends Token
  case class Parentheses(t: Token) extends Token
  case class Brackets(t: Token) extends Token
  case class Braces(t: Token) extends Token
}
