package io.ousia
package parser

import Tokens._

object Statements {

  trait Statement

  case class Val(id: String, term: Token) extends Statement
  case class Var(id: String, term: Token) extends Statement
  case class Package(pkg: Seq[Identifier]) extends Statement
  case class Function(name: Identifier, args: Seq[Identifier], term: Token) extends Statement
}
