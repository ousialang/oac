package org.ousia
package parser

import Tokens._

object Statements {
  sealed trait Statement
  case class Val(name: String, term: Token) extends Statement
  case class Var(name: String, term: Token) extends Statement
  case class Function(name: Identifier, args: Seq[Identifier], term: Token) extends Statement
}
