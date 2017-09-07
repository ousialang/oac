package io.zuse
package parser

import scala.io.Source
import org.scalatest.{WordSpec, Matchers}


class ParserSpec extends WordSpec with Matchers {

  "A .zuse source file" when {
    "empty" should {
      "not produce any code" in {
        Lexer("") shouldBe Seq()
      }
    }
    "containing a single ‹package› statement" should {
      val tokens = Seq(
        Tokens.Identifier("package"),
        Tokens.Identifier("abc"),
        Tokens.Identifier("."),
        Tokens.Identifier("xyz")
      )
      "return a well-formed ‹Package› instance" in {
        Parser(tokens).head shouldBe Statements.Package(Seq(tokens(1), tokens(3)))
      }
    }
  }
}
