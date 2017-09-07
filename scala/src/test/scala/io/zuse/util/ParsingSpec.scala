package io.zuse
package util

import scala.io.Source
import org.scalatest.{WordSpec, Matchers}
import io.zuse.parser.Tokens

class ParsingSpec extends WordSpec with Matchers {

  "‹Parsing.splitBySemicolons›" when {
    "the source contains only semicolons" should {
      val tokens = Seq.fill(3)(Tokens.Identifier(";"))
      "return empty statements" in {
        assert(Parsing.splitBySemicolons(tokens) forall (_.isEmpty))
      }
    }
    "the source is empty" should {
      val split = Parsing.splitBySemicolons(Seq.empty)
      "return no statement" in {
        assert(split.size == 1)
        assert(split.head.isEmpty)
      }
    }
    "the source contains no semicolons" should {
      val tokens = Seq(
        Tokens.Identifier("package"),
        Tokens.Identifier("abc")
      )
      val split = Parsing.splitBySemicolons(tokens)
      "return a single statement equal to the tokenized source" in {
        split.size shouldBe 1
        split.head shouldBe tokens
      }
    }
  }
}
