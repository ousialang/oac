package ousia.util

import ousia.parser.Tokens

object Parsing {

  def splitBySemicolons(tokens: Seq[Tokens.Token]): Seq[Seq[Tokens.Token]] = {
    if (tokens contains Tokens.Identifier(";")) {
      val semicolonIndex = tokens indexOf Tokens.Identifier(";")
      val branches = tokens splitAt semicolonIndex
      // The semicolon is included in the right branch               ~~~~~
      splitBySemicolons(branches._1) ++ splitBySemicolons(branches._2.tail)
    } else {
      Seq(tokens)
    }
  }

  def matchArgsList(tokens: Seq[Tokens.Token]): Unit /*(Seq[String], Seq[Tokens.Token])*/ = {
    val expectedComma = false
    def expectedIdentifier = !expectedComma
    var index = 1
  }
}
