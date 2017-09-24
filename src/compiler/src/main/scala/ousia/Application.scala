package org.ousia

import parser.Lexer

object Application {

  def main(args: Array[String]): Unit = {
    if (args.size == 0) {
      println(usage)
    // Check if the given command name is known
    } else if (commands contains args(0)) {
      commands(args(0)) match {
        case build => println(Lexer("hello word 0xEFFE 123.987 ++++"))
      }
    } else {
      println(wrongCommand(args(0)))
    }
  }

  // Scala bug: string interpolation doesn't work with escapes
  val wrongCommand = (s: String) => "\"" + s + "\" is not an Ousia command."
  val usage = "Usage: ousia ‹action› ‹options›"

  val build: Command = Command("build", "Builds and compiles a project.", 0)
  val clean: Command = Command("clean", "Cleans and correclty formats a Ousia project.", 0)

  val commands: Map[String, Command] = (List(build, clean) map (c => c.name -> c)).toMap

  case class Command(name: String, description: String, argv: Int)
  case class Option(name: String, abbreviation: String, description: String, argv: Int)
}
