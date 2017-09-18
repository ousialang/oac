package org.ousia

object Application {

  def main(args: Array[String]): Unit = {
    if (args.size == 0) {
      println(usage)
    } else {
      val command = commands(args(0))
      command match {
        case build => None
      }
    }
  }

  val usage = "Usage: ousia ‹action› ‹options›"

  val build: Command = Command("build", "Builds and compiles a project.", 0)
  val clean: Command = Command("clean", "Cleans and correclty formats a Ousia project.", 0)

  val commands: Map[String, Command] = (List(build, clean) map (c => c.name -> c)).toMap

  case class Command(name: String, description: String, argv: Int)
  case class Option(name: String, abbreviation: String, description: String, argv: Int)
}
