package io.ousia

object Application {

  def main(args: Array[String]): Unit = args.size match {
    case 0 => usage
    case 1 => {
      val source = scala.io.Source.fromFile(args.head)
      val text = source.mkString
      source.close()
    }
  }
}
