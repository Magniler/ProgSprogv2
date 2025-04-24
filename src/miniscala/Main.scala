package miniscala

import miniscala.Options
import miniscala.Unparser
import miniscala.parser.Parser

object Main {

  /**
    * The main entry of MiniScala.
    */
  def main(args: Array[String]): Unit = {
    try {
      // read the command-line arguments
      Options.read(args)
      val file = Options.file.get

      // parse the program
      val program = Parser.parse(Parser.readFile(file)).getOrElse(throw RuntimeException("the program did not parse"))



      // unparse the program, if enabled
      if (Options.unparse)
        println(Unparser.unparse(program, Map[String, Interpreter.Val]()))

      // type check the program, if enabled
      if (Options.types) {
        val initialTypeEnv = TypeChecker.makeInitialTypeEnv(program)
        TypeChecker.typeCheck(program, initialTypeEnv)
      }

      // execute the program, if enabled
      if (Options.run) {
        val initialEnv = Interpreter.makeInitialEnv(program)
        val result = Interpreter.eval(program, initialEnv)
        println(s"Output: ${Interpreter.valueToString(result)}")
      }

      // translate to lambda calculus, unparse, run, and decode result as a number, if enabled
      if (Options.lambda) {
        val encoded = Lambda.encode(program)
        println(s"Encoded program: ${Unparser.unparse(encoded)}")
        val initialEnv = Lambda.makeInitialEnv(program)
        val result = Interpreter.eval(encoded, initialEnv)
        println(s"Output from encoded program: ${Interpreter.valueToString(result)}")
        println(s"Decoded output: ${Lambda.decodeNumber(result)}")
      }

    } catch { // report all errors to the console
      case e: Options.OptionsError =>
        println(e.getMessage)
        println(Options.usage)
      case e: MiniScalaError =>
        println(e.getMessage)
    }
  }
}
