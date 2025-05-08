package miniscala

import miniscala.parser.{Files, Parser}

object Main {

  /**
    * The main entry of MiniScala.
    */
  def main(args: Array[String]): Unit = {
    try {
      // read the command-line arguments
      Options.read(args)
      val file = Options.file.get

      // load and execute abstract machine code, if enabled
      if (Options.machine) {
        val bin = Files.load(file)
        println(s"Executable (symbolic form): $bin")
        val initialEnv = AbstractMachine.makeInitialEnv(bin)
        time {
          val result = AbstractMachine.execute(bin, initialEnv)
          println(s"Output: $result")
        }

      } else {

        // parse the program
        val program = Parser.parse(Parser.readFile(file))

        // unparse the program, if enabled
        if (Options.unparse)
          println(Unparser.unparse(program))

        // type check the program, if enabled
        if (Options.types) {
          val initialTypeEnv = TypeChecker.makeInitialTypeEnv(program)
          TypeChecker.typeCheck(program, initialTypeEnv, Map())
        }

        // execute the program, if enabled
        if (Options.run) {
          val initialEnv = Interpreter.makeInitialEnv(program)
          time {
            val (result, _) = Interpreter.eval(program, initialEnv, Map(), Map())
            println(s"Output: ${Interpreter.valueToString(result)}")
          }
        }

        // compile to abstract machine code, if enabled
        if (Options.compile) {
          val outfile = (if (file.endsWith(".s")) file.substring(0, file.length - 2) else file) + ".sam"
          val bin = Compiler.compile(program)
          println(s"Executable (symbolic form): $bin")
          println(s"Writing executable to $outfile")
          Files.save(bin, outfile)
        }

      }

    } catch { // report all errors to the console
      case e: Options.OptionsError =>
        println(e.getMessage)
        println(Options.usage)
      case e: MiniScalaError =>
        println(e.getMessage)
    }
  }

  def time(block: => Unit): Unit = {
    val t0 = System.nanoTime()
    block
    val t1 = System.nanoTime()
    println("Elapsed time: " + (t1 - t0)/1000000 + "ms")
  }
}
