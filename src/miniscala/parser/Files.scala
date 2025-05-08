package miniscala.parser

import miniscala.AbstractMachine.Executable
import miniscala.MiniScalaError

import java.io.*
import scala.util.parsing.input.NoPosition

object Files {

  def save(code: Executable, filename: String): Unit = {
    try {
      val oos = ObjectOutputStream(FileOutputStream(filename))
      oos.writeObject(code)
      oos.close()
    } catch {
      case e: IOException =>
        throw MiniScalaError(s"Unable to write file ${e.getMessage}", NoPosition)
    }
  }

  def load(filename: String): Executable = {
    try {
      val ois = ObjectInputStream(FileInputStream(filename))
      val code = ois.readObject.asInstanceOf[Executable]
      ois.close()
      code
    } catch {
      case e: IOException =>
        throw MiniScalaError(s"Unable to read file ${e.getMessage}", NoPosition)
    }
  }
}
