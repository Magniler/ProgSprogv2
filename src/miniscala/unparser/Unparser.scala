package miniscala

import miniscala.Ast.*
import miniscala.Interpreter.{BoolVal, ClosureVal, FloatVal, IntVal, StringVal, Val, eval}

object Unparser {

  type Env = Map[Id, Val]

  // Unparser for MiniScala.
  def unparse(n: AstNode, env: Env): String = n match {
    case IntLit(c) => c.toString
    case BoolLit(c) => c.toString
    case FloatLit(c) => c.toString
    case StringLit(c) => c
    case IntType() => ": Int"
    case BoolType() => ": Bool"
    case FloatType() => ": Float"
    case StringType() => ": String"
    case VarExp(x) => x
    case BinOpExp(leftexp, op, rightexp) =>
      op match {
        case PlusBinOp() =>
          unparse(leftexp, env) + " + " + unparse(rightexp, env)
        case MinusBinOp() =>
          unparse(leftexp, env) + " - " + unparse(rightexp, env)
        case MultBinOp() =>
          unparse(leftexp, env) + " * " + unparse(rightexp, env)
        case DivBinOp() =>
          if (eval(rightexp, env) == IntVal(0))
            throw UnparserError(s"Division by zero", n)
          unparse(leftexp, env) + " / " + unparse(rightexp, env)
        case ModuloBinOp() =>
          unparse(leftexp, env) + " % " + unparse(rightexp, env)
        case MaxBinOp() =>
          "max(" + unparse(leftexp, env) + ", " + unparse(rightexp, env) + ")"
        case AndBinOp() =>
          unparse(leftexp, env) + " & " + unparse(rightexp, env)
        case OrBinOp() =>
          unparse(leftexp, env) + " | " + unparse(rightexp, env)
        case EqualBinOp() =>
          unparse(leftexp, env) + " == " + unparse(rightexp, env)
        case LessThanBinOp() =>
          unparse(leftexp, env) + " < " + unparse(rightexp, env)
        case LessThanOrEqualBinOp() =>
          unparse(leftexp, env) + " <= " + unparse(rightexp, env)

      }
    case UnOpExp(op, exp) =>
      op match {
        case NegUnOp() => "-" + unparse(exp, env)
      }
    case BlockExp(vals, defs, exp) =>
      var env1 = Map[Id, Val]()
      for (d <- vals)
        env1 = env1 + (d.x -> eval(d.exp, env1))
      unparse(exp, env)
    case TupleExp(exps) =>
      var res: String = ""
      for (c <- exps){
        res = res + unparse(c, env) + ","
      }
      "(" + res + ")"
    case IfThenElseExp(condexp, thenexp, elseexp) => "if " + unparse(condexp, env) + " then " + unparse(thenexp, env) + " else " + unparse(elseexp, env)
    case MatchExp(exp, cases) =>
      var res: String = "match " + unparse(exp, env)
      for (c <- cases){
        res = res + unparse(c, env) + "\n"
      }
      res
    case MatchCase(pat, exp) => "(" + pat +  ")" + " => " + unparse(exp, env)
    case CallExp(fun, args) =>
      var argsEval: String = ""
      for (c <- args){
        argsEval = argsEval + unparse(c, env) + ","
      }
      fun + "(" + argsEval + ")"
    case ValDecl(x, opttype, exp) =>
      "val " + x + ": " + opttype + " = " + unparse(exp, env)
    case DefDecl(fun, params, rtype, exp) =>
      var unparsePara: String = ""
      var env1 = env
      for (para <- params){
        unparsePara = unparsePara + ", " + unparse(para, env1)
      }
      "def " + fun + "(" + unparsePara + ")" + ": " + rtype + " = {" + unparse(exp, env) + "}"
    case FunParam(x, optype) => x + ": " + optype
  }

  def unparse(ot: Option[Type]): String = ot match {
    case Some(t) => ": " + unparse(Option(t))
    case None => ""
  }
} // this unparse function can be used for all kinds of AstNode objects, including Exp objects (see Ast.scala)

/**
 * Exception thrown in case of MiniScala runtime errors.
 */
class UnparserError(msg: String, node: AstNode) extends MiniScalaError(s"Runtime error: $msg", node.pos)