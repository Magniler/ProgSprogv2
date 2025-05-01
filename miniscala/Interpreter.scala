package miniscala

import miniscala.Ast.*
import miniscala.Unparser.unparse

import scala.io.StdIn

/**
  * Interpreter for MiniScala.
  */
object Interpreter {

  sealed abstract class Val
  case class IntVal(v: Int) extends Val
  case class BoolVal(v: Boolean) extends Val
  case class FloatVal(v: Float) extends Val
  case class StringVal(v: String) extends Val
  case class TupleVal(vs: List[Val]) extends Val
  case class ClosureVal(params: List[FunParam], optrestype: Option[Type], body: Exp, env: Env) extends Val
  case class RefVal(loc: Loc, opttype: Option[Type]) extends Val

  val unitVal: Val = TupleVal(Nil)

  type Env = Map[Id, Val]

  type Sto = Map[Loc, Val]

  type Loc = Int

  def nextLoc(sto: Sto): Loc = sto.size

  /**
    * Evaluates an expression.
    */
  def eval(e: Exp, env: Env, sto: Sto): (Val, Sto) = e match {
    case IntLit(c) => (IntVal(c), sto)
    case BoolLit(c) => ???
    case FloatLit(c) => ???
    case StringLit(c) => ???
    case VarExp(x) =>
      env.getOrElse(x, throw InterpreterError(s"Unknown identifier '$x'", e)) match {
        case RefVal(loc, _) => (sto(loc), sto)
        case v: Val => (v, sto)
      }
    case BinOpExp(leftexp, op, rightexp) =>
      val (leftval, sto1) = eval(leftexp, env, sto)
      val (rightval, sto2) = eval(rightexp, env, sto1)
      op match {
        case PlusBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (IntVal(v1 + v2), sto2)
            case (FloatVal(v1), FloatVal(v2)) => (FloatVal(v1 + v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (FloatVal(v1 + v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (FloatVal(v1 + v2), sto2)
            case (StringVal(v1), StringVal(v2)) => (StringVal(v1 + v2), sto2)
            case (StringVal(v1), IntVal(v2)) => (StringVal(v1 + v2.toString), sto2)
            case (StringVal(v1), FloatVal(v2)) => (StringVal(v1 + v2.toString), sto2)
            case (IntVal(v1), StringVal(v2)) => (StringVal(v1.toString + v2), sto2)
            case (FloatVal(v1), StringVal(v2)) => (StringVal(v1.toString + v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '+', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case MinusBinOp() => ???
        case MultBinOp() => ???
        case DivBinOp() =>
          if (rightval == IntVal(0) || rightval == FloatVal(0.0f))
            throw InterpreterError(s"Division by zero", op)
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (IntVal(v1 / v2), sto2)
            case (FloatVal(v1), FloatVal(v2)) => (FloatVal(v1 / v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (FloatVal(v1 / v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (FloatVal(v1 / v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '/', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case ModuloBinOp() => ???
        case EqualBinOp() => ???
        case LessThanBinOp() => ???
        case LessThanOrEqualBinOp() => ???
        case MaxBinOp() => ???
        case AndBinOp() => ???
        case OrBinOp() => ???
      }
    case UnOpExp(op, exp) =>
      val (expval, sto1) = eval(exp, env, sto)
      op match {
        case NegUnOp() =>
          expval match {
            case IntVal(v) => (IntVal(-v), sto1)
            case FloatVal(v) => (FloatVal(-v), sto1)
            case _ => throw InterpreterError(s"Type mismatch at '-', unexpected value ${valueToString(expval)}", op)
          }
        case NotUnOp() => ???
      }
    case IfThenElseExp(condexp, thenexp, elseexp) => ???
    case b @ BlockExp(vals, vars, defs, exps) =>
      var env1 = env
      var sto1 = sto
      for (d <- vals ++ vars ++ defs) {
        val (env2, sto2) = eval(d, env1, sto1, b)
        env1 = env2
        sto1 = sto2
      }
      var v1 = unitVal
      for (e <- exps) {
        val (v2, sto2) = eval(e, env1, sto1)
        v1 = v2
        sto1 = sto2
      }
      (v1, sto1)
    case TupleExp(exps) =>
      var (vals, sto1) = (List[Val](), sto)
      for (exp <- exps) {
        val (v, sto2) = eval(exp, env, sto1)
        vals = v :: vals
        sto1 = sto2
      }
      (TupleVal(vals.reverse), sto1)
    case MatchExp(exp, cases) =>
      val (expval, sto1) = eval(exp, env, sto)
      expval match {
        case TupleVal(vs) =>
          var res: Option[(Val, Sto)] = None
          for (c <- cases) {
            if (vs.length == c.pattern.length) {
              ???
            }
          }
          res match {
            case Some(v) => v
            case None => throw InterpreterError(s"No case matches value ${valueToString(expval)}", e)
          }
        case _ => throw InterpreterError(s"Tuple expected at match, found ${valueToString(expval)}", e)
      }
    case CallExp(funexp, args) =>
      ???
    case LambdaExp(params, body) =>
      ???
    case AssignmentExp(x, exp) =>
      ???
    case WhileExp(cond, body) =>
      ???
  }

  /**
    * Evaluates a declaration.
    */
  def eval(d: Decl, env: Env, sto: Sto, b: BlockExp): (Env, Sto) = d match {
    case ValDecl(x, opttype, exp) =>
      val (v, sto1) = eval(exp, env, sto)
      val env1 = env + (x -> v)
      (env1, sto1)
    case VarDecl(x, opttype, exp) =>
      ???
    case DefDecl(fun, params, optrestype, body) =>
      ???
  }

  /**
    * Checks whether value `v` has type `ot` (if present), generates runtime type error otherwise.
    */
  def checkValueType(v: Val, ot: Option[Type], n: AstNode): Unit = ot match {
    case Some(t) =>
      (v, t) match {
        case (IntVal(_), IntType()) |
             (BoolVal(_), BoolType()) |
             (FloatVal(_), FloatType()) |
             (IntVal(_), FloatType()) |
             (StringVal(_), StringType()) => // do nothing
        case (TupleVal(vs), TupleType(ts)) if vs.length == ts.length =>
          for ((vi, ti) <- vs.zip(ts))
            checkValueType(vi, Some(ti), n)
        case (ClosureVal(cparams, optcrestype, _, _), FunType(paramtypes, restype)) if cparams.length == paramtypes.length =>
          for ((p, t) <- cparams.zip(paramtypes))
            checkTypesEqual(t, p.opttype, n)
          checkTypesEqual(restype, optcrestype, n)
        case _ =>
          throw InterpreterError(s"Type mismatch: value ${valueToString(v)} does not match type ${unparse(t)}", n)
      }
    case None => // do nothing
  }

  /**
    * Checks that the types `t1` and `ot2` are equal (if present), throws type error exception otherwise.
    */
  def checkTypesEqual(t1: Type, ot2: Option[Type], n: AstNode): Unit = ot2 match {
    case Some(t2) =>
      if (t1 != t2)
        throw InterpreterError(s"Type mismatch: type ${unparse(t1)} does not match type ${unparse(t2)}", n)
    case None => // do nothing
  }

  /**
    * Converts a value to its string representation (for error messages).
    */
  def valueToString(v: Val): String = v match {
    case IntVal(c) => c.toString
    case FloatVal(c) => c.toString
    case BoolVal(c) => c.toString
    case StringVal(c) => c
    case TupleVal(vs) => vs.map(valueToString).mkString("(", ",", ")")
    case ClosureVal(params, _, exp, _) => // the resulting string ignores the result type annotation and the declaration environment
      s"<(${params.map(unparse).mkString(",")}), ${unparse(exp)}>"
    case RefVal(loc, _) => s"#$loc" // the resulting string ignores the type annotation
  }

  /**
    * Builds an initial environment, with a value for each free variable in the program.
    */
  def makeInitialEnv(program: Exp): Env = {
    var env = Map[Id, Val]()
    for (x <- Vars.freeVars(program)) {
      print(s"Please provide an integer value for the variable $x: ")
      env = env + (x -> IntVal(StdIn.readInt()))
    }
    env
  }

  /**
    * Prints message if option -trace is used.
    */
  def trace(msg: String): Unit =
    if (Options.trace)
      println(msg)

  /**
    * Exception thrown in case of MiniScala runtime errors.
    */
  class InterpreterError(msg: String, node: AstNode) extends MiniScalaError(s"Runtime error: $msg", node.pos)
}
