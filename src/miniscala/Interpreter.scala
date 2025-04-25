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

  case class ClosureVal(params: List[FunParam], optrestype: Option[Type], body: Exp,
                        env: Env) extends Val

  type Env = Id => Option[Val]

  def makeEmpty(): Env =
    (x: Id) => None

  def getOrElse(env: Env, id: Id, default: => Val): Val =
    env(id).getOrElse(default)

  def extend(e: Env, x: Id, v: Val): Env =
    (y: Id) => if (x == y) Some(v) else e(y)

  def extendWithClosure(env: Env, d: DefDecl): Env = {
    def env2(y: Id): Option[Val] =
      extend(env, d.fun, ClosureVal(d.params, d.optrestype, d.body, env2))(y)
    env2
  }

  def extendWithClosures(env: Env, defs: List[DefDecl]): Env = {
    def env2(y: Id): Option[Val] =
      defs.foldLeft(env)((env3, d) => extend(env3, d.fun, ClosureVal(d.params, d.optrestype, d.body, env2)))(y)

    env2
  }

  /**
   * Evaluates an expression.
   */
  def eval(e: Exp, env: Env): Val = e match {
    case IntLit(c) => IntVal(c)
    case BoolLit(c) => BoolVal(c)
    case FloatLit(c) => FloatVal(c)
    case StringLit(c) => StringVal(c)
    case VarExp(x) =>
      getOrElse(env, x, throw InterpreterError(s"Unknown identifier '$x'", e))
    case BinOpExp(leftexp, op, rightexp) =>
      val leftval = eval(leftexp, env)
      val rightval = eval(rightexp, env)
      op match {
        case PlusBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => IntVal(v1 + v2)
            case (FloatVal(v1), FloatVal(v2)) => FloatVal(v1 + v2)
            case (IntVal(v1), FloatVal(v2)) => FloatVal(v1 + v2)
            case (FloatVal(v1), IntVal(v2)) => FloatVal(v1 + v2)
            case (StringVal(v1), StringVal(v2)) => StringVal(v1 + v2)
            case (StringVal(v1), IntVal(v2)) => StringVal(v1 + v2.toString)
            case (StringVal(v1), FloatVal(v2)) => StringVal(v1 + v2.toString)
            case (IntVal(v1), StringVal(v2)) => StringVal(v1.toString + v2)
            case (FloatVal(v1), StringVal(v2)) => StringVal(v1.toString + v2)
            case _ => throw InterpreterError(s"Type mismatch at '+', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case MinusBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => IntVal(v1 - v2)
            case (FloatVal(v1), FloatVal(v2)) => FloatVal(v1 - v2)
            case (IntVal(v1), FloatVal(v2)) => FloatVal(v1 - v2)
            case (FloatVal(v1), IntVal(v2)) => FloatVal(v1 - v2)
            case (StringVal(v1), IntVal(v2)) => IntVal(v1.toInt - v2)
            case (StringVal(v1), FloatVal(v2)) => FloatVal(v1.toFloat - v2)
            case (IntVal(v1), StringVal(v2)) => FloatVal(v1 - v2.toFloat)
            case (FloatVal(v1), StringVal(v2)) => FloatVal(v1 - v2.toFloat)
            case _ => throw InterpreterError(s"Type mismatch at '-', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case MultBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => IntVal(v1 * v2)
            case (FloatVal(v1), FloatVal(v2)) => FloatVal(v1 * v2)
            case (IntVal(v1), FloatVal(v2)) => FloatVal(v1 * v2)
            case (FloatVal(v1), IntVal(v2)) => FloatVal(v1 * v2)
            case (StringVal(v1), IntVal(v2)) => StringVal(v1 * v2)
            case (StringVal(v1), FloatVal(v2)) => StringVal(v1 * v2.toInt)
            case (IntVal(v1), StringVal(v2)) => StringVal(v2 * v1)
            case (FloatVal(v1), StringVal(v2)) => StringVal(v2 * v1.toInt)
            case _ => throw InterpreterError(s"Type mismatch at '*', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case DivBinOp() =>
          if (rightval == IntVal(0) || rightval == FloatVal(0.0f))
            throw InterpreterError(s"Division by zero", op)
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => IntVal(v1 / v2)
            case (FloatVal(v1), FloatVal(v2)) => FloatVal(v1 / v2)
            case (IntVal(v1), FloatVal(v2)) => FloatVal(v1 / v2)
            case (FloatVal(v1), IntVal(v2)) => FloatVal(v1 / v2)
            case _ => throw InterpreterError(s"Type mismatch at '/', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case ModuloBinOp() =>
          if (rightval == IntVal(0) || rightval == FloatVal(0.0f))
            throw InterpreterError(s"Module by zero (divsiion by zero)", op)
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => IntVal(v1 % v2)
            case (FloatVal(v1), FloatVal(v2)) => FloatVal(v1 % v2)
            case (IntVal(v1), FloatVal(v2)) => FloatVal(v1 % v2)
            case (FloatVal(v1), IntVal(v2)) => FloatVal(v1 % v2)
            case _ => throw InterpreterError(s"Type mismatch at '%', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case EqualBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => BoolVal(v1 == v2)
            case (FloatVal(v1), IntVal(v2)) => BoolVal(v1 == v2)
            case (IntVal(v1), FloatVal(v2)) => BoolVal(v1 == v2)
            case (StringVal(v1), IntVal(v2)) => BoolVal(v1 == v2.toString)
            case (IntVal(v1), StringVal(v2)) => BoolVal(v1.toString == v2)
            case (BoolVal(v1), BoolVal(v2)) => BoolVal(v1 == v2)
            case _ => throw InterpreterError(s"Type mismatch at '==', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case LessThanBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => BoolVal(v1 < v2)
            case (FloatVal(v1), IntVal(v2)) => BoolVal(v1 < v2)
            case (IntVal(v1), FloatVal(v2)) => BoolVal(v1 < v2)
            case _ => throw InterpreterError(s"Type mismatch at '<', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case LessThanOrEqualBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => BoolVal(v1 <= v2)
            case (FloatVal(v1), IntVal(v2)) => BoolVal(v1 <= v2)
            case (IntVal(v1), FloatVal(v2)) => BoolVal(v1 <= v2)
            case _ => throw InterpreterError(s"Type mismatch at '<=', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case MaxBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => IntVal(v1)
              if v1 > v2 then IntVal(v1) else IntVal(v2)
            case (FloatVal(v1), IntVal(v2)) =>
              if v1 > v2 then FloatVal(v1) else FloatVal(v2)
            case (IntVal(v1), FloatVal(v2)) =>
              if v1 > v2 then FloatVal(v1) else FloatVal(v2)
            case _ => throw InterpreterError(s"Type mismatch at 'Max', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
            case AndBinOp() =>
              (leftval, rightval) match {
                case (BoolVal(v1), BoolVal(v2)) => BoolVal(v1 & v2)
                case _ => throw InterpreterError(s"Type mismatch at '&', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
              }
            case OrBinOp() =>
              (leftval, rightval) match {
                case (BoolVal(v1), BoolVal(v2)) => BoolVal(v1 | v2)
                case _ => throw InterpreterError(s"Type mismatch at '&', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
              }
          }
      }
    case UnOpExp(op, exp) =>
      val expval = eval(exp, env)
      op match {
        case NegUnOp() =>
          expval match {
            case IntVal(v) => IntVal(-v)
            case FloatVal(v) => FloatVal(-v)
            case _ => throw InterpreterError(s"Type mismatch at '-', unexpected value ${valueToString(expval)}", op)
          }
        case NotUnOp() =>
          expval match {
            case BoolVal(v) => BoolVal(!v)
            case _ => throw InterpreterError(s"Type mismatch at '!', unexpected value ${valueToString(expval)}", op)
          }
      }
    case IfThenElseExp(condexp, thenexp, elseexp) =>
      eval(condexp, env) match {
        case BoolVal(true) => eval(thenexp, env)
        case BoolVal(false) => eval(elseexp, env)
        case _ => throw InterpreterError("Condition must be boolean", condexp)
      }
    case b@BlockExp(vals, defs, exp) =>
      var env1 = env
      for (d <- vals ++ defs)
        env1 = eval(d, env1, b)
      eval(exp, env1)
    case TupleExp(exps) =>
      var vals = List[Val]()
      for (exp <- exps)
        vals = eval(exp, env) :: vals
      TupleVal(vals.reverse)
    case MatchExp(exp, cases) =>
      val expval = eval(exp, env)
      expval match {
        case TupleVal(vs) =>
          var matchResult: Option[Val] = None
          // Iterate through cases to find the first match
          for (c <- cases if matchResult.isEmpty) {
            if (c.pattern.length == vs.length) {
              var newEnv = env
              for ((patternVar, value) <- c.pattern.zip(vs)) {
                newEnv = extend(newEnv, patternVar, value)
              }
              // Evaluate the case expression in the new environment
              matchResult = Some(eval(c.exp, newEnv))
            }
          }
          // Return the result or throw an error if no match found
          matchResult match {
            case Some(value) => value
            case None => throw InterpreterError(s"No case matches value ${valueToString(expval)}", e)
          }
        case _ =>
          throw InterpreterError(s"Tuple expected at match, found ${valueToString(expval)}", e)
      }
    case CallExp(funexp, args) =>
      val funVal = eval(funexp, env)
      funVal match {
        case ClosureVal(params, optrestype, body, closureEnv) =>
          if (args.length != params.length) {
            throw InterpreterError(
              s"Function called with ${args.length} arguments but expects ${params.length} parameters",
              e
            )
          }
          // evaluate all arguments in the current environment, not the new enviroment
          val argVals = args.map(arg => eval(arg, env))
          // Start on new env
          var newEnv = makeEmpty()
          // bind parameters to their argument values
          for ((param, argVal) <- params.zip(argVals)) {
            newEnv = extend(newEnv, param.x, argVal)
          }
          // Type checking if necessary
          for ((param, argVal) <- params.zip(argVals)) {
            checkValueType(argVal, param.opttype, e)
          }
          val result = eval(body, newEnv)
          checkValueType(result, optrestype, e)
          result
        case _ =>
          throw InterpreterError(s"Expected a function but found ${valueToString(funVal)}", funexp)
      }
    case LambdaExp(params, body) =>
      // Create a closure with type annotations
      ClosureVal(params, None, body, env)
  }

      /**
       * Evaluates a declaration.
       */
      def eval(d: Decl, env: Env, b: BlockExp): Env = d match {
        case ValDecl(x, opttype, exp) =>
          extend(env, x, eval(exp, env))
        case DefDecl(fun, params, optrestype, body) =>
          // Create a mute-Map to allow for self-reference
          val recursiveEnv = env
          val closure = ClosureVal(params, optrestype, body, recursiveEnv)
          // Update the env
          extend(recursiveEnv, fun, closure)
          // We Return the updated original environment
          extend(env, fun, closure)
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
              throw InterpreterError(s"Type mismatch: value ${valueToString(v)} does not match type ${unparse(Option(t))}", n)
          }
        case None => // do nothing
      }

      /**
       * Checks that the types `t1` and `ot2` are equal (if present), throws type error exception otherwise.
       */
      def checkTypesEqual(t1: Type, ot2: Option[Type], n: AstNode): Unit = ot2 match {
        case Some(t2) =>
          if (t1 != t2)
            throw InterpreterError(s"Type mismatch: type ${unparse(Option(t1))} does not match type ${unparse(Option(t2))}", n)
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
        case ClosureVal(params, _, _, _) => // the resulting string ignores the result type annotation and the declaration environment
          // Simple format: <function: (param1, param2, ...)>
          val paramStr = params.map(_.x).mkString(", ")
          s"<function: ($paramStr)>"
      }

      /**
       * Builds an initial environment, with a value for each free variable in the program.
       */
      def makeInitialEnv(program: Exp): Env = {
        var env = makeEmpty()
        for (x <- Vars.freeVars(program)) {
          print(s"Please provide an integer value for the variable $x: ")
          env = extend(env, x, IntVal(StdIn.readInt()))
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