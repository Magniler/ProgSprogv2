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
  case class ClosureVal(params: List[FunParam], optrestype: Option[Type], body: Exp, env: Env, cenv: ClassEnv) extends Val
  case class RefVal(loc: Loc, opttype: Option[Type]) extends Val
  case class ObjRefVal(loc: Loc) extends Val
  case class ObjectVal(members: Env) extends Val

  val unitVal: Val = TupleVal(Nil)

  case class Constructor(params: List[FunParam], body: BlockExp, env: Env, cenv: ClassEnv, classes: List[ClassDecl])

  type Env = Map[Id, Val]

  type ClassEnv = Map[Id, Constructor]

  type Sto = Map[Loc, Val]

  type Loc = Int

  def nextLoc(sto: Sto): Loc = sto.size

  /**
   * Evaluates an expression.
   */
  def eval(e: Exp, env: Env, cenv: ClassEnv, sto: Sto): (Val, Sto) = e match {
    case IntLit(c) => (IntVal(c), sto)
    case BoolLit(c) => (BoolVal(c), sto)
    case FloatLit(c) => (FloatVal(c), sto)
    case StringLit(c) => (StringVal(c), sto)
    case VarExp(x) =>
      (getValue(env.getOrElse(x, throw InterpreterError(s"Unknown identifier '$x'", e)), sto), sto)
    case BinOpExp(leftexp, op, rightexp) =>
      val (leftval, sto1) = eval(leftexp, env, cenv, sto)
      val (rightval, sto2) = eval(rightexp, env, cenv, sto1)
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
        case MinusBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (IntVal(v1 - v2), sto2)
            case (FloatVal(v1), FloatVal(v2)) => (FloatVal(v1 - v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (FloatVal(v1 - v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (FloatVal(v1 - v2), sto2)
            case (StringVal(v1), IntVal(v2)) => (IntVal(v1.toInt - v2), sto2)
            case (StringVal(v1), FloatVal(v2)) => (FloatVal(v1.toFloat - v2), sto2)
            case (IntVal(v1), StringVal(v2)) => (FloatVal(v1 - v2.toFloat), sto2)
            case (FloatVal(v1), StringVal(v2)) => (StringVal(v1 - v2.toFloat), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '-', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case MultBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (IntVal(v1 * v2), sto2)
            case (FloatVal(v1), FloatVal(v2)) => (FloatVal(v1 * v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (FloatVal(v1 * v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (FloatVal(v1 * v2), sto2)
            case (StringVal(v1), StringVal(v2)) => (StringVal(v1 * v2), sto2)
            case (StringVal(v1), IntVal(v2)) => (StringVal(v1 * v2.toString), sto2)
            case (StringVal(v1), FloatVal(v2)) => (StringVal(v1 * v2.toString), sto2)
            case (IntVal(v1), StringVal(v2)) => (StringVal(v1.toString * v2), sto2)
            case (FloatVal(v1), StringVal(v2)) => (StringVal(v1.toString * v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '*', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
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
        case ModuloBinOp() =>
          if (rightval == IntVal(0) || rightval == FloatVal(0.0f))
            throw InterpreterError(s"Module by zero (divsiion by zero)", op)
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (IntVal(v1 % v2), sto2)
            case (FloatVal(v1), FloatVal(v2)) => (FloatVal(v1 % v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (FloatVal(v1 % v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (FloatVal(v1 % v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '%', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case EqualBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (BoolVal(v1 == v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (BoolVal(v1 == v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (BoolVal(v1 == v2), sto2)
            case (StringVal(v1), IntVal(v2)) => (BoolVal(v1 == v2.toString), sto2)
            case (IntVal(v1), StringVal(v2)) => (BoolVal(v1.toString == v2), sto2)
            case (BoolVal(v1), BoolVal(v2)) => (BoolVal(v1 == v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '==', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case LessThanBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (BoolVal(v1 < v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (BoolVal(v1 < v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (BoolVal(v1 < v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '<', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case LessThanOrEqualBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) => (BoolVal(v1 <= v2), sto2)
            case (FloatVal(v1), IntVal(v2)) => (BoolVal(v1 <= v2), sto2)
            case (IntVal(v1), FloatVal(v2)) => (BoolVal(v1 <= v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '<=', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case MaxBinOp() =>
          (leftval, rightval) match {
            case (IntVal(v1), IntVal(v2)) =>
              if (v1 > v2) (IntVal(v1), sto2) else (IntVal(v2), sto2)
            case (FloatVal(v1), IntVal(v2)) =>
              if (v1 > v2) (FloatVal(v1), sto2) else (FloatVal(v2), sto2)
            case (IntVal(v1), FloatVal(v2)) =>
              if (v1 > v2) (FloatVal(v1), sto2) else (FloatVal(v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at 'Max', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case AndBinOp() =>
          (leftval, rightval) match {
            case (BoolVal(v1), BoolVal(v2)) => (BoolVal(v1 & v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '&', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
        case OrBinOp() =>
          (leftval, rightval) match {
            case (BoolVal(v1), BoolVal(v2)) => (BoolVal(v1 | v2), sto2)
            case _ => throw InterpreterError(s"Type mismatch at '|', unexpected values ${valueToString(leftval)} and ${valueToString(rightval)}", op)
          }
      }
    case UnOpExp(op, exp) =>
      val (expval, sto1) = eval(exp, env, cenv, sto)
      op match {
        case NegUnOp() =>
          expval match {
            case IntVal(v) => (IntVal(-v), sto1)
            case FloatVal(v) => (FloatVal(-v), sto1)
            case _ => throw InterpreterError(s"Type mismatch at '-', unexpected value ${valueToString(expval)}", op)
          }
        case NotUnOp() =>
          expval match {
            case BoolVal(v) => (BoolVal(!v), sto1)
            case _ => throw InterpreterError(s"Type mismatch at '!', unexpected value ${valueToString(expval)}", op)
          }
      }
    case IfThenElseExp(condexp, thenexp, elseexp) =>
      val (condval, sto1) = eval(condexp, env, cenv, sto)
      condval match {
        case BoolVal(true) => eval(thenexp, env, cenv, sto1)
        case BoolVal(false) => eval(elseexp, env, cenv, sto1)
        case _ => throw InterpreterError(s"Condition must be a boolean, found ${valueToString(condval)}", condexp)
      }
    case b: BlockExp =>
      val (res, _, sto1) = evalBlock(b, env, cenv, sto)
      (res, sto1)
    case TupleExp(exps) =>
      var (vals, sto1) = (List[Val](), sto)
      for (exp <- exps) {
        val (v, sto2) = eval(exp, env, cenv, sto1)
        vals = v :: vals
        sto1 = sto2
      }
      (TupleVal(vals.reverse), sto1)
    case MatchExp(exp, cases) =>
      val (expval, sto1) = eval(exp, env, cenv, sto)
      expval match {
        case TupleVal(vs) =>
          var res: Option[(Val, Sto)] = None
          for (c <- cases) {
            if (vs.length == c.pattern.length) {
              var env1 = env
              for ((x, v) <- c.pattern.zip(vs))
                env1 = env1 + (x -> v)
              val (v1, sto2) = eval(c.body, env1, cenv, sto1)
              res = Some((v1, sto2))
            }
          }
          res match {
            case Some(v) => v
            case None => throw InterpreterError(s"No case matches value ${valueToString(expval)}", e)
          }
        case _ => throw InterpreterError(s"Tuple expected at match, found ${valueToString(expval)}", e)
      }
    case CallExp(funexp, args) =>
      // First we evaluate the function expression
      val (funval, sto1) = eval(funexp, env, cenv, sto)
      funval match {
        // we make sure the function has returned an closure
        case ClosureVal(params, optrestype, body, closureEnv, closureCenv) =>
          // Check to see if the arguments given match the amount of parameters needed
          if (args.length != params.length) {
            throw InterpreterError(s"Function called with ${args.length} arguments but expects ${params.length} parameters", e)
          }
          // We update the enviroment and store
          var (env1, sto2) = (closureEnv, sto1)
          // We iterate over each parameter and argument two-by-two
          for ((param, arg) <- params.zip(args)) {
            // We evaluate the argument in the new store, resulting in a value and a third store
            val (argval, sto3) = eval(arg, env, cenv, sto2)
            // Typechecking
            checkValueType(argval, param.opttype, arg)
            // Update the enviroment woth the mapping from ID to value
            env1 = env1 + (param.x -> argval)
            // update the store for next iteration
            sto2 = sto3
          }
          // finally we evaluate in the new updated env and sto, which contains the new bindings
          eval(body, env1, closureCenv, sto2)
        case _ =>
          throw InterpreterError(s"Expected a function but found ${valueToString(funval)}", funexp)
      }
    case LambdaExp(params, optResultType, body) =>
      (ClosureVal(params, optResultType, body, env, cenv), sto)
    case AssignmentExp(x, exp) =>
      val (v, sto1) = eval(exp, env, cenv, sto)
      env.get(x) match {
        case Some(RefVal(loc, opttype)) =>
          opttype.foreach(t => checkValueType(v, Some(t), e))
          val sto2 = sto1 + (loc -> v)
          (unitVal, sto2)
        case _ => throw InterpreterError(s"Cannot assign to non-variable '$x'", e)
      }
    case WhileExp(cond, body) =>
      val (condval, sto1) = eval(cond, env, cenv, sto)
      condval match {
        case BoolVal(false) => (unitVal, sto1)
        case BoolVal(true) =>
          val (_, sto2) = eval(body, env, cenv, sto1)
          eval(WhileExp(cond, body), env, cenv, sto2)
        case _ => throw InterpreterError(s"Condition must be a boolean, found ${valueToString(condval)}", cond)
      }
    case NewObjExp(klass, args) =>
      // we find the constructor in the class env, throw an error otherwise
      val c = cenv.getOrElse(klass, throw InterpreterError(s"Unknown class name '$klass'", e))
      // we rebind the class, using the store data from the constructor, to allow recursion
      val declcenv1 = rebindClasses(c.env, c.cenv, c.classes)
      // evaluate the args to get a new env and sto
      val (declenv1, sto1) = evalArgs(args, c.params, env, sto, cenv, c.env, e)
      // same for the block, we dont care about the value since we only want to updated env and sto
      val (_, env1, sto2) = evalBlock(c.body, declenv1, declcenv1, sto1)
      val newloc = nextLoc(sto2)
      // we create the object
      val objenv = (c.body.defs.map(d => d.fun -> env1(d.fun)) ++ c.body.vars.map(d => d.x -> env1(d.x)) ++ c.body.vals.map(d => d.x -> env1(d.x))).toMap
      val sto3 = sto2 + (newloc -> ObjectVal(objenv))
      // We return a ref to the new object, which has been placed at the newloc, with a updated store
      (ObjRefVal(newloc), sto3)
    case LookupExp(objexp, member) =>
      // We get the value and store from evaluating the expresion
      val (objval, sto1) = eval(objexp, env, cenv, sto)
      objval match {
        case ObjRefVal(loc) =>
          sto1(loc) match {
            case ObjectVal(members) =>
              // in case the val is a member of the object, return the value from this member
              (getValue(members.getOrElse(member, throw InterpreterError(s"No such member: $member", e)), sto1), sto1)
            case _ => throw RuntimeException(s"Expected an object value") // (unreachable case)
          }
        case _ => throw InterpreterError(s"Base value of lookup is not a reference to an object: ${valueToString(objval)}", e)
      }
  }

  /**
   * Evaluates a declaration.
   */
  def eval(d: Decl, env: Env, cenv: ClassEnv, sto: Sto, b: BlockExp): (Env, ClassEnv, Sto) = d match {
    case ValDecl(x, opttype, exp) =>
      val (v, sto1) = eval(exp, env, cenv, sto)
      opttype.foreach(t => checkValueType(v, Some(t), d))
      val env1 = env + (x -> v)
      (env1, cenv, sto1)
    case VarDecl(x, opttype, exp) =>
      val (v, sto1) = eval(exp, env, cenv, sto)
      opttype.foreach(t => checkValueType(v, Some(t), d))
      val loc = nextLoc(sto1)
      val env1 = env + (x -> RefVal(loc, opttype))
      val sto2 = sto1 + (loc -> v)
      (env1, cenv, sto2)
    case DefDecl(fun, params, optrestype, body) =>
      val closure = ClosureVal(params, optrestype, body, env, cenv)
      val env1 = env + (fun -> closure)
      (env1, cenv, sto)
    case ClassDecl(klass, params, body) =>
      val cenv1 = cenv + (klass -> Constructor(params, body, env, cenv, b.classes))
      (env, cenv1, sto)
  }

  /**
   * Evaluates the given block.
   * Returns the resulting value, the updated environment after evaluating all declarations, and the latest store.
   */
  def evalBlock(b: BlockExp, env: Env, cenv: ClassEnv, sto: Sto): (Val, Env, Sto) = {
    var env1 = env
    var cenv1 = cenv
    var sto1 = sto
    // We evaluate vals, vars, defs and classes, in that order, in the block and update the env, cenv and store
    for (d <- b.vals ++ b.vars ++ b.defs ++ b.classes) {
      val (env2, cenv2, sto2) = eval(d, env1, cenv1, sto1, b)
      env1 = env2
      cenv1 = cenv2
      sto1 = sto2
    }
    // unitialize the return value to unit value
    var v1 = unitVal
    // We evaluate each expression in the block and update the store. We also update the reutrn value to be the latest evaluated value
    for (e <- b.exps) {
      val (v2, sto2) = eval(e, env1, cenv1, sto1)
      v1 = v2
      sto1 = sto2
    }
    (v1, env1, sto1)
  }

  /**
   * Evaluates the arguments `args` in environment `env` with store `sto`,
   * extends the environment `declenv` with the new bindings, and
   * returns the extended environment and the latest store.
   */
  def evalArgs(args: List[Exp], params: List[FunParam], env: Env, sto: Sto, cenv: ClassEnv, declenv: Env, e: Exp): (Env, Sto) = {
    if (args.length != params.length) throw InterpreterError("Wrong number of arguments at call/new", e)
    var (env1, sto1) = (declenv, sto)
    // for each pair of parameters and arguemnts, we evaluate the arguemnts and updated the env and store
    for ((p, arg) <- params.zip(args) ) {
      val (argval, sto2) = eval(arg, env, cenv, sto1)
      // check that the type between parameter and arg are right
      checkValueType(argval, p.opttype, arg)
      env1 = env1 + (p.x -> argval)
      sto1 = sto2
    }
    // return the most updated env and store
    (env1, sto1)
  }

  /**
   * Resolves reference values by looking up the referenced value in the store.
   */
  def getValue(v: Val, sto: Sto): Val = v match {
    // of v is a Reference, use it to loc into the given store and return it. Otherwise just return v
    case RefVal(loc, _) => sto(loc)
    case _ => v
  }

  /**
   * Rebinds `classes` in `cenv` to support recursive class declarations.
   */
  def rebindClasses(env: Env, cenv: ClassEnv, classes: List[ClassDecl]): ClassEnv = {
    var cenv1 = cenv
    // for each class, we rebind its consturctor to the cenv
    for (d <- classes)
      cenv1 = cenv1 + (d.klass -> Constructor(d.params, d.body, env, cenv, classes))
    cenv1
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
        case (ClosureVal(cparams, optcrestype, _, _, _), FunType(paramtypes, restype)) if cparams.length == paramtypes.length =>
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
    case ClosureVal(params, _, exp, _, _) => // the resulting string ignores the result type annotation and the declaration environments
      s"<(${params.map(unparse).mkString(",")}), ${unparse(exp)}>"
    case RefVal(loc, _) => s"#$loc" // the resulting string ignores the type annotation
    case ObjRefVal(loc) => s"object#$loc"
    case _ => throw RuntimeException(s"Unexpected value $v") // (unreachable case)
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