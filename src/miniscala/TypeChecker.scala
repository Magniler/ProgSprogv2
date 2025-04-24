package miniscala

import miniscala.Ast.*
import miniscala.Unparser.unparse

/**
  * Type checker for MiniScala.
  */
object TypeChecker {

  type TypeEnv = Map[Id, Type]

  def typeCheck(e: Exp, tenv: TypeEnv): Type = e match {
    case IntLit(_) => IntType()
    case BoolLit(_) => BoolType()
    case FloatLit(_) => FloatType()
    case StringLit(_) => StringType()
    case VarExp(x) => tenv.getOrElse(x, throw TypeError("missing type for VarExp", e))
    case BinOpExp(leftexp, op, rightexp) =>
      val lefttype = typeCheck(leftexp, tenv)
      val righttype = typeCheck(rightexp, tenv)
      op match {
        case PlusBinOp() =>
          (lefttype, righttype) match {
            case (IntType(), IntType()) => IntType()
            case (FloatType(), FloatType()) => FloatType()
            case (IntType(), FloatType()) => FloatType()
            case (FloatType(), IntType()) => FloatType()
            case (StringType(), StringType()) => StringType()
            case (StringType(), IntType()) => StringType()
            case (StringType(), FloatType()) => StringType()
            case (IntType(), StringType()) => StringType()
            case (FloatType(), StringType()) => StringType()
            case _ => throw TypeError(s"Type mismatch at '+', unexpected types ${unparse(Option(lefttype))} and ${unparse(Option(righttype))}", op)
          }
        case MinusBinOp() | MultBinOp() | DivBinOp() | ModuloBinOp() | MaxBinOp() =>
          (lefttype, righttype) match {
            case (IntType(), IntType()) => IntType()
            case (FloatType(), FloatType()) => FloatType()
            case (IntType(), FloatType()) => FloatType()
            case (FloatType(), IntType()) => FloatType()
            case _ => throw TypeError(s"Type mismatch, unexpected types ${unparse(Option(lefttype))} and ${unparse(Option(righttype))}", op)
          }
        case EqualBinOp() => BoolType()
        case LessThanBinOp() | LessThanOrEqualBinOp() => BoolType()
        case AndBinOp() | OrBinOp() =>
          (lefttype, righttype) match {
            case (lefttype: BoolType, righttype: BoolType) => BoolType()
            case _ => throw TypeError(s"Type mismatch, unexpected types ${unparse(Option(lefttype))} and ${unparse(Option(righttype))}", op)
          }
      }
  case UnOpExp(op, exp) => op match {
    case NegUnOp() => IntType()
    case NotUnOp() => BoolType()
  }
    case IfThenElseExp(condexp, thenexp, elseexp) =>
      val thentype = typeCheck(thenexp, tenv)
      val elsetype = typeCheck(elseexp, tenv)
      if (elsetype == thentype) elsetype else throw TypeError(s"Type mismatch, unexpected types ${unparse(Option(thentype))} and ${unparse(Option(elsetype))}", e)
    case BlockExp(vals, defs, exp) =>
      var tenv1 = tenv
      for (d <- defs) {
        val funType = makeFunType(d)
        tenv1 = tenv1 + (d.fun -> funType)
      }
      // Process value declarations
      for (d <- vals) {
        val t = typeCheck(d.exp, tenv1)
        checkTypesEqual(t, d.opttype, d)
        tenv1 = tenv1 + (d.x -> d.opttype.getOrElse(t))
      }
      for (d <- defs) {
        // Create new environment with parameter types
        var bodyEnv = tenv1
        for (param <- d.params) {
          val paramType = param.opttype.getOrElse(
            throw TypeError(s"Type annotation missing at parameter ${param.x}", param)
          )
          bodyEnv = bodyEnv + (param.x -> paramType)
        }
        // check body
        val bodyType = typeCheck(d.body, bodyEnv)
        checkTypesEqual(bodyType, d.optrestype, d.body)
      }
      typeCheck(exp, tenv1)
    case TupleExp(exps) =>
      var types: List[Type] = List()
      for (d <- exps) {
        val t = List(typeCheck(d, tenv))
        types = types:::t
      }
      TupleType(types)
    case MatchExp(exp, cases) =>
      val exptype = typeCheck(exp, tenv)
      exptype match {
        case TupleType(ts) =>
          for (c <- cases) {
            if (ts.length == c.pattern.length) {
              for (c <- cases) {
                if (ts.length == c.pattern.length) {
                  var tenv1 = tenv
                  val z = ts.zip(c.pattern)
                  for ((v, pat) <- z) {
                    tenv1 = tenv1 + (pat -> v)
                  }
                  return typeCheck(c.exp, tenv)
                }
              }
            }
          }
          throw TypeError(s"No case matches type ${unparse(Option(exptype))}", e)
        case _ => throw TypeError(s"Tuple expected at match, found ${unparse(Option(exptype))}", e)
      }
    case CallExp(funexp, args) =>
      val funType = typeCheck(funexp, tenv)
      funType match {
        case FunType(paramTypes, returnType) =>
          if (args.length != paramTypes.length) {
            throw TypeError(s"Function ${funexp} called with ${args.length} arguments but expects ${paramTypes.length} parameters", e)
          }
          // Type check arguments against parameter types
          for ((arg, paramType) <- args.zip(paramTypes)) {
            val argType = typeCheck(arg, tenv)
            checkTypesEqual(argType, Some(paramType), arg)
          }
          returnType
        case _ => throw TypeError(s"Expected a function type but found ${unparse(Option(funType))}", e)
      }
    case LambdaExp(params, body) =>
      var bodyEnv = tenv
      for (param <- params) {
        val paramType = param.opttype.getOrElse(throw TypeError(s"Type annotation missing at parameter ${param.x}", param))
        bodyEnv = bodyEnv + (param.x -> paramType)
      }
      val resultType = typeCheck(body, bodyEnv)

      FunType(params.map(_.opttype.get), resultType)
  }

  /**
    * Returns the function type for the function declaration `d`.
    */
  def makeFunType(d: DefDecl): FunType =
    FunType(d.params.map(p => p.opttype.getOrElse(throw TypeError(s"Type annotation missing at parameter ${p.x}", p))),
      d.optrestype.getOrElse(throw TypeError(s"Type annotation missing at function result ${d.fun}", d)))

  /**
    * Checks that the types `t1` and `ot2` are equal (if present), throws type error exception otherwise.
    */
  def checkTypesEqual(t1: Type, ot2: Option[Type], n: AstNode): Unit = ot2 match {
    case Some(t2) =>
      if (t1 != t2)
        throw TypeError(s"Type mismatch: expected type ${unparse(Option(t2))}, found type ${unparse(Option(t1))}", n)
    case None => // do nothing
  }

  /**
    * Builds an initial type environment, with a type for each free variable in the program.
    */
  def makeInitialTypeEnv(program: Exp): TypeEnv = {
    var tenv: TypeEnv = Map()
    for (x <- Vars.freeVars(program))
      tenv = tenv + (x -> IntType())
    tenv
  }

  /**
    * Exception thrown in case of MiniScala type errors.
    */
  class TypeError(msg: String, node: AstNode) extends MiniScalaError(s"Type error: $msg", node.pos)
}
