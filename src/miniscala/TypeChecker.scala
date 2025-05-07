package miniscala

import miniscala.Ast.*
import miniscala.Unparser.unparse

/**
  * Type checker for MiniScala.
  */
object TypeChecker {

  type TypeEnv = Map[Id, Type]

  val unitType: Type = TupleType(Nil)

  def typeCheck(e: Exp, tenv: TypeEnv): Type = e match {
    case IntLit(_) => IntType()
    case BoolLit(_) => BoolType()
    case FloatLit(_) => FloatType()
    case StringLit(_) => StringType()
    case VarExp(x) => tenv.getOrElse(x, throw TypeError(s"Unknown identifier '$x'", e)) match {
      case MutableType(thetype) => thetype
      case t: Type => t
    }
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
            case _ => throw TypeError(s"Type mismatch at '+', unexpected types ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
        case MinusBinOp() | MultBinOp() | DivBinOp() | ModuloBinOp() | MaxBinOp() =>
          (lefttype, righttype) match {
            case (IntType(), IntType()) => IntType()
            case (FloatType(), FloatType()) => FloatType()
            case (IntType(), FloatType()) => FloatType()
            case (FloatType(), IntType()) => FloatType()
            case _ => throw TypeError(s"Type mismatch at operator, unexpected types ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
        case EqualBinOp() =>
          BoolType()
        case LessThanBinOp() | LessThanOrEqualBinOp() =>
          (lefttype, righttype) match {
            case (IntType(), IntType()) => BoolType()
            case (FloatType(), FloatType()) => BoolType()
            case (IntType(), FloatType()) => BoolType()
            case (FloatType(), IntType()) => BoolType()
            case _ => throw TypeError(s"Type mismatch at comparison operator, unexpected types ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
        case AndBinOp() | OrBinOp() =>
          (lefttype, righttype) match {
            case (BoolType(), BoolType()) => BoolType()
            case _ => throw TypeError(s"Type mismatch at logical operator, unexpected types ${unparse(lefttype)} and ${unparse(righttype)}", op)
          }
      }
    case UnOpExp(op, exp) =>
      val exptype = typeCheck(exp, tenv)
      op match {
        case NegUnOp() =>
          exptype match {
            case IntType() => IntType()
            case FloatType() => FloatType()
            case _ => throw TypeError(s"Type mismatch at negation, unexpected type ${unparse(exptype)}", op)
          }
        case NotUnOp() =>
          exptype match {
            case BoolType() => BoolType()
            case _ => throw TypeError(s"Type mismatch at logical not, unexpected type ${unparse(exptype)}", op)
          }
      }
    case IfThenElseExp(condexp, thenexp, elseexp) =>
      val condtype = typeCheck(condexp, tenv)
      if (condtype != BoolType())
        throw TypeError(s"Condition must be boolean, found ${unparse(condtype)}", condexp)
      val thentype = typeCheck(thenexp, tenv)
      val elsetype = typeCheck(elseexp, tenv)
      if (thentype != elsetype)
        throw TypeError(s"Then and else branches must have same type, found ${unparse(thentype)} and ${unparse(elsetype)}", e)
      thentype
    case BlockExp(vals, vars, defs, exps) =>
      var tenv1 = tenv
      // val
      for (d <- vals) {
        val t = typeCheck(d.exp, tenv1)
        checkTypesEqual(t, d.opttype, d)
        tenv1 = tenv1 + (d.x -> d.opttype.getOrElse(t))
      }
      // var
      for (d <- vars) {
        val t = typeCheck(d.exp, tenv1)
        checkTypesEqual(t, d.opttype, d)
        tenv1 = tenv1 + (d.x -> MutableType(d.opttype.getOrElse(t)))
      }
      // def-decl
      for (d <- defs) {
        val funType = makeFunType(d)
        tenv1 = tenv1 + (d.fun -> funType)
      }
      for (d <- defs) {
        val funType = tenv1(d.fun).asInstanceOf[FunType]
        val bodyEnv = tenv1 ++ d.params.zip(funType.paramtypes).map { case (p, t) => p.id -> t }
        val bodyType = typeCheck(d.body, bodyEnv)
        checkTypesEqual(bodyType, Some(funType.restype), d.body)
      }
      // Type check expressions in block
      if (exps.isEmpty) unitType
      else exps.map(e => typeCheck(e, tenv1)).last
    case TupleExp(exps) =>
      TupleType(exps.map(e => typeCheck(e, tenv)))
    case MatchExp(exp, cases) =>
      val exptype = typeCheck(exp, tenv)
      exptype match {
        case TupleType(ts) =>
          var res: Option[Type] = None
          for (c <- cases) {
            if (ts.length == c.pattern.length) {
              // Create new environment with pattern variables
              val caseEnv = tenv ++ c.pattern.zip(ts).map { case (x, t) => x -> t }
              val caseType = typeCheck(c.exp, caseEnv)
              res match {
                case None => res = Some(caseType)
                case Some(t) =>
                  if (t != caseType)
                    throw TypeError(s"All case expressions must have same type, found ${unparse(t)} and ${unparse(caseType)}", c)
              }
            }
          }
          res match {
            case Some(t) => t
            case None => throw TypeError(s"No case matches type ${unparse(exptype)}", e)
          }
        case _ => throw TypeError(s"Tuple expected at match, found ${unparse(exptype)}", e)
      }
    case CallExp(funexp, args) =>
      val funtype = typeCheck(funexp, tenv)
      funtype match {
        case FunType(paramtypes, restype) =>
          if (args.length != paramtypes.length)
            throw TypeError(s"Function called with ${args.length} arguments but expects ${paramtypes.length} parameters", e)

          for ((arg, paramType) <- args.zip(paramtypes)) {
            val argType = typeCheck(arg, tenv)
            if (argType != paramType)
              throw TypeError(s"Parameter type mismatch, expected ${unparse(paramType)}, found ${unparse(argType)}", arg)
          }
          restype

        case _ => throw TypeError(s"Expected a function type, found ${unparse(funtype)}", funexp)
      }
    case LambdaExp(params, optrestype, body) =>
      // Create new environment with parameter types
      val paramTypes = params.map(p => p.opttype.getOrElse(throw TypeError(s"Type annotation missing at parameter ${p.id}", p)))
      val bodyEnv = tenv ++ params.zip(paramTypes).map { case (p, t) => p.id -> t }
      val bodyType = typeCheck(body, bodyEnv)
      // Check result type if specified
      optrestype.foreach(t => checkTypesEqual(bodyType, Some(t), body))
      FunType(paramTypes, optrestype.getOrElse(bodyType))
    case AssignmentExp(x, exp) =>
      tenv.get(x) match {
        case Some(MutableType(t)) =>
          val expType = typeCheck(exp, tenv)
          if (expType != t)
            throw TypeError(s"Assignment type mismatch, variable has type ${unparse(t)}, expression has type ${unparse(expType)}", e)
          unitType
        case _ => throw TypeError(s"Cannot assign to non-mutable variable '$x'", e)
      }
    case WhileExp(cond, body) =>
      val condType = typeCheck(cond, tenv)
      if (condType != BoolType())
        throw TypeError(s"While condition must be boolean, found ${unparse(condType)}", cond)
      // Type check the body (the type is ignored always returns Unit)
      typeCheck(body, tenv)
      // Return the unit type
      unitType
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
        throw TypeError(s"Type mismatch: expected type ${unparse(t2)}, found type ${unparse(t1)}", n)
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
