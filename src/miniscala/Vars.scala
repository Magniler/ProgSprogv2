package miniscala

import miniscala.Ast.*

/**
  * Computation of free variables (or rather, identifiers).
  */
object Vars {

  def freeVars(e: Exp): Set[Id] = e match {
    case _: Literal => Set()
    case VarExp(x) => Set(x)
    case BinOpExp(leftexp, _, rightexp) => freeVars(leftexp) ++ freeVars(rightexp)
    case UnOpExp(_, exp) => freeVars(exp)
    case IfThenElseExp(condexp, thenexp, elseexp) => freeVars(condexp) ++ freeVars(thenexp) ++ freeVars(elseexp)
    case BlockExp(vals, vars, defs, classdefs, exps) =>
      var fv = Set[Id]()
      for (e2 <- exps)
        fv = fv ++ freeVars(e2)
      for (d <- defs)
        fv = fv ++ freeVars(d)
      for (d <- defs)
        fv = fv -- declaredVars(d)
      for (d <- vars.reverse ++ vals.reverse)
        fv = fv -- declaredVars(d) ++ freeVars(d)
      fv
    case TupleExp(exps) =>
      var fv = Set[Id]()
      for (exp <- exps)
        fv = fv ++ freeVars(exp)
      fv
    case MatchExp(exp, cases) =>
      var fv = freeVars(exp)
      for (c <- cases)
        fv = fv ++ (freeVars(c.exp) -- c.pattern)
      fv
    case CallExp(funexp, args) =>
      ??? // note: the first field, funexp, is now an expression!
    case LambdaExp(params, body) => freeVars(body) -- params.map(p => p.x)
    case AssignmentExp(x, exp) => freeVars(exp) + x
    case WhileExp(guard, body) => freeVars(guard) ++ freeVars(body)
  }

  def freeVars(decl: Decl): Set[Id] = decl match {
    case ValDecl(_, _, exp) => freeVars(exp)
    case VarDecl(_, _, exp) => freeVars(exp)
    case DefDecl(_, params, _, body) => freeVars(body) -- params.map(p => p.x)
  }

  def declaredVars(decl: Decl): Set[Id] = decl match {
    case ValDecl(x, _, _) => Set(x)
    case VarDecl(x, _, _) => Set(x)
    case DefDecl(x, _, _, _) => Set(x)
  }
}
