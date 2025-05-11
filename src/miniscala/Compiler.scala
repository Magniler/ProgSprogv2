package miniscala

import miniscala.AbstractMachine.*
import miniscala.Ast.*

object Compiler {

  def compile(e: Exp): Executable = {

    case class IdDesc(x: Id, mutable: Boolean)

    val True = Const(1)
    val False = Const(0)
    val EmptyTuple = Const(0)

    def lookup(x: Id, idstack: List[IdDesc]): (IdIndex, Boolean) = {
      // find the position of identifier x in idstack
      val index = idstack.indexWhere(p => p.x == x)
      if (index == -1) throw Exception(s"$x not found")
      // return the position and a boolean flag that indicates whether the identifier was declared with 'var'
      (index, idstack(index).mutable)
    }

    def compileFun(params: List[FunParam], body: Exp, freeids: List[Id], defs: List[DefDecl], idstack: List[IdDesc]): List[Instruction] = {
      // prepare the new idstack for the function body, with an entry for each free non-def identifier, each def, and each parameter
      val defids = defs.map(d => d.fun).toSet
      val freenondefs = freeids.filterNot(defids.contains)
      val freeidsstack = freenondefs.map(x => IdDesc(x, lookup(x, idstack)._2))
      val defsstack = defs.map(d => IdDesc(d.fun, mutable = false))
      val paramsstack = params.map(p => IdDesc(p.x, mutable = false))
      // compile the function body
      val bodycode = compile(body, freeidsstack ++ paramsstack ++ defsstack, ???) ++ List(Return)
      // find idstack index for each free identifier (excluding defs in same block)
      val indices = freenondefs.map(x => lookup(x, idstack)._1)
      // produce a Lambda instruction
      List(AbstractMachine.Lambda(indices, bodycode))
    }

    def compile(e: Exp, idstack: List[IdDesc], tailpos: Boolean): List[Instruction] = e match {
      case IntLit(c) =>
        List(Const(c))
      case BoolLit(true) =>
        List(True)
      case BoolLit(false) =>
        List(False)
      case BinOpExp(leftexp, op, rightexp) =>
        compile(leftexp, idstack, false) ++ compile(rightexp, idstack, false) ++ List(op match {
          case PlusBinOp() => Add
          case MinusBinOp() => Sub
          case MultBinOp() => Mul
          case DivBinOp() => Div
          case EqualBinOp() => Eq
          case LessThanBinOp() => Lt
          case LessThanOrEqualBinOp() => Leq
          case AndBinOp() => And
          case OrBinOp() => Or
          case _ => throw UnsupportedFeatureError(e)
        })
      case UnOpExp(op, exp) =>
        compile(exp, idstack, false) ++ List(op match {
          case NegUnOp() => Neg
          case NotUnOp() => Not
        })
      case IfThenElseExp(condexp, thenexp, elseexp) =>
        compile(condexp, idstack, false) ++ List(Branch(compile(thenexp, idstack, tailpos), compile(elseexp, idstack, tailpos)))
      case WhileExp(cond, body) =>
        List(Loop(compile(body, idstack, false), compile(cond, idstack, false)), EmptyTuple)
      case BlockExp(vals, vars, defs, Nil, exps) =>
        var code = List[Instruction]()
        var newIdstack = idstack
        var numDeclared = 0
        // Process val declarations
        for (valDecl <- vals) {
          code = code ++ compile(valDecl.exp, newIdstack, false) ++ List(EnterScope)
          newIdstack = IdDesc(valDecl.x, mutable = false) :: newIdstack
          numDeclared += 1
        }
        // Process var declarations
        for (varDecl <- vars) {
          code = code ++ List(Alloc, Dup) ++
            compile(varDecl.exp, newIdstack, false) ++
            List(Store, EnterScope)
          newIdstack = IdDesc(varDecl.x, mutable = true) :: newIdstack
          numDeclared += 1
        }
        // Process def declarations
        if (defs.nonEmpty) {
          // First, create all the lambda closures
          for (defDecl <- defs) {
            val freeVars = Vars.freeVars(defDecl.body).toList.sorted
            val params = defDecl.params
            code = code ++ compileFun(params, defDecl.body, freeVars, defs, newIdstack)
            newIdstack = IdDesc(defDecl.fun, mutable = false) :: newIdstack
            numDeclared += 1
          }
          // Then use EnterScopeDefs to support recursion
          code = code ++ List(EnterScopeDefs(defs.length))
        }
        // Process expressions
        for (i <- 0 until exps.length - 1) {
          // For all expressions except the last one, discard their values
          code = code ++ compile(exps(i), newIdstack, false) ++ List(Pop)
        }
        // Compile the last expression (its value is the block's return value)
        if (exps.nonEmpty) {
          code = code ++ compile(exps.last, newIdstack, tailpos)
        } else {
          // If no expressions, return unit value
          code = code ++ List(EmptyTuple)
        }
        // Clean up the environment by popping all declared variables
        code = code ++ List(ExitScope(numDeclared))
        code
      case VarExp(x) =>
        val (index, mutable) = lookup(x, idstack)
        if (mutable)
          List(Read(index), Load)
        else
          List(Read(index))        // For immutable variables (val)
      case AssignmentExp(x, exp) =>
        val (index, mutable) = lookup(x, idstack)
        if (!mutable) throw UnsupportedFeatureError(e) // Check mutablility
        List(Read(index)) ++ compile(exp, idstack, false) ++ List(Store, EmptyTuple)
      case LambdaExp(params, body) =>
        compileFun(params, body, Vars.freeVars(e).toList.sorted, Nil, idstack)
      case CallExp(funexp, args) =>
        // compile funexp and args, and then add a Call instruction
        compile(funexp, idstack, tailpos) ++ args.flatMap(arg => compile(arg, idstack, false)) ++ List(Call(args.length, tailpos))
      case _ => throw UnsupportedFeatureError(e)
    }
    val freeids = Vars.freeVars(e).toList.sorted
    Executable(freeids, compile(e, freeids.map(x => IdDesc(x, mutable = false)), false))
  }

  class UnsupportedFeatureError(node: AstNode) extends MiniScalaError(s"Sorry, I don't know how to compile $node", node.pos)
}
