package miniscala

import miniscala.Ast.*
import miniscala.Interpreter.*
import miniscala.parser.Parser

import scala.io.StdIn

/**
  * Compiler from (a large part of) MiniScala v5 to lambda calculus.
  */
object Lambda {

  val FIX: Exp = Parser.parse("(x=>y=>(y(z=>x(x)(y)(z))))(x=>y=>(y(z=>x(x)(y)(z))))") // slide 26

  /**
    * Convenience function for creating a LambdaExp with a single parameter without type annotation.
    */
  def lambda(x: Id, body: Exp): LambdaExp = LambdaExp(List(FunParam(x, None)), body)

  /**
    * Convenience function for creating a CallExp with a single argument.
    */
  def call(funexp: Exp, arg: Exp): CallExp = CallExp(funexp, List(arg))

  def encode(e: Exp): Exp =
    e match {
      case IntLit(c) if c >= 0 => // non-negative integer literals are encoded as on slide 18
        def int_lit_encode_rec(n: Int): Exp = n match {
          case 0 => lambda("s", lambda("z", VarExp("z")))
          case n => lambda("s", lambda("z",
            call(VarExp("s"), call(call(int_lit_encode_rec(n-1), VarExp("s")), VarExp("z")))
          ))
        }
        int_lit_encode_rec(c)
      case BoolLit(c) => // boolean literals are encoded as on slide 15
        if (c) lambda("t", lambda("e", VarExp("t")))
        else lambda("t", lambda("e", VarExp("e")))
      case VarExp(_) => // variables need no encoding
        e
      case BinOpExp(leftexp, EqualBinOp(), IntLit(0)) => // e == 0, slide 18
        call(
          call(encode(leftexp),
            lambda("n", encode(BoolLit(false)))),
          encode(BoolLit(true))
        )
      case BinOpExp(leftexp, MinusBinOp(), IntLit(1)) => // e - 1, slide 20
        lambda("s", lambda("z",
          call(call(call(encode(leftexp),
            lambda("g", lambda("h",
              call(VarExp("h"), call(VarExp("g"), VarExp("s")))))),
            lambda("u", VarExp("z"))),
            lambda("u", VarExp("u")))))
      case BinOpExp(leftexp, op, rightexp) =>
        op match {
          case PlusBinOp() => // e1 + e2, slide 20 (we assume there are no floats or strings)
            lambda("s", lambda("z",
              call(call(encode(leftexp), VarExp("s")),
                call(call(encode(rightexp), VarExp("s")), VarExp("z")))))
          case MultBinOp() => // e1 * e2, slide 20
            lambda("s", call(encode(rightexp), call(encode(leftexp), VarExp("s"))))
          case AndBinOp() => // e1 & e2, slide 15
            call(call(encode(leftexp), encode(rightexp)), encode(BoolLit(false)))
          case OrBinOp() => // e1 | e2, slide 15
            call(call(encode(leftexp), encode(BoolLit(true))), encode(rightexp))
          case MinusBinOp() => // e1 - e2 (not in slides, see https://en.wikipedia.org/wiki/Church_encoding)
            call(call(encode(rightexp),
              lambda("n",
                lambda("s", lambda("z",
                  call(call(call(VarExp("n"),
                    lambda("g", lambda("h",
                      call(VarExp("h"), call(VarExp("g"), VarExp("s")))))),
                    lambda("u", VarExp("z"))),
                    lambda("u", VarExp("u"))))))),
              encode(leftexp))
          case LessThanOrEqualBinOp() => // e1 <= e2 (not in slides, see https://en.wikipedia.org/wiki/Church_encoding)
            encode(BinOpExp(BinOpExp(leftexp, MinusBinOp(), rightexp), EqualBinOp(), IntLit(0)))
          case LessThanBinOp() => // e1 < e2 (not in slides)
            encode(BinOpExp(BinOpExp(BinOpExp(leftexp, PlusBinOp(), IntLit(1)), MinusBinOp(), rightexp), EqualBinOp(), IntLit(0)))
          case _ => // remaining cases are not (yet) implemented
            throw EncoderError(e)
        }
      case UnOpExp(op, subexp) =>
        op match {
          case NotUnOp() => // !e, slide 15
            call(
              call(encode(subexp),
                lambda("t", lambda("e", VarExp("e")))),
              lambda("t", lambda("e", VarExp("t")))
            )
          case _ => // remaining cases are not (yet) implemented
            throw EncoderError(e)
        }
      case IfThenElseExp(condexp, thenexp, elseexp) => // if (e1) e2 else e3, slide 15
        // call(call(encode(condexp), encode(thenexp)), encode(elseexp)) // no good, evaluates both branches if using call-by-value
        call(call(encode(condexp),
          lambda("a", call(encode(thenexp), VarExp("a")))),
          lambda("b", call(encode(elseexp), VarExp("b")))) // mimics call-by-name
      case BlockExp(List(ValDecl(id, _, e1)), List(), e2: Exp) => // { val x = e1; e2 }, slide 24
        call(lambda(id, encode(e2)), encode(e1))
      case BlockExp(List(), List(DefDecl(f, List(FunParam(x, _)), _, e1)), e2: Exp) => // { def f(x) = e1; e2 }, slide 26
        call(lambda(f, encode(e2)),
          call(FIX,
            lambda(f, lambda(x, encode(e1)))))
      case TupleExp(List(e1, e2)) => // (e1, e2), slide 21
        lambda("p",
          call(call(VarExp("p"), encode(e1)), encode(e2)))
      case MatchExp(mexp, List(MatchCase(List(x, y), caseexp))) => // e1 match { case (x,y) => e2 }, slide 21
        encode(BlockExp(List(ValDecl("p", None, mexp)), List(),
          BlockExp(List(ValDecl(x, None, call(VarExp("p"), lambda("x", lambda("y", VarExp("x")))))), List(),
            BlockExp(List(ValDecl(y, None, call(VarExp("p"), lambda("x", lambda("y", VarExp("y")))))), List(),
              caseexp))))
      case CallExp(target, List(arg)) => // call with one argument, slide 23
        call(encode(target), encode(arg))
      case CallExp(target, List()) => // call with zero arguments, slide 23
        call(encode(target), encode(lambda("x", VarExp("x"))))
      case CallExp(target, args) => // call with more than one argument, slide 23
        args.foldLeft(encode(target))((acc, arg) => call(acc, encode(arg)))
      case LambdaExp(List(FunParam(x, _)), body) => // lambda with one parameter, slide 23
        lambda(x, encode(body))
      case LambdaExp(List(), body) => // lambda with zero parameters, slide 23
        val freshvar = Vars.freeVars(body).foldLeft("_")((acc, x) => acc + x) // produces a variable name that is definitely not a free variable in body
        lambda(freshvar, encode(body))
      case LambdaExp(params, body) => // lambda with more than one parameter, slide 23
        params.foldRight(encode(body))((p, acc) => lambda(p.x, acc))
      case _ => // remaining cases are not (yet) implemented
        throw EncoderError(e)
    }

  def decodeNumber(v: Val): Int = v match {
    case ClosureVal(List(FunParam(x, _)), _, exp, env) =>
      val unchurch = // see slide 22
        call(call(lambda(x, exp),
          lambda("n", BinOpExp(VarExp("n"), PlusBinOp(), IntLit(1)))),
          IntLit(0))
      Interpreter.eval(unchurch, env) match {
        case IntVal(c) => c
        case _ => throw RuntimeException(s"Unexpected decoded value $v")
      }
    case _ => throw RuntimeException(s"Unexpected encoded value $v")
  }

  def decodeBoolean(v: Val): Boolean = v match {
    case ClosureVal(List(FunParam(x, _)), _, exp, env) =>
      val unchurch = // see slide 22
        call(call(lambda(x, exp), BoolLit(true)), BoolLit(false))
      Interpreter.eval(unchurch, env) match {
        case BoolVal(c) => c
        case _ => throw RuntimeException(s"Unexpected decoded value $v")
      }
    case _ => throw RuntimeException(s"Unexpected encoded value $v")
  }

  /**
    * Builds an initial environment, with a lambda-encoded value for each free variable in the program.
    */
  def makeInitialEnv(program: Exp): Env = {
    var env = Map[Id, Val]()
    for (x <- Vars.freeVars(program)) {
      print(s"Please provide an integer value for the variable $x: ")
      env = env + (x -> Interpreter.eval(encode(IntLit(StdIn.readInt())), Map[Id, Val]()))
    }
    env
  }

  class EncoderError(node: AstNode) extends MiniScalaError(s"Don't know how to encode $node", node.pos)
}
