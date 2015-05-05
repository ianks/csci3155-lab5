object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._

  /*
   * CSCI 3155: Lab 5
   * <Ian Ker-Seymer> <Daniel Bye>
   *
   * Collaborators: <Rick Osborne;>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   *
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */



  /*** Helper: mapFirst to DoWith ***/

  // Take a lambda function from the user and a list. It then calls the users's
  // lamda, and if that return value is Some, it replaces the value with what
  // was returned by the lamda which is a Option[DoWith[W,A]].
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
    case Nil => doreturn( Nil )
    case h :: t => f(h) match {
      // Case when the lamda returns nothing meaningful. Keep recursing,
      // yeilding the current h :: tp to the users's lambda
      case None => for (tp <- mapFirstWith(f)(t)) yield h :: tp
      // Case something meaningful is found. We are done searching
      // through the list, yeild hp :: t back to lamda
      case Some(withhp) => for (hp <- withhp) yield hp :: t
    }
  }

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    // Base cases
    case (TNull, TObj(_)) => true
    case (_, _) if (t1 == t2) => true
    case (TObj(fields1), TObj(fields2)) => {
      // If all of the fields match, then it is OK to cast an Object to another Object. Otherwise it is not.
      (fields2 forall { case (f2, t2) => fields1.get(f2) match { case Some(t1) => t1 == t2 case None => false } }) ||
      (fields1 forall { case (f2, t2) => fields2.get(f2) match { case Some(t1) => t1 == t2 case None => false } })
    }

    // Inductive cases
    // If it is an interface, substitute the type with tvar (tvar must be
    // string)
    case (TInterface(tvar, t1p), _) => castOk(typSubstitute(t1p, t1, tvar), t2)
    case (_, TInterface(tvar, t2p)) => castOk(t1, typSubstitute(t2p, t2, tvar))
    case _ => false
  }

  /*** Type Inference ***/

  def hasFunctionTyp(t: Typ): Boolean = t match {
    // All functions have function type
    case TFunction(_, _) => true

    // An object has a function typ if one of its fields is a function
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def mut(m: PMode): Mutability = m match {
    case PName => MConst
    case PVar | PRef => MVar
  }

  def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ = {
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw new StaticTypeError(tgot, e1, e)
    def check[T](e1: Expr)(cases: PartialFunction[Typ,T]): T = {
      val errpfun: PartialFunction[Typ,T] = { case tgot => err(tgot, e1) }
      (cases orElse errpfun)(typ(e1))
    }

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        val (_, t) = env(x)
        t
      case Unary(Neg, e1) => check(e1){
        case TNumber => TNumber
      }
      case Unary(Not, e1) => check(e1){
        case TBool => TBool
      }
      case Binary(Plus, e1, e2) => check(e1){
        case TNumber => check(e2){ case TNumber => TNumber }
        case TString => check(e2){ case TString => TString }
      }
      case Binary(Minus|Times|Div, e1, e2) => check(e1){
        case TNumber => check(e2){ case TNumber => TNumber }
      }
      case Binary(Eq|Ne, e1, e2) => check(e1){
        case t1 if !hasFunctionTyp(t1) => check(e2){ case t2 if (t1 == t2) => TBool }
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => check(e1){
        case TNumber => check(e2){ case TNumber => TBool }
        case TString => check(e2){ case TString => TBool }
      }
      case Binary(And|Or, e1, e2) => check(e1){
        case TBool => check(e2){ case TBool => TBool }
      }
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)
      case If(e1, e2, e3) => check(e1){
        case TBool => check(e2){
          case t2 => check(e3){ case t3 if (t2 == t3) => t2 }
        }
      }

      case Obj(fields) => TObj(fields map { case (f,t) => (f, typ(t)) })

      case GetField(e1, f) => check(e1){
        case tgot @ TObj(tfields) => tfields.getOrElse(f, err(tgot, e1))
      }

      case Decl(mut, x, e1, e2) => typeInfer(env + (x -> (mut, typ(e1))), e2)

      case Function(p, paramse, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(rt)) =>
            val tprime = TFunction(paramse, rt)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with the parameters.
        val env2 = paramse match {
          case Left(params) => params.foldLeft(env1){ case (acc, (x,t)) => acc + (x -> (MConst, t)) }
          case Right((mode,x,t)) => env1 + (x -> (mut(mode), t))
        }
        // Infer the type of the function body
        val t1 = typeInfer(env2, e1)
        tann foreach { rt => if (rt != t1) err(t1, e1) };
        TFunction(paramse, t1)
      }

      case Call(e1, args) => check(e1){
        // Case that we are calling a function; we need to check that the correct
        // number of arguments were passed.
        case TFunction(Left(params), tret) if (params.length == args.length) => {
          // Matches each param and each arg together in a tuple
          (params, args).zipped.foreach {
            case ((_, tparami), ei) => check(ei){
              case ti if (ti == tparami) => ()
            }
          }
          tret
        }

        // Expected one type, but got another. This can either be an error or
        // that the args are unneccesary
        case tgot @ TFunction(Right((mode,_,tparam)), tret) => {
          args match {
            // Alphabet soup
            case earg :: Nil => check(earg){
              case targ if (targ == tparam  && (mode != PRef || isLExpr(earg))) => ()
            }
            case _ => err(tgot, e1)
          }

          tret
        }
      }

      // Case we are assigning a to a variable
      case Assign(Var(x), e1) =>
        val t1 = typ(e1)

        // Check if x is in the env
        env.get(x) match {
          // If so and the expressions are of same type, we return the type of
          // type of e1
          case Some((MVar, t)) if (t1 == t) => t1

          // Otherwise we have experienced an error
          case _ => err(t1, e1)
        }

      // Assigning to an object, in this case we have to assign fields
      // Similar logic to assigning to a variable
      case Assign(GetField(e1, f), e2) => check(e1){
        case TObj(fields) =>
          val t2 = typ(e2)
          fields.get(f) match {
            case Some(t) if (t2 == t) => t2
            case _ => err(t2, e2)
          }
      }
      case Assign(_, _) => err(TUndefined, e)

      case Null => TNull

      case Unary(Cast(t), e1) => check(e1) {
        case t1 if (castOk(t1, t)) => t
        case t1 =>
          /* println("Casting to: " + t) */
          err(t1, e1)
      }

      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /* Do the operation for an inequality. */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = substitute(e, esub, x)

    // Rename bound variables in e to avoid capturing free variables in esub
    val ep = avoidCapture(freeVars(esub), e)

    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => ep
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
      case Function(p, paramse, retty, e1) =>
        // Check if parameter exists, if so, use the expression
        if (
          p == Some(x) ||
          paramse.fold(
            { params => params exists { case (y,_) => x == y } },
            { case (_,y,_) => x == y }
          )
        ) e
        else Function(p, paramse, retty, subst(e1))
      case Call(e1, args) => Call(subst(e1), args map subst)
      case Obj(fields) => Obj(fields map { case (fi,ei) => (fi, subst(ei)) })
      case GetField(e1, f) => GetField(subst(e1), f)
      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
      case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))

    /*** Helpers for Call ***/

    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))

    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1)                                          => for (m <- doget) yield { println(pretty(m, v1)); Undefined }
      case Unary(Neg, N(n1))                                                 => doreturn( N(- n1) )
      case Unary(Not, B(b1))                                                 => doreturn( B(! b1) )
      case Binary(Seq, v1, e2) if isValue(v1)                                => doreturn( e2 )
      case Binary(Plus, S(s1), S(s2))                                        => doreturn( S(s1 + s2) )
      case Binary(Plus, N(n1), N(n2))                                        => doreturn( N(n1 + n2) )
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(inequalityVal(bop, v1, v2)))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2)                  => doreturn( B(v1 == v2) )
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2)                  => doreturn( B(v1 != v2) )
      case Binary(And, B(b1), e2)                                            => doreturn( if (b1) e2 else B(false) )
      case Binary(Or, B(b1), e2)                                             => doreturn( if (b1) B(true) else e2 )
      case Binary(Minus, N(n1), N(n2))                                       => doreturn( N(n1 - n2) )
      case Binary(Times, N(n1), N(n2))                                       => doreturn( N(n1 * n2) )
      case Binary(Div, N(n1), N(n2))                                         => doreturn( N(n1 / n2) )
      case If(B(b1), e2, e3)                                                 => doreturn( if (b1) e2 else e3 )

      // Case: all fields contain values
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        // Loops thought all the memory allocated for the expression,
        // yielding it back to the caller
        for (a <- Mem.alloc(e)) yield a

      // Get the field for the object, yeild the value to caller
      case GetField(a @ A(_), f) => for (m <- doget) yield {
        val vopt = for {
          Obj(fields) <- m.get(a)
          v <- fields.get(f)
        } yield v
        vopt.getOrElse(throw StuckError(e))
      }

      // If MConst has a value the substitute it
      case Decl(MConst, x, v1, e2) if isValue(v1) => doreturn( substitute(e2, v1, x) )

      // If its a variable, loop through all memory allocated for value,
      // then substitute the values
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        for (a <- Mem.alloc(v1)) yield
        substitute(e2, Unary(Deref, a), x)
      case Unary(Deref, a @ A(_)) => for (m <- doget) yield m(a)

      // Assigning the unary, you modify the memory, add the keys
      // and values to the memory map
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        for (_ <- domodify { (m: Mem) => m + (a -> v) }) yield v

      // Modify the object fields in memory
      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
        for {
          m <- doget[Mem]
          fields = m.get(a) match {
            case Some(Obj(fields)) if (fields.contains(f)) => fields
            case _ => throw StuckError(e)
          }

          //Physically modifies the memory map
          _ <- domodify { (m: Mem) => m + (a -> Obj(fields + (f -> v))) }
        } yield
        v

      case Call(v1, args) if isValue(v1) =>
        // If there are parameters, substitute the expression
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }

        (v1, args) match {
          // If the value is a function, and all the args are values,
          // we substitute vi for xi in all the params.
          case (Function(p, Left(params), _, e1), _) if (args forall isValue) => {
            // Zip the params and args in a tuple
            val e1p = (params, args).zipped.foldRight(e1){
              case (((xi, _),vi), acc) => substitute(acc, vi, xi)
            }
            doreturn( substfun(e1p, p) )
          }

          case (Function(p, Right((mode,x,_)), _, e1), earg :: Nil) if argApplyable(mode, earg) => mode match {
            case PName | PRef => doreturn( substfun(substitute(e1, earg, x), p) )
            case PVar =>
              for (a <- Mem.alloc(earg)) yield
              substfun(substitute(e1, Unary(Deref, a), x), p)
          }
          case (Function(_, Left(_), _, _), args) =>
            for (argsp <- mapFirstWith(stepIfNotValue)(args)) yield Call(v1, argsp)
          case (Function(_, Right(_), _, _), earg :: Nil) =>
            for (eargp <- step(earg)) yield Call(v1, eargp :: Nil)
          case _ => throw StuckError(e)
        }

      case Unary(Cast(t), Null) => t match {
        case TObj(_) | TInterface(_, TObj(_)) => doreturn( Null )
        case _ => throw StuckError(e)
      }
      case Unary(Cast(t), a @ A(_)) => for (m <- doget) yield {
        m.get(a) match {
          case Some(Obj(fields)) => t match {
            case TObj(fieldst) if fieldst forall { case (fi, _) => fields.contains(fi) } => a
            case TInterface(_, TObj(fieldst)) if fieldst forall { case (fi, _) => fields.contains(fi) } => a
            case _ => throw DynamicTypeError(e)
          }
          case _ => throw StuckError(e)
        }
      }
      case Unary(Cast(_), v1) if isValue(v1) => doreturn( v1 )

      /* Base Cases: Error Rules */
      case Unary(Deref, Null) | GetField(Null, _) | Assign(Unary(Deref, Null), _) | Assign(GetField(Null, _), _) => throw NullDereferenceError(e)

      /* Inductive Cases: Search Rules */
      case Print(e1) =>
        for (e1p <- step(e1)) yield Print(e1p)
      case Unary(uop, e1) =>
        for (e1p <- step(e1)) yield Unary(uop, e1p)
      case Binary(bop, v1, e2) if isValue(v1) =>
        for (e2p <- step(e2)) yield Binary(bop, v1, e2p)
      case Binary(bop, e1, e2) =>
        for (e1p <- step(e1)) yield Binary(bop, e1p, e2)
      case If(e1, e2, e3) =>
        for (e1p <- step(e1)) yield If(e1p, e2, e3)

      // The case where the field is not a value
      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) =>
          // Step on ei to get it closer to a value
          for (eip <- step(ei)) yield Obj(fields + (fi -> eip))
        case None => throw StuckError(e)
      }

      // It its a field, step on e1 and yeild the field
      case GetField(e1, f) =>
        for (e1p <- step(e1)) yield GetField(e1p, f)

      case Decl(mut, x, e1, e2) =>
        for (e1p <- step(e1)) yield Decl(mut, x, e1p, e2)
      case Assign(e1, e2) if (isLValue(e1)) =>
        for (e2p <- step(e2)) yield Assign(e1, e2p)
      case Assign(e1, e2) =>
        for (e1p <- step(e1)) yield Assign(e1p, e2)

      case Call(e1, args) =>
        for (e1p <- step(e1)) yield Call(e1p, args)

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** External Interfaces ***/

  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.

  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    }
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }

  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging.

  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }

  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(Mem.empty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }

    handle() {
      val t = inferType(exprlowered)
    }

    handle() {
      val v1 = iterateStep(exprlowered)
      println(pretty(v1))
    }
  }

}
