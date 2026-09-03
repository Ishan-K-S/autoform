// Joern query: export each method's AST as a language-neutral JSON tree.
//
// This is Layer 3 (Transpiler), and it is deterministic — no LLM anywhere on this path.
//
// The reason one exporter suffices for many languages is that Joern has already done the
// normalization: C, C++, Java, JavaScript, Python, Kotlin and binaries all land in the
// same CPG node vocabulary (CALL / IDENTIFIER / LITERAL / CONTROL_STRUCTURE / RETURN /
// BLOCK / FIELD_IDENTIFIER / METHOD_REF / TYPE_REF), with operators as `<operator>.*`
// calls. We map that vocabulary onto `Autoform.Core`, and anything we do not recognise
// becomes a *hole tagged with the node label that produced it*. Nothing is silently
// dropped, and nothing is guessed: where a construct cannot be translated faithfully the
// hole label says precisely which shape defeated us.
//
// Beyond the per-node mapping, the exporter answers three whole-program questions that
// the node vocabulary alone cannot: which names are module-level (exported as one
// `setGlobal` initializer per file), which function values capture an enclosing scope
// (`closure` rather than `fnref`), and — because the CPG is multi-language — which
// operators change meaning under the source dialect (a C `char*` is an address, so `+`
// and `<` are not the string operations they look like).
//
// Run: joern --script cartographer/export_ast.sc --param cpgPath=... --param out=ast.json

import io.shiftleft.codepropertygraph.generated.nodes._
import scala.annotation.tailrec

@main def exec(cpgPath: String, out: String = "ast.json", maxMethods: Int = 100000,
               dataModel: String = "lp64") = {
  importCpg(cpgPath)

  // `seqOf` and `moduleObjectsInit` (below) both fold a flat statement list into a
  // right-nested `"seq"` chain; `maxSeqChainLen` tracks the longest one either producer
  // has built so far. Declared here (rather than next to `writeJson`, which uses it) so
  // every use -- including `moduleObjectsInit`'s, which appears earlier in this file --
  // is a backward, not forward, reference; Scala's forward-reference check otherwise
  // rejects a `def` defined before this `var` reading it. See `writeJson`'s own comment
  // (search "seqChainCompactThreshold") for what this threshold is actually for.
  var maxSeqChainLen = 0
  val seqChainCompactThreshold = 1000

  // CPG operator name -> Core binary operator.
  //
  // `floorDiv` is Python's `//`. It maps to "/" because the Core semantics is
  // dialect-parameterized: `Dialect.python` already floors, `Dialect.cLike` truncates.
  //
  // `<operator>.and` / `.or` / `.xor` / the shifts are **bitwise**, not logical
  // (`logicalAnd` / `logicalOr` are the logical ones). They used to be mapped to
  // `"&&"`/`"||"`, which returned a boolean where C returns a number, and they were then
  // deliberately left *unmapped* because a hole beats a silent wrong answer. They are now
  // mapped to their own operator strings — `"&"`, `"|"`, `"^"`, `"<<"` — which
  // `applyBinop` implements with `NumConfig.band`/`bor`/`bxor`/`shl`, i.e. genuine
  // two's-complement bit operations at the dialect's width. They are *not* aliases of the
  // logical operators and must never become so.
  //
  // `>>` is absent from this table on purpose: it is two operators wearing one spelling
  // (arithmetic on a signed operand, logical on an unsigned one) and needs the operand's
  // static type to choose. See `shiftRightExpr`.
  val binops = Map(
    "<operator>.addition" -> "+", "<operator>.subtraction" -> "-",
    "<operator>.multiplication" -> "*", "<operator>.division" -> "/",
    "<operator>.floorDiv" -> "/",
    "<operator>.modulo" -> "%", "<operator>.lessThan" -> "<",
    "<operator>.lessEqualsThan" -> "<=", "<operator>.greaterThan" -> ">",
    "<operator>.greaterEqualsThan" -> ">=", "<operator>.equals" -> "==",
    "<operator>.notEquals" -> "!=", "<operator>.logicalAnd" -> "&&",
    "<operator>.logicalOr" -> "||",
    // Bitwise. See the note above: these are not `&&`/`||`.
    "<operator>.and" -> "&", "<operator>.or" -> "|", "<operator>.xor" -> "^",
    "<operator>.shiftLeft" -> "<<",
    // Java's `>>>`: zero-filling, whatever the operand's sign. C has no such spelling.
    "<operator>.logicalShiftRight" -> ">>>"
  )

  /** `a >> b`, which is **two** operators.
    *
    * C's `>>` on a *signed* negative value is arithmetic (sign-extending); on an
    * *unsigned* value it is logical (zero-filling), and `0x80000000u >> 31` is `1` while
    * `((int)0x80000000) >> 31` is `-1`. Joern spells both `<operator>.arithmeticShiftRight`
    * — the name records the token, not the semantics — so the choice has to be made from
    * the left operand's static type, which is the only place the signedness survives.
    *
    * A `Val.int` carries no type, so this cannot be deferred to the interpreter: if the
    * exporter cannot tell, nobody downstream can, and the honest answer is a hole that
    * says which piece of information was missing.
    *
    * Outside the C family the token is unambiguous (Java/Kotlin `>>` is arithmetic and
    * `>>>` is the logical one; Python and JS have only the arithmetic form), so no type is
    * consulted there. */
  val unsignedTypeNames = Set(
    "uint8_t", "unsignedchar", "uint16_t", "unsignedshort", "uint32_t", "unsignedint",
    "unsigned", "uint64_t", "unsignedlonglong", "unsignedlong", "longunsigned",
    "size_t", "uintptr_t", "u8", "u16", "u32", "u64", "__u8", "__u16", "__u32", "__u64",
    "__be16", "__be32", "__be64", "__le16", "__le32", "__le64", "gfp_t", "dev_t",
    "sector_t", "phys_addr_t", "dma_addr_t", "resource_size_t", "uid_t", "gid_t"
  )
  val signedTypeNames = Set(
    "int8_t", "signedchar", "int16_t", "short", "shortint", "int32_t", "int", "signedint",
    "long", "signedlong", "int64_t", "longlong", "ptrdiff_t", "s8", "s16", "s32", "s64",
    "__s8", "__s16", "__s32", "__s64", "ssize_t", "loff_t", "off_t", "pid_t", "cycles_t",
    "ktime_t", "intptr_t"
  )

  /** Augmented assignment operators, `x op= e`, mapped to the binary operator they
    * expand to. `>>=` is absent for the reason `>>` is: it needs the target's type, and
    * `shiftRightOp` supplies it. */
  val augOps = Map(
    "<operator>.assignmentPlus" -> "+", "<operator>.assignmentMinus" -> "-",
    "<operator>.assignmentMultiplication" -> "*", "<operator>.assignmentDivision" -> "/",
    "<operator>.assignmentModulo" -> "%",
    "<operator>.assignmentAnd" -> "&", "<operator>.assignmentOr" -> "|",
    "<operator>.assignmentXor" -> "^", "<operator>.assignmentShiftLeft" -> "<<",
    "<operator>.assignmentLogicalShiftRight" -> ">>>"
  )

  // Operators whose Core meaning is wrong when an operand is a C `char*`. `+`/`-` are
  // pointer arithmetic, not concatenation; the orderings and equalities compare
  // addresses, not contents. Each keeps its own hole label so the cause is separable in
  // the ledger.
  val cStringUnsafe = Map(
    "<operator>.addition"           -> "cstr:pointer-arith",
    "<operator>.subtraction"        -> "cstr:pointer-arith",
    "<operator>.assignmentPlus"     -> "cstr:pointer-arith",
    "<operator>.assignmentMinus"    -> "cstr:pointer-arith",
    "<operator>.lessThan"           -> "cstr:address-compare",
    "<operator>.lessEqualsThan"     -> "cstr:address-compare",
    "<operator>.greaterThan"        -> "cstr:address-compare",
    "<operator>.greaterEqualsThan"  -> "cstr:address-compare",
    "<operator>.equals"             -> "cstr:address-equality",
    "<operator>.notEquals"          -> "cstr:address-equality"
  )

  // `<operator>.not` is **`~`**, not `!`. Joern's `logicalNot` is `!`; `not` is the
  // bitwise complement, in C, C++, Java and Python alike (`~x` in all four). Mapping it
  // to `"!"` — as this file did — turned `~CRYPTO_ALG_TYPE_MASK` into a boolean, and
  // `flags & ~MASK` into `flags && false`. That is the same mistake as `<operator>.and`
  // in its unary form, and it was live on every corpus, Python included.
  val unops = Map(
    "<operator>.minus" -> "-", "<operator>.logicalNot" -> "!", "<operator>.not" -> "~"
  )

  // ---- parameter star-ness ---------------------------------------------------
  //
  // `def f(*args, **kwargs)` is only half visible in the CPG: pysrc2cpg sets IS_VARIADIC
  // on `*args` and sets **nothing** on `**kwargs`, whose node is indistinguishable from an
  // ordinary parameter by any graph property. What *is* present is OFFSET, the parameter
  // name's byte offset in its source file, and the stars sit immediately before it. So the
  // discriminator is read from the source text rather than guessed at.
  //
  // This makes the exporter require the source tree that the CPG was built from. That is
  // a real new precondition, and it fails loudly (below) rather than quietly emitting a
  // `**kwargs` as a positional parameter -- which would be a silent mistranslation of
  // exactly the kind the hole mechanism exists to prevent.
  val srcRoot = cpg.metaData.root.l.headOption.getOrElse("")
  val fileTextCache = collection.mutable.Map.empty[String, Option[String]]
  def fileText(fn: String): Option[String] = fileTextCache.getOrElseUpdate(fn, {
    val cands = List(os.Path(srcRoot, os.pwd) / os.RelPath(fn), os.Path(fn, os.pwd))
    cands.find(p => os.exists(p) && os.isFile(p)).map(os.read(_))
  })

  /** How many `*`s immediately precede this parameter's name in the source.
    *
    * Python only. `*args`/`**kwargs` is a Python calling convention; in C and C++ a `*`
    * before a parameter name is a POINTER, and reading it as a splat would be a
    * mistranslation rather than a hole. Worse, the source-read below is a hard error by
    * design, so running this on C++ aborted the whole export -- every non-Python corpus
    * (V8, Linux) stopped exporting the moment the varargs work merged. Gate first, fail
    * loudly second. */
  def paramStars(p: MethodParameterIn, file: String): Int =
    if (!file.toLowerCase.endsWith(".py")) 0 else
    (for {
       off <- p.offset
       txt <- fileText(file)
       if off <= txt.length
     } yield {
       var i = off - 1
       var n = 0
       while (i >= 0 && txt.charAt(i) == '*') { n += 1; i -= 1 }
       n
     }).getOrElse {
       sys.error(s"export_ast: cannot read source for $file (root='$srcRoot') to decide "
               + s"whether parameter '${p.name}' is `*args` or `**kwargs`. Run the "
               + "exporter against the tree the CPG was built from.")
     }

/** `++`/`--`, and which way they go. In *statement* position all four are `x = x ± 1`
    * and nothing distinguishes prefix from postfix — the value is discarded. In
    * *expression* position they differ and neither is expressible, so `callExpr` holes
    * them under a `:value` label. Keeping the two positions apart is the whole point:
    * `for (i = 0; i < n; i++)` is translatable, `a[i++]` is not. */
  val incrOps = Map(
    "<operator>.preIncrement" -> "+", "<operator>.postIncrement" -> "+",
    "<operator>.preDecrement" -> "-", "<operator>.postDecrement" -> "-"
  )

  def hole(label: String): ujson.Obj  = ujson.Obj("k" -> "hole", "label" -> label)
  def holeS(label: String): ujson.Obj = ujson.Obj("k" -> "holeS", "label" -> label)
  val skip = ujson.Obj("k" -> "skip")

  /** Kernel synchronisation primitives, which a SEQUENTIAL semantics cannot observe.
    *
    * Core is a single-threaded interpreter: no threads, no scheduler, no interleaving.
    * In that semantics `spin_lock(&l)` acquires an uncontended lock and `spin_unlock(&l)`
    * releases it, and neither changes any value the program can read. Eliding them is not
    * an approximation of concurrent behaviour -- it is the exact behaviour of the
    * semantics Core defines, and the assumption it rests on ("execution is sequential") is
    * one Core makes globally, not a new one introduced here.
    *
    * This matters because these calls dominate the C hole count: 2,577 of the 2,867
    * `op:addressOf:local` sites across Linux `lib/` and `crypto/` -- 90% -- are `&lock`
    * passed to one of these. They were holes for a reason that has nothing to do with
    * pointers: `&l` cannot be represented, so the call could not be translated, so a
    * `mutex_lock` made its whole function unanalysable.
    *
    * WHAT IS GIVEN UP, stated plainly: Core will run a program whose locking is wrong
    * exactly as it runs one whose locking is right, so no data race, deadlock or missing
    * critical section is detectable here. That was already true -- Core has no threads to
    * race -- and it is now true without also losing the surrounding code.
    *
    * Kept deliberately narrow: acquire/release pairs for the standard lock families only.
    * A primitive that RETURNS something (`spin_trylock`, `down_read_trylock`) is NOT here,
    * because its result is a value the program branches on. */
  var syncElided: Int = 0
  var metaElided: Int = 0
  var useElided: Int = 0
  // `006-reduce-remaining-holes`, Story 3: counter for `freshExprVTemp`'s
  // never-collides synthetic name (a postfix increment/decrement used as a value).
  var exprVTempCounter: Int = 0

  /** Kernel declaration macros that emit METADATA, not code.
    *
    * `MODULE_LICENSE("GPL")` writes a string into an ELF section read by the module
    * loader; it compiles to no instructions and no function can observe it. Joern parses
    * C without running the preprocessor, so these arrive as `CASTProblemDeclaration`
    * nodes and became `stmt:UNKNOWN` holes -- and because they sit at file scope, each one
    * made its module initialiser unanalysable. On Linux `lib/` that is ~300 holes for
    * declarations with no runtime semantics at all.
    *
    * Same argument as eliding an uncontended lock in a sequential semantics: `Stmt.skip`
    * is the exact translation, not an approximation of one.
    *
    * `module_param` is deliberately NOT here. It binds a variable from the module command
    * line at load time, which is an assignment the program can observe -- eliding it would
    * be a claim about a value, not about metadata. */
  val kernelMetaMacros: Set[String] = Set(
    "MODULE_LICENSE", "MODULE_AUTHOR", "MODULE_DESCRIPTION", "MODULE_VERSION",
    "MODULE_ALIAS", "MODULE_PARM_DESC", "MODULE_FIRMWARE", "MODULE_DEVICE_TABLE",
    "MODULE_SOFTDEP", "MODULE_INFO", "MODULE_IMPORT_NS",
    "EXPORT_SYMBOL", "EXPORT_SYMBOL_GPL", "EXPORT_SYMBOL_NS", "EXPORT_SYMBOL_NS_GPL",
    "EXPORT_TRACEPOINT_SYMBOL", "EXPORT_TRACEPOINT_SYMBOL_GPL")

  /** Does this unparsed declaration start with one of them? */
  def isKernelMeta(code: String): Boolean = {
    val head = code.trim.takeWhile(c => c.isLetterOrDigit || c == '_')
    kernelMetaMacros.contains(head)
  }


  val syncPrimitives: Set[String] = Set(
    "spin_lock", "spin_unlock", "spin_lock_irq", "spin_unlock_irq",
    "spin_lock_bh", "spin_unlock_bh", "spin_lock_nested", "spin_lock_nest_lock",
    "raw_spin_lock", "raw_spin_unlock", "raw_spin_lock_irq", "raw_spin_unlock_irq",
    "read_lock", "read_unlock", "write_lock", "write_unlock",
    "read_lock_irq", "read_unlock_irq", "write_lock_irq", "write_unlock_irq",
    "mutex_lock", "mutex_unlock", "mutex_lock_nested",
    "rcu_read_lock", "rcu_read_unlock",
    "down_read", "up_read", "down_write", "up_write",
    "local_lock", "local_unlock", "local_irq_save", "local_irq_restore",
    "preempt_disable", "preempt_enable")


  def kidsOf(n: AstNode): List[AstNode] = n.astChildren.collect { case a: AstNode => a }.l

  /** A block's source text with its braces and any comments stripped, leaving only
    * what would actually execute. Distinguishes a genuinely empty `{}` body (or a
    * documented no-op like `{ /* NO-OP */ }`) from a body the C frontend failed to
    * parse into any AST children despite the source showing real statements --
    * confirmed against the SQLite CPG, where every zero-child block's stripped code
    * is either empty or at least 7 characters, with nothing in between. */
  def stripBlockCode(code: String): String = {
    val braceless = code.trim.stripPrefix("{").stripSuffix("}").trim
    braceless.replaceAll("/\\*(?s:.*?)\\*/", "").replaceAll("//[^\n]*", "").trim
  }

  /** Joern's ARGUMENT index: -1 = the callee/receiver expression, 0 = the implicit
    * `self`/`this` the Python frontend threads through, >=1 = the real arguments. */
  def aidx(n: AstNode): Int = n match {
    case e: Expression => e.argumentIndex
    case _             => -1
  }

  def isOp(n: AstNode, op: String): Boolean = n match {
    case c: Call => c.methodFullName == op
    case _       => false
  }

  // ---- Python private name mangling -----------------------------------------
  //
  // Inside a class body, CPython rewrites any identifier with **two or more leading
  // underscores and at most one trailing underscore** to `_<Class><name>`, with leading
  // underscores stripped from the class name. So `self.__maxsize` in `class Cache` is
  // really the attribute `_Cache__maxsize`, and `class _Foo`'s `__bar` is `_Foo__bar`.
  //
  // The CPG carries the *unmangled* source text on every FIELD_IDENTIFIER, so translating
  // it literally produces a read that misses and yields `unit` — the silently-wrong
  // category, not the absent category. This is the same shape as the `floorDiv` and
  // `<operator>.and` finds.
  //
  // The rewrite is **lexical and compile-time**: it depends on where the code is written,
  // not on the receiver's runtime class. That is exactly why it matters here — `Cache`'s
  // methods reach `_Cache__data` even when `self` is an `LRUCache`.
  //
  // A class's lexical path is its TypeDecl `fullName`, so the enclosing class is found the
  // same way closures found their enclosing function: walk the `fullName` prefixes and
  // test *membership* in a map of known full names, taking the simple name from the node
  // rather than splitting the string (see `enclosingFunctionBindings` for why).
  val classByFullName: Map[String, String] =
    cpg.typeDecl.isExternal(false).l
      .filter(_.method.name.l.contains("<body>"))
      .map(t => t.fullName -> t.name).toMap

  val enclClassCache = collection.mutable.HashMap.empty[String, Option[String]]

  /** The innermost class lexically enclosing `fn`, by simple name. */
  def enclosingClassOf(fn: String): Option[String] =
    enclClassCache.getOrElseUpdate(fn, {
      def go(cur: String): Option[String] = {
        val i = cur.lastIndexOf('.')
        if (i < 0) None
        else {
          val parent = cur.substring(0, i)
          classByFullName.get(parent).orElse(go(parent))
        }
      }
      go(fn)
    })

  /** CPython's rule, exactly: 2+ leading underscores, at most one trailing. `__x__` and
    * `_x` are untouched; a class whose name is all underscores does not mangle. */
  def mangleName(name: String, cls: Option[String]): String = cls match {
    case Some(c) if name.startsWith("__") && !name.endsWith("__") =>
      val bare = c.dropWhile(_ == '_')
      if (bare.isEmpty) name else "_" + bare + name
    case _ => name
  }

  /** The class lexically enclosing the method currently being translated. Mangling is a
    * property of the *writing* site, so this is the method's own class, never the
    * receiver's. */
  var currentClass: Option[String] = None

  /** The two CPG spellings of "select a field of something".
    *
    * C and C++ distinguish `o.f` (`fieldAccess`) from `p->f` (`indirectFieldAccess`), and
    * Joern keeps the distinction. **Core does not need it.** A `Val.ref` *is* the object,
    * so `Expr.field` on a ref already looks the field up in the heap object it names;
    * `p->f` and `(*p).f` are the same expression, and both are `Expr.field`. The C++
    * frontend gives `indirectFieldAccess` exactly the shape `fieldAccess` has —
    * `[pointerExpr, FIELD_IDENTIFIER]` — so this is a *mapping* gap, not a semantics gap,
    * and closing it is one line here rather than a constructor in `Syntax.lean`.
    *
    * Same story for `p[i]`: `indirectIndexAccess` has `indexAccess`'s shape and
    * `Expr.index`'s meaning. (What `Expr.index` then *does* with a C array is a separate
    * question, and the answer is an honest `index:unsupported` hole at run time — the
    * array itself has no Core value. The mapping is still the right one: it puts the
    * ignorance on the array, where it belongs, instead of on the subscript syntax.) */
  val fieldOps = Set("<operator>.fieldAccess", "<operator>.indirectFieldAccess")
  val indexOps = Set("<operator>.indexAccess", "<operator>.indirectIndexAccess")

  /** `e.f` — a fieldAccess is [receiver, FIELD_IDENTIFIER], except that when the Python
    * frontend has *resolved* the attribute it prepends the resolved METHOD_REF/TYPE_REF,
    * giving [METHOD_REF, receiver, FIELD_IDENTIFIER]. */
  def asField(n: AstNode): Option[(AstNode, String)] = n match {
    case c: Call if fieldOps.contains(c.methodFullName) =>
      val k = kidsOf(c)
      k.lastOption match {
        // The attribute name is mangled here, once, so every consumer — `field`,
        // `setField`, and the `mcall` method name, which all read it from this one
        // place — stays consistent with the definition names mangled below.
        case Some(f: FieldIdentifier) if k.size >= 2 =>
          Some((k(k.size - 2), mangleName(f.canonicalName, currentClass)))
        case _                                       => None
      }
    case _ => None
  }

  /** A resolved attribute reference: `Cls.meth` where Joern already knows the target. */
  def resolvedRef(n: AstNode): Option[AstNode] = n match {
    case c: Call if fieldOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case (m: MethodRef) :: _ :: _ :: Nil => Some(m)
        case (t: TypeRef) :: _ :: _ :: Nil   => Some(t)
        case _                               => None
      }
    case _ => None
  }

  /** `e[i]`. */
  def asIndex(n: AstNode): Option[(AstNode, AstNode)] = n match {
    case c: Call if indexOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case a :: b :: Nil => Some((a, b))
        case _             => None
      }
    case _ => None
  }

  /** Re-evaluable without observable effect. Augmented assignment (`o.f += 1`) is
    * desugared by duplicating the target expression, which is only faithful if
    * evaluating it twice is the same as evaluating it once. */
  def pureNode(n: AstNode): Boolean = n match {
    case _: Identifier | _: Literal | _: MethodParameterIn | _: TypeRef | _: MethodRef => true
    case c: Call if fieldOps.contains(c.methodFullName) =>
      asField(c).exists(p => pureNode(p._1))
    case c: Call if indexOps.contains(c.methodFullName) =>
      asIndex(c).exists(p => pureNode(p._1) && pureNode(p._2))
    case _ => false
  }

  /** `pureNode`, plus the container displays. Core's lists/tuples/dicts are *values*
    * (`Val.list`/`Val.tuple`/`Val.dict`), not heap objects, so building one allocates
    * nothing observable and re-evaluating `{}` is indistinguishable from evaluating it
    * once. This is what makes the frontend's `tmp0 = {}; tmp0` blocks removable. */
  def pureExpr(n: AstNode): Boolean = pureNode(n) || (n match {
    case c: Call if c.methodFullName == "<operator>.listLiteral" ||
                    c.methodFullName == "<operator>.tupleLiteral" ||
                    c.methodFullName == "<operator>.dictLiteral" => kidsOf(c).forall(pureExpr)
    case _ => false
  })

  // Classes declared in the analysed code. A call to one of these is construction, not
  // a plain function call. Joern usually marks it by resolving to `...Cls.__init__`, but
  // not always (unresolved bases, decorated classes), so we keep the name set as a
  // second, still-conservative signal.
  // A TYPE_DECL is also emitted for every *function* (its function-object type), so the
  // name alone would classify `f(x)` as construction. A TYPE_DECL from a real `class`
  // statement is the one carrying a `<body>` method for the class body.
  val classNames: Set[String] =
    cpg.typeDecl.isExternal(false).l
      .filter(_.method.name.l.contains("<body>"))
      .map(_.name).filterNot(_.contains("<")).toSet

  // ---- classes with a builtin base type --------------------------------------
  //
  // `class _HashedTuple(tuple)` is not an ordinary class: in CPython the instance *is* a
  // tuple, and `hashkey(0) == (0,)` is `True`. Core models this with `Val.bobj`, keyed by
  // `Program.builtinBases`, and the base is visible right here in the CPG and was
  // previously discarded. See STRATEGY.md §31/§33/§34 and `Autoform/BuiltinBase.lean`.
  //
  // Deliberately conservative in three ways, because a *wrong* base is a silent wrong
  // answer while a missing one is just the old opaque-reference behaviour:
  //
  //   * exactly one base, so multiple inheritance is never guessed at;
  //   * that base must be one of the four builtins `Core.BuiltinBase` models — `object`,
  //     `Exception` and everything transitive are left alone;
  //   * a short class name that resolves to two *different* bases anywhere in the corpus
  //     is dropped entirely, because `Expr.alloc` carries only the short name.
  val modelledBases = Set("tuple", "list", "dict", "str")

  val builtinBaseRows: List[(String, String, String)] =
    cpg.typeDecl.isExternal(false).l
      .filter(_.method.name.l.contains("<body>"))
      .filterNot(_.name.contains("<"))
      .flatMap { td =>
        val bases = td.inheritsFromTypeFullName
          .filterNot(b => b.isEmpty || b == "ANY" || b == "object" || b.endsWith(".object"))
        if (bases.size != 1) None
        else {
          // `tuple`, `builtins.tuple`, `__builtin.tuple`, `<unresolvedNamespace>.tuple`:
          // the frontends disagree on the prefix, never on the last segment.
          val short = bases.head.split('.').last.split(':').last
          if (modelledBases.contains(short)) Some((td.filename, td.name, short)) else None
        }
      }

  val conflictingBaseNames: Set[String] =
    builtinBaseRows.groupBy(_._2)
      .collect { case (n, rs) if rs.map(_._3).distinct.size > 1 => n }.toSet

  /** Builtin bases of the classes declared in one file, by short class name. */
  val classBasesByFile: Map[String, Map[String, String]] =
    builtinBaseRows.filterNot(r => conflictingBaseNames.contains(r._2))
      .groupBy(_._1).map { case (f, rs) => f -> rs.map(r => r._2 -> r._3).toMap }

  // ---- lexical scope analysis ------------------------------------------------
  //
  // Joern's `fullName` *is* the lexical nesting path: `f.py:<module>.outer.inner`,
  // `f.py:<module>.Cls.<body>.meth`. So the scope chain is recoverable by prefix, with no
  // need to walk AST parent edges (which differ between frontends).
  //
  // We need it for exactly one decision: is a `METHOD_REF` a plain `fnref` (a top-level
  // function, resolvable by name) or a `closure` (it reads a variable of an enclosing
  // *function*)? Module-level names are not captures — `Expr.name` falls back to the
  // globals frame — and class bodies are not a closure scope in Python, so only enclosing
  // function scopes count.
  val allMethods   = cpg.method.isExternal(false).l
  val methodByName = allMethods.map(m => m.fullName -> m).toMap

  /** Names a method binds itself: parameters plus identifier assignment targets — which
    * is exactly Python's rule (a name assigned anywhere in a body is local throughout),
    * minus the names a `global`/`nonlocal` statement explicitly un-localises.
    *
    * `m.local` is deliberately **not** used. A CPG fact that defeats the obvious version
    * of this analysis: pysrc2cpg emits a LOCAL in the *inner* method for every name it
    * closes over, and for module-level names it reads — `inner` has `locals = [k]` even
    * though `k` is the enclosing function's parameter. LOCAL here is a *reference*
    * declaration, not a binding, so trusting it reports that nothing ever captures. */
  val boundOf: Map[String, Set[String]] = allMethods.map { m =>
    val assigned = m.body.ast.isCall
      .filter(c => c.methodFullName.startsWith("<operator>.assignment"))
      .l.flatMap(c => kidsOf(c).headOption).collect { case i: Identifier => i.name }.toSet
    val unlocalised = m.body.ast.collect {
      case u: Unknown if u.code.trim.startsWith("global ") || u.code.trim.startsWith("nonlocal ") =>
        u.code.trim.dropWhile(_ != ' ').split(",").map(_.trim).filter(_.nonEmpty)
    }.l.flatten.toSet
    m.fullName -> ((m.parameter.name.toSet ++ assigned) -- unlocalised)
  }.toMap

  /** Identifier names a method mentions in its own body (not its nested methods'). */
  val usedOf: Map[String, Set[String]] = allMethods.map { m =>
    m.fullName -> m.body.ast.isIdentifier.filter(_.method.fullName == m.fullName).name.toSet
  }.toMap

  /** Methods lexically nested one level inside `fn`. */
  val nestedOf: Map[String, List[String]] =
    allMethods.map(_.fullName).groupBy { fn =>
      val i = fn.lastIndexOf('.')
      if (i < 0) "" else fn.substring(0, i)
    }.withDefaultValue(Nil)

  /** Free names of a method, including those its nested definitions leave free:
    *   free(m) = (used(m) ∪ ⋃ free(nested)) \ bound(m)
    * The nesting relation is a prefix order, so this terminates. */
  def freeOf(fn: String): Set[String] = {
    val used   = usedOf.getOrElse(fn, Set.empty)
    val inner  = nestedOf(fn).filter(_ != fn).flatMap(freeOf).toSet
    (used ++ inner) -- boundOf.getOrElse(fn, Set.empty)
  }

  /** Names bound by the enclosing *function* scopes of `fn` — skipping `<module>`
    * (globals) and `<body>`/`<meta>` (class bodies, which Python does not close over). */
  def enclosingFunctionBindings(fn: String): Set[String] = {
    def go(cur: String, acc: Set[String]): Set[String] = {
      val i = cur.lastIndexOf('.')
      if (i < 0) acc
      else {
        val parent = cur.substring(0, i)
        // The *simple* name has to come from the node, not from splitting the fullName:
        // `cachetools/keys.py:<module>` ends in a dot-segment `py:<module>`, so string
        // surgery would classify the module scope as an ordinary function and report that
        // every module-level `def` captures the module.
        val isFunctionScope =
          methodByName.get(parent).exists(p => !p.name.startsWith("<"))
        go(parent, if (isFunctionScope) acc ++ boundOf.getOrElse(parent, Set.empty) else acc)
      }
    }
    go(fn, Set.empty)
  }

  /** Every file-level pseudo-method, keyed by its `fullName` (`pkg/mod.py:<module>`).
    * This is the import resolver's whole notion of "a module in the analysed program". */
  val moduleFullNames: Set[String] =
    allMethods.filter(m => m.name == "<module>" || m.name == "<global>").map(_.fullName).toSet

  /** The file-level pseudo-method for a slash-separated module path, if the analysed
    * program contains it — either `p.py` or the package `p/__init__.py`. */
  def moduleAt(path: String): Option[String] = {
    // The empty path is the parse root itself. `moduleAtTolerant` never asks for it (see
    // the note there: the root would answer `import os` as readily as `import ansible`),
    // so no caller reaches this today. It is written out rather than left to
    // `"" + ".py:<module>"` accidentally matching a file literally named `.py`, because
    // `modulePath` does fold the root package to `""` and a future caller will pass it.
    if (path.isEmpty) {
      if (moduleFullNames.contains("__init__.py:<module>")) Some("__init__.py:<module>")
      else None
    } else {
      val a = path + ".py:<module>"
      val b = path + "/__init__.py:<module>"
      if (moduleFullNames.contains(a)) Some(a)
      else if (moduleFullNames.contains(b)) Some(b)
      else None
    }
  }

  /** `moduleAt`, tolerating the package prefix the parse root already stands for.
    *
    * An absolute import names a module by its *installed* path: `from ansible.errors
    * import AnsibleError`. But a CPG is built from a directory, and that directory is
    * usually the package itself — parse `ansible/lib/ansible` and `ansible.errors` lives
    * at `errors.py`, not `ansible/errors.py`. `moduleAt` therefore missed every
    * first-party absolute import and reported it `import:unresolved`, which on Ansible was
    * 3,550 holes — the single largest category in the corpus, and not a language gap at
    * all.
    *
    * So: try the path as given, then try dropping leading segments one at a time. Only a
    * module that actually exists in this CPG can match, and a shorter path is tried only
    * after every longer one has failed, so this cannot prefer a wrong module over a right
    * one. It CAN match a same-named module from a different package if the real target is
    * absent from the CPG — a genuine risk, and the reason the resolved name is recorded
    * rather than assumed. */
  def moduleAtTolerant(path: String): Option[String] = {
    val segs = path.split('/').filter(_.nonEmpty).toList
    // `until`, not `to`, and deliberately. Dropping *every* segment would ask for the
    // parse root, which is what a bare `import ansible` names when the CPG was built from
    // the `ansible` package itself -- but the CPG does not record the name of the
    // directory it was built from, so `import ansible` and `import os` are the same shape
    // and the root would answer both. Resolving `os` to the analysed package is a silent
    // mistranslation of every stdlib import; leaving the root package unnameable is a
    // hole. The hole wins.
    (0 until segs.length).view
      .map(i => moduleAt(segs.drop(i).mkString("/")))
      .collectFirst { case Some(m) => m }
  }

  /** A function value that reads a variable of an enclosing function is a *closure*;
    * one that does not is an `fnref`, which is cheaper and needs no captured frame. */
  val capturesEnv: Map[String, Boolean] = allMethods.map { m =>
    m.fullName -> freeOf(m.fullName).intersect(enclosingFunctionBindings(m.fullName)).nonEmpty
  }.toMap

  /** A method *definition* mangles too: `def __touch` in `class LRUCache` is stored as
    * `_LRUCache__touch`. Reference and definition must be mangled together — mangling
    * only the reference would trade a silently-wrong field read for a silently
    * unresolvable call, which is not an improvement. */
  def mangledFullName(fn: String): String = methodByName.get(fn) match {
    case Some(m) if fn.endsWith(m.name) =>
      val mg = mangleName(m.name, enclosingClassOf(fn))
      if (mg == m.name) fn else fn.dropRight(m.name.length) + mg
    case _ => fn
  }

  /** `target` is the *unmangled* CPG fullName: capture analysis is keyed on it, and the
    * emitted name is mangled on the way out so it matches the exported definition. */
  def fnValue(target: String): ujson.Obj = {
    val out = mangledFullName(target)
    if (capturesEnv.getOrElse(target, false)) ujson.Obj("k" -> "closure", "f" -> out)
    else ujson.Obj("k" -> "fnref", "v" -> out)
  }

  /** A class used as a value. Usually an `fnref` — but a class *defined inside a function*
    * whose methods read that function's variables carries an environment, and `Expr.closure`
    * names a function, not a class. `Expr.classClosure` is the constructor for that case:
    * it captures the environment at the point the `class` statement runs, `Expr.alloc`
    * stores it on the instance, and method dispatch on such an instance resolves free
    * names against it. Handing back a plain `fnref` here — the thing this refused to do
    * while there was no constructor — would have produced methods whose names were unbound. */
  def typeValue(target: String): ujson.Obj = {
    val cls = target.stripSuffix("<meta>")
    val captures = allMethods.exists(m =>
      m.fullName.startsWith(cls + ".") && capturesEnv.getOrElse(m.fullName, false))
    if (captures) ujson.Obj("k" -> "classClosure", "c" -> target)
    else ujson.Obj("k" -> "fnref", "v" -> target)
  }

  // ---- module objects ---------------------------------------------------------
  //
  // ## What a module is, in Core
  //
  // `import functools` used to be a hole because Core has no module value, and pointing
  // the name at `fnref "functools"` would claim `functools.reduce` is an attribute of a
  // *function*. But a module does not need a new `Val` constructor: it is an **object**.
  // `Obj` has a class and a field table, `Expr.field` on a `Val.ref` already reads a
  // field from the heap, and `Stmt.setField` already writes one — so a module is an
  // object whose fields are its top-level names, and `os.path.join` is an ordinary field
  // access with no new semantics at all.
  //
  // ## Where they come from
  //
  // One synthetic zero-argument initializer, `<module-objects>:<module>`, emitted **first**
  // in `moduleInits`. Its body allocates one object per Python module of this CPG and
  // binds it into the globals frame under a reserved key, then writes the members. All
  // allocations precede all field writes, so a package that contains a module which
  // imports the package back (`ansible` / `ansible.errors`) is fine, and nesting is
  // unbounded: `a.b.c.d` is three field reads.
  //
  // ## What a module object contains, and what it deliberately does not
  //
  // Members are the module's top-level **functions**, **classes** and **submodules** —
  // exactly the names whose value is fixed by the CPG and does not depend on when the
  // module body ran. Module-level *data* (`__version__ = "7.1.7"`) is **not** a member,
  // and that is not an oversight: Core has a single globals frame shared by every module,
  // so a module-level constant is not module-scoped in the first place, and copying its
  // value into the module object at init time would capture it *before* the module body
  // that computes it has run. Binding `mod.__version__` to `unit` is precisely the silent
  // wrong answer this project keeps finding.
  //
  // So a miss has to be loud. `Semantics.evalExpr`'s `.field` case answers `unit` for a
  // field an object does not have — a documented hazard — and for a module object it
  // instead answers the hole `module-attr:<name>`. That is why the class name carries the
  // `<module>` prefix: it is the marker the interpreter tests, and no `class` statement
  // in any language can produce a class of that name.
  //
  // ## Cost
  //
  // One heap object per module (Ansible: 584) allocated once by `initGlobals`, plus one
  // `setField` per exported member. Linear in the program, paid once, and nothing in the
  // per-call path changes.

  /** Python modules of this CPG. `<global>` — the C frontend's file scope — is excluded:
    * this is Python's `import`, and a C translation unit is not a value. */
  val pyModuleFullNames: List[String] =
    moduleFullNames.filter(_.endsWith(".py:<module>")).toList.sorted

  /** The globals key, and the class name, of a module object. The `<module>` prefix is
    * the marker `Semantics` tests to turn a missing attribute into a hole. */
  def moduleKey(mod: String): String = "<module>" + mod.stripSuffix(":<module>")

  /** A module's dotted path in slash form, with `/__init__` folded away, so that a
    * package and the modules inside it stand in a parent/child relation:
    * `cachetools/__init__.py:<module>` is `cachetools`, and the parse root is `""`. */
  def modulePath(mod: String): String = {
    val f = mod.stripSuffix(".py:<module>")
    if (f == "__init__") "" else if (f.endsWith("/__init__")) f.dropRight("/__init__".length) else f
  }

  /** A module used as a value: a read of the reserved global the initializer bound. */
  def moduleRef(mod: String): ujson.Obj = ujson.Obj("k" -> "name", "v" -> moduleKey(mod))

  /** Module-level **aliases**: `to_native = to_text` at file scope, where the right-hand
    * side names a top-level function or class of the same module.
    *
    * This is the one kind of module-level assignment whose value is fixed by the CPG
    * rather than by when the module body ran, so it is the one kind that can be a member
    * without the ordering problem that keeps module-level data out. It is not a
    * curiosity: `to_native = to_text` in `module_utils/common/text/converters.py` is
    * imported 87 times in Ansible, and every one of them was a hole.
    *
    * An alias to anything else — another module-level variable, a call, a conditional
    * rebinding — is *not* collected: its value depends on execution and a fixed field
    * would be a guess. Nor is a name assigned more than once, since which assignment a
    * later import sees is a flow-sensitive question and this is not a flow analysis. */
  val moduleAliasesOf: String => List[(String, String)] = {
    val cache = collection.mutable.HashMap.empty[String, List[(String, String)]]
    mod => cache.getOrElseUpdate(mod, methodByName.get(mod) match {
      case None => Nil
      case Some(m) =>
        val pairs = m.body.ast.isCall.filter(_.methodFullName == "<operator>.assignment").l
          .flatMap(a => kidsOf(a) match {
            case (t: Identifier) :: (r: Identifier) :: Nil => Some(t.name -> r.name)
            case _                                         => None
          })
        pairs.groupBy(_._1).collect { case (k, List(one)) => k -> one._2 }.toList
          .filter { case (k, v) =>
            k != v &&
            (methodByName.contains(mod + "." + v) || classByFullName.contains(mod + "." + v)) &&
            !methodByName.contains(mod + "." + k) && !classByFullName.contains(mod + "." + k)
          }.sortBy(_._1)
    })
  }

  /** The value a module-level alias stands for. */
  def aliasValue(mod: String, target: String): ujson.Obj =
    if (methodByName.contains(mod + "." + target)) fnValue(mod + "." + target)
    else typeValue(mod + "." + target + "<meta>")

  /** The exported members of a module: top-level functions, top-level classes, aliases of
    * either, and immediate submodules. See the note above for why module-level *data* is
    * absent. */
  def moduleMembers(mod: String): List[(String, ujson.Value)] = {
    def simple(k: String): Option[String] = {
      val n = k.drop(mod.length + 1)
      if (k.startsWith(mod + ".") && !n.contains('.') && !n.contains('<') && n.nonEmpty)
        Some(n) else None
    }
    val fns = methodByName.keys.toList.flatMap(k => simple(k).map(n => n -> (fnValue(k): ujson.Value)))
    val cls = classByFullName.keys.toList.flatMap(k =>
      simple(k).map(n => n -> (typeValue(k + "<meta>"): ujson.Value)))
    val als = moduleAliasesOf(mod).map { case (n, t) => n -> (aliasValue(mod, t): ujson.Value) }
    val here   = modulePath(mod)
    val prefix = if (here.isEmpty) "" else here + "/"
    val subs = pyModuleFullNames.filter { m2 =>
      val p = modulePath(m2)
      m2 != mod && p.startsWith(prefix) && p.length > prefix.length &&
        !p.drop(prefix.length).contains('/')
    }.map(m2 => modulePath(m2).drop(prefix.length) -> (moduleRef(m2): ujson.Value))
    // A name defined twice (a `def` shadowed by a submodule of the same name) keeps the
    // first in this fixed order rather than being decided by map iteration order, so the
    // export stays deterministic.
    (fns.sortBy(_._1) ++ cls.sortBy(_._1) ++ als.sortBy(_._1) ++ subs.sortBy(_._1))
      .foldLeft((Set.empty[String], List.empty[(String, ujson.Value)])) {
        case ((seen, acc), (n, v)) => if (seen(n)) (seen, acc) else (seen + n, (n, v) :: acc)
      }._2.reverse
  }

  /** The synthetic initializer that builds every module object, or `None` when this CPG
    * has no Python modules — which is what keeps C/C++/Java/Go/JS corpora byte-identical. */
  def moduleObjectsInit: Option[ujson.Obj] =
    if (pyModuleFullNames.isEmpty) None
    else {
      val allocs: List[ujson.Value] = pyModuleFullNames.map(m =>
        ujson.Obj("k" -> "setGlobal", "x" -> moduleKey(m),
                  "e" -> ujson.Obj("k" -> "alloc", "cls" -> moduleKey(m),
                                   "args" -> ujson.Arr())))
      val sets: List[ujson.Value] = pyModuleFullNames.flatMap(m =>
        moduleMembers(m).map { case (f, v) =>
          ujson.Obj("k" -> "setField", "r" -> moduleRef(m), "f" -> f, "v" -> v)
        })
      // Same iterative right-to-left construction as `seqOf`, and the same reason: an
      // O(1)-JVM-stack loop in place of `foldRight`, for this feature's second unbounded
      // producer of the same "seq" shape (research.md item 2).
      val body: ujson.Value = {
        val xs = (allocs ++ sets).toArray
        if (xs.length > maxSeqChainLen) maxSeqChainLen = xs.length
        var acc: ujson.Value = ujson.Obj("k" -> "skip")
        var i = xs.length - 1
        while (i >= 0) {
          acc = ujson.Obj("k" -> "seq", "a" -> xs(i), "b" -> acc)
          i -= 1
        }
        acc
      }
      // The `:<module>` suffix is what `render_lean.py` recognises as an initializer;
      // emitting this entry before the real ones puts it first in `moduleInits`, so every
      // module object exists before any module body runs.
      Some(ujson.Obj("name" -> "<module-objects>:<module>", "file" -> "",
                     "params" -> ujson.Arr(), "body" -> body))
    }

  // ---- per-method translation state ------------------------------------------
  // `moduleScope` is set while translating a `<module>`/`<global>` pseudo-method: every
  // identifier assignment there defines a module-level binding, so it becomes `setGlobal`.
  // `declaredGlobals` holds the names a `global x` statement rebound in the current
  // function, whose assignments must also write the globals frame rather than a local.
  var moduleScope     = false
  var declaredGlobals = Set.empty[String]
  // Set while translating a method from a C-family file, where a `char*` is an address,
  // not a string value.
  var cLikeFile       = false

  /** The label a `goto` may currently be translated as a `break` for — see `methodBody`.
    * `None` everywhere except inside the prefix of a function whose single `goto` target
    * has been proved to be a structured forward jump. */
  var gotoAsBreak: Option[String] = None

  /** C and C++ specifically, as opposed to the whole `cLike` *dialect* family (which
    * includes Java, Go, JS, TS and Kotlin). The constructor spelling `Cls::Cls`, the
    * implicit `this`, and stack object construction are C++ facts, not `cLike` facts. */
  var cppFile         = false
  // The source file of the method being translated. `import` is resolved relative to it.
  var currentFile     = ""
  // Serial number for the flag variable `try/except/else` needs; nested `try`s in one
  // function must not share it, or the inner one's flag would drive the outer's `else`.
  var elseFlagSeq     = 0
  /** `t -> (receiver, method)` for every `t = r.m` in the method being translated, where
    * `r` is a plain identifier. The Python frontend's `with` lowering binds the context
    * manager's `__enter__`/`__exit__` this way and then calls the *temporary*, which
    * leaves a call with no name at all. See `boundMethodCall`. */
  var boundMethods    = Map.empty[String, (String, String)]
  /** Receiver name -> attribute names read off it anywhere in the method being
    * translated. Corroborates the second form of `boundMethodCall`. */
  var attrsOf         = Map.empty[String, Set[String]]

  /** Static evidence that an operand is a C string/array-of-char. Joern's C frontend
    * types both `char *s` and `"abc"` as `char*`, including on literals. */
  /** The type Joern *wrote on the node*, which for C is very often `ANY`. */
  def nodeType(x: AstNode): String = x match {
    case c: Call              => c.typeFullName
    case i: Identifier        => i.typeFullName
    case l: Literal           => l.typeFullName
    case p: MethodParameterIn => p.typeFullName
    case t: TypeRef           => t.typeFullName
    case _                    => ""
  }

  /** Declared types of the locals and parameters of the method being translated. */
  var localTypes = Map.empty[String, String]

  /** Names this method selects a field off with `.`, and names it selects one off with
    * `->`. C's two spellings are a *syntactic* proof of what the name holds: `x.f`
    * cannot be written unless `x` is an aggregate, and `p->f` cannot be written unless
    * `p` is a pointer. Nothing else in the CPG says this as reliably — Joern's C frontend
    * leaves 2,848 of `lib/`'s address-taken identifiers typed `ANY` and absent from the
    * LOCAL table — and it is derived from the code rather than from type recovery, so it
    * cannot be defeated by a missing header. */
  var valueReceivers = Set.empty[String]
  var ptrReceivers   = Set.empty[String]

  /** `003-box-address-taken-locals`: names of every local/parameter of the method
    * being translated whose address is taken anywhere in its body, restricted to the
    * "local" shape (see `addrShape`) and excluding the already-handled aggregate
    * identity case -- see `boxableName` below for the exact eligibility predicate.
    * Populated once per `emit(m, isModule)` call and reset after, matching every
    * other per-method `var` in this file (`moduleScope`, `declaredGlobals`, etc.).
    * A name in this set has every plain read/write/address-of reference to it,
    * anywhere in the method, routed through a boxed heap cell instead of an ordinary
    * binding (`expr`'s `Identifier`/`MethodParameterIn` cases, `assignTo`, `incrStmt`,
    * and the `<operator>.addressOf` case in `callExpr`). */
  var boxedLocals = Set.empty[String]

  /** `003-box-address-taken-locals`: `pointerLocalName -> boxedLocalName`, for a
    * pointer-typed local that is PROVABLY, syntactically, an alias of one specific
    * boxed local for its entire lifetime in this method -- i.e. `p = &n` is the ONLY
    * assignment to `p` anywhere in the method (mirroring this file's own
    * `boundMethods` precedent: a name is trusted as "the" binding only when the
    * function assigns it in exactly one place -- see `emit` for the computation).
    *
    * This is what makes `*p`/`*p = v` translatable without a general points-to
    * analysis: `<operator>.indirection`'s operand is almost never the boxed name
    * itself (`&n` is usually assigned to a separate pointer variable `p`, then
    * dereferenced through `p`, not written as the redundant `*(&n)`), so the
    * indirection sites (`callExpr`'s `<operator>.indirection` case, and the matching
    * write case in `assignTo`) resolve through THIS map, not through `boxedLocals`
    * directly. A `p` reassigned to anything else anywhere in the method -- including
    * to a different boxed local's address -- is deliberately EXCLUDED (not merely
    * approximated): the "exactly one assignment, and it is this shape" requirement is
    * stronger than `boundMethods`'s own "exactly one ADDRESS-OF-shaped assignment"
    * check, because a `p` that is later repointed elsewhere and then dereferenced
    * must fall through to today's hole, not silently keep reading `n`'s box -- the
    * exact silent-wrong failure mode Constitution Principle III forbids. */
  var ptrAliases = Map.empty[String, String]

  /** `003-box-address-taken-locals`, Increment B: names of parameters of THIS method
    * that are dereferenced (`*p`/`*p = v`) and have been verified, across the WHOLE
    * analyzed program, to satisfy FR-006's closed-call-site precondition
    * (`closedOutParam` below) -- so `p` itself, not some OTHER name it aliases,
    * already directly holds the caller's `Val.ref` and can be read/written through
    * `Expr.field`/`Stmt.setField` with no `boxNew` prologue of its own (unlike a
    * boxed local/parameter, `p`'s VALUE, not `p`'s identity, is the thing that was
    * boxed -- by the CALLER's own boxing of the local whose address it passed).
    * Disjoint from `boxedLocals` by construction (a parameter whose OWN address is
    * taken within this method is Increment A's parameter-boxing case, not this one).
    * Populated once per `emit` call and reset after, matching every other per-method
    * `var` in this file. */
  var closedOutParams = Set.empty[String]

  /** `004-function-pointer-tracking`: `varName -> resolvedFunctionName`, for every
    * local/parameter of THIS method that is assigned a known, non-capturing,
    * in-program function or method value in exactly one place in the entire method
    * (whole-function single-assignment, mirroring `003-box-address-taken-locals`'s
    * own `ptrAliases` precedent exactly, applied to a different value shape -- a
    * function reference instead of an address-of-a-local). `resolvedFunctionName` is
    * already in the exact form `fnValue`/`mangledFullName` would use for a direct
    * call, so a `pointerCall` resolved through this map renders byte-identical to
    * what the exporter would already emit for a source-level direct call to that
    * function. Populated once per `emit` call and reset after, matching every other
    * per-method `var` in this file. */
  var fnPtrVars = Map.empty[String, String]

  /** `006-reduce-remaining-holes`, Story 5: array-typed locals of THIS method
    * admitted under the scope boundary (research.md §5.3, generalising `003`'s
    * Increment A from scalars to aggregates) -- `name -> element count`. A name
    * here gets an unconditional `boxFields` allocation prologue (one field per
    * element, decimal-string-keyed) and every `a[i]`/`&a[i]`/bare-`a`-as-pointer
    * site is rewritten through it. Populated once per `emit` call and reset after,
    * matching every other per-method `var` in this file. */
  var boxedArrays = Map.empty[String, Int]

  /** `006-reduce-remaining-holes`, Story 5: struct-typed locals of THIS method
    * admitted under the same scope boundary -- `name -> member-name list`. Also
    * closes research.md §5.1's latent gap (a plain struct local that looked
    * hole-free but silently depended on a `setField` special case that did not
    * cover it) for every struct this admits, as a structural consequence of the
    * unconditional prologue. */
  var boxedStructs = Map.empty[String, List[String]]

  /** `006-reduce-remaining-holes`, Story 5: plain (unboxed) pointer-typed locals
    * PROVABLY, for their whole lifetime in this method, holding an interior
    * pointer VALUE -- `p = &a[i]`, `p = &s.f`, or `p = a` (array-to-pointer decay),
    * as the ONLY assignment to `p` anywhere in the method (mirroring `ptrAliases`'s
    * own whole-function single-assignment discipline). Unlike `ptrAliases`, no
    * resolution target is needed: `p` itself already holds the `Val.iref` value
    * directly (an interior pointer is a VALUE, not a box), so `*p`/`*p = v`/`p++`
    * read/write/bump `p`'s own binding via `derefIref`/`setDerefIref`/ordinary
    * `binop` arithmetic (`applyBinop`'s new `Val.iref` arms) -- no allocation of
    * any kind for `p`. */
  var ptrIrefNames = Set.empty[String]

  /** `(owning type, member name) -> member type`, for the whole program.
    *
    * `007-reduce-remaining-holes-2`: Joern's C frontend emits multiple `TypeDecl`
    * nodes per struct when it parses the same declaration more than once across
    * translation contexts -- `AioFile`, `AioFile<duplicate>0`, `AioFile<duplicate>1`
    * -- and empirically (live-CPG-sampled on SQLite) the PLAIN, un-suffixed name is
    * often the one with ZERO members, while a `<duplicate>N` sibling carries the
    * real member list. A lookup here is always keyed by a USE SITE's own type
    * string (`bareType(staticTypeOf(receiver))`), which never itself contains a
    * `<duplicate>` suffix -- so without stripping it here first, the member-bearing
    * TypeDecl's data was simply never found, correct or not. Safe to strip
    * unconditionally: a member-EMPTY duplicate contributes no tuples to this map at
    * all (`td.member.l` is empty), so there is no risk of a real member list being
    * overwritten by an empty one after normalizing the key. */
  def stripDuplicateSuffix(name: String): String = name.replaceAll("""<duplicate>\d+$""", "")
  lazy val memberTypes: Map[(String, String), String] =
    cpg.typeDecl.l.flatMap { td =>
      td.member.l.map(mm => (stripDuplicateSuffix(bareType(td.fullName)), mm.name) -> mm.typeFullName)
    }.toMap

  /** The static type of an expression, **recovered from declarations when the node does
    * not carry one**.
    *
    * This is not a nicety. Measured on Linux `lib/`, 2,849 of 3,145 `&x` sites had
    * operand type `ANY` on the node — the C frontend simply does not propagate types onto
    * IDENTIFIER nodes — and `ANY` is the one answer that decides nothing: it cannot say
    * whether `&x` is the address of a struct (which Core represents, because a `Val.ref`
    * *is* an address) or the address of an `int` (which it does not). The declaration is
    * right there in the same method, on the LOCAL node, and the field's type is right
    * there on the owning TypeDecl's MEMBER.
    *
    * So the ledger's largest label was in large part a *type-recovery* gap masquerading
    * as a semantics gap. That is worth stating precisely, because the two have completely
    * different remedies and only one of them is expensive. */
  /** Whole-program: file-scope (`static` or plain global) C variable types, read
    * from the `Local`s Joern scopes to each file's own synthetic `<global>`
    * method. Confirmed live this session: `sqlite3SharedCacheList: BtShared*`,
    * `zMagicHeader: char[]`, and others resolve correctly there -- but
    * `localTypes` (`staticTypeOf`'s existing fallback below) is rebuilt PER
    * ORDINARY METHOD (`m.local.l`, which never includes a *different* method's
    * scope) and so never covers them, leaving a global's identifier no
    * whole-program alternative when the node's own `direct` type is `ANY`.
    *
    * `cpg.local` filtered by each Local's OWN `.method` back-edge, NOT
    * `cpg.method.name("<global>").local`'s forward traversal -- confirmed live,
    * this session, the two disagree: the forward direction found 468 globals,
    * the (correct) reverse direction 821, missing 353 real ones (`sqlite3Hooks`,
    * `sqlite3Autoext`, `mem0`, ...) including well-typed ones the forward
    * traversal had no excuse to drop. Not a hypothetical Joern quirk avoided on
    * principle: measured, and the reverse direction is the one this file now
    * uses everywhere it needs "every global", for exactly this reason.
    *
    * A global whose OWN `typeFullName` is one of Joern's generic anonymous-type
    * fallbacks (`struct`/`union`, no tag name to report) is rescued through a
    * SECOND path: Joern names an anonymous struct/union's synthesized `TypeDecl`
    * after the variable it is declared on, when that variable is the only thing
    * naming it. Confirmed live: `gMultiplex`'s own `Local.typeFullName` is the
    * bare word `struct`, but `cpg.typeDecl` has a real, member-bearing
    * `TypeDecl` named exactly `gMultiplex` (`pOrigVfs`, `sThisVfs`, ...) --
    * Joern recovered the full shape, it is just filed under the variable's own
    * name rather than a (nonexistent) tag name. Gated on a non-empty member
    * list, matching `structTypeDeclOf`'s own "skip a forward-only declaration"
    * discipline, so a global that is genuinely just an opaque anonymous blob
    * with no member evidence anywhere stays unresolved rather than guessed.
    *
    * Same "every declaration agrees, or it is not trusted at all" discipline
    * `typeAliases`'s own `byShort` map already uses for an ambiguous short name:
    * two unrelated `static`s in different files sharing a name (`state`, `buf`,
    * ...) are common in C, and are excluded here exactly like a same-named
    * `using` alias with two different targets is excluded there. Consulted only
    * as `staticTypeOf`'s LAST resort, after `localTypes` -- ordinary C scoping (a
    * local/parameter shadows a same-named global) is what that ordering already
    * encodes, unchanged. */
  lazy val globalTypes: Map[String, String] = {
    val anonymous = Set("struct", "union", "")
    val namedTypeDeclsWithMembers: Set[String] =
      cpg.typeDecl.filter(_.member.nonEmpty).map(_.name).toSet
    cpg.local.l
      .filter(_.method.name.headOption.contains("<global>"))
      .flatMap { l =>
        if (l.typeFullName.nonEmpty && l.typeFullName != "ANY" && !anonymous.contains(l.typeFullName))
          Some(l.name -> l.typeFullName)
        else if (namedTypeDeclsWithMembers.contains(l.name))
          Some(l.name -> l.name)
        else None
      }
      .groupBy(_._1)
      .collect { case (nm, entries) if entries.map(_._2).distinct.size == 1 =>
        nm -> entries.head._2 }
  }

  def staticTypeOf(x: AstNode): String = {
    val direct = nodeType(x)
    if (direct.nonEmpty && direct != "ANY") direct
    else x match {
      case i: Identifier => localTypes.getOrElse(i.name, globalTypes.getOrElse(i.name, direct))
      case c: Call if fieldOps.contains(c.methodFullName) =>
        asField(c).flatMap { case (r, f) =>
          // `p->f` and `o.f` are one node kind here, so strip any pointer depth off the
          // receiver's type before looking the member up on the owning declaration.
          val owner = bareType(staticTypeOf(r)).reverse.dropWhile(_ == '*').reverse
          memberTypes.get((owner, f))
        }.getOrElse(direct)
      // `*p` has the type `p` points to.
      case c: Call if c.methodFullName == "<operator>.indirection" =>
        kidsOf(c) match {
          case k :: Nil =>
            val t = bareType(staticTypeOf(k))
            if (t.endsWith("*")) t.dropRight(1) else direct
          case _ => direct
        }
      // `007-reduce-remaining-holes-2`: `a[i]` has the type `a`'s own elements are --
      // Joern does not always propagate this onto the index-access node itself (live-
      // CPG-sampled on SQLite: 1,763 of 2,933 `&a[i]:unknown-type` sites have a
      // perfectly resolved RECEIVER type -- `char**`, `int*`, `Foo[]` -- with only the
      // index EXPRESSION's own type left unresolved), so it is derived here from the
      // receiver the same way `<operator>.indirection` above derives `*p`'s type from
      // `p`'s: strip one level of `*`, or one `[N]`/`[]` array dimension.
      case c: Call if indexOps.contains(c.methodFullName) =>
        asIndex(c) match {
          case Some((r, _)) =>
            val t = bareType(staticTypeOf(r))
            if (t.endsWith("*")) t.dropRight(1)
            // Inlined rather than reusing `arrayShape` (defined later in this file):
            // referencing that `val` from this earlier `def` is a genuine forward-
            // reference error in this file's script-object compilation, not merely a
            // style choice -- confirmed by trying it first.
            else """^(.+)\[\d*\]$""".r.findFirstMatchIn(t) match {
              case Some(m) => m.group(1)
              case None    => direct
            }
          case None => direct
        }
      case _ => direct
    }
  }

  def isCString(n: AstNode): Boolean = {
    val ty = staticTypeOf(n).replace(" ", "")
    ty.matches("""(const|volatile|signed|unsigned)*char(\*|\[.*\]).*""")
  }

  /** A null-literal spelling (`NULL`, `nullptr`, `null`, `None`, `nil`) -- the same set
    * `expr`'s own literal dispatch recognises and renders as `Val.unit`. Used to let a
    * `char*` null CHECK (`z == NULL`, `z != NULL`) through `callExpr`'s `cStringUnsafe`
    * guard below: it needs no address/pointer-arithmetic semantics at all. `Val.beq`
    * (`Syntax.lean`) has an explicit wildcard `_, _ => false` for any two different `Val`
    * constructors, so `.str _ == .unit` evaluates to `false` (a real string is never
    * null) and `.unit == .unit` to `true` (both null) -- exactly the reasoning already
    * relied on for ordinary (non-string) pointer null checks, which never reach this
    * guard at all since `isCString` only matches `char*`/`char[]`. */
  def isNullLiteral(n: AstNode): Boolean = n match {
    case l: Literal =>
      val c = l.code.trim
      c == "None" || c == "null" || c == "nil" || c == "nullptr" || c == "NULL"
    case _ => false
  }

  // ---- C and C++ types ------------------------------------------------------
  //
  // Everything below is about telling apart three things that C spells with much the same
  // syntax: a **number**, a **pointer**, and an **object**. Core models the first and the
  // third; it has no model of an address at all. So each pointer-shaped construct is
  // routed by what its operand's static type says, and the ones that land on "address"
  // keep a hole whose label says *which* address shape it was.

  /** Strip cv-qualifiers and whitespace, so `const unsigned char *` compares equal to
    * `unsigned char*`. */
  def bareType(ty: String): String =
    ty.replace("const ", "").replace("volatile ", "")
      .replace("struct ", "").replace("union ", "").replace("enum ", "")
      .replace(" ", "")

  /** A pointer or an array — a value Core cannot represent, because it is an address.
    * `char[311]` is one of these: an array decays to a pointer. */
  def isPointerType(ty: String): Boolean = {
    val b = bareType(ty)
    b.endsWith("*") || b.matches(""".*\[.*\]""") || b == "std.nullptr_t"
  }

  /** Integer types whose width is fixed by the **language**, not by the target.
    *
    * `long` is not here, and its absence is the point. `long` is 64 bits under LP64
    * (Linux and macOS on x86-64 and arm64) and 32 bits under LLP64 (Windows): its width
    * is a property of the target *data model*, not of C. It used to be mapped to `i32`,
    * which meant `(long)x` truncated to 32 bits on the very platforms both C corpora
    * target — a well-typed, hole-free, silently wrong translation, which is the one
    * failure mode the ledger cannot see, because a hole-free function is what it counts
    * as good. The same is true of `size_t`, `ssize_t`, `ptrdiff_t`, `intptr_t` and
    * `uintptr_t`, all of which are pointer- or target-sized; they live in
    * `modelDependentInts` below and are resolved only against a *stated* data model.
    *
    * `char` is deliberately absent for a different reason: its signedness is
    * implementation-defined, so `(char)300` has no standard-mandated value.
    *
    * The kernel's `s8`..`u64` and `__s8`..`__u64` **are** here: those spellings exist
    * precisely to name an exact width and mean the same thing on every target. `__le32`
    * and friends are not, because their value is byte-swapped as well as narrowed and
    * only the narrowing would be modelled. */
  val intTypeNames: Map[String, String] = Map(
    "int8_t" -> "i8", "signedchar" -> "i8", "s8" -> "i8", "__s8" -> "i8",
    "uint8_t" -> "u8", "unsignedchar" -> "u8", "u8" -> "u8", "__u8" -> "u8",
    "int16_t" -> "i16", "short" -> "i16", "shortint" -> "i16", "s16" -> "i16",
    "__s16" -> "i16",
    "uint16_t" -> "u16", "unsignedshort" -> "u16", "u16" -> "u16", "__u16" -> "u16",
    "int32_t" -> "i32", "int" -> "i32", "signedint" -> "i32", "s32" -> "i32",
    "__s32" -> "i32",
    "uint32_t" -> "u32", "unsignedint" -> "u32", "unsigned" -> "u32", "u32" -> "u32",
    "__u32" -> "u32",
    "int64_t" -> "i64", "longlong" -> "i64", "s64" -> "i64", "__s64" -> "i64",
    "uint64_t" -> "u64", "unsignedlonglong" -> "u64", "u64" -> "u64", "__u64" -> "u64"
  )

  /** Integer types whose width is a property of the **target data model**.
    *
    * Three models are tabulated. `lp64` is Linux/macOS/BSD on any 64-bit architecture and
    * is the default, because that is what both C corpora — the Linux kernel and V8 — are
    * built for. `llp64` is 64-bit Windows, where `long` stays 32 bits. `ilp32` is any
    * 32-bit target. Passing `--param dataModel=unknown` (or any unlisted name) makes every
    * one of these types a hole labelled `op:cast:model-dependent`, which is the honest
    * answer when the model is not known: the alternative is to guess a width silently,
    * and guessing a width silently is exactly the defect this table exists to remove.
    *
    * The assumption does not have to be taken on trust when reading the output: the
    * emitted operator names the width it chose, so `(long)x` under `lp64` renders as
    * `Expr.unop "cast:i64"` and under `llp64` as `"cast:i32"`. The number is in the
    * artifact, at every site. */
  val dataModelTable: Map[String, Map[String, String]] = Map(
    "lp64" -> Map(
      "long" -> "i64", "longint" -> "i64", "signedlong" -> "i64",
      "unsignedlong" -> "u64", "longunsigned" -> "u64", "unsignedlongint" -> "u64",
      "size_t" -> "u64", "ssize_t" -> "i64", "ptrdiff_t" -> "i64",
      "intptr_t" -> "i64", "uintptr_t" -> "u64"),
    "llp64" -> Map(
      "long" -> "i32", "longint" -> "i32", "signedlong" -> "i32",
      "unsignedlong" -> "u32", "longunsigned" -> "u32", "unsignedlongint" -> "u32",
      "size_t" -> "u64", "ssize_t" -> "i64", "ptrdiff_t" -> "i64",
      "intptr_t" -> "i64", "uintptr_t" -> "u64"),
    "ilp32" -> Map(
      "long" -> "i32", "longint" -> "i32", "signedlong" -> "i32",
      "unsignedlong" -> "u32", "longunsigned" -> "u32", "unsignedlongint" -> "u32",
      "size_t" -> "u32", "ssize_t" -> "i32", "ptrdiff_t" -> "i32",
      "intptr_t" -> "i32", "uintptr_t" -> "u32")
  )

  /** Every type name whose width depends on the model, whichever model is in force. */
  val modelDependentNames: Set[String] = dataModelTable.values.flatMap(_.keys).toSet

  /** The widths in force, empty when the model is unknown. */
  val modelInts: Map[String, String] =
    dataModelTable.getOrElse(dataModel.toLowerCase, Map.empty)

  /** The typedef graph, taken from the CPG rather than from a table of names we happen to
    * recognise.
    *
    * V8 does almost no arithmetic on the spelling of a fixed-width type. It writes
    * `Address`, `word_t`, `Chunk`, `unsigned_type` — names introduced by `using` /
    * `typedef` inside a class or namespace — and the frontend records each one as a
    * TypeDecl carrying `aliasTypeFullName`, the type it was declared equal to. Following
    * that edge is the difference between *knowing* a width and guessing one: an alias
    * chain that ends at `uint32_t` is a proof that the C++ compiler will truncate to 32
    * bits, and a chain that ends anywhere else (a template parameter, a Windows type with
    * no declaration in this translation unit, a function-pointer type) ends the search
    * with no answer, which is what a hole is for. */
  lazy val typeAliases: Map[String, String] = {
    val ds = cpg.typeDecl.l.filter(_.aliasTypeFullName.nonEmpty)
    val byFull = ds.map(td => bareType(td.fullName) -> bareType(td.aliasTypeFullName.get)).toMap
    // A cast writes the *qualified* name it can see, and that is usually the TypeDecl's
    // `fullName`, so the qualified map is the primary one. The unqualified name is used
    // only when every declaration of that name in the program agrees on the target —
    // `Address` is `uintptr_t` in nine different V8 classes — because a short name that
    // means two things is exactly the case where guessing changes arithmetic.
    val byShort = ds.groupBy(td => bareType(td.name)).collect {
      case (n, tds) if tds.map(td => bareType(td.aliasTypeFullName.get)).distinct.size == 1 =>
        n -> bareType(tds.head.aliasTypeFullName.get)
    }
    byShort ++ byFull
  }

  /** The fixed-width tag for `ty`, following typedefs, or `None`.
    *
    * The loop is bounded by a visited set because the alias table really does contain
    * self-edges (Joern records the macro `__BEGIN_DECLS` as an alias of itself), and a
    * pointer or function type ends the search rather than being followed, so that
    * `DiscardVirtualMemoryFunction = DWORD(*)(PVOID, SIZE_T)` stays an address and not a
    * `u32`. There is deliberately no default: an unresolved name yields `None` and the
    * caller keeps a hole. */
  def resolveIntType(ty0: String): Option[String] = {
    var t    = bareType(ty0)
    var seen = Set.empty[String]
    var res  = Option.empty[String]
    var go   = true
    while (go) {
      if (intTypeNames.contains(t)) { res = intTypeNames.get(t); go = false }
      else if (modelInts.contains(t)) { res = modelInts.get(t); go = false }
      else if (seen.contains(t) || isPointerType(t) || t.contains("(")) go = false
      else {
        seen += t
        typeAliases.get(t) match {
          case Some(n) => t = n
          case None    => go = false
        }
      }
    }
    res
  }

  /** `005-sizeof-constant-folding`: byte count of a SCALAR type under the resolved
    * data model -- `resolveIntType`'s width label (`"i32"`/`"u64"`/...) divided by
    * 8, reused exactly as `<operator>.cast` already computes it, plus one
    * `sizeof`-specific addition `resolveIntType` deliberately does not cover: bare
    * `char`/`signed char`/`unsigned char` is unconditionally 1 byte, guaranteed by
    * the C standard itself regardless of data model -- unlike `resolveIntType`'s
    * OTHER exclusion of bare `char` (correct and load-bearing there: char's
    * *signedness* is implementation-defined, which matters for a cast's wrapping
    * behaviour and does not matter for a byte count). Deliberately NOT added to
    * the shared `intTypeNames` table -- that would silently change
    * `<operator>.cast`'s own, unrelated, already-correct behaviour for an
    * unrequested reason. `None` for anything this cannot resolve (an aggregate, an
    * opaque type, or a data-model-dependent type under an unspecified model). */
  def scalarSizeofBytes(ty: String): Option[Int] =
    if (Set("char", "signedchar", "unsignedchar").contains(bareType(ty))) Some(1)
    else resolveIntType(ty).map(w => w.drop(1).toInt / 8)

  /** `005-sizeof-constant-folding`: a pointer's `sizeof` is not a per-type fact at
    * all -- it is definitionally the target data model's own pointer width, the
    * same three `dataModel` values `dataModelTable` is already keyed by (LP64/
    * LLP64 = Pointers are 64-bit; ILP32 = Pointers are 32-bit). `None` for an
    * unspecified/unlisted model, mirroring `resolveIntType`'s own "guessing a
    * width silently is exactly the defect this exists to prevent" rule. */
  def pointerSizeofBytes: Option[Int] = dataModel.toLowerCase match {
    case "lp64" | "llp64" => Some(8)
    case "ilp32"          => Some(4)
    case _                => None
  }

  /** `005-sizeof-constant-folding`: `<element>[<N>]`, matching the OUTERMOST
    * dimension of a (possibly multi-dimensional) array's `typeFullName`.
    * `sizeofBytes` below recurses on `<element>`, which naturally unwinds a
    * multi-dimensional shape one dimension per call -- confirmed directly against
    * a live CPG, not assumed: `int arr[4][8]` is `typeFullName = "int[4][8]"`
    * (nested bracket suffixes, outermost last), so `sizeofBytes` on it correctly
    * computes `4 (int) * 4 * 8 = 128`. Research.md's own Phase 0 pass originally
    * scoped this to one dimension only because the multi-dimensional shape had not
    * yet been checked against a live CPG at spec-writing time; verified during
    * implementation and folded in here rather than left an unmeasured guess, per
    * this project's own "measure, don't assume" standard applied to a scope
    * decision made mid-implementation, not just at planning time. */
  val arrayShape = """^(.+)\[(\d+)\]$""".r

  /** `008-reduce-remaining-holes-3` US1: a local array's declared size, when
    * Joern's own type string does NOT carry a literal integer (`arrayShape`
    * above requires `\d+`) but a raw, unresolved size EXPRESSION instead --
    * Joern preserves the source text verbatim inside the brackets since it never
    * runs the preprocessor.
    *
    * Confirmed live against this corpus before writing this, not assumed: the
    * common real shape is NOT a bare macro name alone, but `MACRO +/- INTEGER`
    * arithmetic (`u8[NB+2]`, `char[MAX_PATHNAME+1]`, `char[SQLITE_MAX_PATHLEN+2]`
    * -- a defensive "reserve a few extra bytes" pattern) -- a first version of
    * this fix that only matched a bare macro name would have resolved close to
    * none of the 20 non-digit-bracket locals sampled live on this corpus. A
    * `sizeof(...)`-based size expression (`u8[sizeof(aJournalMagic)+4]`,
    * `u32[((int)(sizeof(aTable)/sizeof(aTable[0])))]`, also seen in that same
    * live sample) is explicitly NOT resolved here -- it needs a different
    * mechanism entirely and stays an honest hole; `macroSizeExpr` below simply
    * does not match that shape, so it falls through unchanged.
    *
    * Deliberately narrow and separate from `arrayShape`: this regex/helper pair
    * is used ONLY by `boxedArrays`'s own construction below, never touching
    * `arrayShape` itself or its other four call sites (`sizeofBytes`,
    * `memberSizeofBytes`, `closedIrefOutParam`'s array check) -- widening a
    * shared helper's behavior for one caller's new need is exactly the kind of
    * change that risks an unrelated silent regression elsewhere, so this stays
    * its own, narrowly-scoped mechanism instead. */
  val macroSizeExpr = """^([A-Za-z_]\w*)\s*([+-]\s*\d+)?$""".r

  /** A single `#define NAME <integer literal>` line -- one identifier, one
    * decimal integer, nothing else. Deliberately excludes function-like macros
    * (`#define F(x) ...`), multi-token expressions, and anything not a bare
    * integer -- those stay unresolved, matching FR-002's "never guess"
    * discipline. */
  // Confirmed live against this corpus, not assumed at design time: a trailing
  // `/* ... */` documentation comment on the SAME line as the value is the
  // common real shape (`#define NB 3  /* (NN*2+1): Total pages... */` in
  // btree.c) -- a first version of this regex without the optional trailing
  // comment matched zero real `#define` lines in this corpus at all, only
  // caught by adding a temporary diagnostic print and checking the ACTUAL source
  // line rather than assuming the "nothing else on the line" shape from
  // spec.md's own FR-002 wording meant literally nothing, comments included.
  val defineLine = """^\s*#\s*define\s+([A-Za-z_]\w*)\s+(\d+)\s*(?:/\*.*\*/\s*)?$""".r

  /** Per-file `#define` table, built once per declaring file and cached (the
    * same file's own macros are checked for every candidate array declared in
    * it). A name defined more than once in the same file with different values
    * is dropped from the table entirely -- ambiguous, not guessed, the same
    * "every declaration agrees, or it is not trusted" discipline `typeAliases`
    * and `globalTypes` already use elsewhere in this file. A macro defined in a
    * DIFFERENT file (a shared header) is intentionally invisible here: reading
    * only the declaring file's own text, not following `#include`, is what
    * keeps this a bounded, single-file text scan rather than a second
    * preprocessor. */
  // `Method.filename` is relative to the ORIGINAL `joern-parse` input root, not
  // to this script's own working directory -- confirmed live: `m.filename` for a
  // `btree.c` method is the bare string `"btree.c"`, which does not exist relative
  // to `cartographer/`'s own cwd. `cpg.metaData.root` recovers the root path
  // Joern itself recorded at parse time (confirmed live: joining it with a bare
  // filename resolves to a real, readable file), so every lookup below joins
  // through it rather than trusting a bare filename to already be openable.
  lazy val sourceRoot: Option[String] = cpg.metaData.root.headOption
  val fileDefinesCache = scala.collection.mutable.Map.empty[String, Map[String, Int]]
  def fileDefines(relPath: String): Map[String, Int] = fileDefinesCache.getOrElseUpdate(relPath, {
    try {
      val f = new java.io.File(relPath)
      val resolved = if (f.isAbsolute) f else sourceRoot.map(r => new java.io.File(r, relPath)).getOrElse(f)
      val found = scala.io.Source.fromFile(resolved).getLines()
        .flatMap(defineLine.findFirstMatchIn).map(m => m.group(1) -> m.group(2).toInt).toList
      found.groupBy(_._1).collect { case (nm, vs) if vs.map(_._2).distinct.size == 1 => nm -> vs.head._2 }
    } catch { case _: Exception => Map.empty }
  })

  /** Resolve a raw array-size expression (the bracket contents Joern preserved
    * verbatim) against the declaring file's own macro table -- `IDENT`,
    * `IDENT + INTEGER`, or `IDENT - INTEGER` only. Anything else (a `sizeof`, a
    * multi-term expression, an identifier not in this file's own table) yields
    * `None`, leaving the declaration exactly where it is today. */
  def resolveMacroArraySize(sizeExpr: String, filePath: String): Option[Int] =
    macroSizeExpr.findFirstMatchIn(sizeExpr.trim).flatMap { m =>
      fileDefines(filePath).get(m.group(1)).map { base =>
        Option(m.group(2)).map(_.filterNot(_.isWhitespace)) match {
          case Some(s) if s.startsWith("+") => base + s.drop(1).toInt
          case Some(s) if s.startsWith("-") => base - s.drop(1).toInt
          case _                            => base
        }
      }
    }

  /** `005-sizeof-constant-folding`: byte count of a `sizeof` operand's type, trying
    * each resolvable shape in turn. The ARRAY check MUST run before the pointer
    * check, not after: `isPointerType` (used elsewhere in this file for the
    * genuinely correct reason that an array decays to a pointer in expression
    * context) would otherwise classify `char[16]` as pointer-shaped and silently
    * return the POINTER width instead of the array's actual size -- a wrong
    * answer, not merely a missed case. Found and fixed before any code shipped, by
    * reading `isPointerType`'s own definition rather than assuming shape checks
    * commute. */
  def sizeofBytes(ty: String): Option[Int] = bareType(ty) match {
    case arrayShape(elem, n) => sizeofBytes(elem).map(_ * n.toInt)
    case _                   => scalarSizeofBytes(ty).orElse(if (isPointerType(ty)) pointerSizeofBytes else None)
  }

  /** Is the target of a cast a pointer or a reference?
    *
    * This cannot be decided from `typeFullName` alone, and the failure was live: for
    * `reinterpret_cast<uint8_t*>(address)` the C++ frontend records the type-ref node's
    * `typeFullName` as `uint8_t`, with the `*` surviving only in the node's `code`. Read
    * from the type alone, a **pointer reinterpretation became an 8-bit truncation** —
    * `v8::base::PageAllocator::ReleasePages` translated `reinterpret_cast<uint8_t*>(addr)
    * + new_size` as `wrap u8 addr + new_size`, which is well-typed, hole-free, and
    * silently wrong arithmetic. Exactly the class of bug the ledger exists to make
    * impossible, so the surface syntax is consulted as well and a `*`, `&` or `[]` in the
    * written type sends the cast to the address hole where it belongs. */
  def castTargetIsPointer(tref: AstNode, ty: String): Boolean =
    isPointerType(ty) || {
      val c = bareType(tref.code)
      c.endsWith("*") || c.endsWith("&") || c.matches(""".*\[.*\]""")
    }

  /** `007-reduce-remaining-holes-2` US3: is a cast's OPERAND (as opposed to its target,
    * `castTargetIsPointer` above) itself pointer-shaped -- i.e. is reinterpreting it as a
    * different pointer type a representation-preserving no-op under `Autoform.Core`'s
    * heap model?
    *
    * Confirmed sound by reading `Semantics.lean`'s `derefIref`/`irefIndex`/`irefField`
    * directly (research.md US3): dereferencing a `Val.iref`/`Val.ref` resolves purely via
    * the object's address and a selector fixed when that value was produced -- never by
    * the casting expression's compile-time target type. So if the operand already
    * evaluates to a pointer-shaped value, the cast changes nothing observable and can be
    * dropped.
    *
    * Two ways an operand is confirmed pointer-shaped: its own static type is ALSO a
    * pointer type (mirrors `castTargetIsPointer`'s own `isPointerType` check, just aimed
    * at the other side of the cast), or it is a direct `&expr` -- an address-of
    * expression is a pointer/reference value by construction regardless of what type
    * inference reports for it, and `expr()`'s own `<operator>.addressOf` handling already
    * correctly resolves every such case on its own terms (a boxed array/struct interior
    * pointer, an aggregate identity, a function identity, or -- if none of those apply --
    * its own honestly-labeled `op:addressOf:*` hole, which then correctly propagates as
    * this cast's own translation too, exactly as it should).
    *
    * An operand that is neither -- most commonly an integer literal or arithmetic
    * expression, e.g. `(int*)0` -- has no `Ref`/`iref` to pass through: `Autoform.Core`
    * has no representation for "a pointer to an arbitrary, non-heap-allocated address",
    * so this MUST NOT be folded into the identity translation (see the
    * `op:cast:pointer:int-to-pointer` branch in `callExpr`, below). */
  def castOperandIsPointerShaped(operand: AstNode): Boolean =
    isPointerType(staticTypeOf(operand)) || isOp(operand, "<operator>.addressOf")

  /** `char` is deliberately absent from `intTypeNames`: its signedness is
    * implementation-defined, so `static_cast<char>(300)` has no standard-mandated value.
    * Naming it separately keeps the hole label specific instead of guessing a sign. */
  def isArithType(ty: String): Boolean =
    intTypeNames.contains(bareType(ty)) || modelDependentNames.contains(bareType(ty))

  /** Aggregates — struct, union, class — for which the CPG carries **positive
    * evidence**: a TypeDecl that has members, or (C++) one that has methods.
    *
    * The test has to be positive. The tempting rule is "not a pointer and not a number,
    * therefore a struct", and it is wrong in the dangerous direction: `loff_t`, `s64` and
    * every other kernel scalar typedef would pass it, and `&some_s64` would then
    * translate to the identity — a well-typed program silently aliasing a number as an
    * object. That is the exact failure mode this ledger exists to prevent, so a type we
    * merely *cannot classify* gets its own hole label (`opaque-type`) rather than the
    * benefit of the doubt. */
  lazy val aggregateNames: Set[String] = {
    val ds = cpg.typeDecl.l.filter(td => td.member.nonEmpty || td.method.nonEmpty)
    (ds.map(_.fullName) ++ ds.map(_.name)).map(bareType).toSet ++ fieldOwnerTypes
  }

  /** Types the *program itself* selects a field off. `x.f` or `p->f` is a proof that `x`
    * is an aggregate that no type table is needed to supply, and on the kernel it is the
    * evidence that actually exists: Joern records 4,892 TypeDecls for `lib/` but members
    * for only 753 of them, so a members-only test calls most real structs unknown.
    * Field selection is derived from the code, not from the frontend's type recovery,
    * which is exactly why it survives where the type table does not. */
  lazy val fieldOwnerTypes: Set[String] =
    cpg.call.l.filter(c => fieldOps.contains(c.methodFullName)).flatMap { c =>
      val ks = c.astChildren.collect { case a: AstNode => a }.l
      if (ks.size < 2) None
      else {
        val t = bareType(nodeType(ks(ks.size - 2)))
        val bare = t.reverse.dropWhile(_ == '*').reverse
        if (bare.isEmpty || bare == "ANY") None else Some(bare)
      }
    }.toSet

  val nonClassScalars = Set("ANY", "void", "bool", "char", "float", "double", "")

  /** Kernel and C scalar typedefs beyond `intTypeNames`, named so that `&x` on one of
    * them is reported as `scalar` (a location model would fix it) rather than as
    * `opaque-type` (better types would fix it). */
  val scalarTypedefs = Set(
    "s8", "s16", "s32", "s64", "u8", "u16", "u32", "u64", "loff_t", "ssize_t",
    "off_t", "gfp_t", "pid_t", "uid_t", "gid_t", "dev_t", "sector_t", "phys_addr_t",
    "dma_addr_t", "resource_size_t", "cycles_t", "ktime_t", "wchar_t", "intptr_t",
    "longdouble", "signedlong", "unsignedlong", "longunsigned", "int128_t", "__u8",
    "__u16", "__u32", "__u64", "__s8", "__s16", "__s32", "__s64", "__be16", "__be32",
    "__be64", "__le16", "__le32", "__le64", "bool_t", "size_type"
  )

  /** The type is an aggregate, so `&it` is the identity: a Core class instance already
    * *is* a heap address, and taking its address changes nothing. */
  def isClassType(ty: String): Boolean = {
    val raw = ty.replace("const ", "").replace("volatile ", "").trim
    val b   = bareType(ty)
    if (isPointerType(b) || isArithType(b) || nonClassScalars.contains(b) ||
        scalarTypedefs.contains(b)) false
    // Joern's C frontend spells the tag in the type name (`unioncodetag_ref`), which is
    // conclusive evidence on its own.
    else raw.startsWith("struct") || raw.startsWith("union") || raw.startsWith("class") ||
         aggregateNames.contains(b)
  }

  // ---- `006-reduce-remaining-holes`, Story 4: struct/union `sizeof` ----------

  /** Every `TypeDecl` of the program, by its bare (tag-stripped) name -- `cpg.typeDecl`
    * itself, not `aggregateNames`, because layout resolution needs the member LIST,
    * not merely a name to test membership against.
    *
    * `007-reduce-remaining-holes-2`: grouped by `stripDuplicateSuffix`'d name, for the
    * exact same reason `memberTypes` needs it (that doc comment has the full
    * explanation) -- without this, a struct's real, member-bearing `TypeDecl`
    * (`Foo<duplicate>0`) groups SEPARATELY from the plain-named, member-empty one
    * (`Foo`) that every use site's own type string actually resolves to, so
    * `.find(_.member.nonEmpty)` below never sees it. */
  lazy val typeDeclsByName: Map[String, List[TypeDecl]] =
    cpg.typeDecl.l.groupBy(td => stripDuplicateSuffix(bareType(td.fullName)))

  /** The `TypeDecl` actually carrying `ty`'s members, if this program has one --
    * `.find(_.member.nonEmpty)` skips a forward-only declaration in favour of the
    * real definition, mirroring `structTypeDeclOf`'s own callers' need for a member
    * LIST, not merely a name. */
  def structTypeDeclOf(ty: String): Option[TypeDecl] =
    typeDeclsByName.get(bareType(ty)).flatMap(_.find(_.member.nonEmpty))

  /** A bitfield member (research.md §4): `typeFullName` alone stays the plain base
    * type (`int x : 3` has `typeFullName=int`), so the width survives only in the
    * member's own surface text -- the same "read `.code` when the type alone does
    * not carry the fact" pattern `castTargetIsPointer` already established. No
    * attempt is made to sum bitfield widths into a byte count: C's own bit-to-byte
    * packing for adjacent bitfields is itself platform/ABI-defined, and this
    * project has no existing model for it. */
  val bitfieldSuffix = """:\s*\d+\s*$""".r
  def isBitfieldMember(m: Member): Boolean = bitfieldSuffix.findFirstIn(m.code).isDefined

  /** A struct-level packing/alignment attribute, visible verbatim on `TypeDecl.code`
    * (research.md §4). Disqualifies the whole struct unconditionally -- not
    * narrowed to specifically `packed`/`aligned`, the same conservative-by-
    * construction choice `005`'s own `modelDependentNames` gate already made,
    * because distinguishing a layout-affecting attribute from an unrelated one
    * (`__attribute__((deprecated))`) would need a hardcoded allowlist that could
    * misclassify an attribute never tested against a live corpus. */
  def hasPackingAttribute(td: TypeDecl): Boolean =
    td.code.contains("__attribute__") || td.code.contains("#pragma pack")

  /** A member's own size: `sizeofBytes` for a scalar/pointer/array-of-scalar member,
    * recursing into `aggregateSizeofBytes` below for a member that is itself an
    * aggregate (research.md §4's scope correction -- resolved HERE, statically,
    * not deferred to Story 5's runtime heap model), and recursing through
    * `sizeofBytes`'s own `arrayShape` one dimension at a time for an array of
    * aggregates.
    *
    * A flexible array member is checked EXPLICITLY, first, rather than trusted to
    * fall through: research.md §4 assumed `char[]` (a flexible array member's own
    * `typeFullName`, confirmed live) already reaches `None` via `sizeofBytes`'s
    * `arrayShape` regex requiring a digit, PLUS `isPointerType` rejecting it too --
    * checked directly against a live fixture during implementation (not merely
    * re-trusted from the citation) and found WRONG for the second half:
    * `isPointerType`'s own `.*\[.*\]` regex matches EMPTY brackets as readily as
    * a sized array, so `char[]` silently fell through to the POINTER width (8),
    * not `None` -- exactly the "well-typed, hole-free, silently wrong" failure
    * mode this whole project exists to catch, caught here before it shipped. */
  def memberSizeofBytes(ty: String): Option[Int] = bareType(ty) match {
    case t if t.endsWith("[]")  => None
    case arrayShape(elem, n)    => memberSizeofBytes(elem).map(_ * n.toInt)
    case _ => sizeofBytes(ty).orElse(if (isClassType(ty)) aggregateSizeofBytes(ty) else None)
  }

  /** `006-reduce-remaining-holes`, Story 4 (FR-009/FR-010): the byte size of a
    * struct or union whose full layout is resolvable -- standard C aggregate
    * layout, each member placed at the next offset that is a multiple of its own
    * alignment (alignment == the member's own resolved size, consistent with this
    * project's existing scalar-sizing convention), a union's members instead all
    * overlapping at offset zero, and the whole aggregate's size rounded up to its
    * own alignment (the max of its members'). `None` -- stays the existing
    * `op:sizeOf:object` hole, unrelabelled, exactly as today -- when the struct
    * itself carries a packing attribute, has no member list this program can see,
    * or any one member is a bitfield or has its own unresolvable size. */
  def aggregateSizeofBytes(ty: String): Option[Int] =
    structTypeDeclOf(ty).flatMap { td =>
      if (hasPackingAttribute(td)) None
      else {
        val members = td.member.l
        if (members.isEmpty) None
        else {
          val isUnion = td.code.trim.startsWith("union")
          var offset = 0
          var maxSize = 0
          var maxAlign = 1
          var ok = true
          members.foreach { m =>
            if (ok) {
              if (isBitfieldMember(m)) ok = false
              else memberSizeofBytes(m.typeFullName) match {
                case Some(sz) if sz > 0 =>
                  if (sz > maxAlign) maxAlign = sz
                  if (isUnion) { if (sz > maxSize) maxSize = sz }
                  else { offset = ((offset + sz - 1) / sz) * sz; offset += sz }
                case _ => ok = false
              }
            }
          }
          if (!ok) None
          else {
            val raw = if (isUnion) maxSize else offset
            Some(((raw + maxAlign - 1) / maxAlign) * maxAlign)
          }
        }
      }
    }

  /** A hole label naming what kind of address defeated us, so the ledger separates
    * "pointer to a number" (which needs a location model) from "we could not tell"
    * (which needs better types). */
  /** What *shape* of thing had its address taken. The kind (below) says what Core would
    * need in order to represent the pointee; the shape says which of four distinct pieces
    * of work would close the case, and they are not the same piece of work:
    *
    *   * `local`   — the address of a variable. Needs a model of a variable's *location*.
    *   * `field`   — `&p->f`. Free for an object-typed field (a `Val.ref` already is its
    *                 own address); needs a location for a scalar one.
    *   * `element` — `&a[i]`. Needs arrays as heap objects, and then interior pointers.
    *   * `call`    — `&f(...)`, or an address taken of something computed. Rare.
    *
    * Reporting them merged is what made `op:addressOf` look like one problem. */
  def addrShape(n: AstNode): String = n match {
    case _: Identifier | _: MethodParameterIn => "local"
    case c: Call if fieldOps.contains(c.methodFullName) => "field"
    case c: Call if indexOps.contains(c.methodFullName) => "element"
    case _: Call => "call"
    case other   => other.label.toLowerCase
  }

  def addrKind(ty: String): String = {
    val b = bareType(ty)
    if (b.isEmpty || b == "ANY")   "unknown-type"
    else if (isPointerType(b))     "pointer"
    else if (isClassType(ty))      "object"
    else if (isArithType(b) || scalarTypedefs.contains(b) ||
             nonClassScalars.contains(b))  "scalar"
    // A name, but no evidence for what is behind it. This is a *type* gap, not a
    // semantics gap, and it is closed by a better frontend rather than by a location
    // model — which is why it must not be filed under either of the other two.
    else                           "opaque-type"
  }

  /** `003-box-address-taken-locals`: is `&n` (for `n` the sole operand of an
    * `<operator>.addressOf` call) the pre-existing "identity" case -- an object whose
    * own value already IS its address, needing no box? Extracted out of the
    * `<operator>.addressOf` case in `callExpr` below so the boxing pre-scan
    * (`boxableName`) and the translation itself can never drift apart: both must
    * agree on exactly the same non-aggregate locals, or a name could be added to
    * `boxedLocals` that the addressOf site still treats as an identity (or vice
    * versa), either of which is a wrong translation, not a hole. */
  def addressOfIsAggregate(n: AstNode): Boolean = {
    val ty = staticTypeOf(n)
    val nm = n match { case i: Identifier => Some(i.name); case _ => None }
    isClassType(ty) ||
    (addrKind(ty) == "unknown-type" &&
     nm.exists(nn => valueReceivers.contains(nn) && !ptrReceivers.contains(nn)))
  }

  /** The declared (un-mapped) name of `n`, if `n` is a local variable or parameter
    * reference -- `None` for anything else, in particular for a `this` reached as
    * something other than a plain identifier. */
  def rawLocalOrParamName(n: AstNode): Option[String] = n match {
    case i: Identifier        => Some(i.name)
    case p: MethodParameterIn => Some(p.name)
    case _                    => None
  }

  /** `003-box-address-taken-locals`: if `n` (the sole operand of an `&`) is eligible
    * to be boxed under this feature's scope, the name it is tracked under in
    * `boxedLocals` (`localName`-mapped, matching every site that reads or writes it
    * through `expr`/`assignTo`) -- `None` otherwise, meaning `&n` falls through to
    * the existing hole path unchanged.
    *
    * Four conditions, each closing a real way this could go silently wrong rather
    * than staying an honest hole:
    *
    *   - `addrShape(n) == "local"` (FR-001's scope: a plain local or parameter, not
    *     an array element, struct field, or call result).
    *   - not the pre-existing aggregate identity case (`addressOfIsAggregate`) --
    *     that path already works and must not be disturbed (FR-007).
    *   - `n`'s raw name is a key of `localTypes`, i.e. an ACTUAL local or parameter
    *     `Local`/`MethodParameterIn` of the method being translated right now, not
    *     merely an identifier that happens to resolve to a global at read time.
    *   - not `moduleScope` (a `<module>` pseudo-method's identifiers are file-level
    *     globals: every assignment there is `setGlobal`, not `assign`, and a boxed
    *     local's write-rewrite assumes `assign`/`setField`, which would silently
    *     create a phantom local invisible to every `setGlobal` read elsewhere), not a
    *     name a `global` statement rebound (`declaredGlobals`, same reason), and not
    *     `this` in a C++ method (`this`/`self` is bound by `applyFunc`'s receiver
    *     mechanism, not through `bindParams`'s ordinary parameter list -- boxing it
    *     would corrupt every method-call dispatch on `self` in the function, not just
    *     the address-of site). */
  /** The AST parent of a node, or `None` for a root. `astParent` throws on a root. */
  def parentOf(n: AstNode): Option[AstNode] = scala.util.Try(n.astParent).toOption

  def boxableName(n: AstNode): Option[String] =
    if (moduleScope || addrShape(n) != "local" || addressOfIsAggregate(n)) None
    else rawLocalOrParamName(n).filter(raw =>
      localTypes.contains(raw) && !declaredGlobals.contains(raw) &&
      !(cppFile && raw == "this")
    ).map(localName)

  /** `003-box-address-taken-locals`: does `&x` (the `addressOf` call `c`) feed
    * directly into an argument position of a call to something OTHER than an
    * in-program function -- an external/library call, e.g. `scanf("%d", &n)`?
    *
    * spec.md's own edge cases are explicit that this case "stays a hole, exactly as
    * today... Core cannot know what an untranslated function does to the pointee" --
    * and `SC-001` scopes its measured hole-count reduction to locals "passed only to
    * in-program functions or dereferenced directly", not to every address-taken
    * local unconditionally. `methodByName` (built from `cpg.method.isExternal(false)`)
    * is the same "is this actually one of our own functions" evidence every other
    * resolution in this file already uses.
    *
    * Deliberately DIRECT/syntactic only: `p = &n; scanf("%d", p);` (the address
    * reaching an external call through an intermediate alias, not `&n` itself as the
    * argument) is NOT traced here -- doing so would need the same general dataflow
    * analysis this feature's whole design avoids. That gap does not risk a WRONG
    * answer regardless (Core's hole propagation aborts the entire dynamic execution
    * at the first hole reached, including the external call's own -- so a stale
    * boxed value can never be observed after it), only a less precise hole label for
    * an already-untranslated external call; closing it further is future work, not a
    * soundness gap in what ships here. */
  def addressOfFeedsExternalCall(c: Call): Boolean = parentOf(c) match {
    case Some(p: Call) if !p.methodFullName.startsWith("<operator>") =>
      !methodByName.contains(p.methodFullName)
    case _ => false
  }

  // ---- `006-reduce-remaining-holes`, Story 5: interior pointers -------------

  /** Does call-argument node `k` (`aidx(k) >= 1`) feed `nm`'s own value to the
    * call -- either directly (a bare identifier/parameter reference, including
    * array-to-pointer decay), or through exactly one layer of `&` (address-of),
    * INCLUDING `&nm[i]`/`&nm.f` (the address of one ELEMENT/FIELD still lets the
    * callee write into `nm`'s own storage from outside this function -- exactly
    * the cross-function escape research.md §5.3's scope boundary excludes;
    * confirmed live, this session, against `helper(&a[0])`, which this check
    * originally missed by only recognizing a BARE name under `&`, not an index/
    * field access rooted at one). Used to detect whether an array/struct local
    * ESCAPES this function via a call argument, matching research.md §5.3's
    * scope boundary ("never passed as an argument to any call, in-program or
    * external, by value or by address"). Deliberately shallow, matching
    * `addressOfFeedsExternalCall`'s own "direct/syntactic only" precedent: a
    * name reaching a call through an intermediate alias is not traced here. */
  def argFeedsName(k: AstNode, nm: String): Boolean = k match {
    case i: Identifier        => localName(i.name) == nm
    case p: MethodParameterIn => p.name == nm
    case c: Call if c.methodFullName == "<operator>.addressOf" =>
      kidsOf(c) match {
        case List(x) =>
          argFeedsName(x, nm) ||
          asIndex(x).exists { case (r, _) => rawLocalOrParamName(r).map(localName).contains(nm) } ||
          asField(x).exists { case (r, _) => rawLocalOrParamName(r).map(localName).contains(nm) }
        case _ => false
      }
    case _ => false
  }

  /** `&a[i]`/`&s.f` once the receiver is a recognized boxed array/struct local
    * -- the two shapes `<operator>.addressOf` rewrites to `Expr.irefIndex`/
    * `Expr.irefField` instead of the existing aggregate-identity/hole paths. */
  def boxedArrayIndexOperand(n: AstNode): Option[(String, AstNode)] =
    asIndex(n).flatMap { case (recv, idx) =>
      rawLocalOrParamName(recv).map(localName).filter(boxedArrays.contains).map(_ -> idx)
    }
  def boxedStructFieldOperand(n: AstNode): Option[(String, String)] =
    asField(n).flatMap { case (recv, f) =>
      rawLocalOrParamName(recv).map(localName).filter(boxedStructs.contains).map(_ -> f)
    }

  /** `003-box-address-taken-locals`, Increment B: every call site in the whole
    * analyzed program, and every function used as a VALUE (`MethodRef` -- evidence
    * its address was taken and it could be called indirectly), each computed once
    * and reused by every `closedOutParam` check rather than re-querying `cpg` per
    * candidate parameter. */
  lazy val allCalls: List[Call] = cpg.call.l
  // Joern's C frontend emits a `MethodRef` for EVERY function, as a per-file
  // declaration/linking marker (`argumentIndex == -1`, its AST parent the file-level
  // BLOCK) -- confirmed empirically against a two-function fixture where neither
  // function's address was ever taken in source, yet both appeared in `cpg.methodRef`
  // unfiltered. `stmt()`'s own pre-existing `case m: MethodRef => skip` (a nested
  // `def`'s declaration marker) draws exactly this same distinction for the same
  // reason. A GENUINE function-pointer use (`fp = helper;`) is instead an operand of
  // a real expression -- its `argumentIndex` is not `-1` and its parent is not a bare
  // block -- so filtering to `aidx(mr) != -1` recovers the true signal.
  lazy val takenAsValueFns: Set[String] =
    cpg.methodRef.l.filter(mr => aidx(mr) != -1).map(_.methodFullName).toSet

  /** Whole-program: the bare owner type of any struct/array-literal initializer's
    * target, OR of a whole-aggregate copy's target (`x = y` where `x` and `y` are
    * both class-typed and share a bare type) -- either shape can set a struct's
    * fields to values `fieldFnTargets` just below, which scans only PLAIN
    * `x.f = v`/`x->f = v` assignment statements, cannot see at all.
    * `fieldFnTargets` excludes every type collected here unconditionally,
    * regardless of what its own assignment-statement scan alone would conclude.
    *
    * Not a hypothetical exclusion: confirmed live, this session, against real
    * SQLite -- `sqlite3_mem_methods.xMalloc`/`.xRealloc` resolve to a single
    * target (`faultsimMalloc`/`faultsimRealloc`) by assignment-statement count
    * alone, but the SAME type is ALSO initialized via three unrelated positional
    * struct literals (`defaultMethods`, `memsys5Methods`, `memmethods`), each
    * assigning a DIFFERENT function to the same field position -- the majority
    * shape for that type, not an edge case. Resolving `xMalloc` from the
    * assignment scan alone would have been a silent wrong answer for most of the
    * objects it actually applies to. */
  lazy val riskyLiteralInitTypes: Set[String] =
    allCalls.filter(_.methodFullName == "<operator>.assignment").flatMap { a =>
      kidsOf(a) match {
        case lhs :: (rhs: Call) :: Nil if rhs.methodFullName == "<operator>.arrayInitializer" =>
          val ty = stripDuplicateSuffix(bareType(staticTypeOf(lhs)))
          if (ty.nonEmpty && ty != "ANY") Some(ty) else None
        case (lhs: AstNode) :: (rhs: AstNode) :: Nil =>
          val lty = stripDuplicateSuffix(bareType(staticTypeOf(lhs)))
          if (lty.nonEmpty && lty != "ANY" && isClassType(lty) &&
              lty == stripDuplicateSuffix(bareType(staticTypeOf(rhs))))
            Some(lty)
          else None
        case _ => None
      }
    }.toSet

  /** Whole-program: `(ownerType, fieldName) -> the one function every assignment
    * to that struct field, anywhere in the program, agrees on`. The field-level
    * analogue of `fnPtrVars`'s own whole-FUNCTION single-assignment discipline,
    * generalized to whole-PROGRAM single-VALUE: unlike a local variable, a
    * struct field is legitimately set at many call sites (one per object
    * constructed), so requiring a single assignment SITE would resolve almost
    * nothing for a real vtable-style field -- what has to hold instead is that
    * every site, however many, assigns the SAME function. Absent real points-to
    * analysis (the "new subsystem" this project has consistently deferred),
    * this is a checkable, sound-when-it-fires substitute: the moment it cannot
    * be shown, this returns no entry and the call site stays a hole, matching
    * `closedOutParam`/`closedIrefOutParam`'s own conservative discipline
    * elsewhere in this file. Reuses `fnPtrVars`'s own closure-safety guard
    * (`capturesEnv`) and external-function guard (`methodByName`) verbatim --
    * both apply here for exactly the same reasons. */
  lazy val fieldFnTargets: Map[(String, String), String] = {
    val assigns = allCalls.filter(_.methodFullName == "<operator>.assignment")
    val targets = scala.collection.mutable.Map[(String, String), Set[String]]().withDefaultValue(Set.empty)
    val unsafe  = scala.collection.mutable.Set[(String, String)]()

    def fnTarget(mr: MethodRef): Option[(String, Boolean)] =
      if (methodByName.contains(mr.methodFullName))
        Some((mangledFullName(mr.methodFullName), capturesEnv.getOrElse(mr.methodFullName, false)))
      else None

    for (a <- assigns) {
      kidsOf(a) match {
        case (lhs: Call) :: rhs :: Nil if fieldOps.contains(lhs.methodFullName) =>
          asField(lhs).foreach { case (recv, field) =>
            val owner = stripDuplicateSuffix(
              bareType(staticTypeOf(recv)).reverse.dropWhile(_ == '*').reverse)
            if (owner.nonEmpty && owner != "ANY") {
              val key = (owner, field)
              val resolved: Option[(String, Boolean)] = rhs match {
                case mr: MethodRef => fnTarget(mr)
                case addr: Call if addr.methodFullName == "<operator>.addressOf" =>
                  kidsOf(addr) match { case List(mr: MethodRef) => fnTarget(mr); case _ => None }
                case _ => None
              }
              resolved match {
                case Some((target, false)) => targets(key) = targets(key) + target
                // A captured closure, or any RHS this cannot resolve to a known
                // in-program function at all, disqualifies the field outright --
                // the same non-negotiable exclusion `fnPtrVars` applies to a
                // variable, extended here to every object that shares this field.
                case Some((_, true)) | None => unsafe += key
              }
            }
          }
        case _ =>
      }
    }
    targets.iterator.collect {
      case (key @ (owner, _), ts) if ts.size == 1 && !unsafe.contains(key) &&
                                      !riskyLiteralInitTypes.contains(owner) =>
        key -> ts.head
    }.toMap
  }

  /** `003-box-address-taken-locals`, Increment B: FR-006's closed-call-site
    * precondition. Is parameter position `paramIndex` (Joern's own `ARGUMENT_INDEX`/
    * `MethodParameterIn.index` convention, so no separate off-by-one translation is
    * needed against `aidx`) of function `fn` safe to treat as an out-parameter --
    * does EVERY call site of `fn`, across the whole analyzed program, pass that
    * position a direct `&x` for a non-aggregate name, AND is `fn`'s own address never
    * taken anywhere (so it cannot be called indirectly, sidestepping this very
    * check)?
    *
    * This exists because `Heap.getField`'s "missing field returns `unit`" behaviour
    * would otherwise silently turn one bad caller into a wrong answer rather than a
    * hole (research.md item 3) -- `fn`'s translation is a single, fixed
    * interpretation shared by every caller, so this must hold for ALL of them, not
    * just the one call site currently being translated.
    *
    * Deliberately more conservative than `boxableName`'s own aggregate check, for a
    * reason specific to this whole-program setting: `boxableName`'s
    * "unknown-type inferred from a sibling `.`/`->` in the SAME method" heuristic
    * (`valueReceivers`/`ptrReceivers`) is per-CALLER-method state this function
    * would have to recompute for every one of `fn`'s potentially-many, potentially-
    * different callers to use correctly -- not impossible, but real additional work
    * this feature does not attempt. Instead, an argument only qualifies when its
    * OWN static type is definitely non-class and definitely not `unknown-type`; an
    * unresolved type at a call site is treated as UNSAFE. This can only exclude
    * MORE parameters than a fuller per-caller analysis would, never wrongly include
    * one — the direction FR-006 requires ("MUST NOT receive this translation" unless
    * provably safe), at the cost of leaving some real, safe cases as holes rather
    * than guessing. */
  def closedOutParam(fn: Method, paramIndex: Int): Boolean =
    if (takenAsValueFns.contains(fn.fullName)) false
    else {
      val callSites = allCalls.filter(_.methodFullName == fn.fullName)
      callSites.nonEmpty && callSites.forall { c =>
        kidsOf(c).find(aidx(_) == paramIndex).exists {
          case addr: Call if addr.methodFullName == "<operator>.addressOf" =>
            kidsOf(addr) match {
              case List(n) if addrShape(n) == "local" =>
                val ty = staticTypeOf(n)
                !isClassType(ty) && addrKind(ty) != "unknown-type"
              case _ => false
            }
          case _ => false
        }
      }
    }

  /** `007-reduce-remaining-holes-2`: `closedOutParam`'s own discipline, generalized
    * from a whole-object scalar out-parameter to an INTERIOR-pointer one -- a
    * parameter receiving `&r[idx]`/`&r.f` (the address of one ELEMENT or FIELD of an
    * array/struct, `Val.iref` at runtime under `006-reduce-remaining-holes` Story 5,
    * not `Val.ref`). Is parameter position `paramIndex` of function `fn` safe to
    * treat this way -- does EVERY call site of `fn`, across the whole analyzed
    * program, pass that position exactly this shape, with `r`'s own static type a
    * plausible boxable array/struct shape, AND is `fn`'s own address never taken
    * anywhere (so it cannot be called indirectly, sidestepping this very check)?
    *
    * Checked purely via `staticTypeOf`/`bareType`/`isClassType` on the argument node
    * itself, which Joern resolves regardless of which method the node belongs to --
    * this needs no per-CALLER precomputed state, so there is no circularity with
    * `boxedArrays`/`boxedStructs`'s own per-method computation (each caller's
    * eligibility to KEEP `r` boxed despite this call, decided separately below,
    * depends on this purely-structural result, never the reverse). */
  def closedIrefOutParam(fn: Method, paramIndex: Int): Boolean =
    if (takenAsValueFns.contains(fn.fullName)) false
    else {
      val callSites = allCalls.filter(_.methodFullName == fn.fullName)
      callSites.nonEmpty && callSites.forall { c =>
        kidsOf(c).find(aidx(_) == paramIndex).exists {
          case addr: Call if addr.methodFullName == "<operator>.addressOf" =>
            kidsOf(addr) match {
              case List(x) =>
                asIndex(x).exists { case (r, _) =>
                  arrayShape.findFirstMatchIn(bareType(staticTypeOf(r))).isDefined
                } ||
                asField(x).exists { case (r, _) =>
                  val ty = staticTypeOf(r)
                  isClassType(ty) && structTypeDeclOf(ty).isDefined
                }
              case _ => false
            }
          case _ => false
        }
      }
    }

  /** `004-function-pointer-tracking`: the name of the variable a `pointerCall`'s
    * callee (the child at `argumentIndex == -1`) reads, if it is one of the two
    * shapes confirmed against the CPG (research.md §4) -- a bare
    * `Identifier`/`MethodParameterIn` (implicit call syntax, `op(...)`), or an
    * `<operator>.indirection` wrapping one (explicit-dereference syntax,
    * `(*op)(...)`) -- unwrapping exactly the one optional indirection layer, no more.
    * `None` for anything else (a struct-field/array-element callee, or any other
    * shape), which is exactly the set of calls that must stay the existing hole. */
  def pointerCallCalleeVar(c: Call): Option[String] = {
    def nameOf(n: AstNode): Option[String] = n match {
      case i: Identifier        => Some(localName(i.name))
      case p: MethodParameterIn => Some(p.name)
      case _                    => None
    }
    kidsOf(c).find(aidx(_) == -1).flatMap {
      case ind: Call if ind.methodFullName == "<operator>.indirection" =>
        kidsOf(ind) match { case List(n) => nameOf(n); case _ => None }
      case n => nameOf(n)
    }
  }

  /** The `(ownerType, fieldName)` a `pointerCall`'s callee reads, when it is a
    * field access (`p->f(...)`/`p.f(...)`) whose receiver's static type Joern
    * actually resolved -- `pointerCallCalleeVar`'s own struct-field exclusion,
    * given a name here instead of staying unconditionally `None`, so
    * `fieldFnTargets` can be tried as a second, independent resolution path.
    * `None` when the receiver's type is Joern's own `ANY` (or otherwise
    * unresolved): there is no owner type to look a target up against, and this
    * must stay a hole exactly as it already does today. */
  def pointerCallCalleeField(c: Call): Option[(String, String)] =
    kidsOf(c).find(aidx(_) == -1).flatMap {
      case fa: Call if fieldOps.contains(fa.methodFullName) =>
        asField(fa).flatMap { case (recv, field) =>
          val owner = stripDuplicateSuffix(
            bareType(staticTypeOf(recv)).reverse.dropWhile(_ == '*').reverse)
          if (owner.nonEmpty && owner != "ANY") Some((owner, field)) else None
        }
      case _ => None
    }

  /** `Expr.name nm` -- the box's own reference, e.g. what `&x` evaluates to once `x`
    * is boxed, or what a boxed local's declared-type-preserving reference looks like. */
  def boxRef(nm: String): ujson.Obj = ujson.Obj("k" -> "name", "v" -> nm)

  /** `Expr.field (Expr.name nm) "v"` -- a read of a boxed local/parameter's one
    * field, i.e. the value it stands for everywhere it is read as a plain name. */
  def boxField(nm: String): ujson.Obj = ujson.Obj("k" -> "field", "a" -> boxRef(nm), "f" -> "v")

  /** `import p.q` / `from <prefix> import <name>`.
    *
    * The Python frontend emits this as a call named `import` with two synthetic literals
    * — the (possibly dot-prefixed, possibly empty) package prefix and the imported name —
    * wrapped in an assignment that binds the resulting value. Those literals are unquoted
    * source fragments, not values, so translating them as expressions produced
    * `lit:unquoted` holes that said nothing about what the statement actually was.
    *
    * What the *statement* means is a binding, and sometimes the bound value is one we
    * already have: `from ._cached import _wrapper` names a function of this program, and
    * `from . import LRUCache` names a class of it. Those become the same `fnref`/`closure`
    * a direct reference would, so the binding is real and cross-module names resolve.
    *
    * What we refuse to invent is a **module object**. `import functools` binds a module,
    * and Core has no module value — `Val.fn` is a function or a class, so pointing a name
    * at `fnref "functools"` would claim `functools.reduce` is an attribute of a function.
    * That is the `fnref`-for-a-capturing-class mistake again, so it stays a hole; only the
    * label improves, from "an unquoted literal" to "a module value we cannot represent".
    *
    * Resolution is lexical and purely syntactic: leading dots count package levels up from
    * the importing file's directory, and the remainder is a path. No sys.path search, no
    * guessing — if the target is not a method or class of the analysed program, we say so. */
  /** Does a proper, non-empty prefix of `path` name a module of this program?
    *
    * This is the evidence that separates the two things `import:unresolved` used to
    * conflate. `os`, `yaml`, `jinja2.nativetypes` have no such prefix: they are simply
    * not in this CPG, and no amount of resolver work will find them. `from
    * ansible.module_utils.common.foo import bar`, where `module_utils/common` *is* in the
    * CPG and `foo.py` is not, is a different situation with a different remedy.
    *
    * The label says only what was measured — a prefix is in the CPG — and not "this is
    * first-party", because it demonstrably is not always: 82 of Ansible's 116 are `from
    * collections.abc import ...`, and they land here because Ansible ships its own
    * `collections/` package. That is the same-name ambiguity `moduleAtTolerant` warns
    * about, surfacing as a measurement instead of as a wrong translation. */
  def prefixInCpg(path: String): Boolean = {
    val segs = path.split('/').filter(_.nonEmpty).toList
    (1 until segs.length).exists(i => moduleAtTolerant(segs.take(i).mkString("/")).isDefined)
  }

  /** A module this CPG does not contain, named by *why* we do not have it.
    *
    * `__future__` is not a module in the ordinary sense and is handled first. A
    * `from __future__ import annotations` is a COMPILER DIRECTIVE: it changes how the
    * *compiler* treats the source and binds a `_Feature` object nobody reads. Its runtime
    * effect on the translated program is nothing, so `Lit.unit` is the exact value, not an
    * approximation -- the same argument as eliding an uncontended lock in a sequential
    * semantics. 518 of Ansible's 2,400 absent-module holes are this one import, and each
    * of them was making a module initialiser unanalysable for a directive that does not
    * execute.
    *
    * Deliberately only `__future__`. Every other absent module is a real value the program
    * may read, and inventing one would be the mistranslation this label exists to prevent. */
  def absentModule(path: String, relative: Boolean): ujson.Obj =
    if (path.split('/').lastOption.contains("__future__") ||
        path.split('/').headOption.contains("__future__"))
                                   ujson.Obj("k" -> "unit")
    /* An absent module is bound to an OPAQUE MARKER, not to a hole.
     *
     * A hole here is a hole in the VALUE, and `execStmt` stops at it -- so one
     * `import time` aborted the whole module initialiser, and every `class` statement
     * after it never ran. In cachetools that left `Cache`, `LRUCache` and every other
     * class unbound in globals, which is why all six subclass constructors reported
     * `mcall:__init__:non-object`: the receiver was not a class value, it was nothing.
     *
     * The name IS bound in Python, to a module object we cannot model. Binding it to an
     * opaque value says exactly that: the binding exists, and every USE of it -- an
     * attribute read, a call -- holes LOCALLY, which is the same information the old hole
     * carried, delivered without destroying the rest of the file. The marker is a name no
     * source language can produce, so it can never be confused with a real function. */
    else if (relative)             externalModule(path, "relative")
    else if (prefixInCpg(path))    externalModule(path, "prefix-in-cpg")
    else                           externalModule(path, "external")

  def externalModule(path: String, why: String): ujson.Obj =
    ujson.Obj("k" -> "fnref", "v" -> s"<absent:$why>$path")

  /** A resolved module, as a value — but only if it is a Python module with an object.
    * A `<global>` C file scope is not a value and must not be handed out as one. */
  def resolvedModule(mod: String): Option[ujson.Obj] =
    if (pyModuleFullNames.contains(mod)) Some(moduleRef(mod)) else None

  /** `import p.q` / `from <prefix> import <name>`, translated to the value it binds.
    *
    * `aliased` is `import x.y as z` / `from p import x as z`. It matters for exactly one
    * case: plain `import a.b.c` binds the **top** package `a`, whereas `import a.b.c as z`
    * binds `a.b.c` itself. Getting that backwards would bind the wrong module. */
  def importValue(prefix: String, name: String, aliased: Boolean): ujson.Obj = {
    val dots = prefix.takeWhile(_ == '.').length
    val rest = prefix.drop(dots)
    if (dots == 0 && rest.isEmpty) {
      val segs = name.split('.').filter(_.nonEmpty).toList
      val path = (if (aliased) segs else segs.take(1)).mkString("/")
      moduleAtTolerant(path).flatMap(resolvedModule)
        .getOrElse(absentModule(path, relative = false))
    } else {
      val dir  = currentFile.split('/').dropRight(1).dropRight(math.max(dots - 1, 0)).toList
      val base = if (dots == 0) Nil else dir
      val segs = base ++ rest.split('.').filter(_.nonEmpty).toList
      val path = segs.mkString("/")
      moduleAtTolerant(path) match {
        case None => absentModule(path, relative = dots > 0)
        case Some(mod) =>
          val target = mod + "." + name
          if (methodByName.contains(target))        fnValue(target)
          else if (classByFullName.contains(target)) typeValue(target + "<meta>")
          // `from ...converters import to_native`, where `to_native = to_text` at file
          // scope. See `moduleAliasesOf`.
          else if (moduleAliasesOf(mod).exists(_._1 == name))
            aliasValue(mod, moduleAliasesOf(mod).find(_._1 == name).get._2)
          // `from . import keys` where `keys` is a sibling *module*, not a member. The
          // child is looked for under the module we actually resolved, not under the
          // written path, because the tolerant resolver may have dropped a prefix.
          else moduleAt(if (modulePath(mod).isEmpty) name else modulePath(mod) + "/" + name)
                 .flatMap(resolvedModule)
                 // The module is here and the name is not a function, a class or a
                 // submodule of it. In practice that is a module-level *variable* or a
                 // re-export, which a module object deliberately does not carry (see the
                 // module-object note above) — a different problem from not having the
                 // module at all, so a different label.
                 .getOrElse(hole("import:member-not-found"))
      }
    }
  }

  /** Is the method currently being translated Python source? f-strings are a Python
    * construct and everything below is gated on this: `<operator>.formatString` is also
    * emitted by other frontends, with other part shapes, and the varargs regression is
    * the standing reminder of what an ungated language-specific helper costs. */
  def pyFile: Boolean = currentFile.toLowerCase.endsWith(".py")

  /** `007-reduce-remaining-holes-2` US4: Go's `switch` does NOT fall through between
    * cases by default (unlike C/C++/Java/JS/TS, which all share `switchStmt`'s
    * fallthrough-by-threading-into-the-next-segment design) -- a `case` implicitly
    * breaks unless the source uses Go's own explicit `fallthrough` statement. Whether
    * Joern's Go frontend normalizes this into the same CPG shape `switchStmt` assumes
    * (an explicit trailing break per case, unless `fallthrough` is used) was not
    * verified this session -- no Go toolchain was available to build a test CPG, and
    * guessing here risks exactly the well-typed-but-silently-wrong translation this
    * project's ledger exists to prevent. So `.go` files keep today's `control:SWITCH`
    * hole, honestly, until this is checked; `switchStmt` is applied everywhere else. */
  def goFile: Boolean = currentFile.toLowerCase.endsWith(".go")

  /** One `{...}` field of an f-string.
    *
    * `Left` carries the reason it is not expressible, so the hole says which of the two
    * different problems it is rather than lumping them together.
    *
    * A field with no conversion and no format spec means exactly `str(value)` — that is
    * the language definition, not an approximation — so it becomes `Expr.call "str"`.
    * `{x!r}` is `repr(x)` and `{x:>10.2f}` is `format(x, '>10.2f')`; Core models neither,
    * and a formatting model invented here would be worse than a hole.
    *
    * The frontend records neither the conversion nor the spec anywhere but the source
    * text — `{command!r}` has a single child whose code is `command` — so the only sound
    * test is whether the field's text *is* the expression's text. `{x}` passes; `{x!r}`,
    * `{x:>10}`, `{x=}` and anything the frontend rewrote into a prelude (`{tmp1 = ...}`)
    * do not, and are refused rather than silently stripped. */
  def fstringField(c: Call): Either[String, ujson.Obj] = {
    val ks = kidsOf(c)
    val inner = c.code.trim.stripPrefix("{").stripSuffix("}")
    if (ks.size != 1) Left("shape")
    else if (inner != ks.head.code.trim) Left("conversion-or-spec")
    else Right(ujson.Obj("k" -> "call", "f" -> "str", "args" -> ujson.Arr(expr(ks.head))))
  }

  /** An f-string: the concatenation of its literal segments and its fields.
    *
    * ## What this does and does not close
    *
    * The *structure* is now translated: `f'version {v}'` is `"version " + str(v)`, which
    * is what CPython does. What it runs into is a Core limitation that already existed
    * and is now visible in more places: `Stdlib.builtin`'s `str` answers on `.int` and
    * `.bool` and **declines on `.str`**, because Core represents an exception as a bare
    * `Val.str` and cannot tell one from an ordinary string. So `f'{n}'` with an integer
    * evaluates; `f'{s}'` with a string is the runtime hole `call:str`.
    *
    * That is a moved hole, not a closed one, and it is recorded as such: the AST-level
    * `op:formatString` count goes to zero while the residue reappears at run time under a
    * label that names the actual blocker — Core's `str`, not the f-string. Inventing a
    * string conversion here to make the number look better is the thing not done. */
  def fstring(kids: List[AstNode]): ujson.Obj = {
    val parts: List[Either[String, ujson.Obj]] = kids.sortBy(_.order).map {
      case l: Literal =>
        // The segment's `code` is the raw source between the braces, so a backslash in it
        // is an escape CPython has already interpreted and we have not. Emitting the text
        // verbatim would put a literal `\` and `n` into the string.
        if (l.code.contains('\\')) Left("escape")
        else Right(ujson.Obj("k" -> "str", "v" -> l.code))
      case c: Call if c.methodFullName == "<operator>.formattedValue" => fstringField(c)
      case _ => Left("shape")
    }
    parts.collectFirst { case Left(r) => r } match {
      case Some(r) => hole("op:formatString:" + r)
      case None =>
        parts.collect { case Right(o) => o } match {
          case Nil       => ujson.Obj("k" -> "str", "v" -> "")
          case p :: rest => rest.foldLeft(p)((a, b) =>
                              ujson.Obj("k" -> "binop", "op" -> "+", "a" -> a, "b" -> b))
        }
    }
  }

  /** C++'s receiver is spelled `this`; Core's — the name `applyFunc` binds a method's
    * receiver to — is `self`. Without this rename `this->f` translated to a read of an
    * unbound name, which is the vacuous outcome: an `Expr.field` on `unit`, holing at run
    * time for a reason that had nothing to do with pointers. The rename is what makes the
    * `indirectFieldAccess` mapping actually reach a heap object. */
  /** The text of a Python string literal, allowing an `r`/`u` prefix and triple quotes.
    * `None` when the code is not a string literal at all. Deliberately does NOT accept a
    * `b` prefix: bytes are a type Core does not have and must stay a hole. */
  def pyStringLit(c: String): Option[String] = {
    val re = "(?is)^([ruRU]{0,2})(\"\"\"|'''|\"|')(.*)\\2$".r
    c match {
      case re(_, _, body) => Some(body)
      case _              => None
    }
  }
  def localName(n: String): String = if (cppFile && n == "this") "self" else n

  // ---- expressions ----------------------------------------------------------
  /** Parse a C/C++/Java integer literal.
    *
    * `toIntOption` alone was the whole implementation, and on V8 it failed on 309 of the
    * literals in `src/base` — every hex constant, every `u`/`U`/`L`/`ULL` suffix, C++14
    * digit separators (`0x0010'0000'0000'0000`), binary `0b10000`, and anything past
    * 2^31. Each became a `lit:unquoted` hole, so a function containing `0xFFFFFFFF` was
    * unanalysable for want of a number.
    *
    * Returns `BigInt` because a C++ literal routinely exceeds `Int` and often exceeds
    * `Long` (`0xFFFFFFFFFFFFFFFF`). The caller emits anything beyond 2^53 as a decimal
    * *string*, since JSON numbers are doubles and would silently round it — the exact
    * class of quiet corruption this project keeps finding.
    */
  def parseIntLiteral(raw: String): Option[BigInt] = {
    var t = raw.trim.replace("'", "")            // C++14 digit separators
    if (t.isEmpty) return None
    var neg = false
    if (t.startsWith("-")) { neg = true; t = t.drop(1) }
    else if (t.startsWith("+")) t = t.drop(1)
    // Integer suffixes, in any order and case: 0u, 1L, 2ULL, 3llu.
    val body = t.reverse.dropWhile(ch => ch == 'u' || ch == 'U' || ch == 'l' || ch == 'L').reverse
    if (body.isEmpty) return None
    val parsed: Option[BigInt] =
      try {
        if (body.length > 2 && (body.startsWith("0x") || body.startsWith("0X")))
          Some(BigInt(body.drop(2), 16))
        else if (body.length > 2 && (body.startsWith("0b") || body.startsWith("0B")))
          Some(BigInt(body.drop(2), 2))
        // A leading zero is octal in C, but plain "0" is zero, and a decimal point or an
        // exponent means this is a float and not ours to claim.
        else if (body.length > 1 && body.head == '0' && body.forall(_.isDigit))
          Some(BigInt(body.drop(1), 8))
        else if (body.forall(_.isDigit)) Some(BigInt(body))
        else None
      } catch { case _: NumberFormatException => None }
    parsed.map(v => if (neg) -v else v)
  }

  /** JSON for an integer literal, without losing precision to a double. */
  def intLit(v: BigInt): ujson.Obj =
    if (v.abs <= BigInt(2).pow(53)) ujson.Obj("k" -> "int", "v" -> v.toLong)
    else ujson.Obj("k" -> "int", "v" -> v.toString)

  def expr(n: AstNode): ujson.Obj = n match {
    case l: Literal =>
      val c0 = l.code.trim
      // String-literal prefixes: L"x" (wide), u8"x", u"x", U"x". The prefix selects an
      // encoding Core does not model; the *content* is what the program uses, and
      // dropping the prefix is exactly what `unquoted` already does for the quotes.
      //
      // Python's `u'x'` is the same object as `'x'` — the prefix has been a no-op since
      // 3.0 and exists only for 2/3 compatibility — but only the double-quoted spelling
      // was stripped, so every `u'...'` in the corpus was reported as an unparsed
      // literal. `b'x'` is *not* covered: bytes are a distinct type Core does not have,
      // and calling one a `str` would be a wrong value rather than a missing one.
      // The single-quoted forms are **Python only**, deliberately: `L'a'` and `u'a'` in
      // C++ are wide/char16_t *character* constants, which are integers, and stripping
      // the prefix there would turn a number into a string.
      val c =
        if (c0.length >= 3 && (c0.startsWith("L\"") || c0.startsWith("u\"") || c0.startsWith("U\""))) c0.drop(1)
        else if (c0.length >= 4 && c0.startsWith("u8\"")) c0.drop(2)
        else if (pyFile && c0.length >= 3 && (c0.startsWith("u'") || c0.startsWith("U'"))) c0.drop(1)
        else c0
      val unquoted =
        if (c.length >= 2 && (c.head == '"' || c.head == '\'')) c.drop(1).dropRight(1) else c
      parseIntLiteral(c) match {
        case Some(i) => intLit(i)
        case None =>
          if (c == "True" || c == "true")        ujson.Obj("k" -> "bool", "v" -> true)
          else if (c == "False" || c == "false") ujson.Obj("k" -> "bool", "v" -> false)
          // `nullptr` is not a number and not a string: it is the absence of an object,
          // and `Val.unit` is the one value Core has that no `Val.ref` is equal to. That
          // makes `p == nullptr` answer `false` for every allocated object, which is the
          // right answer, and `Val.unit` for a *dereferenced* null is not reachable
          // because dereference is itself a hole.
          // `007-reduce-remaining-holes-2` US1: `NULL` (the standard C/C++ macro spelling,
          // all-caps) was missing here -- it fell through to the bare-identifier check below
          // and was mislabeled `import:operand` (a label meant for Python's `import` operand
          // shape) on every C/C++ file, live-CPG-sampled at 1,927 of 1,927 non-Python
          // `import:operand` hits on the SQLite corpus (research.md US1 sampling results).
          else if (c == "None" || c == "null" || c == "nil" || c == "nullptr" || c == "NULL")
            ujson.Obj("k" -> "unit")
          // A float is not a string. Core has no floats, so this is a hole, not a lie.
          // Float forms, including the C/C++ `f`/`F`/`l`/`L` suffix and exponent-only
          // spellings (`1e300`). These were falling through to `lit:unquoted`, which
          // reported a *parsing* failure for something we simply do not model yet —
          // wrong label, wrong remedy. `Autoform/Lang/Core/Float.lean` models IEEE-754,
          // so emitting `Lit.float` here is real pending work, not a permanent hole.
          else if (c.matches("""[-+]?(\d+\.\d*|\.\d+|\d+)([eE][-+]?\d+)?[fFlL]?""") &&
                   c.exists(ch => ch == '.' || ch == 'e' || ch == 'E'))
            // `Autoform/Lang/Core/Float.lean` models IEEE-754 by bit pattern and has sat in
            // the tree, fully verified and entirely unused by the pipeline, since it was
            // written. The decimal text is emitted here and `render_lean.py` converts it to
            // the exact binary64 pattern: Python's float() is correctly rounded, and it is
            // the same conversion `Float.lean` names in its own docstring.
            ujson.Obj("k" -> "float", "v" -> c)
          // Joern synthesises `<global>` as a namespace marker. It is not a literal the
          // source contains, and counting it as an unparsed one overstated the literal
          // problem roughly tenfold on V8.
          else if (c == "<global>") hole("lit:joern-synthetic")
          // A PREFIXED or TRIPLE-QUOTED Python string. r"\d+" is an ordinary `str`: the
          // prefix only suppresses escape processing at parse time, and `unquoted` does no
          // escape processing anyway -- so a raw string is precisely the case the existing
          // path was already correct for, and it was refused only because it does not
          // start with a quote. 404 `lit:unquoted` holes on Ansible were these, mostly
          // regexes.
          //
          // Triple quotes are fixed here too: `unquoted` dropped ONE character from each
          // end, so a triple-quoted string kept two stray quotes at each end. That is a
          // wrong VALUE rather than a hole -- the silent kind.
          //
          // `b`/`rb`/`br` cannot match (the prefix class is `[ruRU]`), so bytes still
          // reach `lit:bytes`; `f"..."` cannot match either, because after an empty
          // prefix the next character must be a quote.
          else if (pyFile && pyStringLit(c).isDefined)
            ujson.Obj("k" -> "str", "v" -> pyStringLit(c).get)
          else if (c.headOption.exists(ch => ch == '"' || ch == '\''))
            ujson.Obj("k" -> "str", "v" -> unquoted)
          else if (c.isEmpty) ujson.Obj("k" -> "unit")
          // A bare dotted identifier in literal position is not a literal at all: the
          // Python frontend synthesises these as the *operands of import statements*
          // (`__future__`, `annotations`, `ansible.errors`, `typing`, `os`). Filing them
          // under `lit:unquoted` reported a literal-parsing problem and pointed at the
          // wrong remedy -- on Ansible it hid 2,157 import operands inside a label that
          // says "we could not read this number". Naming them `import:operand` puts them
          // with the other import holes, where the actual work is.
          // `007-reduce-remaining-holes-2` US1: guarded by `pyFile`, matching every sibling
          // branch in this chain -- this label means Python's import-operand shape
          // specifically, and was previously reachable on any file. Live-CPG sampling on the
          // SQLite (C) corpus found 100% of what this let through was `NULL` (now handled
          // above); this guard is the correctness fix for any other, unsampled case, so a
          // non-Python bare identifier falls through to the ordinary `lit:unquoted` catch-all
          // below instead of being mislabeled as a Python import operand.
          else if (pyFile &&
                   (c.matches("""[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*""") ||
                    c == "."))
            hole("import:operand")
          // `b'...'` / `rb"..."`: a **bytes** literal. Core has `str` and no `bytes`, and
          // the two are not interchangeable in Python 3 (`b'a' == 'a'` is `False`), so
          // this is a missing *type*, not a parsing failure, and the label says which.
          else if (pyFile && c.matches("""(?i)(b|rb|br)['"].*"""))
            hole("lit:bytes")
          // `...` — the `Ellipsis` singleton, which Python uses as a stub body and as a
          // typing placeholder. A value Core does not have, again not a parse failure.
          else if (pyFile && c == "...") hole("lit:ellipsis")
          // Unquoted, non-numeric, non-identifier literal code. Calling it a string would
          // be inventing a value.
          else hole("lit:unquoted")
      }
    // `003-box-address-taken-locals`: a plain read of a boxed local/parameter reads
    // the box's one field instead of the name directly -- `x` itself now holds the
    // `Val.ref`, not the value (see `boxedLocals`, `boxableName`).
    case i: Identifier if boxedLocals.contains(localName(i.name)) => boxField(localName(i.name))
    // `006-reduce-remaining-holes`, Story 5: array-to-pointer decay -- a boxed
    // array read as a bare VALUE (an assignment RHS, a binop operand, ...) is,
    // in C, the address of its first element; `&a[i]`/`a[i]` themselves are
    // intercepted earlier (`callExpr`'s `addressOf`/`indexOps` cases), never
    // reaching this generic identifier-read case, so this rule cannot fire on
    // those and mistranslate an ordinary index into a decayed pointer.
    case i: Identifier if boxedArrays.contains(localName(i.name)) =>
      ujson.Obj("k" -> "irefIndex", "a" -> ujson.Obj("k" -> "name", "v" -> localName(i.name)),
                "i" -> intLit(0))
    case i: Identifier        => ujson.Obj("k" -> "name", "v" -> localName(i.name))
    case p: MethodParameterIn if boxedLocals.contains(p.name) => boxField(p.name)
    case p: MethodParameterIn => ujson.Obj("k" -> "name", "v" -> p.name)
    // A function/method or a class used as a value. Whether it needs to carry the
    // enclosing environment is decided by `capturesEnv`, above.
    case m: MethodRef         => fnValue(m.methodFullName)
    case t: TypeRef           => typeValue(t.typeFullName)
    case c: Call              => callExpr(c)
    case b: Block             => blockExpr(b)
    // A control structure reached in *expression* position. This is only ever the tail of
    // a BLOCK that `blockExpr` was asked for the value of, and on V8 it is macro fallout:
    // `CHECK_EQ(a, b)` expands to `do { ... } while (false)`, and the frontend hands the
    // expansion back where an argument was expected. A statement has no value, so there is
    // nothing to translate — but *which* statement it was decides whether the remedy is a
    // frontend fix (`DO`, a macro body) or a real language feature Core lacks, so the
    // label carries it instead of merging them all under one count.
    case cs: ControlStructure => controlStructureExpr(cs)
    case other                => hole("expr:" + other.label)
  }

  /** A control structure in EXPRESSION position, which on V8 is always macro fallout.
    *
    * 326 of these in `base.cpg`, and they were one undifferentiated label. They are four
    * different things with four different remedies, and eliding them uniformly would be
    * silently wrong for all but one:
    *
    *   - `USE(x)` is defined as `(void)x`. It is EXACTLY a no-op, the same argument as an
    *     elided uncontended lock, so it becomes `unit` and is counted.
    *   - `UNREACHABLE()` and `IMMEDIATE_CRASH()` ABORT. Translating them to `unit` would
    *     let control continue past a point the program guarantees it does not reach --
    *     the one direction that turns a missing feature into a wrong answer. They keep a
    *     hole, now named, so the count is attributable to "Core has no abort".
    *   - `CHECK*` is an assertion. Eliding it ASSUMES it passes, which is a real
    *     assumption rather than an exactness argument, so it stays a hole and says so.
    *   - `GET_HIGH_WORD`/`EXTRACT_WORDS` write through out-parameters: they COMPUTE. An
    *     elision would drop the computation, which is the silent-wrong class.
    */
  def controlStructureExpr(cs: ControlStructure): ujson.Obj = {
    val code  = cs.code.trim
    val macro_ = "^([A-Z_][A-Z0-9_]*)\\s*\\(".r.findFirstMatchIn(code).map(_.group(1))
    macro_ match {
      case Some("USE") =>
        useElided += 1
        ujson.Obj("k" -> "unit")
      case Some(n) if n == "UNREACHABLE" || n == "IMMEDIATE_CRASH" =>
        hole("expr:abort:" + n)
      case Some(n) if n.startsWith("CHECK") || n.startsWith("DCHECK") =>
        hole("expr:assert:" + n)
      case Some(n) =>
        hole("expr:macro:" + n)
      case None =>
        hole("expr:CONTROL_STRUCTURE:" + cs.controlStructureType)
    }
  }

  def exprs(ns: List[AstNode]): ujson.Arr = ujson.Arr.from(ns.map(expr))

  // ---- the calling convention ------------------------------------------------
  //
  // Three argument shapes that a flat positional list cannot express, and that this
  // exporter previously either holed or -- worse -- dropped in silence:
  //
  //   f(*xs)     `<operator>.starredUnpack` wrapping the operand. Was `op:starredUnpack`,
  //              36 holes on `cachetools`, the largest single category.
  //   f(**d)     an argument carrying ARGUMENT_NAME `<keyword_dict>` and ARGUMENT_INDEX
  //              -1. Because the old code selected arguments by `argumentIndex >= 1`,
  //              this was **silently discarded**: `hashkey(*args, **kwargs)` translated
  //              to a call that passed no keywords at all, and nothing counted it.
  //   f(k = v)   an argument carrying its parameter's name. Discarded the same way --
  //              `_wrapper(..., info = make_info)` lost `info`.
  //
  // The last two are the §31 category exactly: well-typed output that type-checked,
  // counted as translated, and did the wrong thing. They are now expressed.

  /** The ARGUMENT_NAME a keyword argument carries, if it is one. */
  def argName(n: AstNode): Option[String] = n match {
    case e: Expression => e.argumentName
    case _             => None
  }

  def isKeywordArg(n: AstNode): Boolean = argName(n).isDefined

  /** One positional argument, recognising `*e`. Outside an argument list a starred
    * unpack has no Core form and stays the hole it was. */
  def argExpr(n: AstNode): ujson.Value = n match {
    case c: Call if c.methodFullName == "<operator>.starredUnpack" =>
      kidsOf(c) match {
        case one :: Nil => ujson.Obj("k" -> "starred", "a" -> expr(one))
        // A starred unpack is unary in every frontend we have seen; a different arity is
        // a shape we have not seen and must not guess at.
        case _          => hole("op:starredUnpack-arity")
      }
    case other => expr(other)
  }

  /** A call's arguments: positional (recognising `*e`) followed by keyword (`k = e` and
    * `**e`), in CPG order. */
  def argExprs(pos: List[AstNode], kw: List[AstNode]): ujson.Arr =
    ujson.Arr.from(pos.map(argExpr) ++ kw.map { a =>
      argName(a) match {
        case Some("<keyword_dict>") => ujson.Obj("k" -> "dstarred", "a" -> expr(a))
        case Some(k)                => ujson.Obj("k" -> "kwargE", "n" -> k, "a" -> expr(a))
        case None                   => expr(a)
      }
    })

  /** Substitute `name` occurrences in an already-translated tree. Used only for the
    * frontend's own `tmpN` temporaries, whose definitions we proved re-evaluable. */
  def substNames(v: ujson.Value, m: Map[String, ujson.Value]): ujson.Value = v match {
    case o: ujson.Obj =>
      val nm = for { k <- o.value.get("k") if k.str == "name"
                     x <- o.value.get("v"); r <- m.get(x.str) } yield r
      nm.getOrElse(ujson.Obj.from(o.value.map { case (k, x) => k -> substNames(x, m) }.toSeq))
    case a: ujson.Arr => ujson.Arr.from(a.value.map(substNames(_, m)))
    case other        => other
  }

  /** The class a C++ constructor call names, if it names one.
    *
    * Joern spells a constructor's `methodFullName` as `<qualified class>.<name>:<sig>`,
    * so `v8.internal.NumberParseIntHelper.NumberParseIntHelper:void(ANY,int)` is a
    * constructor exactly when the last two dotted segments agree. `ANY.ANY:void()` agrees
    * too and names nothing, and `int64_t.int64_t:void(int)` — the frontend's spelling of
    * `int64_t{1}` — names a *number*, not a class; both are rejected, because an
    * `Expr.alloc` of either would be a heap object standing in for something that is not
    * one. */
  def ctorClassOf(c: Call): Option[String] = {
    val segs = c.methodFullName.takeWhile(_ != ':').split('.').filter(_.nonEmpty).toList
    segs.reverse match {
      case n :: p :: _ if n == p && n != "ANY" && !intTypeNames.contains(bareType(n)) &&
                          !nonClassScalars.contains(n) => Some(n)
      case _ => None
    }
  }

  /** C++ stack object construction: `Foo x(a, b);`.
    *
    * The frontend lowers it to three siblings —
    *
    *     <tmp>0 = <operator>.alloc
    *     Foo.Foo(a, b)
    *     <tmp>0
    *
    * — which is `Expr.alloc "Foo" [a, b]` and nothing else. Reading it as three
    * independent statements produced an `op:alloc` hole for a construct Core has had a
    * constructor for since the beginning; this is the second-largest purely-exporter gap
    * in the C++ ledger after `p->f`.
    *
    * The constructor *body* is reached because `emit` exports a C++ constructor under the
    * name `__init__`, which is the name `evalExpr`'s `.alloc` case looks for. Without that
    * the object would be allocated with no fields and every later `p->f` would read
    * `unit` — allocated, well-typed, and silently empty. */
  def ctorAlloc(ks: List[AstNode]): Option[ujson.Obj] = ks match {
    case (asg: Call) :: (ctor: Call) :: (last: Identifier) :: Nil
        if asg.methodFullName == "<operator>.assignment" =>
      for {
        (tgt, rhs) <- kidsOf(asg) match {
                        case (i: Identifier) :: r :: Nil => Some((i, r))
                        case _                           => None
                      }
        if tgt.name == last.name
        if isOp(rhs, "<operator>.alloc") && kidsOf(rhs).isEmpty
        cls <- ctorClassOf(ctor)
      } yield ujson.Obj("k" -> "alloc", "cls" -> cls,
                        "args" -> exprs(kidsOf(ctor).filter(aidx(_) >= 1)))
    case _ => None
  }

  /** Is this childless `<operator>.alloc` sitting in the block shape `ctorAlloc` looks for
    * — so that the only thing that stopped the fold was `ctorClassOf` finding no class
    * name? Used purely to give the residual hole an accurate label. */
  def inCtorShape(alloc: Call): Boolean = {
    val asg = alloc.astParent
    val ok = asg match { case c: Call => c.methodFullName == "<operator>.assignment"
                         case _       => false }
    ok && (asg.astParent match {
      case b: Block => kidsOf(b).filterNot(_.isInstanceOf[Local]) match {
        case (_: Call) :: (ctor: Call) :: (_: Identifier) :: Nil => ctorClassOf(ctor).isEmpty
        case _ => false
      }
      case _ => false
    })
  }

  /** A BLOCK in *expression* position.
    *
    * pysrc2cpg lowers several expressions into a statement sequence ending in its value —
    * `d.pop(k)` becomes `tmp0 = d; tmp0.pop(k)`, `{}` becomes `tmp0 = {}; tmp0`. In
    * statement position `valueOf` splits that into a prelude plus a value, but an argument
    * has nowhere to put statements, so these were `expr:BLOCK` holes.
    *
    * They can be recovered exactly when the prelude is *inlinable*: every preceding
    * statement binds one of the frontend's own `tmpN` names to a re-evaluable expression.
    * Then substituting the definitions into the value is a pure renaming — no statement is
    * dropped (a pure binding has no effect) and no evaluation is reordered (the substituted
    * expression is evaluated exactly where the temporary was read, and evaluating it
    * earlier or later is unobservable). Hoisting an *impure* prelude out to the enclosing
    * statement would reorder it past the arguments evaluated before it, so anything that
    * does not fit the inlinable shape — generator expressions, most notably — stays a hole
    * with a label naming what defeated it. */
  def blockExpr(b: Block): ujson.Obj = {
    val ks = kidsOf(b).filterNot(_.isInstanceOf[Local])
    if (ks.isEmpty) hole("expr:empty-block")
    else if (ctorAlloc(ks).isDefined) ctorAlloc(ks).get
    else {
      var subst = Map.empty[String, ujson.Value]
      var bad   = ""
      ks.init.foreach {
        case c: Call if c.methodFullName == "<operator>.assignment" =>
          kidsOf(c) match {
            case (i: Identifier) :: rhs :: Nil
                if i.name.matches("tmp\\d+") && pureExpr(rhs) =>
              subst += (i.name -> substNames(expr(rhs), subst))
            case (_: Identifier) :: rhs :: Nil => if (bad.isEmpty) bad = "expr:BLOCK-impure"
            case _                             => if (bad.isEmpty) bad = "expr:BLOCK-prelude"
          }
        // `tmp0 = <operator>.genExp` plus the loop that fills it: a generator expression,
        // which is lazy and has no Core representation at all.
        case n if n.isInstanceOf[Block] || n.isInstanceOf[ControlStructure] =>
          if (bad.isEmpty) bad = "expr:BLOCK-prelude"
        case _ => if (bad.isEmpty) bad = "expr:BLOCK-prelude"
      }
      val isGenExp = ks.exists(k => k.isInstanceOf[Call] &&
        k.asInstanceOf[Call].code.contains("<operator>.genExp"))
      if (isGenExp) hole("expr:genExp")
      else if (bad.nonEmpty) hole(bad)
      else substNames(expr(ks.last), subst) match {
        case o: ujson.Obj => o
        case _            => hole("expr:BLOCK")
      }
    }
  }

  /** A call whose callee is a *bound method held in a variable*.
    *
    * `with cm as x:` is lowered by pysrc2cpg to
    *
    *     manager_tmp0 = <cm>;  enter_tmp0 = manager_tmp0.__enter__
    *     exit_tmp0 = manager_tmp0.__exit__;  value_tmp0 = enter_tmp0()
    *     try: ... finally: __exit__()
    *
    * so the invocation carries no name — the callee is the temporary — while still
    * repeating the receiver at argument index 0, which is where the frontend always puts
    * the implicit `self`. Both halves of the method's identity are therefore present, just
    * split across two statements: the receiver on the call, the attribute name on the
    * assignment that produced the temporary. Rejoining them recovers the `mcall` exactly,
    * which is what makes `with` translatable rather than an unnamed call into nothing.
    *
    * The binding must name the *same* receiver the call passes, so this cannot mistake
    * `g = a.m; g()` for a call on some other object. */
  def boundMethodCall(c: Call, callee: Option[AstNode],
                      args: List[AstNode]): Option[ujson.Obj] =
    for {
      cal <- callee
      t   <- Option(cal).collect { case i: Identifier => i.name }
      // The receiver is where the Python frontend always puts it: argument index 0.
      r   <- c.astChildren.collect { case a: AstNode => a }.l
               .collectFirst { case i: Identifier if aidx(i) == 0 => i.name }
      // Two spellings, both grounded in this method's own CPG rather than assumed. The
      // frontend names the callee after the temporary for `__enter__` and after the
      // attribute itself for `__exit__`, so accept either — but only when the receiver
      // that the *binding* used is the receiver this call passes, or the attribute is one
      // this method is seen to read off that receiver. Neither can turn `g = a.m; g()`
      // into a call on some unrelated object.
      m   <- boundMethods.get(t).collect { case (br, bm) if br == r => bm }
               .orElse(if (attrsOf.getOrElse(r, Set.empty).contains(t)) Some(t) else None)
    } yield ujson.Obj("k" -> "mcall", "recv" -> ujson.Obj("k" -> "name", "v" -> r),
                      "m" -> mangleName(m, currentClass),
                      "args" -> argExprs(args.filterNot(isKeywordArg), args.filter(isKeywordArg)))

  /** Which right-shift `a >> b` is, from the left operand's static type.
    *
    * `None` means the type is unrecovered (`ANY`, an opaque typedef), and then neither
    * `">>"` nor `">>>"` can be justified — 531 of `crypto/`'s 1,545 right shifts are in
    * that state. The caller turns it into `op:shiftRight:unknown-signedness`, which names
    * the missing *type* rather than pretending to a semantics.
    *
    * A `char*` operand cannot reach here (shifting a pointer is not C). */
  def shiftRightOp(lhs: AstNode): Option[String] =
    if (!cppFile) Some(">>")     // Java `>>`/`>>>`, JS, Python: the token is unambiguous
    else {
      val b = bareType(staticTypeOf(lhs))
      if (signedTypeNames.contains(b)) Some(">>")
      else if (unsignedTypeNames.contains(b)) Some(">>>")
      else None
    }

  /** One element of a brace initializer, classified.
    *
    * C gives an element three spellings and they are three different things:
    *
    *   `{ 1, 2, 3 }`               positional  — order *is* the meaning
    *   `{ .name = "x" }`           a **field** designator
    *   `{ [IDX] = v }`             an **index** designator — position is `IDX`, not the
    *                               element's place in the list
    *
    * Joern spells the two designated forms identically (an `<operator>.assignment` whose
    * left child is an Identifier), and only the source text separates them. The index
    * form must not be read positionally: `{ [3] = 7 }` is a four-element array whose
    * fourth entry is 7, and emitting `[7]` would be a one-element list with the wrong
    * value at the wrong place — the exact silent-wrong-answer failure mode. It gets its
    * own hole. */
  def initElement(n: AstNode): (String, Option[String], AstNode) = n match {
    case c: Call if c.methodFullName == "<operator>.assignment" && c.code.trim.startsWith(".") =>
      kidsOf(c) match {
        case (i: Identifier) :: v :: Nil => ("field", Some(i.name), v)
        case _                           => ("shape", None, n)
      }
    case c: Call if c.methodFullName == "<operator>.assignment" && c.code.trim.startsWith("[") =>
      ("index", None, n)
    case other => ("plain", None, other)
  }

  /** `<operator>.arrayInitializer`, which is **two unrelated constructs** sharing a name.
    *
    * 1. A brace initializer, `{ ... }`: each child is a BLOCK wrapping one element.
    *    - all-positional  -> `Expr.listE`. A C array is an ordered sequence of values and
    *      that is what `Val.list` is; `a[i]` already maps to `Expr.index`, so the reads
    *      work. (Writes do not: `Stmt.setIndex` on a `Val.list` is Core's known
    *      immutable-container hole, unchanged by this.)
    *    - all-field-designated -> `Expr.dictE` keyed by the field names. A struct literal
    *      is a finite map from field names to values, C copies structs by value, and
    *      `Dialect.fieldsOnDicts` makes `s.f` read it back. This is what makes the
    *      kernel's `static struct x foo = { .a = 1 }` tables mean something.
    *    - anything mixed, or an index designator anywhere -> a hole naming which.
    *
    * 2. An array **declarator**: `u8 buf[NH_KEY_WORDS]` arrives as an arrayInitializer
    *    whose single child is the *size*, in statement position. It is a declaration, not
    *    a value, and modelling it needs the size model this project does not have — so it
    *    keeps a hole, but under `op:arrayDecl:size`, which says what it actually is
    *    rather than filing it with the initializers it has nothing to do with. */
  def arrayInit(kids: List[AstNode]): ujson.Obj =
    if (kids.isEmpty) hole("op:arrayInitializer:zero-init")
    else if (!kids.forall(_.isInstanceOf[Block])) hole("op:arrayDecl:size")
    else {
      val inner = kids.map(b => kidsOf(b))
      if (!inner.forall(_.size == 1)) hole("op:arrayInitializer:element-shape")
      else {
        val es = inner.map(_.head).map(initElement)
        val kinds = es.map(_._1).distinct
        if (kinds == List("plain"))
          ujson.Obj("k" -> "listE", "items" -> ujson.Arr.from(es.map(e => expr(e._3))))
        else if (kinds == List("field"))
          ujson.Obj("k" -> "dictE", "pairs" -> ujson.Arr.from(es.map { e =>
            ujson.Arr(ujson.Obj("k" -> "str", "v" -> e._2.get), expr(e._3))
          }))
        else if (kinds.contains("index")) hole("op:arrayInitializer:index-designator")
        else if (kinds.contains("shape")) hole("op:arrayInitializer:element-shape")
        else hole("op:arrayInitializer:mixed-designators")
      }
    }

  def callExpr(c: Call): ujson.Obj = {
    val kids = kidsOf(c)
    val mfn  = c.methodFullName
    // A `char*` is an address, not a string value. Core has one `Val.str` for Python's
    // `str` and C's `char*`, and its `+` concatenates while `<`/`>`/`==` compare contents
    // — all three are the wrong answer in C, where they are pointer arithmetic and
    // address comparison. This is the §12 lesson again: the constructs that *look* alike
    // across languages are the dangerous ones. So under a C-family dialect, an operand
    // with static `char*` evidence turns the whole operator into a hole.
    // A null CHECK (`z == NULL` / `z != NULL`) on a char* is exempted from the guard
    // just below: see `isNullLiteral`'s own doc comment for why it needs no address
    // semantics at all, unlike every other `cStringUnsafe` shape.
    val isNullCheck = (mfn == "<operator>.equals" || mfn == "<operator>.notEquals") &&
                       kids.exists(isNullLiteral)
    if (cLikeFile && kids.size == 2 && kids.exists(isCString) &&
        cStringUnsafe.contains(mfn) && !isNullCheck)
      hole(cStringUnsafe(mfn))
    else if (binops.contains(mfn) && kids.size == 2)
      ujson.Obj("k" -> "binop", "op" -> binops(mfn), "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if (mfn == "<operator>.arithmeticShiftRight" && kids.size == 2)
      shiftRightOp(kids(0)) match {
        case Some(op) => ujson.Obj("k" -> "binop", "op" -> op,
                                   "a" -> expr(kids(0)), "b" -> expr(kids(1)))
        case None     => hole("op:shiftRight:unknown-signedness")
      }
    else if (unops.contains(mfn) && kids.size == 1)
      ujson.Obj("k" -> "unop", "op" -> unops(mfn), "a" -> expr(kids(0)))
    // `006-reduce-remaining-holes`, Story 5: `a[i]`, `a` a recognized boxed array
    // -- reads through the box (`irefIndex`+`derefIref`) rather than the ordinary
    // `Expr.index`/`Val.list` machinery, which a heap-boxed array does not use.
    // Checked BEFORE the generic `indexOps` case just below, which still handles
    // every other (unboxed) index expression unchanged.
    else if (indexOps.contains(mfn) && kids.size == 2 &&
             rawLocalOrParamName(kids(0)).map(localName).exists(boxedArrays.contains))
      ujson.Obj("k" -> "derefIref", "p" -> ujson.Obj("k" -> "irefIndex",
        "a" -> ujson.Obj("k" -> "name", "v" -> rawLocalOrParamName(kids(0)).map(localName).get),
        "i" -> expr(kids(1))))
    else if (indexOps.contains(mfn) && kids.size == 2)
      ujson.Obj("k" -> "index", "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if (fieldOps.contains(mfn))
      resolvedRef(c).map(expr) getOrElse (asField(c) match {
        case Some((r, f)) => ujson.Obj("k" -> "field", "a" -> expr(r), "f" -> f)
        case None         => hole("op:fieldAccess-shape")
      })
    else if ((mfn == "<operator>.is" || mfn == "<operator>.isNot") && kids.size == 2)
      ujson.Obj("k" -> "isOp", "neg" -> (mfn == "<operator>.isNot"),
                "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if ((mfn == "<operator>.in" || mfn == "<operator>.notIn") && kids.size == 2)
      ujson.Obj("k" -> "inOp", "neg" -> (mfn == "<operator>.notIn"),
                "a" -> expr(kids(0)), "b" -> expr(kids(1)))
    else if (mfn == "<operator>.conditional" && kids.size == 3)
      ujson.Obj("k" -> "cond", "c" -> expr(kids(0)), "t" -> expr(kids(1)), "e" -> expr(kids(2)))
    else if (mfn == "<operator>.listLiteral")
      ujson.Obj("k" -> "listE", "items" -> exprs(kids))
    else if (mfn == "<operator>.tupleLiteral")
      ujson.Obj("k" -> "tupleE", "items" -> exprs(kids))
    else if (mfn == "<operator>.dictLiteral")
      // The Python frontend emits `{}` here and fills it with indexed stores; a
      // dictLiteral with children would be a shape we have not seen and must not guess at.
      (if (kids.isEmpty) ujson.Obj("k" -> "dictE", "pairs" -> ujson.Arr())
       else hole("op:dictLiteral-nonempty"))
    // `static_cast<uint8_t>(e)` — a **width conversion**, which Core does model.
    //
    // `Autoform/Lang/Core/Numeric.lean` already has `Width`/`IntType`/`IntType.wrap`, and
    // C++20 fixed the one thing that used to make this implementation-defined: conversion
    // to a narrower integer type is two's-complement truncation, which is exactly
    // `IntType.wrap`. So the cast becomes a unary operator `cast:u8` (see `applyUnop`),
    // and `static_cast<uint8_t>(300)` is `44` in Core as it is under `cc`.
    //
    // A **pointer** cast is a different thing wearing the same syntax and is not
    // collapsed into it: reinterpreting an address has no meaning in a language with no
    // addresses. `char` is excluded too — its signedness is implementation-defined — and
    // so is `double`, which is a rounding conversion rather than a truncation.
    //
    // Two refinements on top of that:
    //
    // * The target type is resolved **through typedefs** (`resolveIntType`). V8 spells
    //   almost every integer as a class-local `using` — `Address`, `Chunk`,
    //   `unsigned_type` — and reading only the surface name reported 128 casts as
    //   `opaque-type` when the CPG holds a declaration saying what they are. A chain that
    //   does not reach a fixed-width type still yields a hole; nothing gets a default.
    //
    // * A cast **to `void`** is a discarded-value expression. `(void)0` alone is 492 of
    //   the 939 casts in `src/base`, because it is what `DCHECK`, `USE` and friends expand
    //   to in a release build. `void` is an incomplete type: `(void)e` has *no value*, and
    //   no well-formed C++ program can read one from it. So the only thing to preserve is
    //   the evaluation of `e`, and the translation splits on whether there is anything to
    //   preserve:
    //
    //     - `e` **pure** (a literal, a name, a field or index read of one): nothing
    //       happens when it is evaluated, so the whole expression is `unit` — the one
    //       value Core has that stands for "no value". Nothing is dropped and nothing is
    //       invented. This is the `(void)0` case, and it matters that it is not `0`:
    //       Joern's macro lowering hands `(void)0` back in *argument* position (`DCHECK`'s
    //       expansion becomes a call with the discarded expression as its argument), and
    //       there `0` would be a number the source never produced.
    //     - `e` **impure** (a call, an assignment, an increment): the effects are the
    //       entire content of the statement and must survive, so the operand is emitted
    //       and the cast disappears. The value it yields is one C++ forbids anyone from
    //       reading, so nothing observes the difference — and the subexpressions inside it
    //       become visible to the ledger, which is why `op:and` and `cstr:pointer-arith`
    //       *rise* slightly here: those were previously hidden underneath a cast hole.
    //
    //   A cast to `void*` is not this; it is a pointer cast, and `isPointerType` sends it
    //   to the address hole.
    else if (mfn == "<operator>.cast" && kids.size == 2) {
      val tty = staticTypeOf(kids(0))
      // `007-reduce-remaining-holes-2` US3: a pointer-to-pointer cast is a transparent
      // pass-through of the operand's own (already-correct) translation -- see
      // `castOperandIsPointerShaped`'s own doc comment for why this is sound under
      // Core's structural heap model. An operand that is NOT confirmed pointer-shaped
      // (most commonly an integer-to-pointer cast, e.g. `(int*)0`) has no `Ref`/`iref`
      // to pass through and gets its own narrower, honestly-named hole instead of
      // silently folding into the identity translation.
      if (castTargetIsPointer(kids(0), tty)) {
        if (castOperandIsPointerShaped(kids(1))) expr(kids(1))
        else hole("op:cast:pointer:int-to-pointer")
      }
      else resolveIntType(tty) match {
        case Some(w) => ujson.Obj("k" -> "unop", "op" -> ("cast:" + w),
                                  "a" -> expr(kids(1)))
        case None =>
          if (bareType(tty) == "void")
            (if (pureExpr(kids(1))) ujson.Obj("k" -> "unit") else expr(kids(1)))
          // The width is known to be a function of the target and the target was not
          // stated. Distinct from `op:cast:scalar`, which is a missing *model*, and from
          // `op:cast:opaque-type`, which is a missing *type*: this one is closed by
          // naming a data model, not by a better frontend.
          else if (modelDependentNames.contains(bareType(tty)))
            hole("op:cast:model-dependent")
          else hole("op:cast:" + addrKind(tty))
      }
    }
    // `&x`.
    //
    // This is the one place where the honest answer depends on what is being addressed,
    // because Core's object model already *is* a pointer model for objects and is not one
    // for anything else:
    //
    //   * `&obj` where `obj` has class type is the identity. A Core class instance is a
    //     `Val.ref` — a heap address — so the address of an object is the object's own
    //     value, and writing through the result mutates the same heap cell. Nothing is
    //     invented and nothing is lost. (What is *not* modelled, and was not before, is
    //     C++ value semantics for such an object: `Foo a = b;` copies in C++ and aliases
    //     in Core. That is a pre-existing Core gap, recorded here rather than introduced.)
    //
    //   * `&n` where `n` is a local number, or `&p` where `p` is a local pointer, needs a
    //     model of *the location of a variable*, which Core does not have. `003-box-
    //     address-taken-locals` closes this for the measured majority shape (a plain
    //     local/parameter, not an array or struct field): such an `n` is boxed into a
    //     single-field heap cell (`boxableName`/`boxedLocals`), and `&n` becomes the
    //     identity too, for exactly the same reason as the aggregate case just below --
    //     `n`'s own binding already holds the `Val.ref` once boxed.
    else if (mfn == "<operator>.addressOf" && kids.size == 1) {
      val ty   = staticTypeOf(kids(0))
      val kind = addrKind(ty)
      val nm   = kids(0) match { case i: Identifier => Some(i.name); case _ => None }
      // `&x` on an aggregate is the identity — see the long note below. When the type is
      // unrecovered, `x.f` elsewhere in the same method is proof of the same thing, and
      // `x->f` is proof of the opposite.
      val aggregate =
        isClassType(ty) ||
        (kind == "unknown-type" &&
         nm.exists(n => valueReceivers.contains(n) && !ptrReceivers.contains(n)))
      // Membership in the FINAL `boxedLocals`, not mere shape-eligibility: a name
      // eligible in shape at THIS site can still be excluded overall because some
      // OTHER address-of site of the same name feeds an external call.
      val boxed = boxableName(kids(0)).filter(boxedLocals.contains)
      // `004-function-pointer-tracking`: `&function` for an in-program function is
      // ALSO an identity, for the same reason the aggregate case above is: Core's
      // `Val.fn` has no notion of pointer depth distinguishing "the function" from
      // "the address of the function" (a C function already decays to its own
      // address for calling purposes), so `&add` is exactly what plain `add` already
      // translates to (`expr()`'s existing `MethodRef` case, `fnValue`). Found
      // necessary, not merely nice-to-have: without this, `op = &add;` still holes
      // on `&add` ITSELF even once `op`'s later `pointerCall` sites correctly
      // resolve (`fnPtrVars`) — and that hole aborts the function before any such
      // call site is ever reached, per Core's own hole-propagation semantics.
      // Restricted to an ACTUALLY in-program function (`methodByName`), matching
      // `fnPtrVars`'s own external-function guard for the identical reason.
      val fnIdentity = kids(0) match {
        case mr: MethodRef if methodByName.contains(mr.methodFullName) => true
        case _ => false
      }
      // `006-reduce-remaining-holes`, Story 5: `&a[i]`/`&s.f` once the receiver is
      // a recognized boxed array/struct -- checked FIRST, since `kids(0)` here is
      // an index/field access, not itself a `local`-shaped `addrShape`, so it
      // would otherwise fall straight through every case below to the generic
      // `op:addressOf:element`/`:field` hole.
      val arrIref = boxedArrayIndexOperand(kids(0))
      val structIref = boxedStructFieldOperand(kids(0))
      if (arrIref.isDefined) {
        val (arrName, idxNode) = arrIref.get
        ujson.Obj("k" -> "irefIndex", "a" -> ujson.Obj("k" -> "name", "v" -> arrName),
                  "i" -> expr(idxNode))
      } else if (structIref.isDefined) {
        val (structName, f) = structIref.get
        ujson.Obj("k" -> "irefField", "a" -> ujson.Obj("k" -> "name", "v" -> structName), "f" -> f)
      }
      else if (aggregate) expr(kids(0))
      else if (boxed.isDefined) boxRef(boxed.get)
      else if (fnIdentity) expr(kids(0))
      else {
        val k = if (kind == "unknown-type" && nm.exists(ptrReceivers.contains)) "pointer"
                else kind
        hole("op:addressOf:" + addrShape(kids(0)) + ":" + k)
      }
    }
    // `*p`. The dual of the above, and the same split — but the *identity* half is
    // already covered, because Joern spells `(*p).f` as `indirectFieldAccess` and `p[i]`
    // as `indirectIndexAccess`, both of which are now mapped. What reaches here is a
    // dereference whose result is a *number* (or another pointer), which is exactly the
    // location model Core lacks -- UNLESS `p` is provably, for its whole lifetime in this
    // method, an alias of one specific boxed local (`ptrAliases`: `p = &n` is the ONLY
    // assignment to `p` anywhere in the method), in which case the dereference is exactly
    // a read of that local's box -- OR (Increment B) `p` is itself a parameter verified
    // closed (`closedOutParams`), in which case `p`'s own value already IS the caller's
    // ref and no alias indirection is needed at all.
    else if (mfn == "<operator>.indirection" && kids.size == 1) {
      val nm = rawLocalOrParamName(kids(0)).map(localName)
      // `006-reduce-remaining-holes`, Story 5: `*p`, `p` PROVABLY holding an
      // interior pointer VALUE for its whole lifetime (`ptrIrefNames`) -- `p`
      // itself is unboxed, so this reads straight through its own binding,
      // unlike the `ptrAliases`/`closedOutParams` box-field reads just below.
      if (nm.exists(ptrIrefNames.contains))
        ujson.Obj("k" -> "derefIref", "p" -> ujson.Obj("k" -> "name", "v" -> nm.get))
      else {
        val target = nm.flatMap(ptrAliases.get) orElse nm.filter(closedOutParams.contains)
        target.map(boxField).getOrElse(hole("op:indirection:" + addrKind(staticTypeOf(kids(0)))))
      }
    }
    // `++x` / `x++` in **expression** position. In statement position these are
    // `x = x ± 1` and are translated as such (see `stmt`); as an expression they also
    // have a value, and for the postfix forms that value is the *old* one. Core has no
    // way to sequence a write before a read inside an expression, so this is a hole —
    // and it is a different hole from the statement form, which is why the label says
    // `:value`.
    else if (incrOps.contains(mfn))
      hole("op:" + opLabel(mfn) + ":value")
    // `<operator>.alloc` with children is a **stack array declaration** (`char b[N]`),
    // not a `new`. Core has no arrays and no sizes, so it stays a hole — but under a
    // label that says which of the two it was, because they are not the same problem.
    // The childless form is C++ stack object construction and is handled as a whole
    // block by `ctorAlloc`; reaching it here means the block did not have that shape.
    //
    // The childless residue was measured rather than guessed at: in V8 `src/base` there
    // are 233 childless allocs, and **every single one** of the 83 that `ctorAlloc` does
    // not fold sits in the expected three-sibling block — the shape is fine. What is
    // missing is the class: the frontend emitted the constructor as `ANY.ANY:void()`,
    // with `code` literally `"ANY.ANY()"` and the temporary's type `ANY`. There is no
    // name, no argument, and no type anywhere in the node to recover one from, so this
    // cannot be closed from the CPG at all, and `op:alloc:ctor-shape` was the wrong name
    // for it: it pointed at a pattern-matching gap in this exporter when the gap is in
    // the C++ frontend's name resolution. The two are separated so the count says which.
    else if (mfn == "<operator>.alloc")
      hole(if (kids.nonEmpty) "op:alloc:array-decl"
           else if (inCtorShape(c)) "op:alloc:ctor-unresolved-class"
           else "op:alloc:ctor-shape")
    else if (mfn == "<operator>.arrayInitializer") arrayInit(kids)
    // `static_assert(cond)` / `static_assert(cond, "msg")`.
    //
    // This is the one construct in the C++ ledger that is genuinely *nothing* at run time,
    // and the argument has to be made carefully because "this has no effect" is how real
    // behaviour gets dropped.
    //
    // `static_assert` is a **declaration**, not a statement ([dcl.pre]). Its first operand
    // is required to be a constant expression contextually converted to `bool`, so it is
    // evaluated by the compiler and never by the program: it occupies no storage, emits no
    // code, and cannot contain a call to anything with a runtime effect, because a
    // constant expression may not. There are exactly two outcomes. If the condition is
    // false the program is **ill-formed** — `cc` refuses to produce a binary, so there is
    // no execution for Core to model and nothing to be faithful to. If it is true the
    // declaration contributes nothing whatever to the translated program. So for every
    // program that compiles — the only programs this pipeline claims to translate — the
    // declaration is observationally equal to the empty statement, and `unit` in
    // expression position (the frontend wraps it as one) is that.
    //
    // What *is* given up is stated plainly: Core will happily run a program whose
    // `static_assert` is false, where `cc` would reject it. That is a loss of *rejection*
    // power, not a change to the behaviour of any program that runs — the ledger is a
    // claim about executions, and this adds no execution that C++ would have run
    // differently.
    else if (mfn == "<operator>.staticAssert")
      ujson.Obj("k" -> "unit")
    // f-strings. Python only — see `pyFile`.
    else if (mfn == "<operator>.formatString" && pyFile) fstring(kids)
    // `004-function-pointer-tracking`: a call through a function-pointer-valued
    // variable Joern itself could not statically resolve (`<operator>.pointerCall`,
    // research.md §1). When the callee names a variable this method's own
    // `fnPtrVars` has proven, by a bounded whole-function single-assignment check,
    // holds exactly one known, non-capturing, in-program function -- rewrite the
    // WHOLE call to an ordinary direct call to that function, reusing the same
    // real-argument extraction (`aidx(_) >= 1`) every other call already uses. Any
    // callee this cannot prove safe (ambiguous, external, a struct field, an array
    // element, or the general shape) falls through to the unchanged generic hole
    // just below, exactly as today.
    else if (mfn == "<operator>.pointerCall") {
      val realArgs = kidsOf(c).filter(aidx(_) >= 1)
      val callee   = kidsOf(c).find(aidx(_) == -1)
      // `007-reduce-remaining-holes-2`: `(size_t)(expr)` -- an ordinary C-style
      // parenthesized cast to a typedef'd scalar type -- is frequently mis-parsed
      // by Joern's C frontend as a CALL to a "variable" whose name happens to be
      // the type name, with the cast's own operand as its sole argument (this
      // node, since `size_t` resolves to no known function). Live-CPG-sampled on
      // SQLite: 831 of 5,724 `pointerCall` sites are exactly this shape -- a
      // bare-identifier callee `resolveIntType` recognizes as a scalar type, with
      // exactly one real argument -- and every one of the sampled 15 is visibly a
      // cast in its own source text (`(size_t) (...)`), not a genuine
      // function-pointer call. Checked before the `004` function-pointer
      // resolution below: a real function is never itself the name of a
      // resolvable scalar type, so there is no collision risk. Reuses the exact
      // `cast:<width>` shape `<operator>.cast` already produces -- no new
      // `Expr`/`Val`.
      val functionalCastWidth: Option[String] = (callee, realArgs) match {
        case (Some(i: Identifier), List(_)) => resolveIntType(i.name)
        case _ => None
      }
      functionalCastWidth match {
        case Some(w) =>
          ujson.Obj("k" -> "unop", "op" -> ("cast:" + w), "a" -> expr(realArgs.head))
        case None =>
          // `004-function-pointer-tracking`: a call through a function-pointer-
          // valued variable Joern itself could not statically resolve (research.md
          // §1). When the callee names a variable this method's own `fnPtrVars`
          // has proven, by a bounded whole-function single-assignment check, holds
          // exactly one known, non-capturing, in-program function -- rewrite the
          // WHOLE call to an ordinary direct call to that function.
          //
          // Second, independent path: the callee is a STRUCT FIELD
          // (`p->xCellSize(...)`, this label's dominant real shape -- 396 of 592
          // raw sites measured live on SQLite, vs 122 identifier-shaped and the
          // rest smaller). `fieldFnTargets` proves the field-level analogue --
          // whole-PROGRAM single-VALUE rather than single-assignment-SITE, with
          // the struct/array-literal and whole-aggregate-copy exclusion
          // `riskyLiteralInitTypes` enforces (its own doc comment: a confirmed,
          // not hypothetical, silent-wrong-answer trap this session found and
          // closed before it could ship). Any callee neither path can prove safe
          // (ambiguous, external, an array element, or the general shape) falls
          // through to the unchanged generic hole just below, exactly as today.
          pointerCallCalleeVar(c).flatMap(fnPtrVars.get)
            .orElse(pointerCallCalleeField(c).flatMap(fieldFnTargets.get)) match {
            case Some(target) => ujson.Obj("k" -> "call", "f" -> target, "args" -> exprs(realArgs))
            case None          => hole("op:" + opLabel(mfn))
          }
      }
    }
    // `005-sizeof-constant-folding`: `sizeof(expr)` and `sizeof(TypeName)` are
    // indistinguishable at this point -- confirmed against the CPG directly
    // (research.md §1): both produce a single child carrying the operand's type
    // directly, which `staticTypeOf` already reads correctly for either shape (a
    // bare type name like `"int"` is never also a real local's name, so the
    // `localTypes` lookup harmlessly falls through to the node's own type). Folds
    // to the literal byte count for a scalar, pointer, or (possibly
    // multi-dimensional) fixed-size array operand; every other shape -- an
    // aggregate, an opaque type, or a data-model-dependent type under an
    // unspecified model -- falls through to a hole, labelled with the exact same
    // taxonomy `<operator>.cast` already uses just above (research.md §5), not the
    // single generic `op:sizeOf`.
    else if (mfn == "<operator>.sizeOf" && kids.size == 1) {
      val ty = staticTypeOf(kids(0))
      // `006-reduce-remaining-holes`, Story 4: a struct/union operand additionally
      // tries the aggregate layout resolver above; every other shape is unchanged
      // from `005`, and an aggregate whose layout does not resolve falls through
      // to the exact same `op:sizeOf:object` hole below it always has.
      sizeofBytes(ty).orElse(if (isClassType(ty)) aggregateSizeofBytes(ty) else None) match {
        case Some(n) => intLit(n)
        case None =>
          if (modelDependentNames.contains(bareType(ty))) hole("op:sizeOf:model-dependent")
          else hole("op:sizeOf:" + addrKind(ty))
      }
    }
    else if (mfn.startsWith("<operator>"))
      hole("op:" + opLabel(mfn))
    // `import x` / `from p import x`: a binding, not a call. See `importValue`.
    // A *fourth* literal is the `as` alias: `import typing as t`, `from p import x as y`.
    // That shape was not matched at all, so all 492 aliased imports in Ansible fell
    // through to the generic call branch and emitted their two source fragments as
    // `import:operand` holes — 984 of the 1,199 in that label, for a construct that
    // differs from a plain import in one bit.
    else if (c.name == "import" && mfn == "<unknownFullName>" &&
             (kids match {
               case (_: Identifier) :: (_: Literal) :: (_: Literal) :: rest =>
                 rest.length <= 1 && rest.forall(_.isInstanceOf[Literal])
               case _ => false
             }))
      importValue(kids(1).asInstanceOf[Literal].code.trim,
                  kids(2).asInstanceOf[Literal].code.trim,
                  aliased = kids.length == 4)
    else {
      // A real call. Arguments are the children with argumentIndex >= 1; the callee sits
      // at -1 and the Python frontend repeats the receiver at 0.
      // Keyword arguments carry ARGUMENT_NAME and ARGUMENT_INDEX -1, which is also the
      // callee's index -- so they must be split off *before* the callee is chosen, or a
      // `**kwargs` could be mistaken for the thing being called.
      val kwArgs = kids.filter(isKeywordArg)
      val args   = kids.filter(k => aidx(k) >= 1 && !isKeywordArg(k))
      val callee = kids.filterNot(isKeywordArg).find(aidx(_) == -1).orElse(kids.headOption)
      // Construction: Joern resolves `Cls(...)` to `...Cls.__init__` while keeping the
      // call's name as the class. An explicit `super().__init__(...)` keeps name
      // `__init__` and is a method call, not an allocation.
      val ctor: Option[String] =
        if (mfn.endsWith(".__init__") && c.name != "__init__") Some(c.name)
        else callee match {
          case Some(i: Identifier) if classNames.contains(i.name) && i.name == c.name => Some(i.name)
          case _                                                                      => None
        }
      // `Cls.<fakeNew>(args)` — the frontend's spelling of allocation inside the metaclass
      // machinery. The receiver at index 0 is the TYPE_REF, so the real arguments start at
      // 1 exactly as for any other call.
      val fakeNew: Option[String] = callee.flatMap(asField).collect {
        case (t: TypeRef, "<fakeNew>") => t.typeFullName.stripSuffix("<meta>").split('.').last
      }
      // `Cls.<body>()` — evaluating a class body *produces the class object*. This is the
      // one shape where an empty call name meant something we can say exactly.
      val classBody: Option[String] = callee.collect {
        case m: MethodRef if m.methodFullName.endsWith(".<body>") =>
          m.methodFullName.stripSuffix(".<body>")
      }
      if (fakeNew.isDefined)
        ujson.Obj("k" -> "alloc", "cls" -> fakeNew.get, "args" -> argExprs(args, kwArgs))
      else if (classBody.isDefined) typeValue(classBody.get + "<meta>")
      else ctor match {
        case Some(cls) => ujson.Obj("k" -> "alloc", "cls" -> cls, "args" -> argExprs(args, kwArgs))
        case None =>
          callee.flatMap(asField) match {
            case Some((recv, m)) =>
              ujson.Obj("k" -> "mcall", "recv" -> expr(recv), "m" -> m,
                        "args" -> argExprs(args, kwArgs))
            // Only a call the frontend left *unnamed* can be one of these; a named call
            // already says what it invokes, and rerouting it on a name coincidence would
            // be a guess.
            case None => (if (c.name.isEmpty) boundMethodCall(c, callee, args) else None)
              .getOrElse {
              // A call with no callee name is not a call we can emit. `Expr.call` is *by
              // name*; there is no "apply this value", so `f(x)(y)` — a callee that is
              // itself computed — has no Core form. Emitting `call ""` (as this did) was
              // worse than a hole: it type-checked, counted as translated, and then
              // resolved to nothing at run time. That is the silently-wrong category the
              // ledger exists to prevent, so it is now a hole that says which shape it was.
              if (c.name.isEmpty)
                hole(if (callee.exists(_.isInstanceOf[Call])) "call:computed-callee"
                     else "call:no-callee-name")
              // Joern often resolves the callee to a method of this program. Emitting that
              // `fullName` rather than the short name is what makes `_wrapper` in
              // `_cached.py` distinguishable from `_wrapper` in `_cachedmethod.py`:
              // `Ctx.resolve` matches the full name exactly, where its short-name fallback
              // needs a *unique* suffix and so resolved neither.
              else if (methodByName.contains(mfn))
                ujson.Obj("k" -> "call", "f" -> mangledFullName(mfn),
                          "args" -> argExprs(args, kwArgs))
              else ujson.Obj("k" -> "call", "f" -> c.name, "args" -> argExprs(args, kwArgs))
            }
          }
      }
    }
  }

  // ---- statements -----------------------------------------------------------
  // `seqOf` (below) and `moduleObjectsInit`'s fold build a right-nested
  // `{"k":"seq","a":...,"b":...}` chain, one level per statement, mirroring Lean's
  // binary `Stmt.seq` constructor exactly (`render_lean.py` reads this shape 1:1). For a
  // long flat statement list that chain is deep enough that `ujson`'s own recursive
  // `Value.transform` -- third-party library code, not ours -- overflows the JVM stack
  // writing it out: confirmed live, a 3,000-statement chain crashes entirely inside
  // `upickle.core.RenderUtils`/`ujson.AstTransformer`, with zero frames in this file's
  // own code (research.md item 1). `maxSeqChainLen`/`seqChainCompactThreshold` are
  // declared near the top of `exec` (search "seqChainCompactThreshold"), not here, so
  // that `moduleObjectsInit` (defined earlier in this file, and also updating
  // `maxSeqChainLen`) is a backward reference to it rather than a forward one.

  /** Renders a `ujson.Value` to JSON text by driving the same `Renderer`/`Visitor`
    * protocol `ujson.write` itself uses (`ujson.Value$.transform` walks a value and
    * calls exactly these `visitObject`/`visitArray`/`visitString`/... methods), but with
    * an explicit heap-allocated frame stack instead of the JVM call stack -- so output is
    * produced for a chain of any depth without recursing once per nesting level. This is
    * research.md item 3's route (a) (drive the streaming visitor directly): confirmed
    * reachable from a `.sc` script via `ujson.Renderer`'s public constructor and
    * `upickle.core.Visitor`'s public methods (no `ujson.Value` internals needed), and
    * confirmed byte-identical to `ujson.write(v, indent)` for both `indent = 1` and
    * compact (`indent = -1`) on every shape tested, including this exact `seq`-chain
    * shape. `indent = 1` pretty-printing is quadratic in output size at deep nesting
    * (indentation alone is a 1..N space triangle) -- confirmed empirically to
    * OutOfMemoryError a 100,000-deep chain regardless of stack safety -- so the caller
    * passes `indent = -1` once `maxSeqChainLen` crosses `seqChainCompactThreshold`;
    * every already-working (shallow) run keeps `indent = 1` and is therefore still
    * byte-identical to today's output (FR-004). */
  def writeJson(root: ujson.Value, indent: Int): String = {
    val sw = new java.io.StringWriter()
    val renderer = new ujson.Renderer(sw, indent, false)

    sealed trait JsonFrame { var awaitingChild: Boolean = false }
    final case class ArrFrame(ov: upickle.core.ArrVisitor[Any, Any], it: Iterator[ujson.Value])
      extends JsonFrame
    final case class ObjFrame(ov: upickle.core.ObjVisitor[Any, Any], it: Iterator[(String, ujson.Value)])
      extends JsonFrame

    val stack = scala.collection.mutable.ArrayBuffer.empty[JsonFrame]
    var lastResult: AnyRef = null

    def visitScalar(v: upickle.core.Visitor[Any, Any], value: ujson.Value): AnyRef = value match {
      case ujson.Str(s) => v.visitString(s, -1).asInstanceOf[AnyRef]
      case ujson.Num(n) => v.visitFloat64(n, -1).asInstanceOf[AnyRef]
      case ujson.True   => v.visitTrue(-1).asInstanceOf[AnyRef]
      case ujson.False  => v.visitFalse(-1).asInstanceOf[AnyRef]
      case ujson.Null   => v.visitNull(-1).asInstanceOf[AnyRef]
      case other        => throw new IllegalArgumentException(s"writeJson: not a scalar: $other")
    }

    // Pushes a frame for Obj/Arr (their children are visited across later loop
    // iterations, not here) or resolves a scalar immediately into `lastResult`.
    def descend(v: upickle.core.Visitor[Any, Any], value: ujson.Value): Unit = value match {
      case a: ujson.Arr =>
        val ov = v.visitArray(a.value.length, -1).asInstanceOf[upickle.core.ArrVisitor[Any, Any]]
        stack.append(ArrFrame(ov, a.value.iterator))
      case o: ujson.Obj =>
        val ov = v.visitObject(o.value.size, true, -1).asInstanceOf[upickle.core.ObjVisitor[Any, Any]]
        stack.append(ObjFrame(ov, o.value.iterator))
      case scalar =>
        lastResult = visitScalar(v, scalar)
    }

    descend(renderer.asInstanceOf[upickle.core.Visitor[Any, Any]], root)
    while (stack.nonEmpty) {
      stack.last match {
        case af: ArrFrame =>
          // `awaitingChild` is true when we come back around to this frame after a
          // previously-pushed child (however many levels it itself descended) finally
          // unwound -- its result must reach `visitValue` before asking for the next item.
          if (af.awaitingChild) { af.ov.visitValue(lastResult, -1); af.awaitingChild = false }
          if (af.it.hasNext) {
            val sub = af.ov.subVisitor.asInstanceOf[upickle.core.Visitor[Any, Any]]
            af.awaitingChild = true
            descend(sub, af.it.next())
            // A scalar child resolves in the same iteration (no frame was pushed);
            // consume it right away instead of waiting for a loop iteration that will
            // never come back to a still-scalar "child".
            if (stack.last eq af) { af.ov.visitValue(lastResult, -1); af.awaitingChild = false }
          } else {
            lastResult = af.ov.visitEnd(-1).asInstanceOf[AnyRef]
            stack.remove(stack.length - 1)
          }
        case of: ObjFrame =>
          if (of.awaitingChild) { of.ov.visitValue(lastResult, -1); of.awaitingChild = false }
          if (of.it.hasNext) {
            val (k, value) = of.it.next()
            val kv = of.ov.visitKey(-1).asInstanceOf[upickle.core.Visitor[Any, Any]]
            of.ov.visitKeyValue(kv.visitString(k, -1))
            val sub = of.ov.subVisitor.asInstanceOf[upickle.core.Visitor[Any, Any]]
            of.awaitingChild = true
            descend(sub, value)
            if (stack.last eq of) { of.ov.visitValue(lastResult, -1); of.awaitingChild = false }
          } else {
            lastResult = of.ov.visitEnd(-1).asInstanceOf[AnyRef]
            stack.remove(stack.length - 1)
          }
      }
    }
    renderer.flushCharBuilder()
    sw.toString
  }

  def seqOf(xs: List[ujson.Obj]): ujson.Obj = {
    if (xs.length > maxSeqChainLen) maxSeqChainLen = xs.length
    if (xs.isEmpty) skip
    else {
      // An explicit right-to-left loop, not `reduceRight`: this is the "iterative
      // sequence writer" -- it builds the exact same right-nested chain `reduceRight`
      // did, but with a JVM-stack cost that is O(1) in `xs.length` by construction,
      // rather than relying on `reduceRight`'s own (unverified, in this planning
      // environment) stack behavior for long lists.
      val arr = xs.toArray
      var acc: ujson.Obj = arr(arr.length - 1)
      var i = arr.length - 2
      while (i >= 0) {
        acc = ujson.Obj("k" -> "seq", "a" -> arr(i), "b" -> acc)
        i -= 1
      }
      acc
    }
  }

  /** Python's frontend turns statement-expressions (comprehensions, display literals)
    * into a BLOCK whose last child is the value. Split it into prelude statements and
    * the value expression rather than losing it to a hole. */
  def valueOf(n: AstNode): (List[ujson.Obj], ujson.Obj) = n match {
    case b: Block =>
      val all = kidsOf(b)
      // C++ stack construction reaches here whenever the constructed object is the value
      // of an assignment, an argument or a `return`, which is most of the time. Splitting
      // it into "two statements and an identifier" is what made `Expr.alloc` unreachable:
      // the pieces are individually meaningless and the middle one is the constructor.
      ctorAlloc(all) match {
        case Some(a) => (Nil, a)
        case None =>
          all match {
            case Nil  => (Nil, hole("expr:empty-block"))
            case ks   => (stmts(ks.init), expr(ks.last))
          }
      }
    // `006-reduce-remaining-holes`: an assignment/increment nested anywhere inside
    // this position's own value now threads its prelude out too (research.md §3) --
    // `exprV`'s base case is `(Nil, expr(other))`, identical to before, whenever
    // `other` contains no such construct.
    case other => exprV(other)
  }

  /** `for x in e:` — the Python frontend desugars it before we ever see it, into
    *     tmp = e.__iter__()
    *     while <UNKNOWN iteratorNonEmptyOrException>: { x = tmp.__next__(); body }
    * Recovering the `forIn` from that shape is what makes iteration translatable at all;
    * there is no FOR control structure in a Python CPG. */
  def forPattern(kids: List[AstNode]): Option[ujson.Obj] = kids match {
    case (a: Call) :: (w: ControlStructure) :: Nil
        if a.methodFullName == "<operator>.assignment" &&
           (w.controlStructureType == "WHILE" || w.controlStructureType == "DO") =>
      val ak = kidsOf(a)
      val wk = kidsOf(w)
      val iterVar = ak.headOption.collect { case i: Identifier => i.name }
      val condIsIter = wk.headOption.exists { c =>
        c.isInstanceOf[Unknown] && c.code.contains("iteratorNonEmptyOrException")
      }
      // rhs is `X.__iter__()`, possibly wrapped in a block that computes X first.
      def iterSource(rhs: AstNode): Option[(List[ujson.Obj], ujson.Obj)] = rhs match {
        case b: Block =>
          kidsOf(b) match {
            case Nil => None
            case ks  => iterSource(ks.last).map { case (_, e) => (ks.init.map(stmt), e) }
          }
        case c: Call if c.name == "__iter__" =>
          kidsOf(c).find(aidx(_) == -1).flatMap(asField).map { case (r, _) => (Nil, expr(r)) }
        case _ => None
      }
      for {
        tmp  <- iterVar
        if condIsIter && ak.size == 2 && wk.size >= 2
        src  <- iterSource(ak(1))
        body <- wk.lift(1).collect { case b: Block => b }
        bk    = kidsOf(body)
        first<- bk.headOption
        (x, ok) = first match {
          case nx: Call if nx.methodFullName == "<operator>.assignment" =>
            kidsOf(nx) match {
              case (i: Identifier) :: (nc: Call) :: Nil if nc.name == "__next__" =>
                val recvOk = kidsOf(nc).find(aidx(_) == -1).flatMap(asField)
                  .exists { case (r, _) => r.isInstanceOf[Identifier] &&
                                           r.asInstanceOf[Identifier].name == tmp }
                (i.name, recvOk)
              case _ => ("", false)
            }
          case _ => ("", false)
        }
        if ok
      } yield seqOf(src._1 :+ ujson.Obj(
        "k" -> "forIn", "x" -> x, "e" -> src._2, "body" -> seqOf(bk.tail.map(stmt))))
    case _ => None
  }

  /** Run `f` with `gotoAsBreak` cleared, and restore it afterwards.
    *
    * Used when descending into a loop body. `methodBody` has already proved that no
    * `goto` sits inside a loop, so this changes nothing today; it is here so that if that
    * proof is ever weakened, the failure is a `control:GOTO` hole rather than a `break`
    * that silently leaves the wrong loop. */
  def outsideLoopScope[A](f: => A): A = {
    val saved = gotoAsBreak
    gotoAsBreak = None
    val r = f
    gotoAsBreak = saved
    r
  }

  /** Rewrite every `continue` that belongs to *this* loop into `step; continue`.
    *
    * This is the whole of the `for`/`while` difference, and it is why the textbook
    * desugaring is not enough. `for (i = 0; i < n; i++) { if (p) continue; f(i); }`
    * becomes `i = 0; while (i < n) { ...; i++ }`, and a `continue` in the body jumps
    * straight back to the test **without running `i++`** — an infinite loop, from a
    * translation that type-checks and looks right. C's `continue` in a `for` jumps to the
    * *step*, so putting a copy of the step in front of each `continue` is not an
    * approximation: it is exactly what the standard says, and it is why this does not
    * need a hole.
    *
    * The recursion stops at `loop` and `forIn`, because a `continue` inside a nested loop
    * belongs to *that* loop and must not be given this one's step. `break` is left alone:
    * C's `break` leaves the loop without running the step, which is what the desugared
    * `break` already does.
    *
    * Duplicating the step is safe however many times it appears — each copy runs on a
    * path where the original would have run exactly once. */
  def pushStep(v: ujson.Value, step: ujson.Value): ujson.Value = v match {
    case o: ujson.Obj =>
      o.value.get("k").map(_.str) match {
        case Some("cont") =>
          ujson.Obj("k" -> "seq", "a" -> step, "b" -> ujson.Obj("k" -> "cont"))
        case Some("loop") | Some("forIn") => o
        case _ =>
          ujson.Obj.from(o.value.toList.map { case (k, x) => (k, pushStep(x, step)) })
      }
    case a: ujson.Arr => ujson.Arr.from(a.value.toList.map(x => pushStep(x, step)))
    case other        => other
  }

  /** A C-family `for (init; cond; step) body`.
    *
    *     init; while (cond) { body-with-step-before-each-continue; step }
    *
    * Joern gives the four clauses as the FOR node's children in source order, with `body`
    * last, and **omits** any clause the source left out — so a node with fewer than four
    * children is ambiguous (is the single expression the condition or the step?) and there
    * is nothing in the graph that says which. Those keep a hole that names the ambiguity
    * rather than picking. Measured on `crypto/`: 194 of 205 `for`s carry all four.
    *
    * `LOCAL` children (`for (int i = 0; ...)`) are declarations and carry no behaviour;
    * the initializing assignment is a separate child and is kept. */
  /** Rewrite every `continue` belonging to *this* do-while into `if (C) continue else
    * break`. See the `DO` case for why: a do-while's `continue` jumps to the condition
    * test, and the `while (true)` shape has no test to jump to. Stops at nested
    * `loop`/`forIn` for the same reason `pushStep` does. */
  /** A bounded label for an unmapped operator.
    *
    * `mfn.stripPrefix("<operator>.")` assumes the name HAS that prefix. Joern also emits
    * bare `<operator>()`, which left the prefix in place and produced
    * `op:<operator>():bool()` -- frontend text verbatim, so the label space grew with the
    * corpus and the ledger's group-by-cause counted one "cause" per spelling. Anything
    * that is not a clean `<operator>.name` becomes `op:unnamed-operator`. */
  def opLabel(mfn: String): String = {
    val n = mfn.stripPrefix("<operator>.")
    if (n.isEmpty || n.contains("<") || n.contains("(")) "unnamed-operator" else n
  }

  def pushDoTest(v: ujson.Value, cond: ujson.Value): ujson.Value = v match {
    case o: ujson.Obj =>
      o.value.get("k").map(_.str) match {
        case Some("cont") =>
          ujson.Obj("k" -> "ifte", "c" -> cond, "t" -> ujson.Obj("k" -> "cont"),
                    "e" -> ujson.Obj("k" -> "brk"))
        case Some("loop") | Some("forIn") => o
        case _ =>
          ujson.Obj.from(o.value.toList.map { case (k, x) => (k, pushDoTest(x, cond)) })
      }
    case a: ujson.Arr => ujson.Arr.from(a.value.toList.map(x => pushDoTest(x, cond)))
    case other        => other
  }

  def forStmt(cs: ControlStructure): ujson.Obj = {
    val ks = kidsOf(cs).filterNot(_.isInstanceOf[Local])
    if (ks.size != 4) holeS("control:FOR:elided-clause")
    else outsideLoopScope {
      val step = stmt(ks(2))
      val body = pushStep(stmt(ks(3)), step)
      seqOf(List(stmt(ks(0)),
                 ujson.Obj("k" -> "loop", "c" -> expr(ks(1)),
                           "body" -> ujson.Obj("k" -> "seq", "a" -> body, "b" -> step))))
    }
  }

  /** Assignment, including the augmented forms, to any of the three target shapes. */
  def assignTo(lhs: AstNode, rhs: AstNode, aug: Option[String]): ujson.Obj = {
    val (prelude, rhsE) = valueOf(rhs)
    def combine(cur: => ujson.Obj): ujson.Obj = aug match {
      case None     => rhsE
      case Some(op) => ujson.Obj("k" -> "binop", "op" -> op, "a" -> cur, "b" -> rhsE)
    }
    val core = lhs match {
      // `s += n` on a `char*` advances a pointer; see `cStringUnsafe`. The augmented form
      // never reaches `callExpr`, so it is guarded here too.
      case _ if cLikeFile && aug.isDefined && (isCString(lhs) || isCString(rhs)) =>
        holeS("cstr:pointer-arith")
      // `003-box-address-taken-locals`: a plain write to a boxed local/parameter
      // writes the box's one field instead of rebinding the name -- see `expr`'s
      // matching read-side case just above, and `boxedLocals`.
      case i: Identifier if boxedLocals.contains(localName(i.name)) =>
        val nm = localName(i.name)
        ujson.Obj("k" -> "setField", "r" -> boxRef(nm), "f" -> "v", "v" -> combine(boxField(nm)))
      // `006-reduce-remaining-holes`, Story 5: the C frontend spells BOTH
      // `int a[4];` and `int a[4] = {0};` as a synthetic assignment to `a`
      // (RHS `<operator>.alloc`/`<operator>.arrayInitializer`) -- confirmed live,
      // this session, against exactly this shape. For a recognized boxed array/
      // struct this is now `skip`, not translated: the unconditional prologue
      // already allocated `a`'s box (every field `.unit`), so the ONLY thing this
      // statement could still contribute is the source initializer's actual
      // values, which this increment does not model (out of scope, matching
      // spec.md's own "no VLA/malloc-sized allocation" exclusion in spirit --
      // every quickstart.md Story 5 acceptance scenario only reads a
      // previously-WRITTEN element/field, never relies on this initializer).
      case i: Identifier if boxedArrays.contains(localName(i.name)) ||
                             boxedStructs.contains(localName(i.name)) =>
        skip
      case i: Identifier =>
        // At module scope, and for a name a `global` statement rebound, an assignment
        // writes the module-level frame rather than creating a local.
        val k = if (moduleScope || declaredGlobals.contains(i.name)) "setGlobal" else "assign"
        ujson.Obj("k" -> k, "x" -> localName(i.name),
                  "e" -> combine(ujson.Obj("k" -> "name", "v" -> localName(i.name))))
      // `*p = v` where `p` is PROVABLY, for its whole lifetime in this method, an
      // alias of one specific boxed local (`ptrAliases`), OR (Increment B) `p` is
      // itself a parameter verified closed (`closedOutParams`) -- the write-side
      // counterpart of the read case in `callExpr`'s `<operator>.indirection`
      // handling. Checked BEFORE the generic `<operator>`-prefixed catch-all below,
      // which still fires (unchanged `assign:lhs:indirection`) for every `*p` this
      // cannot prove safe. `ptrAliases.getOrElse(nm, nm)` reads as: if `nm` aliases
      // some OTHER boxed local, write through that; otherwise (must be because the
      // guard's `closedOutParams` branch matched) `nm` itself already IS the ref.
      // `006-reduce-remaining-holes`, Story 5: `*p = v`, `p` PROVABLY holding an
      // interior pointer VALUE for its whole lifetime (`ptrIrefNames`) -- write
      // side of `callExpr`'s matching `<operator>.indirection` read case. `p`
      // itself is unboxed, so this writes straight through its own binding.
      case c: Call if c.methodFullName == "<operator>.indirection" && kidsOf(c).size == 1 &&
                       rawLocalOrParamName(kidsOf(c)(0)).map(localName).exists(ptrIrefNames.contains) =>
        val nm = rawLocalOrParamName(kidsOf(c)(0)).map(localName).get
        val pRef = ujson.Obj("k" -> "name", "v" -> nm)
        ujson.Obj("k" -> "setDerefIref", "p" -> pRef,
                  "v" -> combine(ujson.Obj("k" -> "derefIref", "p" -> pRef)))
      case c: Call if c.methodFullName == "<operator>.indirection" && kidsOf(c).size == 1 &&
                       rawLocalOrParamName(kidsOf(c)(0)).map(localName)
                         .exists(n => ptrAliases.contains(n) || closedOutParams.contains(n)) =>
        val nm = rawLocalOrParamName(kidsOf(c)(0)).map(localName).get
        val target = ptrAliases.getOrElse(nm, nm)
        ujson.Obj("k" -> "setField", "r" -> boxRef(target), "f" -> "v",
                  "v" -> combine(boxField(target)))
      case fa if asField(fa).isDefined =>
        val (r, f) = asField(fa).get
        if (aug.isDefined && !pureNode(r)) holeS("assign:aug-impure-receiver")
        else ujson.Obj("k" -> "setField", "r" -> expr(r), "f" -> f,
                       "v" -> combine(ujson.Obj("k" -> "field", "a" -> expr(r), "f" -> f)))
      // `006-reduce-remaining-holes`, Story 5: `a[i] = v`, `a` a recognized boxed
      // array -- write side of `callExpr`'s matching `indexOps` read case.
      // Checked BEFORE the generic `asIndex` case just below.
      case ia if asIndex(ia).isDefined &&
                 rawLocalOrParamName(asIndex(ia).get._1).map(localName).exists(boxedArrays.contains) =>
        val (a, b) = asIndex(ia).get
        val arrName = rawLocalOrParamName(a).map(localName).get
        val p = ujson.Obj("k" -> "irefIndex", "a" -> ujson.Obj("k" -> "name", "v" -> arrName),
                          "i" -> expr(b))
        ujson.Obj("k" -> "setDerefIref", "p" -> p,
                  "v" -> combine(ujson.Obj("k" -> "derefIref", "p" -> p)))
      case ia if asIndex(ia).isDefined =>
        val (a, b) = asIndex(ia).get
        if (aug.isDefined && !(pureNode(a) && pureNode(b))) holeS("assign:aug-impure-target")
        else ujson.Obj("k" -> "setIndex", "r" -> expr(a), "i" -> expr(b),
                       "v" -> combine(ujson.Obj("k" -> "index", "a" -> expr(a), "b" -> expr(b))))
      case c: Call if c.methodFullName.startsWith("<operator>") =>
        holeS("assign:lhs:" + c.methodFullName.stripPrefix("<operator>."))
      case other => holeS("assign:lhs:" + other.label)
    }
    seqOf(prelude :+ core)
  }

  /** `global a, b` — the names it rebinds. */
  def globalDeclNames(u: Unknown): List[String] =
    u.code.trim.stripPrefix("global").split(",").map(_.trim).filter(_.nonEmpty).toList

  /** `++x` / `x++` / `--x` / `x--` as a **statement**.
    *
    * With the value discarded, all four are `x = x ± 1`, and prefix and postfix are
    * indistinguishable — this is the ordinary desugaring, not an approximation.
    *
    * Two things it refuses. A **pointer** target is not `p = p + 1`: C scales by
    * `sizeof(*p)`, Core has no sizes, and `p + 1` on a `char*` is only accidentally right
    * (`sizeof(char) == 1`). Writing the accidental case and holing the rest would put a
    * silent type dependency into the translation, so every pointer target holes — the
    * same rule `cstr:pointer-arith` already applies to `p += n`. And an **impure**
    * target holes, because the desugaring evaluates the target twice; that is
    * `assign:aug-impure-*`'s rule, applied here for the same reason. */
  def incrStmt(tgt: AstNode, op: String, opName: String): ujson.Obj = {
    val one = ujson.Obj("k" -> "int", "v" -> ujson.Num(1.0))
    def bump(cur: ujson.Obj): ujson.Obj =
      ujson.Obj("k" -> "binop", "op" -> op, "a" -> cur, "b" -> one)
    // `006-reduce-remaining-holes`, Story 5: `p++`/`p--`, `p` PROVABLY holding an
    // interior pointer VALUE for its whole lifetime (`ptrIrefNames`) -- checked
    // BEFORE the general pointer-target guard just below, which exists precisely
    // because Core cannot scale plain `+1` by `sizeof(*p)` for an ORDINARY
    // pointer; an interior pointer needs no such scaling (`applyBinop`'s new
    // `Val.iref`+`Val.int` arm is already element-indexed, not byte-based), so
    // this is the ordinary, unboxed-identifier bump `incrStmt` already applies to
    // any other scalar local -- `p`'s own binding holds the value directly.
    if (rawLocalOrParamName(tgt).map(localName).exists(ptrIrefNames.contains)) {
      val nm = rawLocalOrParamName(tgt).map(localName).get
      val k = if (moduleScope || declaredGlobals.contains(nm)) "setGlobal" else "assign"
      ujson.Obj("k" -> k, "x" -> nm, "e" -> bump(ujson.Obj("k" -> "name", "v" -> nm)))
    }
    else if (isPointerType(staticTypeOf(tgt)) || isCString(tgt)) holeS("op:" + opName + ":pointer")
    else tgt match {
      // `003-box-address-taken-locals`: `x++`/`x--` on a boxed local, same rewrite as
      // a plain write (`assignTo`'s matching case) -- `x`'s own binding holds the ref,
      // not the value, so the bump has to go through the box's field.
      case i: Identifier if boxedLocals.contains(localName(i.name)) =>
        val nm = localName(i.name)
        ujson.Obj("k" -> "setField", "r" -> boxRef(nm), "f" -> "v", "v" -> bump(boxField(nm)))
      case i: Identifier =>
        val k = if (moduleScope || declaredGlobals.contains(i.name)) "setGlobal" else "assign"
        ujson.Obj("k" -> k, "x" -> localName(i.name),
                  "e" -> bump(ujson.Obj("k" -> "name", "v" -> localName(i.name))))
      case fa if asField(fa).isDefined =>
        val (r, f) = asField(fa).get
        if (!pureNode(r)) holeS("op:" + opName + ":impure-receiver")
        else ujson.Obj("k" -> "setField", "r" -> expr(r), "f" -> f,
                       "v" -> bump(ujson.Obj("k" -> "field", "a" -> expr(r), "f" -> f)))
      case ia if asIndex(ia).isDefined =>
        val (a, b) = asIndex(ia).get
        if (!(pureNode(a) && pureNode(b))) holeS("op:" + opName + ":impure-target")
        else ujson.Obj("k" -> "setIndex", "r" -> expr(a), "i" -> expr(b),
                       "v" -> bump(ujson.Obj("k" -> "index", "a" -> expr(a), "b" -> expr(b))))
      // `++*p` — the target is a dereference, which is the location model Core lacks.
      case _ => holeS("op:" + opName + ":unsupported-target")
    }
  }

  // ---- `006-reduce-remaining-holes`, Story 3: assignment/increment as a VALUE ----
  //
  // `valueOf`'s prelude-threading pattern (research.md §3), generalised into a proper
  // recursive helper reachable from every expression position, not just `return`/an
  // assignment's own RHS.

  /** Walk a `seqOf`-built right-nested `seq` chain to its innermost statement. */
  @tailrec def tailStmt(v: ujson.Obj): ujson.Obj =
    if (v.value.get("k").exists(_.str == "seq")) tailStmt(v("b").obj) else v

  /** If `write` (as built by `assignTo`/`incrStmt`) is, at its core, a hole statement
    * for any of THEIR OWN internal reasons (an impure receiver/target, a `char*`
    * pointer target, an unsupported target shape, ...), the label -- so callers can
    * surface it as an `Expr.hole` with the identical text, rather than trusting a
    * write that never actually happened. */
  def holeLabelOf(write: ujson.Obj): Option[String] = {
    val t = tailStmt(write)
    if (t.value.get("k").exists(_.str == "holeS")) Some(t("label").str) else None
  }

  /** The current-value READ expression for an assignment/increment target, mirroring
    * exactly what `assignTo`/`incrStmt` read internally: a boxed local's field, an
    * ordinary name, or a field/index read. `None` for a target shape neither
    * translates to a plain write at all (e.g. `*p`). */
  def targetReadExpr(lhs: AstNode): Option[ujson.Obj] = lhs match {
    case i: Identifier =>
      val nm = localName(i.name)
      Some(if (boxedLocals.contains(nm)) boxField(nm) else ujson.Obj("k" -> "name", "v" -> nm))
    case fa if asField(fa).isDefined =>
      val (r, f) = asField(fa).get
      Some(ujson.Obj("k" -> "field", "a" -> expr(r), "f" -> f))
    // `006-reduce-remaining-holes`, Story 5: consistent with `assignTo`'s/
    // `callExpr`'s own boxed-array read -- a plain `index` read would silently
    // mistranslate (Core's `Expr.index` does not accept a `Val.iref` receiver).
    case ia if asIndex(ia).isDefined &&
               rawLocalOrParamName(asIndex(ia).get._1).map(localName).exists(boxedArrays.contains) =>
      val (a, b) = asIndex(ia).get
      val arrName = rawLocalOrParamName(a).map(localName).get
      Some(ujson.Obj("k" -> "derefIref", "p" -> ujson.Obj("k" -> "irefIndex",
        "a" -> ujson.Obj("k" -> "name", "v" -> arrName), "i" -> expr(b))))
    case ia if asIndex(ia).isDefined =>
      val (a, b) = asIndex(ia).get
      Some(ujson.Obj("k" -> "index", "a" -> expr(a), "b" -> expr(b)))
    case _ => None
  }

  /** A name no source program can spell, so it can never collide with a real local —
    * used only to carry a postfix increment/decrement's PRE-bump value across the
    * bump statement (`Env.set` binds any name; no prior declaration is needed). */
  def freshExprVTemp(): String = { val n = "$exprV$" + exprVTempCounter; exprVTempCounter += 1; n }

  /** FR-005/FR-008: an assignment (plain or augmented) reached in expression
    * position. On a provably pure target, the write is `assignTo` verbatim and the
    * value is a fresh READ of the target after the write -- deliberately NOT a
    * second evaluation of `rhs` itself, even for a plain assignment: `rhs` may be
    * impure (a call), and `assignTo`'s own write already evaluates it exactly once
    * as part of computing what to store, so reusing that RHS expression node again
    * here would evaluate it a SECOND time -- the double-evaluation FR-008 exists to
    * rule out, just relocated to the wrong side of the assignment. Reading the
    * target back is sound because the target is provably pure (gated below): the
    * same location is written and re-read, once each. An impure target keeps a hole
    * under `assignTo`'s own aug-impure label for a field/index target, or today's
    * existing generic `op:assignment`/`op:<op>` label for any other shape `assignTo`
    * was never going to attempt in the first place. */
  def assignAsValue(lhs: AstNode, rhs: AstNode, aug: Option[String],
                     genericLabel: String): (List[ujson.Obj], ujson.Obj) = {
    def proceed(): (List[ujson.Obj], ujson.Obj) = {
      val write = assignTo(lhs, rhs, aug)
      holeLabelOf(write) match {
        case Some(label) => (Nil, hole(label))
        case None         => (List(write), targetReadExpr(lhs).getOrElse(hole(genericLabel)))
      }
    }
    lhs match {
      case _: Identifier               => proceed()
      case fa if asField(fa).isDefined =>
        if (pureNode(asField(fa).get._1)) proceed() else (Nil, hole("assign:aug-impure-receiver"))
      case ia if asIndex(ia).isDefined =>
        val (a, b) = asIndex(ia).get
        if (pureNode(a) && pureNode(b)) proceed() else (Nil, hole("assign:aug-impure-target"))
      case _ => (Nil, hole(genericLabel))
    }
  }

  /** FR-006/FR-007/FR-008: `++x`/`x++`/`--x`/`x--` reached in expression position.
    * Prefix yields the POST-bump value (a fresh read after `incrStmt`'s write, sound
    * under the same pure-target reasoning as the augmented-assignment case above);
    * postfix yields the PRE-bump value, captured into a fresh temporary immediately
    * before the bump runs, since Core's evaluator has no way to look "backwards"
    * past a statement it already ran. Reuses `incrStmt` verbatim for the bump/write
    * itself -- no new arithmetic. */
  def incrAsValue(tgt: AstNode, op: String, opName: String,
                  postfix: Boolean): (List[ujson.Obj], ujson.Obj) = {
    val genericLabel = "op:" + opName + ":value"
    def proceed(): (List[ujson.Obj], ujson.Obj) = {
      val write = incrStmt(tgt, op, opName)
      holeLabelOf(write) match {
        case Some(label) => (Nil, hole(label))
        case None =>
          val cur = targetReadExpr(tgt).getOrElse(hole(genericLabel))
          if (postfix) {
            val tmp = freshExprVTemp()
            (List(ujson.Obj("k" -> "assign", "x" -> tmp, "e" -> cur), write),
             ujson.Obj("k" -> "name", "v" -> tmp))
          } else (List(write), cur)
      }
    }
    tgt match {
      case _: Identifier               => proceed()
      case fa if asField(fa).isDefined =>
        if (pureNode(asField(fa).get._1)) proceed() else (Nil, hole("op:" + opName + ":impure-receiver"))
      case ia if asIndex(ia).isDefined =>
        val (a, b) = asIndex(ia).get
        if (pureNode(a) && pureNode(b)) proceed() else (Nil, hole("op:" + opName + ":impure-target"))
      case _ => (Nil, hole(genericLabel))
    }
  }

  /** `expr()`'s prelude-threading counterpart (research.md §3): for a node that may
    * itself carry an assignment/increment used as a VALUE, returns the statements
    * that must run first plus the resulting value expression, in source evaluation
    * order. Every node shape that cannot itself contain such a construct -- the
    * overwhelming majority -- is the unchanged base case, `(Nil, expr(n))`. */
  def exprV(n: AstNode): (List[ujson.Obj], ujson.Obj) = n match {
    case c: Call if c.methodFullName == "<operator>.assignment" =>
      kidsOf(c) match {
        case lhs :: rhs :: Nil => assignAsValue(lhs, rhs, None, "op:assignment")
        case _                 => (Nil, hole("assign:arity"))
      }
    case c: Call if augOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case lhs :: rhs :: Nil =>
          assignAsValue(lhs, rhs, Some(augOps(c.methodFullName)), "op:" + opLabel(c.methodFullName))
        case _ => (Nil, hole("assign:arity"))
      }
    case c: Call if incrOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case tgt :: Nil =>
          val opName = c.methodFullName.stripPrefix("<operator>.")
          incrAsValue(tgt, incrOps(c.methodFullName), opName, postfix = opName.startsWith("post"))
        case _ => (Nil, hole("op:" + c.methodFullName.stripPrefix("<operator>.") + ":arity"))
      }
    // Compound-expression pass-through (research.md §3, point 2): thread and
    // concatenate sub-preludes left-to-right, matching source evaluation order.
    case c: Call if c.methodFullName == "<operator>.arithmeticShiftRight" && kidsOf(c).size == 2 =>
      val List(a, b) = kidsOf(c)
      shiftRightOp(a) match {
        case Some(op) =>
          val (pa, ae) = exprV(a); val (pb, be) = exprV(b)
          (pa ++ pb, ujson.Obj("k" -> "binop", "op" -> op, "a" -> ae, "b" -> be))
        case None => (Nil, hole("op:shiftRight:unknown-signedness"))
      }
    case c: Call if binops.contains(c.methodFullName) && kidsOf(c).size == 2 &&
                    !(cLikeFile && kidsOf(c).exists(isCString) && cStringUnsafe.contains(c.methodFullName)) =>
      val List(a, b) = kidsOf(c)
      val (pa, ae) = exprV(a); val (pb, be) = exprV(b)
      (pa ++ pb, ujson.Obj("k" -> "binop", "op" -> binops(c.methodFullName), "a" -> ae, "b" -> be))
    case c: Call if unops.contains(c.methodFullName) && kidsOf(c).size == 1 =>
      val (pa, ae) = exprV(kidsOf(c).head)
      (pa, ujson.Obj("k" -> "unop", "op" -> unops(c.methodFullName), "a" -> ae))
    // `006-reduce-remaining-holes`, Story 5: `a[i]`, `a` a recognized boxed array
    // -- mirrors `callExpr`'s own matching case exactly (this file's `exprV`
    // never routes an `indexOps` call through `callExpr`, so without this the
    // Story 5 rewrite there would silently never fire for an index reached via
    // `exprV` -- an `if`/`while`/`do`/`for` condition, a `return`/assignment-RHS
    // position, or any compound expression -- which is most real call sites).
    case c: Call if indexOps.contains(c.methodFullName) && kidsOf(c).size == 2 &&
                    rawLocalOrParamName(kidsOf(c)(0)).map(localName).exists(boxedArrays.contains) =>
      val List(a, b) = kidsOf(c)
      val arrName = rawLocalOrParamName(a).map(localName).get
      val (pb, be) = exprV(b)
      (pb, ujson.Obj("k" -> "derefIref", "p" -> ujson.Obj("k" -> "irefIndex",
        "a" -> ujson.Obj("k" -> "name", "v" -> arrName), "i" -> be)))
    case c: Call if indexOps.contains(c.methodFullName) && kidsOf(c).size == 2 =>
      val List(a, b) = kidsOf(c)
      val (pa, ae) = exprV(a); val (pb, be) = exprV(b)
      (pa ++ pb, ujson.Obj("k" -> "index", "a" -> ae, "b" -> be))
    case c: Call if fieldOps.contains(c.methodFullName) && resolvedRef(c).isEmpty &&
                    asField(c).isDefined =>
      val (r, f) = asField(c).get
      val (pr, re) = exprV(r)
      (pr, ujson.Obj("k" -> "field", "a" -> re, "f" -> f))
    // An ordinary named call's positional arguments (research.md §3, point 2,
    // "function-call arguments"). Delegates the actual call classification to
    // `expr`/`callExpr` unchanged (ctor/mcall/`<fakeNew>`/class-body and every other
    // special form are simply not touched here, and fall to the base case below) --
    // only the positional-argument VALUES are threaded through `exprV`, and only when
    // at least one of them actually has a prelude to hoist; otherwise this returns
    // `expr(c)` verbatim; byte-identical to today.
    case c: Call if !c.methodFullName.startsWith("<operator>") && c.methodFullName != "<unknownFullName>" =>
      val baseline = expr(c)
      val posArgs = kidsOf(c).filter(k => aidx(k) >= 1 && !isKeywordArg(k))
      val ok = baseline.value.get("k").exists(_.str == "call") &&
               baseline.value.get("args").flatMap(_.arrOpt).exists(_.length >= posArgs.length)
      if (!ok) (Nil, baseline)
      else {
        val argsArr = baseline("args").arr.toList
        val recur = posArgs.map {
          case sc: Call if sc.methodFullName == "<operator>.starredUnpack" =>
            (List.empty[ujson.Obj], argExpr(sc))
          case a => val (pa, ae) = exprV(a); (pa, ae: ujson.Value)
        }
        val prelude = recur.flatMap(_._1)
        if (prelude.isEmpty) (Nil, baseline)
        else (prelude, ujson.Obj("k" -> "call", "f" -> baseline("f"),
                                 "args" -> ujson.Arr.from(recur.map(_._2) ++ argsArr.drop(posArgs.length))))
      }
    case other => (Nil, expr(other))
  }

  /** Translate a statement list, merging the two-statement C++ stack-construction shape
    * (`x = <operator>.alloc` followed by `Cls.Cls(args)`) into one `Expr.alloc`. See
    * `ctorAlloc` for the expression-position form of the same pattern. */
  @tailrec
  def stmts(ks: List[AstNode], acc: List[ujson.Obj] = Nil): List[ujson.Obj] = ks match {
    case (asg: Call) :: (ctor: Call) :: rest if asg.methodFullName == "<operator>.assignment" =>
      val merged =
        for {
          tr  <- kidsOf(asg) match {
                   case (i: Identifier) :: r :: Nil => Some((i, r))
                   case _                           => None
                 }
          if isOp(tr._2, "<operator>.alloc") && kidsOf(tr._2).isEmpty
          cls <- ctorClassOf(ctor)
        } yield {
          val k = if (moduleScope || declaredGlobals.contains(tr._1.name)) "setGlobal"
                  else "assign"
          ujson.Obj("k" -> k, "x" -> localName(tr._1.name),
                    "e" -> ujson.Obj("k" -> "alloc", "cls" -> cls,
                                     "args" -> exprs(kidsOf(ctor).filter(aidx(_) >= 1))))
        }
      merged match {
        case Some(m) => stmts(rest, m :: acc)
        case None    => stmts(ctor :: rest, stmt(asg) :: acc)
      }
    case k :: rest => stmts(rest, stmt(k) :: acc)
    case Nil       => acc.reverse
  }

  /** `007-reduce-remaining-holes-2` US4: lower a `switch` statement to a FLAT sequence
    * of `fell`/`matched` flag updates (one pair of statements per segment, in source
    * order) wrapped in `Stmt.breakBlock` (research.md §4: the one existing construct
    * missing the property `switch` needs -- absorbing a `break` without also absorbing
    * a `continue`, unlike `Stmt.loop`/`Stmt.forIn`).
    *
    * REJECTED design, and why: an earlier version of this function built one `Stmt.ifte`
    * per segment whose `t`/`e` branches threaded into a bottom-up `rests(i) =
    * seq(body_i, rests(i+1))` chain shared BOTH as segment i's own dispatch target AND
    * embedded inside every EARLIER segment's own `rests`. Sharing a `ujson.Obj`
    * *reference* is free in memory, but JSON has no notion of a shared reference: a node
    * reachable from `k` different paths in the tree is serialized `k` times. For `n`
    * segments that is O(n^2) total output size -- confirmed, not assumed, via an
    * out-of-memory crash on SQLite's own `sqlite3VdbeExec` (`src/vdbe.c`, ~190-case
    * opcode dispatch) that reproduced identically even at 4x the default JVM heap,
    * proving it was this quadratic blowup and not merely "a large function needs more
    * memory" (`006-reduce-remaining-holes`'s own `maxHeartbeats` precedent). The flat
    * encoding below has each segment's body appear exactly ONCE in the output, full stop.
    *
    * The encoding: `fell` starts false and is set true the first time either (a) the
    * controlling value matches one of THIS segment's case values, or (b) this is the
    * `default` segment and `matched` (computed ONCE, up front, as the OR of every real
    * case's values, regardless of `default`'s own lexical position) is false. Once
    * `fell` is true, every subsequent segment's body runs unconditionally -- exactly
    * `switch`'s real fallthrough semantics -- until a `break` (`Stmt.brk`) is hit, which
    * propagates out of the flat `Stmt.seq` chain via its ordinary short-circuit-on-
    * non-normal-result behavior (unchanged, existing `execStmt` semantics) straight to
    * the wrapping `breakBlock`, ending the whole dispatch there.
    *
    * The controlling expression is evaluated at most ONCE: `pureExpr` decides whether
    * it is safe to duplicate across every comparison, or must be hoisted into a fresh
    * temp first (the same discipline `006-reduce-remaining-holes` Story 3 established
    * for assignment-as-value's own double-evaluation risk).
    *
    * Empirically confirmed against this Joern version (not assumed): a `switch`'s body
    * `Block` interleaves, per label, a `JumpTarget` (`parserTypeName` `CASTCaseStatement`
    * for `case`, `CASTDefaultStatement` for `default`) immediately followed -- for
    * `case` only -- by a `Literal` sibling holding the label's value; ordinary
    * statements appear between labels exactly as `stmts` already expects. */
  def switchStmt(cond: AstNode, bodyNode: AstNode): ujson.Obj = {
    case class Segment(caseValues: List[AstNode], isDefault: Boolean, body: List[AstNode])

    def consumeLabels(ks: List[AstNode], caseVals: List[AstNode],
                       isDefault: Boolean): (List[AstNode], List[AstNode], Boolean) = ks match {
      case (j: JumpTarget) :: rest if j.parserTypeName == "CASTDefaultStatement" =>
        consumeLabels(rest, caseVals, true)
      case (j: JumpTarget) :: (v: AstNode) :: rest if j.parserTypeName == "CASTCaseStatement" =>
        consumeLabels(rest, caseVals :+ v, isDefault)
      // Defensive only: no other JumpTarget shape is expected inside a SWITCH body per
      // this file's own empirical inspection; consumed with no value rather than looping.
      case (_: JumpTarget) :: rest => consumeLabels(rest, caseVals, isDefault)
      case _ => (ks, caseVals, isDefault)
    }

    def segmentsOf(ks: List[AstNode]): List[Segment] = ks match {
      case Nil => Nil
      case _ =>
        val (afterLabels, caseVals, isDefault) = consumeLabels(ks, Nil, false)
        val (body, rest) = afterLabels.span { case _: JumpTarget => false; case _ => true }
        Segment(caseVals, isDefault, body) :: segmentsOf(rest)
    }

    val bodyKids = kidsOf(bodyNode)
    val segments = segmentsOf(bodyKids)

    // The controlling expression, evaluated at most once (see doc comment above).
    val (condPrelude, condVal) =
      if (pureExpr(cond)) (Nil, expr(cond))
      else {
        val tmp = freshExprVTemp()
        (List(ujson.Obj("k" -> "assign", "x" -> tmp, "e" -> expr(cond))),
         ujson.Obj("k" -> "name", "v" -> tmp))
      }

    def eqOr(vals: List[AstNode]): ujson.Obj =
      vals.map(v => ujson.Obj("k" -> "binop", "op" -> "==", "a" -> condVal, "b" -> expr(v)))
          .reduceRight((a, b) => ujson.Obj("k" -> "binop", "op" -> "||", "a" -> a, "b" -> b))

    val fellVar = freshExprVTemp()
    val matchedVar = freshExprVTemp()
    def name(v: String): ujson.Obj = ujson.Obj("k" -> "name", "v" -> v)
    def boolLit(b: Boolean): ujson.Obj = ujson.Obj("k" -> "bool", "v" -> b)
    def assignBool(x: String, b: Boolean): ujson.Obj = ujson.Obj("k" -> "assign", "x" -> x, "e" -> boolLit(b))
    def not(e: ujson.Obj): ujson.Obj = ujson.Obj("k" -> "unop", "op" -> "!", "a" -> e)
    def and(a: ujson.Obj, b: ujson.Obj): ujson.Obj = ujson.Obj("k" -> "binop", "op" -> "&&", "a" -> a, "b" -> b)

    val allCaseVals = segments.flatMap(s => if (s.isDefault) Nil else s.caseValues)
    val matchedInit = if (allCaseVals.isEmpty) boolLit(false) else eqOr(allCaseVals)

    val init = List(assignBool(fellVar, false), ujson.Obj("k" -> "assign", "x" -> matchedVar, "e" -> matchedInit))

    val segStmts = segments.map { seg =>
      val ownGuard =
        if (seg.isDefault) not(name(matchedVar))
        else if (seg.caseValues.isEmpty) boolLit(false)
        else eqOr(seg.caseValues)
      val setFell = ujson.Obj("k" -> "ifte", "c" -> and(not(name(fellVar)), ownGuard),
                               "t" -> assignBool(fellVar, true), "e" -> skip)
      // `outsideLoopScope`, matching WHILE/DO/FOR's own precedent for their nested
      // bodies: a case body is a fresh scope for the goto-as-break heuristic, defense
      // in depth (the function-wide precondition that heuristic already checks --
      // `insideLoop` already treats SWITCH as a boundary -- makes this
      // belt-and-suspenders rather than load-bearing, but costs nothing).
      val runBody = ujson.Obj("k" -> "ifte", "c" -> name(fellVar),
                               "t" -> outsideLoopScope(seqOf(stmts(seg.body))), "e" -> skip)
      ujson.Obj("k" -> "seq", "a" -> setFell, "b" -> runBody)
    }

    val breakBlockStmt = ujson.Obj("k" -> "breakBlock", "body" -> seqOf(segStmts))
    seqOf(condPrelude ++ init ++ List(breakBlockStmt))
  }

  def stmt(n: AstNode): ujson.Obj = n match {
    case b: Block =>
      val kids = kidsOf(b)
      // An empty `kidsOf` is ambiguous by itself: it is the correct shape for a real
      // no-op body (`{}`, or `{ /* NO-OP */ }`), but it is ALSO what the C frontend
      // produces when it gives up parsing a body it could not fully resolve --
      // silently, with the raw source text still sitting on `.code`. Telling those
      // apart by whether anything survives stripping braces and comments is the
      // difference between "nothing to translate" and "something was dropped
      // on the floor": on the SQLite CPG, 15%+ of core-file functions hit the
      // latter, each exporting as a hole-free `skip` that in fact translated
      // nothing of the function's real body.
      if (kids.isEmpty && stripBlockCode(b.code).nonEmpty) holeS("stmt:empty-ast-children")
      else forPattern(kids).getOrElse(seqOf(stmts(kids)))
    case l: Local => skip   // declarations carry no behaviour here
    case td: TypeDecl => skip   // a struct/union/typedef/class decl carries no behaviour either
    case r: Return =>
      kidsOf(r).headOption match {
        case Some(e) =>
          val (prelude, ev) = valueOf(e)
          seqOf(prelude :+ ujson.Obj("k" -> "ret", "e" -> ev))
        case None => ujson.Obj("k" -> "ret", "e" -> ujson.Obj("k" -> "unit"))
      }
    case c: Call if c.methodFullName == "<operator>.assignment" =>
      kidsOf(c) match {
        case lhs :: rhs :: Nil => assignTo(lhs, rhs, None)
        case _                 => holeS("assign:arity")
      }
    case c: Call if augOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case lhs :: rhs :: Nil => assignTo(lhs, rhs, Some(augOps(c.methodFullName)))
        case _                 => holeS("assign:arity")
      }
    // `x >>= n`. Same two-operators-one-token problem as `>>`, and the target's type is
    // what decides; an unrecovered type is a hole rather than a guessed sign.
    case c: Call if c.methodFullName == "<operator>.assignmentArithmeticShiftRight" =>
      kidsOf(c) match {
        case lhs :: rhs :: Nil =>
          shiftRightOp(lhs) match {
            case Some(op) => assignTo(lhs, rhs, Some(op))
            case None     => holeS("op:shiftRight:unknown-signedness")
          }
        case _ => holeS("assign:arity")
      }
    case c: Call if incrOps.contains(c.methodFullName) =>
      kidsOf(c) match {
        case tgt :: Nil =>
          incrStmt(tgt, incrOps(c.methodFullName),
                   c.methodFullName.stripPrefix("<operator>."))
        case _ => holeS("op:" + c.methodFullName.stripPrefix("<operator>.") + ":arity")
      }
    case c: Call if c.methodFullName == "<operator>.pass" => skip
    case c: Call if c.methodFullName == "<operator>.raise" =>
      // Children: the exception, plus an optional `from <e>` cause we do not model.
      kidsOf(c).headOption match {
        case Some(e) => ujson.Obj("k" -> "raise", "e" -> expr(e))
        // A bare `raise` re-raises the exception in flight; Core has no such notion.
        case None    => holeS("op:raise-bare")
      }
    case c: Call if c.methodFullName == "<operator>.delete" =>
      kidsOf(c) match {
        case (i: Identifier) :: Nil => ujson.Obj("k" -> "del", "x" -> i.name)
        // `del d[k]` / `del o.f` remove a binding from a container or object; Core's
        // `del` only unbinds a variable, so translating them would be a lie.
        case (x: AstNode) :: Nil if isOp(x, "<operator>.indexAccess") => holeS("op:delete-index")
        case (x: AstNode) :: Nil if asField(x).isDefined => holeS("op:delete-field")
        case (x: Call) :: Nil if x.methodFullName.startsWith("<operator>") =>
          holeS("op:delete-" + x.methodFullName.stripPrefix("<operator>."))
        case _ => holeS("op:delete-shape")
      }
    // A synchronisation primitive in statement position is `Stmt.skip`: Core is
    // sequential, so an uncontended acquire/release changes nothing the program can
    // read. See `syncPrimitives` for what is given up (nothing Core could observe)
    // and why the trylock family is excluded (it returns a value).
    case c: Call if syncPrimitives.contains(c.methodFullName.split("\\.").last) =>
      syncElided += 1; skip
    case c: Call => ujson.Obj("k" -> "exprS", "e" -> expr(c))
    case cs: ControlStructure =>
      val kids = kidsOf(cs)
      cs.controlStructureType match {
        // `006-reduce-remaining-holes`: an `if` condition is evaluated exactly once,
        // so splicing `exprV`'s prelude ahead of the `ifte` (mirroring how `Return`
        // already splices `valueOf`'s) is exactly as sound here as there.
        case "IF" if kids.size >= 2 =>
          val (prelude, condVal) = exprV(kids(0))
          seqOf(prelude :+ ujson.Obj("k" -> "ifte", "c" -> condVal, "t" -> stmt(kids(1)),
                                     "e" -> (if (kids.size > 2) stmt(kids(2)) else skip)))
        // A loop's own condition is instead evaluated ONCE PER ITERATION, so the same
        // "splice the prelude once, ahead of the loop" trick would be wrong: an
        // assignment-as-value inside a `while`/`do`/`for` condition would fire only on
        // the very first check, then read a permanently stale value on every
        // subsequent one -- a silent wrong answer, not merely a missed improvement.
        // Fixing that needs the condition's prelude re-run before every re-check
        // (and before every `continue`, matching `pushStep`'s own precedent for a
        // `for`-loop's step) -- a real, separate increment this plan does not
        // attempt, so a loop condition keeps the plain `expr(cond)` it has today.
        case "WHILE" if kids.size >= 2 =>
          // A `while` whose condition is the frontend's synthetic iterator probe only
          // makes sense inside the `for` shape above; on its own it is not a condition.
          if (kids(0).isInstanceOf[Unknown]) holeS("control:WHILE-iterator")
          else ujson.Obj("k" -> "loop", "c" -> expr(kids(0)),
                         "body" -> outsideLoopScope(stmt(kids(1))))

        // `do B while (C)` is NOT `while (C) B`, and translating it as one was a silent
        // mistranslation: a do-while runs its body at least once, so with `C` initially
        // false the two disagree on the first iteration. Checked against `cc -O0`:
        // `do { n = n + 1; } while (0)` returns 1, `while (0) { n = n + 1; }` returns 0.
        // The translation type-checked and looked right, which is how it survived.
        //
        // The faithful shape is `while (true) { B; if (C) skip else break }`. `break`
        // needs nothing: C's `break` leaves the loop, and so does this one. `continue`
        // does: in a do-while it jumps to the CONDITION TEST, whereas here it would skip
        // the test and spin forever — so each `continue` belonging to this loop becomes
        // `if (C) continue else break`, which is exactly what the standard says. Nested
        // loops keep their own `continue` (`pushDoTest` stops at `loop`/`forIn`), and `C`
        // may be evaluated more than once per source iteration only on paths where the
        // original would have evaluated it too.
        case "DO" if kids.size >= 2 =>
          if (kids(0).isInstanceOf[Unknown]) holeS("control:WHILE-iterator")
          else {
            val cond = expr(kids(0))
            val test = ujson.Obj("k" -> "ifte", "c" -> cond, "t" -> skip,
                                 "e" -> ujson.Obj("k" -> "brk"))
            val body = pushDoTest(outsideLoopScope(stmt(kids(1))), cond)
            ujson.Obj("k" -> "loop", "c" -> ujson.Obj("k" -> "bool", "v" -> true),
                      "body" -> ujson.Obj("k" -> "seq", "a" -> body, "b" -> test))
          }
        case "FOR"      => forStmt(cs)
        // `007-reduce-remaining-holes-2` US4: see `switchStmt`'s own doc comment for the
        // lowering and why `Stmt.breakBlock` is required, not merely convenient.
        case "SWITCH" if kids.size >= 2 && !goFile => switchStmt(kids(0), kids(1))
        // `goto L` where `L` has been proved to be the single forward exit label of this
        // function, and this `goto` is not inside any loop or switch: see `methodBody`.
        // Everything else keeps the `control:GOTO` hole.
        case "GOTO" if gotoAsBreak.isDefined &&
                       kids.map(_.code.trim) == List(gotoAsBreak.get) =>
          ujson.Obj("k" -> "brk")
        case "BREAK"    => ujson.Obj("k" -> "brk")
        case "CONTINUE" => ujson.Obj("k" -> "cont")
        case "ELSE" | "CATCH" | "FINALLY" => seqOf(kids.map(stmt))
        case "TRY"      => tryStmt(kids)
        case t          => holeS("control:" + t)
      }
    case i: Identifier => ujson.Obj("k" -> "exprS", "e" -> expr(i))
    case l: Literal    => ujson.Obj("k" -> "exprS", "e" -> expr(l))
    case m: MethodRef  => skip   // a nested `def`; its body is exported as its own function
    case t: TypeRef    => skip   // a nested `class`, likewise
    case j: JumpTarget => skip
    // `global x` / `nonlocal x` arrive as UNKNOWN nodes carrying their source text; the
    // Python frontend models neither.
    //
    // `global` *is* representable: it rebinds `x` to the module-level frame, and
    // `declGlobal` records that. (The assignments themselves are independently rewritten
    // to `setGlobal` in `assignTo`, so the translation is correct even if `declGlobal`
    // carries no weight in the semantics.)
    //
    // `nonlocal` is **not**. `Expr.closure` captures the enclosing scope *by value*, so a
    // write can never be observed by the frame that owns the variable. Emitting an
    // `assign` here would produce a program that runs and quietly computes the wrong
    // answer, which is the one outcome worse than a hole.
    case u: Unknown if u.code.trim.startsWith("global ") =>
      seqOf(globalDeclNames(u).map(x => ujson.Obj("k" -> "declGlobal", "x" -> x)))
    case u: Unknown if u.code.trim.startsWith("nonlocal ") =>
      holeS("scope:nonlocal-write")
    // The label carries the frontend's PARSER NODE TYPE, not the source text.
    //
    // It used to be the first word of the code, which made the label space unbounded:
    // V8 alone produced `stmt:UNKNOWN:)`, `stmt:UNKNOWN:}`, `stmt:UNKNOWN:V8_WEAK;` and
    // `stmt:UNKNOWN:requires(!internal::can_use_memcpy_v<InputIt,`. A taxonomy whose
    // cardinality grows with the corpus cannot be counted, compared across runs, or acted
    // on -- the ledger groups by label, so every new source fragment became its own
    // "cause". The parser type is a closed set and says the same thing about the remedy:
    // `CASTProblemDeclaration` means the C preprocessor was not run.
    case u: Unknown if isKernelMeta(u.code) => metaElided += 1; skip
    case u: Unknown    =>
      val kind = Option(u.parserTypeName).map(_.trim).filter(_.nonEmpty).getOrElse("node")
      holeS("stmt:UNKNOWN:" + kind)
    // A `namespace v8 { ... }` is a *naming* construct: it has no runtime effect at all,
    // and the functions and classes inside it are exported as their own entries with
    // their qualified names already on them. Nothing is dropped by skipping it — the
    // block itself never had behaviour to drop. This is the same call `case m: MethodRef`
    // and `case t: TypeRef` already make one line below.
    case nb: NamespaceBlock => skip
    case other         => holeS("stmt:" + other.label)
  }

  /** try / except / else / finally.
    *
    * Note what the CPG does *not* carry: pysrc2cpg drops the exception *type* of each
    * handler entirely (a CATCH has only its body). So a single handler is translated as
    * catch-all — the only reading available — and anything where the choice of handler
    * would be observable stays a hole. */
  def tryStmt(kids: List[AstNode]): ujson.Obj = {
    def of(t: String) = kids.collect {
      case c: ControlStructure if c.controlStructureType == t => c
    }
    val catches   = of("CATCH")
    val finallys  = of("FINALLY")
    val elses     = of("ELSE")
    val bodyNodes = kids.filterNot(_.isInstanceOf[ControlStructure])
    val body      = seqOf(bodyNodes.map(stmt))
    if (bodyNodes.isEmpty) holeS("control:TRY-shape")
    // Which handler runs depends on the exception type, which the CPG discarded.
    else if (catches.size > 1) holeS("control:TRY-multiCatch")
    else {
      // `try: B except: H else: E finally: F` is three independent layers, and now that
      // `Stmt.tryFinally` exists each one has a constructor, so they compose:
      //
      //   inner = B                                    (no handler)
      //         | tryCatch(B, e, H)                     (handler, no else)
      //         | ok = true; tryCatch(B, e, {ok = false; H}); if ok then E
      //   whole = inner | tryFinally(inner, F)
      //
      // The `else` encoding is the only one that needs an explanation. `E` must run only
      // when `B` raised nothing, and `E`'s own exceptions must not reach `H`. The flag is
      // not an invention: it is exactly the "did the body complete normally" bit the
      // construct is about. `E` sits outside the `tryCatch`, so its exceptions propagate;
      // every other way out of `B` — return, break, continue, or a handler that re-raises
      // — leaves before the `if`, which is Python's rule that `else` is skipped whenever
      // the body did not complete normally. The flag is numbered per `try`, because a
      // nested `try/else` completing normally would otherwise re-arm the enclosing one's.
      //
      // `finally` is outermost, which is what makes it run on the `return`/`break`/
      // `continue` paths as well: `Stmt.tryFinally` intercepts every `Ctl`, re-raising the
      // body's outcome after the finalizer unless the finalizer itself leaves abnormally.
      // The previous encoding — `tryCatch(B, e, F; raise e); F` — could not, because `ret`
      // passes straight through a `tryCatch` and would have skipped the trailing copy;
      // that is the whole of what `control:TRY-finally-escaping` was recording.
      val inner =
        if (catches.isEmpty && elses.isEmpty) body
        else if (catches.size == 1 && elses.isEmpty)
          ujson.Obj("k" -> "tryCatch", "body" -> body, "x" -> "__exc",
                    "handler" -> stmt(catches.head))
        else if (catches.size == 1) {
          elseFlagSeq += 1
          val flag = "__else_ok" + elseFlagSeq
          seqOf(List(
            ujson.Obj("k" -> "assign", "x" -> flag,
                      "e" -> ujson.Obj("k" -> "bool", "v" -> true)),
            ujson.Obj("k" -> "tryCatch", "body" -> body, "x" -> "__exc",
                      "handler" -> ujson.Obj("k" -> "seq",
                        "a" -> ujson.Obj("k" -> "assign", "x" -> flag,
                                         "e" -> ujson.Obj("k" -> "bool", "v" -> false)),
                        "b" -> stmt(catches.head))),
            ujson.Obj("k" -> "ifte", "c" -> ujson.Obj("k" -> "name", "v" -> flag),
                      "t" -> seqOf(elses.map(stmt)), "e" -> skip)))
        }
        // `else` with no `except` is not legal Python; if the CPG says so, say so.
        else holeS("control:TRY-else-without-except")
      if (finallys.isEmpty) inner
      else if (finallys.size == 1)
        ujson.Obj("k" -> "tryFinally", "body" -> inner, "fin" -> stmt(finallys.head))
      else holeS("control:TRY-multiFinally")
    }
  }

  // ---- drive ----------------------------------------------------------------
  // Joern synthesises `<metaClassAdapter>` wrappers that duplicate real methods, plus
  // `<body>` class-body pseudo-methods. Counting them inflates every coverage number, so
  // they are excluded rather than quietly padding the verifiable core. The file-level
  // `<module>`/`<global>` pseudo-methods are excluded from *this* list too, and re-added
  // below as initializers, so they never inflate the function count either.
  val cLikeExts = List(".c", ".h", ".cpp", ".cc", ".hpp", ".java", ".js", ".ts", ".kt", ".go")
  val cppExts   = List(".c", ".h", ".cpp", ".cc", ".hpp")

  /** The name a method is exported under.
    *
    * For C++ this rewrites a **constructor** — whose `fullName` repeats the class, as in
    * `v8.internal.SimpleStringBuilder.SimpleStringBuilder:void(char*,int)` — to
    * `v8.internal.SimpleStringBuilder.__init__`. That is not cosmetic: `evalExpr`'s
    * `.alloc` case runs `ctx.resolveMethod cls "__init__"` and nothing else, so without
    * the rewrite every `Expr.alloc` produced by `ctorAlloc` would allocate an object with
    * no fields, and every subsequent `p->f` would read `unit`. Core's constructor
    * convention is Python's spelling of a universal idea; this is the C++ spelling of the
    * same one, and naming them alike is what makes the two frontends share a semantics.
    *
    * Java's `<init>` and Kotlin's are *not* caught by this rule (their last two segments
    * differ), which is deliberate — they have their own conventions and no evidence here. */
  def exportName(m: Method): String = {
    val fn = mangledFullName(m.fullName)
    if (!cppFile) fn
    else {
      val base = fn.takeWhile(_ != ':')
      val segs = base.split('.').filter(_.nonEmpty).toList
      segs.reverse match {
        case n :: p :: _ if n == p && n != "ANY" => segs.dropRight(1).mkString(".") + ".__init__"
        case _                                   => fn
      }
    }
  }

  /** A method body, translating the kernel's `goto out;` idiom when — and only when — it
    * is a *reducible forward jump to a tail label*, which is structured control flow
    * wearing an unstructured spelling.
    *
    *     A;  if (e) goto out;  B;  out:  C;  return r;
    *
    * is exactly
    *
    *     while (true) { A; if (e) break; B; break }   C;  return r;
    *
    * The `while (true) { ...; break }` runs its body once; a jump inside it is a `break`,
    * which leaves for `C`. Nothing is invented: `Stmt.loop` plus `Stmt.brk` already mean
    * "a block you can jump out of", and that is all this jump is. `return` passes
    * straight through a loop, so the early-return paths are unaffected.
    *
    * **Every one of these conditions is load-bearing**, and each one, dropped, turns the
    * translation from correct into silently wrong rather than into a hole:
    *
    *  - Exactly **one** label in the function, and every jump targets it. Two labels need
    *    two nested wrappers and a choice about which; jumps between them can be
    *    irreducible, and an irreducible flow graph is not structured control flow at all.
    *  - The label is a **direct child of the function body**, so "the rest of the
    *    function" is a suffix of one statement list rather than a jump into the middle of
    *    a nested block.
    *  - Every jump is **before** the label in that list — a *forward* jump. A backward one
    *    is a loop, and this encoding would turn it into a straight line.
    *  - No jump is inside a `for`/`while`/`do`/`switch`. This is the one that would bite:
    *    `break` inside a loop leaves *that* loop, so the jump would land in the wrong
    *    place and the program would still type-check. (`switch` is a hole today, so its
    *    body is not translated at all — but the check does not rely on that.)
    *
    * Measured on `crypto/`: 234 functions contain a jump of this kind, 161 have a single
    * label, 105 of those are forward jumps to a tail label, and 82 also clear the loop
    * condition. The other 152 keep `control:GOTO`, which is the honest answer for them. */
  def methodBody(m: Method): ujson.Obj = {
    val body   = m.body
    val ks     = kidsOf(body)
    val labels = body.ast.collect {
      case j: JumpTarget if j.parserTypeName == "CASTLabelStatement" => j
    }.l
    val jumps  = body.ast.collect {
      case c: ControlStructure if c.controlStructureType == "GOTO" => c
    }.l
    val idx = ks.indexWhere {
      case j: JumpTarget => j.parserTypeName == "CASTLabelStatement"
      case _             => false
    }
    def ancestorsTo(n: AstNode): List[AstNode] = {
      var cur = n; var acc = List.empty[AstNode]; var guard = 0
      while (guard < 500 && !(cur eq body) && parentOf(cur).isDefined) {
        guard += 1; cur = parentOf(cur).get; acc = cur :: acc
      }
      acc
    }
    def insideLoop(n: AstNode): Boolean = ancestorsTo(n).exists {
      case cs: ControlStructure =>
        Set("FOR", "WHILE", "DO", "SWITCH").contains(cs.controlStructureType)
      case _ => false
    }
    def topIndex(n: AstNode): Int = {
      var cur = n; var guard = 0
      while (guard < 500 && parentOf(cur).isDefined && !(parentOf(cur).get eq body)) {
        guard += 1; cur = parentOf(cur).get
      }
      ks.indexWhere(_ eq cur)
    }
    val targets = jumps.flatMap(g => kidsOf(g).map(_.code.trim)).distinct
    val ok =
      jumps.nonEmpty && labels.size == 1 && idx >= 0 && (labels.head eq ks(idx)) &&
      targets == List(labels.head.name) &&
      jumps.forall(g => !insideLoop(g) && { val i = topIndex(g); i >= 0 && i < idx })
    if (!ok) stmt(body)
    else {
      val saved = gotoAsBreak
      gotoAsBreak = Some(labels.head.name)
      val prefix = seqOf(stmts(ks.take(idx)))
      gotoAsBreak = saved
      val suffix = seqOf(stmts(ks.drop(idx + 1)))
      ujson.Obj("k" -> "seq",
        "a" -> ujson.Obj("k" -> "loop", "c" -> ujson.Obj("k" -> "bool", "v" -> true),
                         "body" -> ujson.Obj("k" -> "seq", "a" -> prefix,
                                             "b" -> ujson.Obj("k" -> "brk"))),
        "b" -> suffix)
    }
  }

  /** Translate one method with the right scope/dialect state installed. `isModule` marks
    * the file-level pseudo-method, where every identifier assignment is a global write. */
  def emit(m: Method, isModule: Boolean): ujson.Obj = {
    moduleScope  = isModule
    currentClass = enclosingClassOf(m.fullName)
    cLikeFile    = cLikeExts.exists(e => m.filename.toLowerCase.endsWith(e))
    cppFile      = cppExts.exists(e => m.filename.toLowerCase.endsWith(e))
    def fieldReceiverNames(op: String): Set[String] =
      m.body.ast.isCall.filter(_.methodFullName == op).l.flatMap { c =>
        val ks = kidsOf(c)
        if (ks.size < 2) None else Some(ks(ks.size - 2))
      }.collect { case i: Identifier => i.name }.toSet
    valueReceivers = fieldReceiverNames("<operator>.fieldAccess")
    ptrReceivers   = fieldReceiverNames("<operator>.indirectFieldAccess")
    localTypes   = (m.local.l.map(l => l.name -> l.typeFullName) ++
                    m.parameter.l.map(pp => pp.name -> pp.typeFullName))
                   .filter(_._2 != "ANY").toMap
    currentFile  = m.filename
    declaredGlobals =
      m.body.ast.collect { case u: Unknown if u.code.trim.startsWith("global ") => u }
        .flatMap(globalDeclNames).toSet
    // `t = r.attr` for a plain identifier receiver, collected once per method. A name
    // bound more than once is dropped: which binding a later call sees would be a
    // flow-sensitive question, and this analysis is not.
    boundMethods = m.body.ast.isCall
      .filter(_.methodFullName == "<operator>.assignment").l
      .flatMap { a =>
        kidsOf(a) match {
          case (t: Identifier) :: rhs :: Nil =>
            asField(rhs).collect { case (r: Identifier, f) => t.name -> (r.name, f) }
          case _ => None
        }
      }
      .groupBy(_._1).collect { case (k, List(one)) => k -> one._2 }.toMap
    attrsOf = m.body.ast.isCall
      .filter(c => fieldOps.contains(c.methodFullName)).l
      .flatMap(fa => asField(fa).collect { case (r: Identifier, f) => r.name -> f })
      .groupBy(_._1).map { case (k, vs) => k -> vs.map(_._2).toSet }
    // `003-box-address-taken-locals`: every name whose address is taken anywhere in
    // this method, restricted to the boxable "local" shape (`boxableName` -- depends
    // on `localTypes`/`declaredGlobals`/`moduleScope`/`cppFile`, all set above) AND
    // -- per spec.md's edge cases and SC-001's own scoping -- never fed to an
    // external call at ANY of its address-of sites (`addressOfFeedsExternalCall`): a
    // name with even one such site is excluded ENTIRELY, so every one of its
    // addressOf/indirection sites keeps today's hole rather than mixing boxed and
    // unboxed behaviour for the same name.
    val addrCalls = m.body.ast.isCall.filter(_.methodFullName == "<operator>.addressOf").l
    val candidates: Map[String, List[Call]] =
      addrCalls.flatMap(c => kidsOf(c) match {
        case List(n) => boxableName(n).map(_ -> c)
        case _       => None
      }).groupBy(_._1).map { case (k, vs) => k -> vs.map(_._2) }
    boxedLocals = candidates.collect {
      case (nm, sites) if !sites.exists(addressOfFeedsExternalCall) => nm
    }.toSet
    // `p -> n`: every pointer-typed local provably aliasing exactly one boxed local
    // for its whole lifetime -- `p = &n` is the ONLY assignment to `p` anywhere in
    // this method (see `ptrAliases`'s own doc comment for why this must be stricter
    // than merely "the only ADDRESS-OF-shaped assignment to `p`").
    ptrAliases = {
      val assigns = m.body.ast.isCall.filter(_.methodFullName == "<operator>.assignment").l
      val assignCounts = assigns.flatMap { a =>
        kidsOf(a) match { case (t: Identifier) :: _ :: Nil => Some(t.name); case _ => None }
      }.groupBy(identity).view.mapValues(_.size).toMap
      assigns.flatMap { a =>
        kidsOf(a) match {
          case (t: Identifier) :: (rhs: Call) :: Nil
              if rhs.methodFullName == "<operator>.addressOf" &&
                 assignCounts.getOrElse(t.name, 0) == 1 &&
                 !boxedLocals.contains(localName(t.name)) =>
            kidsOf(rhs) match {
              // The alias TARGET must be in the FINAL `boxedLocals` -- not merely
              // `boxableName`-eligible -- since `boxableName` alone no longer implies
              // membership (a name can be eligible in shape but still excluded for
              // feeding an external call at some OTHER address-of site).
              case List(x) => boxableName(x).filter(boxedLocals.contains).map(localName(t.name) -> _)
              case _       => None
            }
          case _ => None
        }
      }.toMap
    }
    // `003-box-address-taken-locals`, Increment B: candidate out-parameters of THIS
    // method -- a parameter actually dereferenced somewhere in the body, and NOT
    // already boxed under Increment A's own-address-taken case (disjoint by
    // construction, see `closedOutParams`'s doc comment) -- each checked against the
    // whole-program precondition (`closedOutParam`).
    closedOutParams = {
      val derefOperands = m.body.ast.isCall.filter(_.methodFullName == "<operator>.indirection").l
        .flatMap(c => kidsOf(c) match { case List(n) => rawLocalOrParamName(n); case _ => None })
        .toSet
      m.parameter.l
        .filter(p => derefOperands.contains(p.name) && !boxedLocals.contains(localName(p.name)))
        .filter(p => closedOutParam(m, p.index))
        .map(p => localName(p.name))
        .toSet
    }
    // `004-function-pointer-tracking`: every local/parameter of THIS method assigned
    // a known, non-capturing, in-program function or method value in exactly one
    // place in the entire method (research.md §5, mirroring `ptrAliases`'s own
    // whole-function single-assignment count above, applied to a different RHS
    // shape). Two rounds: `direct` sources (a plain `METHOD_REF`, or `&function`
    // wrapping one -- research.md §1) resolve immediately; `chained` sources (RHS is
    // itself a single-assignment identifier) resolve via a small, bounded
    // fixed-point pass so `op3 = op2 = op1 = add` all resolve to `add`, not just a
    // single hop -- bounded rather than recursive, matching this file's own
    // established style (e.g. `ancestorsTo`'s `guard` counter) since a real chain in
    // source is never more than a handful of assignments long regardless.
    fnPtrVars = {
      val assigns = m.body.ast.isCall.filter(_.methodFullName == "<operator>.assignment").l
      val assignCounts = assigns.flatMap { a =>
        kidsOf(a) match { case (t: Identifier) :: _ :: Nil => Some(t.name); case _ => None }
      }.groupBy(identity).view.mapValues(_.size).toMap
      // `methodByName.contains(...)` (built from `cpg.method.isExternal(false)`, the
      // same "is this actually one of our own functions" evidence
      // `addressOfFeedsExternalCall` already uses) is REQUIRED here, not optional: a
      // `MethodRef` naming an external/library function is a real value `fnValue`
      // happily represents today, but rewriting a call through it would change that
      // call site's hole from `op:pointerCall` to some OTHER hole shape at
      // evaluation time (the unresolved call name), not leave it "unchanged" as
      // FR-004 requires — silently relabeling a hole is not the same violation as
      // answering wrong, but it is still not what this feature is licensed to do.
      def fnTarget(mr: MethodRef): Option[(String, Boolean)] =
        if (methodByName.contains(mr.methodFullName))
          Some((mangledFullName(mr.methodFullName), capturesEnv.getOrElse(mr.methodFullName, false)))
        else None
      val direct: Map[String, (String, Boolean)] = assigns.flatMap { a =>
        kidsOf(a) match {
          case (t: Identifier) :: (mr: MethodRef) :: Nil if assignCounts.getOrElse(t.name, 0) == 1 =>
            fnTarget(mr).map(localName(t.name) -> _)
          case (t: Identifier) :: (addr: Call) :: Nil
              if assignCounts.getOrElse(t.name, 0) == 1 && addr.methodFullName == "<operator>.addressOf" =>
            kidsOf(addr) match {
              case List(mr: MethodRef) => fnTarget(mr).map(localName(t.name) -> _)
              case _                   => None
            }
          case _ => None
        }
      }.toMap
      val chained: Map[String, String] = assigns.flatMap { a =>
        kidsOf(a) match {
          case (t: Identifier) :: (src: Identifier) :: Nil if assignCounts.getOrElse(t.name, 0) == 1 =>
            Some(localName(t.name) -> localName(src.name))
          case _ => None
        }
      }.toMap
      var resolved = direct
      var changed  = true
      var guard    = 0
      while (changed && guard < 20) {
        changed = false; guard += 1
        chained.foreach { case (nm, alias) =>
          if (!resolved.contains(nm) && resolved.contains(alias)) {
            resolved += (nm -> resolved(alias)); changed = true
          }
        }
      }
      // The closure-safety guard (research.md §3): a resolved target that captures
      // its enclosing scope is excluded -- `Expr.call name args` dispatches with no
      // captured environment, so translating a call through such a value directly
      // would silently run it with the wrong (empty) captures instead of a hole.
      resolved.collect { case (nm, (target, false)) => nm -> target }
    }
    // `006-reduce-remaining-holes`, Story 5: array/struct locals of THIS method
    // admitted under research.md §5.3's scope boundary -- generalising `003`'s
    // Increment A boundary from scalars to aggregates: never passed as an
    // argument to any call (in-program or external, by value or by address,
    // `argFeedsName`) across the WHOLE function, and (automatically, since these
    // are drawn from `m.local.l`, never `m.parameter.l`) not itself a function
    // parameter.
    // A `Call` here means a REAL call (`!startsWith("<operator>")`) only --
    // Joern represents indexing/assignment/address-of as `Call` nodes too, with
    // the receiver/operands at `aidx >= 1` exactly like a real argument, so
    // scanning every `Call` indiscriminately would misclassify `a[1]`'s own
    // receiver as `a` "escaping" through a call argument. Checked directly
    // against a live fixture this session (`a[1]` wrongly excluded `a` from
    // `boxedArrays` before this filter was added), not merely assumed correct
    // from the operator-call convention alone.
    def nameEverPassedToCall(nm: String): Boolean =
      m.body.ast.isCall.filterNot(_.methodFullName.startsWith("<operator>")).l
        .exists(c => kidsOf(c).exists(k => aidx(k) >= 1 && argFeedsName(k, nm)))
    // `007-reduce-remaining-holes-2`: the one narrow exception to the exclusion
    // above -- `nm` still escapes via a call argument, but SAFELY, when EVERY such
    // feeding site is `&nm[idx]`/`&nm.f` (an element/field address, not a bare
    // pass-by-value/decay and not `&nm` naming the whole object -- `argFeedsName`
    // still catches both of those as disqualifying, unconditionally) to an
    // in-program callee whose corresponding parameter is `closedIrefOutParam`-
    // verified across the WHOLE program. `nm` stays boxed and the callee's
    // parameter (populated into `ptrIrefNames` below) reads/writes `nm`'s own
    // storage directly via `derefIref`/`setDerefIref` -- exactly the cross-function
    // interior-pointer case Story 5's own scope boundary originally excluded
    // wholesale, now narrowed to the one shape this can verify sound without a
    // general points-to analysis.
    def nameEscapesSafely(nm: String, wholeObjectAddressOk: Boolean): Boolean =
      m.body.ast.isCall.filterNot(_.methodFullName.startsWith("<operator>")).l
        .forall { c =>
          kidsOf(c).filter(k => aidx(k) >= 1 && argFeedsName(k, nm)).forall { k =>
            val elementOrFieldAddress = k match {
              case addr: Call if addr.methodFullName == "<operator>.addressOf" =>
                kidsOf(addr) match {
                  case List(x) =>
                    asIndex(x).exists { case (r, _) => rawLocalOrParamName(r).map(localName).contains(nm) } ||
                    asField(x).exists { case (r, _) => rawLocalOrParamName(r).map(localName).contains(nm) }
                  case _ => false
                }
              case _ => false
            }
            // `007-reduce-remaining-holes-2`: a WHOLE-OBJECT address (`&nm`, not
            // `&nm[i]`/`&nm.f`) fed to an in-program call is ALSO safe -- but only for
            // a STRUCT (`wholeObjectAddressOk`, set from `isClassType` at the call
            // site below), never an array. `&s` for a class-typed local is aggregate
            // IDENTITY (`addressOfIsAggregate`/`callExpr`'s own `aggregate` branch --
            // `s`'s `Val.ref` already IS its own address, no wrapper), so the callee's
            // parameter receives `s`'s own already-boxed reference directly and every
            // `p->f`/`p.f` on it translates via the ordinary, UNCONDITIONAL
            // `setField`/`field` mechanism -- correct for ANY object-shaped runtime
            // value, needing no `ptrIrefNames`/`closedIrefOutParam`-style per-parameter
            // tracking at all. This is what `boxedLocals` (`003`, scalars) already
            // does for `&n` fed to any in-program call (`addressOfFeedsExternalCall`
            // checks only for an EXTERNAL callee) -- structs get the identical
            // treatment here, closing a real, confirmed "hole-free but dynamically
            // wrong" gap (`setField:*:non-object` at evaluation time) that existed
            // because this exclusion was stricter than `boxedLocals`'s own for no
            // reason specific to structs. An ARRAY'S whole-object address (`&arr`,
            // distinct from decay) is NOT eligible here: unlike a struct, it is not
            // already handled by an existing unconditional mechanism, and today's own
            // `addressOf` handling has no case for it at all (falls to its existing
            // hole) -- extending that is a separate, unverified change this fix does
            // not make.
            val wholeObjectAddress = wholeObjectAddressOk && (k match {
              case addr: Call if addr.methodFullName == "<operator>.addressOf" =>
                kidsOf(addr) match {
                  case List(x) => argFeedsName(x, nm)
                  case _       => false
                }
              case _ => false
            })
            val calleeIsInProgram = !c.methodFullName.startsWith("<operator>") && methodByName.contains(c.methodFullName)
            (elementOrFieldAddress && calleeIsInProgram &&
              methodByName.get(c.methodFullName).exists(callee => closedIrefOutParam(callee, aidx(k)))) ||
            (wholeObjectAddress && calleeIsInProgram)
          }
        }
    def nameSafelyBoxable(nm: String, wholeObjectAddressOk: Boolean): Boolean =
      !nameEverPassedToCall(nm) || nameEscapesSafely(nm, wholeObjectAddressOk)
    // `moduleScope` is checked FIRST and unconditionally, mirroring `boxableName`'s
    // own existing precedent for scalar boxing: a `<module>`/`<global>` pseudo-
    // method's own "locals" are actually FILE-SCOPE globals, and every assignment
    // there already goes through `setGlobal`, not a real local binding -- boxing
    // one would create a phantom local no `setGlobal`/`name` read anywhere else in
    // the program would ever see. Missing this exclusion is a confirmed, live bug,
    // not a hypothetical: `test_vdbecov.c`'s own `<global>` initializer declares a
    // 200,000-element file-scope array, and boxing it unconditionally produced a
    // single `Expr.boxFields` with 200,000 fields -- which `render_lean.py` renders
    // as a 200,000-entry Lean list literal, whose `List.cons` chain blew through
    // both `maxHeartbeats` and `maxRecDepth` on a real SQLite build. A *global*
    // array/struct's declaration keeps its existing, unrelated hole
    // (`op:alloc:array-decl`/`op:arrayDecl:size`/etc.) exactly as before Story 5 --
    // Story 5's own scope boundary (research.md §5.3) was written for locals within
    // one function's activation, and a module-scope name was never meant to be in
    // scope for it at all.
    boxedArrays = if (moduleScope) Map.empty else {
      // `008-reduce-remaining-holes-3` US1: `arrayShape` (a literal integer size)
      // is tried FIRST, byte-identical to before this feature -- only when it does
      // NOT match does `resolveMacroArraySize` get a chance, on the SAME bracket
      // contents, via the broader `arrayShapeAny`. This ordering means a literal
      // size is never routed through the macro path, and a non-digit size that
      // `resolveMacroArraySize` cannot resolve (a `sizeof`, multi-term expression,
      // or macro not in this file's own table) falls through to `None` exactly as
      // it did before this feature existed.
      val arrayShapeAny = """^(.+)\[(.+)\]$""".r
      val candidates = m.local.l.flatMap { l =>
        localTypes.get(l.name).flatMap { ty =>
          val bt = bareType(ty)
          arrayShape.findFirstMatchIn(bt).map(mt => localName(l.name) -> mt.group(2).toInt)
            .orElse {
              arrayShapeAny.findFirstMatchIn(bt).flatMap { mt =>
                resolveMacroArraySize(mt.group(2), m.filename).map(localName(l.name) -> _)
              }
            }
        }
      }.toMap
      candidates.filter { case (nm, _) => nameSafelyBoxable(nm, wholeObjectAddressOk = false) }
    }
    boxedStructs = if (moduleScope) Map.empty else {
      val candidates = m.local.l.flatMap { l =>
        localTypes.get(l.name).filter(isClassType).flatMap { ty =>
          structTypeDeclOf(ty).map(td => localName(l.name) -> td.member.l.map(_.name))
        }
      }.toMap
      candidates.filter { case (nm, _) => nameSafelyBoxable(nm, wholeObjectAddressOk = true) }
    }
    // `006-reduce-remaining-holes`, Story 5: plain pointer locals PROVABLY, for
    // their whole lifetime, holding an interior pointer VALUE -- `p = &a[i]`,
    // `p = &s.f` (mirroring `ptrAliases`'s own whole-function single-assignment
    // discipline), or `p = a` (array-to-pointer decay, C's own rule that an
    // array used as a value is the address of its first element).
    ptrIrefNames = {
      val assigns = m.body.ast.isCall.filter(_.methodFullName == "<operator>.assignment").l
      val assignCounts = assigns.flatMap { a =>
        kidsOf(a) match { case (t: Identifier) :: _ :: Nil => Some(t.name); case _ => None }
      }.groupBy(identity).view.mapValues(_.size).toMap
      assigns.flatMap { a =>
        kidsOf(a) match {
          case (t: Identifier) :: (rhs: Call) :: Nil
              if rhs.methodFullName == "<operator>.addressOf" &&
                 assignCounts.getOrElse(t.name, 0) == 1 =>
            kidsOf(rhs) match {
              case List(operand)
                  if boxedArrayIndexOperand(operand).isDefined ||
                     boxedStructFieldOperand(operand).isDefined =>
                Some(localName(t.name))
              case _ => None
            }
          case (t: Identifier) :: (src: Identifier) :: Nil
              if assignCounts.getOrElse(t.name, 0) == 1 &&
                 boxedArrays.contains(localName(src.name)) =>
            Some(localName(t.name))
          case _ => None
        }
      }.toSet ++
      // `007-reduce-remaining-holes-2`: parameters of THIS method verified, across
      // the whole program (`closedIrefOutParam`), to always receive the address of
      // an element/field of a boxed array/struct -- the cross-function counterpart
      // to the local-only shapes just above. `p` itself already holds the caller's
      // `Val.iref` value directly, exactly like a local `ptrIrefNames` member;
      // excluded when `p`'s OWN address is separately taken within this method
      // (`boxedLocals`), matching `closedOutParams`'s own disjointness precedent.
      m.parameter.l
        .filter(p => closedIrefOutParam(m, p.index) && !boxedLocals.contains(localName(p.name)))
        .map(p => localName(p.name)).toSet
    }
    val body0 = methodBody(m)
    // `003-box-address-taken-locals`: allocate every boxed local's/parameter's cell
    // exactly once, unconditionally, before the translated body's first real
    // statement runs -- for a parameter, reboxing the plain incoming value; for a
    // local, starting from `unit` (Core's existing answer for an unassigned local
    // read before its first write, boxed or not). This is deliberately UNCONDITIONAL
    // rather than inserted "at the declaration/first assignment": a declaration
    // without an initializer, first written inside an `if`/`else`, has no single
    // textual "first binding" that dominates every other write and read, and boxing
    // only one branch would leave the other reading/writing an unboxed name that
    // every other reference in the function now expects to be a `Val.ref` -- exactly
    // the silent-wrong failure Constitution Principle III forbids. An unconditional
    // prologue sidesteps the question entirely: the box exists before ANY branch of
    // the body can run, for every control-flow shape, not just the straight-line one.
    val boxedParamNames = m.parameter.l.map(_.name).filter(boxedLocals.contains).toSet
    val prologues: List[ujson.Obj] = boxedLocals.toList.sorted.map { nm =>
      val init = if (boxedParamNames.contains(nm)) boxRef(nm) else ujson.Obj("k" -> "unit")
      ujson.Obj("k" -> "assign", "x" -> nm, "e" -> ujson.Obj("k" -> "boxNew", "e" -> init))
    }
    // `006-reduce-remaining-holes`, Story 5: the same unconditional-prologue
    // discipline as `boxedLocals` above, extended to arrays/structs -- every
    // field starts `unit` (Core's own "unassigned local" convention; `003`'s own
    // precedent for a boxed LOCAL with no incoming value, and every array/struct
    // this story boxes is a local, never a parameter, per the scope boundary).
    def boxFieldsExpr(keys: List[String]): ujson.Obj =
      ujson.Obj("k" -> "boxFields", "fields" -> ujson.Arr.from(
        keys.map(k => (ujson.Arr(ujson.Str(k), ujson.Obj("k" -> "unit")): ujson.Value))))
    val aggPrologues: List[ujson.Obj] =
      boxedArrays.toList.sortBy(_._1).map { case (nm, n) =>
        ujson.Obj("k" -> "assign", "x" -> nm, "e" -> boxFieldsExpr((0 until n).map(_.toString).toList))
      } ++
      boxedStructs.toList.sortBy(_._1).map { case (nm, members) =>
        ujson.Obj("k" -> "assign", "x" -> nm, "e" -> boxFieldsExpr(members))
      }
    val allPrologues = prologues ++ aggPrologues
    val body = if (allPrologues.isEmpty) body0 else seqOf(allPrologues :+ body0)
    moduleScope = false
    localTypes = Map.empty
    valueReceivers = Set.empty
    ptrReceivers = Set.empty
    currentClass = None
    declaredGlobals = Set.empty
    boundMethods = Map.empty
    attrsOf = Map.empty
    boxedLocals = Set.empty
    ptrAliases = Map.empty
    closedOutParams = Set.empty
    fnPtrVars = Map.empty
    boxedArrays = Map.empty
    boxedStructs = Map.empty
    ptrIrefNames = Set.empty
    // `self` is stripped ONLY for a method of a class, where `applyFunc` binds the
    // receiver itself. A MODULE-LEVEL function whose first parameter happens to be named
    // `self` is not a method and its `self` is an ordinary positional: cachetools defines
    // `def methodkey(self, *args, **kwargs)` at file scope, and stripping it made Core
    // compute `hashkey(10, -4)` where CPython computes `hashkey(-4)`. That was 5 of the
    // remaining divergences, and it read as a `_HashedTuple` shape problem rather than a
    // missing parameter.
    // `astParentType` is not `TYPE_DECL` for pythonsrc methods -- using it strips nothing
    // and changes 140 functions. The reliable signal is the one this file already computes:
    // `classNames` holds every real `class` statement, so a function is a method exactly
    // when the segment before its own name is one of them. Split on `:<module>.` first --
    // the filename itself contains dots (`__init__.py`).
    val qualSegs = exportName(m).split(":<module>\\.").lastOption
                     .map(_.split('.').toList).getOrElse(Nil)
    val isMethodDecl =
      qualSegs.length >= 2 && classNames.contains(qualSegs(qualSegs.length - 2))
    val ps = m.parameter.l.sortBy(_.index)
               .filterNot(p => isMethodDecl && p.name == "self")
    val stars = ps.map(p => p.name -> paramStars(p, m.filename)).toMap
    val obj = ujson.Obj(
      "name"   -> exportName(m),
      "file"   -> m.filename,
      // `ps` is already sorted and self-filtered (needed for `*args`/`**kwargs`
      // detection). `this` leaves the list for the same reason `self` does: `applyFunc`
      // binds the receiver itself, under the name the body now uses.
      "params" -> ujson.Arr.from(ps.map(_.name).filterNot(x => cppFile && x == "this")),
      "body"   -> body
    )
    // Builtin bases ride on the module *initializer* entry — the function that runs the
    // file's `class` statements — rather than on the methods, so that a builtin-based
    // class with no methods at all is still recorded. The key is optional and absent when
    // empty, which is what keeps every existing AST byte-identical.
    if (isModule) {
      val cb = classBasesByFile.getOrElse(m.filename, Map.empty)
      if (cb.nonEmpty)
        obj("classBases") = ujson.Obj.from(cb.toList.sortBy(_._1).map { case (k, v) =>
          k -> (ujson.Str(v): ujson.Value)
        })
    }
    // Emitted only when present, so an AST with no variadic parameters renders exactly
    // as it did before this existed.
    //
    // PYTHON ONLY. `paramStars` is gated on `.py`, but `isVariadic` is not: C and C++
    // set it for `...`, and C varargs are NOT Python varargs. `void V8_Fatal(char*, ...)`
    // was being marked `vararg`, which tells `bindParams` to pack surplus arguments into
    // a `Val.tuple` under Python's calling convention -- a silent mistranslation of every
    // printf-style function in V8. C's `...` has no calling convention Core models: the
    // callee reads it through `va_arg`, which is not translated. So the field is not
    // emitted at all for non-Python, and such a call keeps whatever hole it already had.
    if (pyFile) {
      ps.find(p => stars(p.name) == 1 || (stars(p.name) == 0 && p.isVariadic))
        .foreach(p => obj("vararg") = p.name)
      ps.find(p => stars(p.name) == 2).foreach(p => obj("kwarg") = p.name)
    }
    obj
  }

  // `<metaClassCallHandler>` joins the list §24 left it off. It is generated *per class*
  // and its body is `cls.__init__(<fakeNew>(...))` — the allocation Joern already models
  // at every real construction site — so it is neither user code nor reachable from user
  // code. Counting it inflated both the denominator and the hole-free numerator; excluding
  // it removes padding, not coverage, and the numbers below separate the two.
  val synthetic = List("<metaClassAdapter>", "<metaClassCallHandler>",
                       "<global>", "<body>", "<fakeNew>")
  val methods = cpg.method.isExternal(false)
    .whereNot(_.nameExact("<module>"))
    .l.filterNot(m => synthetic.exists(m.fullName.contains))
    .take(maxMethods)

  // The file-level pseudo-method. It was previously excluded outright, which meant every
  // module-level constant, class and `def` was an unresolvable free name — the single
  // biggest contributor to the call-closure gap. It is now exported as an *initializer*:
  // a zero-argument function whose body is a run of `setGlobal`s establishing the
  // module-level frame. `<global>` is the C frontend's spelling of the same thing.
  val moduleMethods = cpg.method.isExternal(false)
    .l.filter(m => m.name == "<module>" || m.name == "<global>")
    .filterNot(m => m.fullName.contains("<includes>"))
    .sortBy(_.fullName)

  val funcs = methods.map(emit(_, false))
  val inits = moduleMethods.map(emit(_, true))
  // The module objects are built **before** any module body runs, so an `import` at the
  // top of a module reads a module object that already exists. `render_lean.py` keeps AST
  // order when it collects `moduleInits`, so placing this entry first here is what puts
  // it first there.
  val all   = funcs ++ moduleObjectsInit.toList ++ inits

  // `writeJson` (not `ujson.write`) for the same reason `seqOf`/`moduleObjectsInit` are
  // now iterative: this is the single call that walks the whole exported tree, including
  // any long "seq" chain either of them built, and `ujson.write` recurses once per
  // nesting level to do it (research.md item 1). `indent = 1` is byte-identical to
  // today's output (verified) and kept whenever nothing long enough to matter was built;
  // past `seqChainCompactThreshold`, `indent = 1`'s whitespace is quadratic in output
  // size (confirmed empirically: pretty-printing a 100,000-deep chain this way
  // OutOfMemoryErrors regardless of stack safety), so compact (`indent = -1`) is used
  // instead -- valid here per data-model.md, since a run that crosses this threshold
  // never produced byte-identical (or any) output before this fix.
  val jsonIndent = if (maxSeqChainLen >= seqChainCompactThreshold) -1 else 1
  os.write.over(os.Path(out, os.pwd), writeJson(ujson.Arr.from(all), indent = jsonIndent))

  // Iterative for the same reason `writeJson` is: `all` may contain a "seq" chain as
  // deep as `maxSeqChainLen`, and this walk is our own code, not `ujson`'s -- a plain
  // self-recursive version (as this was before) would overflow the JVM stack right after
  // the write above succeeds, on the very inputs this feature exists to fix.
  def countKind(v: ujson.Value, k: String): Int = {
    var total = 0
    val work = scala.collection.mutable.ArrayBuffer.empty[ujson.Value]
    work.append(v)
    while (work.nonEmpty) {
      work.remove(work.length - 1) match {
        case o: ujson.Obj =>
          if (o.value.get("k").exists(_.str == k)) total += 1
          o.value.values.foreach(work.append(_))
        case a: ujson.Arr =>
          a.value.foreach(work.append(_))
        case _ => ()
      }
    }
    total
  }
  val doc = ujson.Arr.from(all)
  println(s"data model assumed for target-sized integer types: ${dataModel.toLowerCase}"
        + (if (modelInts.isEmpty) " (UNKNOWN -- `long`/`size_t` casts are holes)" else ""))
  if (metaElided > 0) println(s"elided $metaElided kernel metadata declaration(s)")
  if (syncElided > 0) println(s"elided $syncElided sequentially-unobservable synchronisation call(s)")
  if (useElided > 0) println(s"elided $useElided USE(x) no-op macro(s)")
  println(s"exported ${funcs.size} functions + ${inits.size} module initializers to $out "
        + s"(${countKind(doc, "closure")} closures, ${countKind(doc, "setGlobal")} global writes)")
}
