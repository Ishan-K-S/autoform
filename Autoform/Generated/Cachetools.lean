import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
--
-- 8000 was not enough either. The binding constraint is not the nesting depth of
-- any one body (Ansible's deepest is 297) but the `funcs := [...]` list literal,
-- which elaborates as nested cons cells -- one frame or more per function, and
-- Ansible has 5,546. So the limit has to scale with the module's function count,
-- not with how deep its code happens to be.
set_option maxRecDepth 9672

/-!
# Cachetools — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.Cachetools
open Autoform.Core

/-- `cachetools/__init__.py:<module>._DefaultSize.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.__getitem__"
  , params := ["_key"]
  , body := (.ret (.lit (.int 1))) }

/-- `cachetools/__init__.py:<module>._DefaultSize.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.__setitem__"
  , params := ["_key", "_value"]
  , body := .skip }

/-- `cachetools/__init__.py:<module>._DefaultSize.pop`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize_pop : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.pop"
  , params := ["_key"]
  , body := (.ret (.lit (.int 1))) }

/-- `cachetools/__init__.py:<module>._DefaultSize.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___DefaultSize_clear : Func :=
  { name := "cachetools/__init__.py:<module>._DefaultSize.clear"
  , params := []
  , body := .skip }

/-- `cachetools/__init__.py:<module>.Cache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__init__"
  , params := ["maxsize", "getsizeof"]
  , body := (.seq
            (.ifte
              (.name "getsizeof")
              (.setField (.name "self") "getsizeof" (.name "getsizeof"))
              .skip)
            (.seq
              (.ifte
                (.isOp
                  true
                  (.field (.name "self") "getsizeof")
                  (.fnref "cachetools/__init__.py:<module>.Cache.getsizeof"))
                (.seq
                  (.assign "tmp0" (.dictE []))
                  (.setField (.name "self") "_Cache__size" (.name "tmp0")))
                .skip)
              (.seq
                (.seq
                  (.assign "tmp1" (.dictE []))
                  (.setField (.name "self") "_Cache__data" (.name "tmp1")))
                (.seq
                  (.setField (.name "self") "_Cache__currsize" (.lit (.int 0)))
                  (.seq
                    (.setField (.name "self") "_Cache__maxsize" (.name "maxsize"))
                    (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/__init__.py:<module>.Cache.__repr__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___repr__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__repr__"
  , params := []
  , body := (.seq
            (.ret
              (.binop
                "%"
                (.lit (.str "%s(%s, maxsize=%r, currsize=%r)"))
                (.tupleE
                  [ (.field (.call "type" [(.name "self")]) "__name__")
                  , (.call "repr" [(.field (.name "self") "_Cache__data")])
                  , (.field (.name "self") "_Cache__maxsize")
                  , (.field (.name "self") "_Cache__currsize") ])))
            (.seq .skip .skip)) }

/-- `cachetools/__init__.py:<module>.Cache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__getitem__"
  , params := ["key"]
  , body := (.tryCatch
            (.ret (.index (.field (.name "self") "_Cache__data") (.name "key")))
            "__exc"
            (.ret (.mcall (.name "self") "__missing__" [(.name "key")]))) }

/-- `cachetools/__init__.py:<module>.Cache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__setitem__"
  , params := ["key", "value"]
  , body := (.seq
            (.assign "maxsize" (.field (.name "self") "_Cache__maxsize"))
            (.seq
              .skip
              (.seq
                (.assign "size" (.mcall (.name "self") "getsizeof" [(.name "value")]))
                (.seq
                  .skip
                  (.seq
                    (.ifte
                      (.binop "<" (.name "size") (.lit (.int 0)))
                      (.raise
                        (.call "ValueError" [(.lit (.str "value size must be non-negative"))]))
                      .skip)
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop ">" (.name "size") (.name "maxsize"))
                          (.raise (.call "ValueError" [(.lit (.str "value too large"))]))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.inOp true (.name "key") (.field (.name "self") "_Cache__data"))
                              (.seq
                                (.assign "diffsize" (.name "size"))
                                (.loop
                                  (.binop
                                    ">"
                                    (.binop
                                      "+"
                                      (.field (.name "self") "_Cache__currsize")
                                      (.name "diffsize"))
                                    (.name "maxsize"))
                                  (.expr (.mcall (.name "self") "popitem" []))))
                              (.seq
                                (.assign
                                  "diffsize"
                                  (.binop
                                    "-"
                                    (.name "size")
                                    (.index (.field (.name "self") "_Cache__size") (.name "key"))))
                                (.loop
                                  (.binop
                                    ">"
                                    (.binop
                                      "+"
                                      (.field (.name "self") "_Cache__currsize")
                                      (.name "diffsize"))
                                    (.name "maxsize"))
                                  (.seq
                                    (.expr (.mcall (.name "self") "popitem" []))
                                    (.ifte
                                      (.inOp
                                        true
                                        (.name "key")
                                        (.field (.name "self") "_Cache__data"))
                                      (.assign "diffsize" (.name "size"))
                                      .skip)))))
                            (.seq
                              (.setIndex
                                (.field (.name "self") "_Cache__data")
                                (.name "key")
                                (.name "value"))
                              (.seq
                                (.setIndex
                                  (.field (.name "self") "_Cache__size")
                                  (.name "key")
                                  (.name "size"))
                                (.setField
                                  (.name "self")
                                  "_Cache__currsize"
                                  (.binop
                                    "+"
                                    (.field (.name "self") "_Cache__currsize")
                                    (.name "diffsize")))))))))))))) }

/-- `cachetools/__init__.py:<module>.Cache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__delitem__"
  , params := ["key"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "_Cache__size"))
              (.assign "size" (.mcall (.name "tmp0") "pop" [(.name "key")])))
            (.seq
              .skip
              (.seq
                (.hole "op:delete-index")
                (.seq
                  .skip
                  (.setField
                    (.name "self")
                    "_Cache__currsize"
                    (.binop "-" (.field (.name "self") "_Cache__currsize") (.name "size"))))))) }

/-- `cachetools/__init__.py:<module>.Cache.__contains__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___contains__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__contains__"
  , params := ["key"]
  , body := (.ret (.inOp false (.name "key") (.field (.name "self") "_Cache__data"))) }

/-- `cachetools/__init__.py:<module>.Cache.__missing__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___missing__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__missing__"
  , params := ["key"]
  , body := (.seq (.raise (.call "KeyError" [(.name "key")])) .skip) }

/-- `cachetools/__init__.py:<module>.Cache.__iter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___iter__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__iter__"
  , params := []
  , body := (.seq (.ret (.call "iter" [(.field (.name "self") "_Cache__data")])) .skip) }

/-- `cachetools/__init__.py:<module>.Cache.__len__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache___len__ : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.__len__"
  , params := []
  , body := (.seq (.ret (.call "len" [(.field (.name "self") "_Cache__data")])) .skip) }

/-- `cachetools/__init__.py:<module>.Cache.get`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_get : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.get"
  , params := ["key", "default"]
  , body := (.ifte
            (.inOp false (.name "key") (.name "self"))
            (.ret (.index (.name "self") (.name "key")))
            (.ret (.name "default"))) }

/-- `cachetools/__init__.py:<module>.Cache.pop`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_pop : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.pop"
  , params := ["key", "default"]
  , body := (.seq
            (.ifte
              (.inOp false (.name "key") (.name "self"))
              (.seq
                (.assign "value" (.index (.name "self") (.name "key")))
                (.hole "op:delete-index"))
              (.ifte
                (.isOp false (.name "default") (.field (.name "self") "_Cache__marker"))
                (.raise (.call "KeyError" [(.name "key")]))
                (.assign "value" (.name "default"))))
            (.seq .skip (.seq (.ret (.name "value")) .skip))) }

/-- `cachetools/__init__.py:<module>.Cache.setdefault`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_setdefault : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.setdefault"
  , params := ["key", "default"]
  , body := (.seq
            (.ifte
              (.inOp false (.name "key") (.name "self"))
              (.assign "value" (.index (.name "self") (.name "key")))
              (.seq
                (.assign "tmp0" (.name "default"))
                (.seq
                  (.setIndex (.name "self") (.name "key") (.name "tmp0"))
                  (.assign "value" (.name "tmp0")))))
            (.seq .skip (.seq (.ret (.name "value")) .skip))) }

/-- `cachetools/__init__.py:<module>.Cache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.clear"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "_Cache__data"))
              (.expr (.mcall (.name "tmp0") "clear" [])))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp1" (.field (.name "self") "_Cache__size"))
                  (.expr (.mcall (.name "tmp1") "clear" [])))
                (.seq .skip (.setField (.name "self") "_Cache__currsize" (.lit (.int 0))))))) }

/-- `cachetools/__init__.py:<module>.Cache.maxsize`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_maxsize : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.maxsize"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "The maximum size of the cache.")))
            (.ret (.field (.name "self") "_Cache__maxsize"))) }

/-- `cachetools/__init__.py:<module>.Cache.currsize`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_currsize : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.currsize"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "The current size of the cache.")))
            (.ret (.field (.name "self") "_Cache__currsize"))) }

/-- `cachetools/__init__.py:<module>.Cache.getsizeof`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__Cache_getsizeof : Func :=
  { name := "cachetools/__init__.py:<module>.Cache.getsizeof"
  , params := ["value"]
  , body := (.seq
            (.expr (.lit (.str "Return the size of a cache element's value.")))
            (.ret (.lit (.int 1)))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.__init__"
  , params := ["maxsize", "getsizeof"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField (.name "self") "_FIFOCache__order" (.alloc "OrderedDict" []))
              (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , body := (.seq
            (.expr (.call "cache_setitem" [(.name "self"), (.name "key"), (.name "value")]))
            (.seq
              .skip
              (.ifte
                (.inOp false (.name "key") (.field (.name "self") "_FIFOCache__order"))
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_FIFOCache__order"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                (.setIndex (.field (.name "self") "_FIFOCache__order") (.name "key") (.lit .unit))))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , body := (.seq
            (.expr (.call "cache_delitem" [(.name "self"), (.name "key")]))
            (.hole "op:delete-index")) }

/-- `cachetools/__init__.py:<module>.FIFOCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.popitem"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "Remove and return the `(key, value)` pair first inserted.")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "__else_ok1" (.lit (.bool true)))
                  (.seq
                    (.tryCatch
                      (.assign
                        "key"
                        (.call
                          "next"
                          [(.call "iter" [(.field (.name "self") "_FIFOCache__order")])]))
                      "__exc"
                      (.seq
                        (.assign "__else_ok1" (.lit (.bool false)))
                        (.raise
                          (.call
                            "KeyError"
                            [ (.binop
                                "%"
                                (.lit (.str "%s is empty"))
                                (.field (.call "type" [(.name "self")]) "__name__")) ]))))
                    (.ifte
                      (.name "__else_ok1")
                      (.ret
                        (.tupleE [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                      .skip)))
                (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>.FIFOCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__FIFOCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.FIFOCache.clear"
  , params := []
  , body := (.seq
            (.expr (.mcall (.name "Cache") "clear" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_FIFOCache__order"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.LFUCache._Link.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache__Link___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache._Link.__init__"
  , params := ["count"]
  , body := (.seq
            (.setField (.name "self") "count" (.name "count"))
            (.seq (.setField (.name "self") "keys" (.call "set" [])) .skip)) }

/-- `cachetools/__init__.py:<module>.LFUCache._Link.unlink`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache__Link_unlink : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache._Link.unlink"
  , params := []
  , body := (.seq
            (.assign "next" (.field (.name "self") "next"))
            (.seq
              (.assign "prev" (.field (.name "self") "prev"))
              (.seq
                (.setField (.name "prev") "next" (.name "next"))
                (.seq .skip (.seq (.setField (.name "next") "prev" (.name "prev")) .skip))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__init__"
  , params := ["maxsize", "getsizeof"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.seq
                (.assign "tmp0" (.mcall (.name "LFUCache") "_Link" [(.lit (.int 0))]))
                (.seq
                  (.setField (.name "self") "_LFUCache__root" (.name "tmp0"))
                  (.assign "root" (.name "tmp0"))))
              (.seq
                (.seq
                  (.assign "tmp1" (.name "root"))
                  (.seq
                    (.setField (.name "root") "prev" (.name "tmp1"))
                    (.setField (.name "root") "next" (.name "tmp1"))))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp2" (.dictE []))
                      (.setField (.name "self") "_LFUCache__links" (.name "tmp2")))
                    (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , body := (.seq
            (.assign "value" (.call "cache_getitem" [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp false (.name "key") (.name "self"))
                  (.expr (.mcall (.name "self") "_LFUCache__touch" [(.name "key")]))
                  .skip)
                (.ret (.name "value"))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , body := (.seq
            (.expr (.call "cache_setitem" [(.name "self"), (.name "key"), (.name "value")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp false (.name "key") (.field (.name "self") "_LFUCache__links"))
                  (.seq
                    (.expr (.mcall (.name "self") "_LFUCache__touch" [(.name "key")]))
                    (.ret (.lit .unit)))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "root" (.field (.name "self") "_LFUCache__root"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "link" (.field (.name "root") "next"))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.field (.name "link") "count") (.lit (.int 1)))
                              (.seq
                                (.assign
                                  "link"
                                  (.mcall (.name "LFUCache") "_Link" [(.lit (.int 1))]))
                                (.seq
                                  (.setField (.name "link") "next" (.field (.name "root") "next"))
                                  (.seq
                                    (.seq
                                      (.assign "tmp0" (.name "link"))
                                      (.seq
                                        (.setField (.name "root") "next" (.name "tmp0"))
                                        (.setField
                                        (.field (.name "link") "next")
                                        "prev"
                                        (.name "tmp0"))))
                                    (.setField (.name "link") "prev" (.name "root")))))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.seq
                                  (.assign "tmp1" (.field (.name "link") "keys"))
                                  (.expr (.mcall (.name "tmp1") "add" [(.name "key")])))
                                (.setIndex
                                  (.field (.name "self") "_LFUCache__links")
                                  (.name "key")
                                  (.name "link"))))))))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , body := (.seq
            (.expr (.call "cache_delitem" [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_LFUCache__links"))
                  (.assign "link" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp1" (.field (.name "link") "keys"))
                      (.expr (.mcall (.name "tmp1") "remove" [(.name "key")])))
                    (.seq
                      .skip
                      (.ifte
                        (.unop "!" (.field (.name "link") "keys"))
                        (.expr (.mcall (.name "link") "unlink" []))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.popitem"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "Remove and return the `(key, value)` pair least frequently used.")))
            (.seq
              .skip
              (.seq
                (.assign "root" (.field (.name "self") "_LFUCache__root"))
                (.seq
                  .skip
                  (.seq
                    (.assign "curr" (.field (.name "root") "next"))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.isOp false (.name "curr") (.name "root"))
                          (.raise
                            (.call
                              "KeyError"
                              [ (.binop
                                  "%"
                                  (.lit (.str "%s is empty"))
                                  (.field (.call "type" [(.name "self")]) "__name__")) ]))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "key"
                              (.call "next" [(.call "iter" [(.field (.name "curr") "keys")])]))
                            (.seq
                              .skip
                              (.seq
                                (.ret
                                  (.tupleE
                                    [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                                (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache.clear"
  , params := []
  , body := (.seq
            (.expr (.mcall (.name "Cache") "clear" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign "root" (.field (.name "self") "_LFUCache__root"))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp0" (.name "root"))
                      (.seq
                        (.setField (.name "root") "prev" (.name "tmp0"))
                        (.setField (.name "root") "next" (.name "tmp0"))))
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "tmp1" (.field (.name "self") "_LFUCache__links"))
                          (.expr (.mcall (.name "tmp1") "clear" [])))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.LFUCache._LFUCache__touch`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LFUCache__LFUCache__touch : Func :=
  { name := "cachetools/__init__.py:<module>.LFUCache._LFUCache__touch"
  , params := ["key"]
  , body := (.seq
            (.expr (.lit (.str "Increment use count")))
            (.seq
              .skip
              (.seq
                (.assign "link" (.index (.field (.name "self") "_LFUCache__links") (.name "key")))
                (.seq
                  .skip
                  (.seq
                    (.assign "curr" (.field (.name "link") "next"))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop
                            "!="
                            (.field (.name "curr") "count")
                            (.binop "+" (.field (.name "link") "count") (.lit (.int 1))))
                          (.seq
                            (.ifte
                              (.binop
                                "=="
                                (.call "len" [(.field (.name "link") "keys")])
                                (.lit (.int 1)))
                              (.seq
                                (.setField
                                  (.name "link")
                                  "count"
                                  (.binop "+" (.field (.name "link") "count") (.lit (.int 1))))
                                (.ret (.lit .unit)))
                              .skip)
                            (.seq
                              (.assign
                                "curr"
                                (.mcall
                                  (.name "LFUCache")
                                  "_Link"
                                  [(.binop "+" (.field (.name "link") "count") (.lit (.int 1)))]))
                              (.seq
                                (.setField (.name "curr") "next" (.field (.name "link") "next"))
                                (.seq
                                  (.seq
                                    (.assign "tmp0" (.name "curr"))
                                    (.seq
                                      (.setField (.name "link") "next" (.name "tmp0"))
                                      (.setField
                                        (.field (.name "curr") "next")
                                        "prev"
                                        (.name "tmp0"))))
                                  (.setField (.name "curr") "prev" (.name "link"))))))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.seq
                              (.assign "tmp1" (.field (.name "curr") "keys"))
                              (.expr (.mcall (.name "tmp1") "add" [(.name "key")])))
                            (.seq
                              .skip
                              (.seq
                                (.seq
                                  (.assign "tmp2" (.field (.name "link") "keys"))
                                  (.expr (.mcall (.name "tmp2") "remove" [(.name "key")])))
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.unop "!" (.field (.name "link") "keys"))
                                      (.expr (.mcall (.name "link") "unlink" []))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.setIndex
                                        (.field (.name "self") "_LFUCache__links")
                                        (.name "key")
                                        (.name "curr")))))))))))))))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__init__"
  , params := ["maxsize", "getsizeof"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField (.name "self") "_LRUCache__order" (.alloc "OrderedDict" []))
              (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , body := (.seq
            (.assign "value" (.call "cache_getitem" [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp false (.name "key") (.name "self"))
                  (.expr (.mcall (.name "self") "_LRUCache__touch" [(.name "key")]))
                  .skip)
                (.ret (.name "value"))))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , body := (.seq
            (.expr (.call "cache_setitem" [(.name "self"), (.name "key"), (.name "value")]))
            (.expr (.mcall (.name "self") "_LRUCache__touch" [(.name "key")]))) }

/-- `cachetools/__init__.py:<module>.LRUCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , body := (.seq
            (.expr (.call "cache_delitem" [(.name "self"), (.name "key")]))
            (.hole "op:delete-index")) }

/-- `cachetools/__init__.py:<module>.LRUCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.popitem"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "Remove and return the `(key, value)` pair least recently used.")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "__else_ok2" (.lit (.bool true)))
                  (.seq
                    (.tryCatch
                      (.assign
                        "key"
                        (.call "next" [(.call "iter" [(.field (.name "self") "_LRUCache__order")])]))
                      "__exc"
                      (.seq
                        (.assign "__else_ok2" (.lit (.bool false)))
                        (.raise
                          (.call
                            "KeyError"
                            [ (.binop
                                "%"
                                (.lit (.str "%s is empty"))
                                (.field (.call "type" [(.name "self")]) "__name__")) ]))))
                    (.ifte
                      (.name "__else_ok2")
                      (.ret
                        (.tupleE [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                      .skip)))
                (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>.LRUCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache.clear"
  , params := []
  , body := (.seq
            (.expr (.mcall (.name "Cache") "clear" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_LRUCache__order"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.LRUCache._LRUCache__touch`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__LRUCache__LRUCache__touch : Func :=
  { name := "cachetools/__init__.py:<module>.LRUCache._LRUCache__touch"
  , params := ["key"]
  , body := (.seq
            (.expr (.lit (.str "Mark as recently used")))
            (.seq
              .skip
              (.tryCatch
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_LRUCache__order"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                "__exc"
                (.setIndex (.field (.name "self") "_LRUCache__order") (.name "key") (.lit .unit))))) }

/-- `cachetools/__init__.py:<module>.RRCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.__init__"
  , params := ["maxsize", "choice", "getsizeof"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField (.name "self") "_RRCache__choice" (.name "choice"))
              (.seq
                (.seq
                  (.assign "tmp0" (.dictE []))
                  (.setField (.name "self") "_RRCache__index" (.name "tmp0")))
                (.seq (.setField (.name "self") "_RRCache__keys" (.listE [])) (.seq .skip .skip))))) }

/-- `cachetools/__init__.py:<module>.RRCache.choice`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache_choice : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.choice"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "The `choice` function used by the cache.")))
            (.ret (.field (.name "self") "_RRCache__choice"))) }

/-- `cachetools/__init__.py:<module>.RRCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , body := (.seq
            (.expr (.call "cache_setitem" [(.name "self"), (.name "key"), (.name "value")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.inOp true (.name "key") (.field (.name "self") "_RRCache__index"))
                  (.seq
                    (.setIndex
                      (.field (.name "self") "_RRCache__index")
                      (.name "key")
                      (.call "len" [(.field (.name "self") "_RRCache__keys")]))
                    (.seq
                      (.assign "tmp0" (.field (.name "self") "_RRCache__keys"))
                      (.expr (.mcall (.name "tmp0") "append" [(.name "key")]))))
                  .skip)
                .skip))) }

/-- `cachetools/__init__.py:<module>.RRCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , body := (.seq
            (.expr (.call "cache_delitem" [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_RRCache__index"))
                  (.assign "index" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.ifte
                      (.binop
                        "!="
                        (.name "index")
                        (.binop
                          "-"
                          (.call "len" [(.field (.name "self") "_RRCache__keys")])
                          (.lit (.int 1))))
                      (.seq
                        (.assign
                          "last"
                          (.index
                            (.field (.name "self") "_RRCache__keys")
                            (.unop "-" (.lit (.int 1)))))
                        (.seq
                          (.setIndex
                            (.field (.name "self") "_RRCache__keys")
                            (.name "index")
                            (.name "last"))
                          (.setIndex
                            (.field (.name "self") "_RRCache__index")
                            (.name "last")
                            (.name "index"))))
                      .skip)
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "tmp1" (.field (.name "self") "_RRCache__keys"))
                          (.expr (.mcall (.name "tmp1") "pop" [])))
                        (.seq .skip .skip)))))))) }

/-- `cachetools/__init__.py:<module>.RRCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.popitem"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "Remove and return a random `(key, value)` pair.")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "__else_ok3" (.lit (.bool true)))
                  (.seq
                    (.tryCatch
                      (.assign
                        "key"
                        (.mcall
                          (.name "self")
                          "_RRCache__choice"
                          [(.field (.name "self") "_RRCache__keys")]))
                      "__exc"
                      (.seq
                        (.assign "__else_ok3" (.lit (.bool false)))
                        (.raise
                          (.call
                            "KeyError"
                            [ (.binop
                                "%"
                                (.lit (.str "%s is empty"))
                                (.field (.call "type" [(.name "self")]) "__name__")) ]))))
                    (.ifte
                      (.name "__else_ok3")
                      (.ret
                        (.tupleE [(.name "key"), (.mcall (.name "self") "pop" [(.name "key")])]))
                      .skip)))
                (.seq .skip .skip)))) }

/-- `cachetools/__init__.py:<module>.RRCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__RRCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.RRCache.clear"
  , params := []
  , body := (.seq
            (.expr (.mcall (.name "Cache") "clear" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_RRCache__index"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                (.seq .skip (.hole "op:delete-slice"))))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___init__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__init__"
  , params := ["timer"]
  , body := (.seq
            (.setField (.name "self") "_Timer__timer" (.name "timer"))
            (.setField (.name "self") "_Timer__nesting" (.lit (.int 0)))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__call__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___call__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__call__"
  , params := []
  , body := (.ifte
            (.binop "==" (.field (.name "self") "_Timer__nesting") (.lit (.int 0)))
            (.ret (.mcall (.name "self") "_Timer__timer" []))
            (.ret (.field (.name "self") "_Timer__time"))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__enter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___enter__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__enter__"
  , params := []
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "self") "_Timer__nesting") (.lit (.int 0)))
              (.seq
                (.assign "tmp0" (.mcall (.name "self") "_Timer__timer" []))
                (.seq
                  (.setField (.name "self") "_Timer__time" (.name "tmp0"))
                  (.assign "time" (.name "tmp0"))))
              (.assign "time" (.field (.name "self") "_Timer__time")))
            (.seq
              .skip
              (.seq
                (.setField
                  (.name "self")
                  "_Timer__nesting"
                  (.binop "+" (.field (.name "self") "_Timer__nesting") (.lit (.int 1))))
                (.seq .skip (.ret (.name "time")))))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__exit__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___exit__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__"
  , params := ["exc"]
  , vararg := some "exc"
  , body := (.setField
            (.name "self")
            "_Timer__nesting"
            (.binop "-" (.field (.name "self") "_Timer__nesting") (.lit (.int 1)))) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__reduce__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___reduce__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__reduce__"
  , params := []
  , body := (.seq
            (.ret
              (.tupleE
                [ (.fnref "cachetools/__init__.py:<module>._TimedCache._Timer")
                , (.tupleE [(.field (.name "self") "_Timer__timer")]) ]))
            .skip) }

/-- `cachetools/__init__.py:<module>._TimedCache._Timer.__getattr__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache__Timer___getattr__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache._Timer.__getattr__"
  , params := ["name"]
  , body := (.seq
            (.ret (.call "getattr" [(.field (.name "self") "_Timer__timer"), (.name "name")]))
            .skip) }

/-- `cachetools/__init__.py:<module>._TimedCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.__init__"
  , params := ["maxsize", "timer", "getsizeof"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "Cache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "getsizeof")]))
            (.seq
              (.setField
                (.name "self")
                "_TimedCache__timer"
                (.mcall (.name "_TimedCache") "_Timer" [(.name "timer")]))
              (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>._TimedCache.__repr__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache___repr__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.__repr__"
  , params := ["cache_repr"]
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.ret (.call "cache_repr" [(.name "self")]))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.__len__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache___len__ : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.__len__"
  , params := ["cache_len"]
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.ret (.call "cache_len" [(.name "self")]))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.currsize`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_currsize : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.currsize"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.ret (.field (.call "super" []) "currsize"))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.timer`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_timer : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.timer"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "The timer function used by the cache.")))
            (.ret (.field (.name "self") "_TimedCache__timer"))) }

/-- `cachetools/__init__.py:<module>._TimedCache.get`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_get : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.get"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.mcall
                          (.name "Cache")
                          "get"
                          [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.pop`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_pop : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.pop"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.mcall
                          (.name "Cache")
                          "pop"
                          [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.setdefault`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_setdefault : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.setdefault"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "_TimedCache__timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.mcall
                          (.name "Cache")
                          "setdefault"
                          [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/__init__.py:<module>._TimedCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.clear"
  , params := []
  , body := (.seq (.expr (.mcall (.name "Cache") "clear" [(.name "self")])) .skip) }

/-- `cachetools/__init__.py:<module>._TimedCache.expire`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module___TimedCache_expire : Func :=
  { name := "cachetools/__init__.py:<module>._TimedCache.expire"
  , params := ["time"]
  , body := (.seq (.raise (.name "NotImplementedError")) .skip) }

/-- `cachetools/__init__.py:<module>.TTLCache._Link.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__Link___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._Link.__init__"
  , params := ["key", "expires"]
  , body := (.seq
            (.setField (.name "self") "key" (.name "key"))
            (.setField (.name "self") "expires" (.name "expires"))) }

/-- `cachetools/__init__.py:<module>.TTLCache._Link.__reduce__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__Link___reduce__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._Link.__reduce__"
  , params := []
  , body := (.seq
            (.ret
              (.tupleE
                [ (.fnref "cachetools/__init__.py:<module>.TTLCache._Link")
                , (.tupleE [(.field (.name "self") "key"), (.field (.name "self") "expires")]) ]))
            .skip) }

/-- `cachetools/__init__.py:<module>.TTLCache._Link.unlink`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__Link_unlink : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._Link.unlink"
  , params := []
  , body := (.seq
            (.assign "next" (.field (.name "self") "next"))
            (.seq
              (.assign "prev" (.field (.name "self") "prev"))
              (.seq
                (.setField (.name "prev") "next" (.name "next"))
                (.seq .skip (.seq (.setField (.name "next") "prev" (.name "prev")) .skip))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__init__"
  , params := ["maxsize", "ttl", "timer", "getsizeof"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "_TimedCache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "timer"), (.name "getsizeof")]))
            (.seq
              (.seq
                (.assign "tmp0" (.mcall (.name "TTLCache") "_Link" []))
                (.seq
                  (.setField (.name "self") "_TTLCache__root" (.name "tmp0"))
                  (.assign "root" (.name "tmp0"))))
              (.seq
                (.seq
                  (.assign "tmp1" (.name "root"))
                  (.seq
                    (.setField (.name "root") "prev" (.name "tmp1"))
                    (.setField (.name "root") "next" (.name "tmp1"))))
                (.seq
                  (.setField (.name "self") "_TTLCache__links" (.alloc "OrderedDict" []))
                  (.seq
                    .skip
                    (.seq
                      (.setField (.name "self") "_TTLCache__ttl" (.name "ttl"))
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__contains__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___contains__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__contains__"
  , params := ["key"]
  , body := (.seq
            (.seq
              (.assign "__else_ok4" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign "link" (.index (.field (.name "self") "_TTLCache__links") (.name "key")))
                  "__exc"
                  (.seq (.assign "__else_ok4" (.lit (.bool false))) (.ret (.lit (.bool false)))))
                (.ifte
                  (.name "__else_ok4")
                  (.ret
                    (.binop
                      "<"
                      (.mcall (.name "self") "timer" [])
                      (.field (.name "link") "expires")))
                  .skip)))
            .skip) }

/-- `cachetools/__init__.py:<module>.TTLCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , body := (.seq
            (.seq
              (.assign "__else_ok5" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign "link" (.mcall (.name "self") "_TTLCache__getlink" [(.name "key")]))
                  "__exc"
                  (.seq
                    (.assign "__else_ok5" (.lit (.bool false)))
                    (.assign "expired" (.lit (.bool false)))))
                (.ifte
                  (.name "__else_ok5")
                  (.assign
                    "expired"
                    (.unop
                      "!"
                      (.binop
                        "<"
                        (.mcall (.name "self") "timer" [])
                        (.field (.name "link") "expires"))))
                  .skip)))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "expired")
                  (.ret (.mcall (.name "self") "__missing__" [(.name "key")]))
                  (.ret (.call "cache_getitem" [(.name "self"), (.name "key")])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.expr
                            (.call "cache_setitem" [(.name "self"), (.name "key"), (.name "value")]))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              (.seq
                (.assign "__else_ok6" (.lit (.bool true)))
                (.seq
                  (.tryCatch
                    (.assign "link" (.mcall (.name "self") "_TTLCache__getlink" [(.name "key")]))
                    "__exc"
                    (.seq
                      (.assign "__else_ok6" (.lit (.bool false)))
                      (.seq
                        (.assign "tmp0" (.mcall (.name "TTLCache") "_Link" [(.name "key")]))
                        (.seq
                          (.setIndex
                            (.field (.name "self") "_TTLCache__links")
                            (.name "key")
                            (.name "tmp0"))
                          (.assign "link" (.name "tmp0"))))))
                  (.ifte (.name "__else_ok6") (.expr (.mcall (.name "link") "unlink" [])) .skip)))
              (.seq
                .skip
                (.seq
                  (.setField
                    (.name "link")
                    "expires"
                    (.binop "+" (.name "time") (.field (.name "self") "_TTLCache__ttl")))
                  (.seq
                    .skip
                    (.seq
                      (.seq
                        (.assign "tmp1" (.field (.name "self") "_TTLCache__root"))
                        (.seq
                          (.setField (.name "link") "next" (.name "tmp1"))
                          (.assign "root" (.name "tmp1"))))
                      (.seq
                        .skip
                        (.seq
                          (.seq
                            (.assign "tmp2" (.field (.name "root") "prev"))
                            (.seq
                              (.setField (.name "link") "prev" (.name "tmp2"))
                              (.assign "prev" (.name "tmp2"))))
                          (.seq
                            .skip
                            (.seq
                              (.seq
                                (.assign "tmp3" (.name "link"))
                                (.seq
                                  (.setField (.name "prev") "next" (.name "tmp3"))
                                  (.setField (.name "root") "prev" (.name "tmp3"))))
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , body := (.seq
            (.expr (.call "cache_delitem" [(.name "self"), (.name "key")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TTLCache__links"))
                  (.assign "link" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.expr (.mcall (.name "link") "unlink" []))
                    (.seq
                      .skip
                      (.ifte
                        (.unop
                          "!"
                          (.binop
                            "<"
                            (.mcall (.name "self") "timer" [])
                            (.field (.name "link") "expires")))
                        (.raise (.call "KeyError" [(.name "key")]))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__iter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___iter__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__iter__"
  , params := []
  , body := (.seq
            (.assign "root" (.field (.name "self") "_TTLCache__root"))
            (.seq
              .skip
              (.seq
                (.assign "curr" (.field (.name "root") "next"))
                (.seq
                  .skip
                  (.seq
                    (.loop
                      (.isOp true (.name "curr") (.name "root"))
                      (.seq
                        (.seq
                          (.assign "manager_tmp0" (.field (.name "self") "timer"))
                          (.seq
                            (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                            (.seq
                              (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp0"
                                  (.mcall (.name "manager_tmp0") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.assign "time" (.name "value_tmp0"))
                                    (.ifte
                                      (.binop "<" (.name "time") (.field (.name "curr") "expires"))
                                      (.ret (.field (.name "curr") "key"))
                                      .skip))
                                  (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                        (.assign "curr" (.field (.name "curr") "next"))))
                    (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__setstate__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___setstate__ : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__setstate__"
  , params := ["state"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "__dict__"))
              (.expr (.mcall (.name "tmp0") "update" [(.name "state")])))
            (.seq
              (.assign "root" (.field (.name "self") "_TTLCache__root"))
              (.seq
                (.seq
                  (.assign "tmp1" (.name "root"))
                  (.seq
                    (.setField (.name "root") "prev" (.name "tmp1"))
                    (.setField (.name "root") "next" (.name "tmp1"))))
                (.seq
                  (.seq
                    (.assign
                      "tmp5"
                      (.call
                        "sorted"
                        [ (.mcall (.field (.name "self") "_TTLCache__links") "values" [])
                        , (.kwargE
                            "key"
                            (.fnref
                              "cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0")) ]))
                    (.forIn
                      "link"
                      (.name "tmp5")
                      (.seq
                        (.setField (.name "link") "next" (.name "root"))
                        (.seq
                          (.seq
                            (.assign "tmp2" (.field (.name "root") "prev"))
                            (.seq
                              (.setField (.name "link") "prev" (.name "tmp2"))
                              (.assign "prev" (.name "tmp2"))))
                          (.seq
                            (.assign "tmp3" (.name "link"))
                            (.seq
                              (.setField (.name "prev") "next" (.name "tmp3"))
                              (.setField (.name "root") "prev" (.name "tmp3"))))))))
                  (.seq
                    .skip
                    (.seq
                      (.expr (.mcall (.name "self") "expire" [(.mcall (.name "self") "timer" [])]))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache___setstate____lambda_0 : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0"
  , params := ["obj"]
  , body := (.ret (.field (.name "obj") "expires")) }

/-- `cachetools/__init__.py:<module>.TTLCache.ttl`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_ttl : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.ttl"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "The time-to-live value of the cache's items.")))
            (.ret (.field (.name "self") "_TTLCache__ttl"))) }

/-- `cachetools/__init__.py:<module>.TTLCache.expire`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_expire : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.expire"
  , params := ["time"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove expired items from the cache and return an iterable of the\n        expired `(key, value)` pairs.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "time") (.lit .unit))
                  (.assign "time" (.mcall (.name "self") "timer" []))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "root" (.field (.name "self") "_TTLCache__root"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "curr" (.field (.name "root") "next"))
                        (.seq
                          .skip
                          (.seq
                            (.assign "links" (.field (.name "self") "_TTLCache__links"))
                            (.seq
                              .skip
                              (.seq
                                (.assign "expired" (.listE []))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "cache_delitem"
                                      (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "cache_getitem"
                                        (.fnref "cachetools/__init__.py:<module>.Cache.__getitem__"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.loop
                                        (.binop
                                        "&&"
                                        (.isOp true (.name "curr") (.name "root"))
                                        (.unop
                                        "!"
                                        (.binop
                                        "<"
                                        (.name "time")
                                        (.field (.name "curr") "expires"))))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "expired")
                                        "append"
                                        [ (.tupleE
                                        [ (.field (.name "curr") "key")
                                        , (.call
                                        "cache_getitem"
                                        [(.name "self"), (.field (.name "curr") "key")]) ]) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "cache_delitem"
                                        [(.name "self"), (.field (.name "curr") "key")]))
                                        (.seq
                                        (.hole "op:delete-index")
                                        (.seq
                                        (.assign "next" (.field (.name "curr") "next"))
                                        (.seq
                                        (.expr (.mcall (.name "curr") "unlink" []))
                                        (.assign "curr" (.name "next"))))))))
                                        (.ret (.name "expired"))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.popitem"
  , params := []
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove and return the `(key, value)` pair least recently used that\n        has not already expired.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.field (.name "self") "timer"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.assign "time" (.name "value_tmp0"))
                            (.seq
                              (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                              (.seq
                                (.assign "__else_ok7" (.lit (.bool true)))
                                (.seq
                                  (.tryCatch
                                    (.assign
                                      "key"
                                      (.call
                                        "next"
                                        [ (.call "iter" [(.field (.name "self") "_TTLCache__links")]) ]))
                                    "__exc"
                                    (.seq
                                      (.assign "__else_ok7" (.lit (.bool false)))
                                      (.raise
                                        (.call
                                        "KeyError"
                                        [ (.binop
                                        "%"
                                        (.lit (.str "%s is empty"))
                                        (.field (.call "type" [(.name "self")]) "__name__")) ]))))
                                  (.ifte
                                    (.name "__else_ok7")
                                    (.ret
                                      (.tupleE
                                        [ (.name "key")
                                        , (.mcall (.name "self") "pop" [(.name "key")]) ]))
                                    .skip)))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache.clear"
  , params := []
  , body := (.seq
            (.expr (.mcall (.name "_TimedCache") "clear" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign "root" (.field (.name "self") "_TTLCache__root"))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp0" (.name "root"))
                      (.seq
                        (.setField (.name "root") "prev" (.name "tmp0"))
                        (.setField (.name "root") "next" (.name "tmp0"))))
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "tmp1" (.field (.name "self") "_TTLCache__links"))
                          (.expr (.mcall (.name "tmp1") "clear" [])))
                        .skip))))))) }

/-- `cachetools/__init__.py:<module>.TTLCache._TTLCache__getlink`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TTLCache__TTLCache__getlink : Func :=
  { name := "cachetools/__init__.py:<module>.TTLCache._TTLCache__getlink"
  , params := ["key"]
  , body := (.seq
            (.assign "value" (.index (.field (.name "self") "_TTLCache__links") (.name "key")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TTLCache__links"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                (.seq .skip (.ret (.name "value")))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._Item.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__Item___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._Item.__init__"
  , params := ["key", "expires"]
  , body := (.seq
            (.setField (.name "self") "key" (.name "key"))
            (.seq
              (.setField (.name "self") "expires" (.name "expires"))
              (.setField (.name "self") "removed" (.lit (.bool false))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._Item.__lt__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__Item___lt__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._Item.__lt__"
  , params := ["other"]
  , body := (.ret (.binop "<" (.field (.name "self") "expires") (.field (.name "other") "expires"))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__init__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___init__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__init__"
  , params := ["maxsize", "ttu", "timer", "getsizeof"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "_TimedCache")
                "__init__"
                [(.name "self"), (.name "maxsize"), (.name "timer"), (.name "getsizeof")]))
            (.seq
              (.setField (.name "self") "_TLRUCache__items" (.alloc "OrderedDict" []))
              (.seq
                (.setField (.name "self") "_TLRUCache__order" (.listE []))
                (.seq (.setField (.name "self") "_TLRUCache__ttu" (.name "ttu")) (.seq .skip .skip))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__contains__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___contains__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__contains__"
  , params := ["key"]
  , body := (.seq
            (.seq
              (.assign "__else_ok8" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign
                    "item"
                    (.index (.field (.name "self") "_TLRUCache__items") (.name "key")))
                  "__exc"
                  (.seq (.assign "__else_ok8" (.lit (.bool false))) (.ret (.lit (.bool false)))))
                (.ifte
                  (.name "__else_ok8")
                  (.ret
                    (.binop
                      "<"
                      (.mcall (.name "self") "timer" [])
                      (.field (.name "item") "expires")))
                  .skip)))
            .skip) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__getitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___getitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__getitem__"
  , params := ["key", "cache_getitem"]
  , body := (.seq
            (.seq
              (.assign "__else_ok9" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.assign "item" (.mcall (.name "self") "_TLRUCache__getitem" [(.name "key")]))
                  "__exc"
                  (.seq
                    (.assign "__else_ok9" (.lit (.bool false)))
                    (.assign "expired" (.lit (.bool false)))))
                (.ifte
                  (.name "__else_ok9")
                  (.assign
                    "expired"
                    (.unop
                      "!"
                      (.binop
                        "<"
                        (.mcall (.name "self") "timer" [])
                        (.field (.name "item") "expires"))))
                  .skip)))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "expired")
                  (.ret (.mcall (.name "self") "__missing__" [(.name "key")]))
                  (.ret (.call "cache_getitem" [(.name "self"), (.name "key")])))
                .skip))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__setitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___setitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__setitem__"
  , params := ["key", "value", "cache_setitem"]
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.seq
                          (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                          (.seq
                            (.assign
                              "expires"
                              (.mcall
                                (.name "self")
                                "_TLRUCache__ttu"
                                [(.name "key"), (.name "value"), (.name "time")]))
                            (.seq
                              (.ifte
                                (.unop "!" (.binop "<" (.name "time") (.name "expires")))
                                (.ret (.mcall (.name "self") "_TLRUCache__delitem" [(.name "key")]))
                                .skip)
                              (.expr
                                (.call
                                  "cache_setitem"
                                  [(.name "self"), (.name "key"), (.name "value")]))))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              (.tryCatch
                (.setField
                  (.mcall (.name "self") "_TLRUCache__getitem" [(.name "key")])
                  "removed"
                  (.lit (.bool true)))
                "__exc"
                .skip)
              (.seq
                .skip
                (.seq
                  (.seq
                    (.assign
                      "tmp0"
                      (.mcall (.name "TLRUCache") "_Item" [(.name "key"), (.name "expires")]))
                    (.seq
                      (.setIndex
                        (.field (.name "self") "_TLRUCache__items")
                        (.name "key")
                        (.name "tmp0"))
                      (.assign "item" (.name "tmp0"))))
                  (.seq
                    .skip
                    (.seq
                      (.expr
                        (.mcall
                          (.name "heapq")
                          "heappush"
                          [(.field (.name "self") "_TLRUCache__order"), (.name "item")]))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__delitem__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___delitem__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__delitem__"
  , params := ["key", "cache_delitem"]
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "timer"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.assign "time" (.name "value_tmp0"))
                        (.expr (.call "cache_delitem" [(.name "self"), (.name "key")])))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TLRUCache__items"))
                  (.assign "item" (.mcall (.name "tmp0") "pop" [(.name "key")])))
                (.seq
                  .skip
                  (.seq
                    (.setField (.name "item") "removed" (.lit (.bool true)))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.unop "!" (.binop "<" (.name "time") (.field (.name "item") "expires")))
                          (.raise (.call "KeyError" [(.name "key")]))
                          .skip)
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.__iter__`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache___iter__ : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.__iter__"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp1" (.field (.name "self") "_TLRUCache__order"))
              (.forIn
                "curr"
                (.name "tmp1")
                (.seq
                  (.assign "manager_tmp0" (.field (.name "self") "timer"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.assign "time" (.name "value_tmp0"))
                            (.ifte
                              (.binop
                                "&&"
                                (.binop "<" (.name "time") (.field (.name "curr") "expires"))
                                (.unop "!" (.field (.name "curr") "removed")))
                              (.ret (.field (.name "curr") "key"))
                              .skip))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.ttu`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_ttu : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.ttu"
  , params := []
  , body := (.seq
            (.expr (.lit (.str "The local time-to-use function used by the cache.")))
            (.ret (.field (.name "self") "_TLRUCache__ttu"))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.expire`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_expire : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.expire"
  , params := ["time"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove expired items from the cache and return an iterable of the\n        expired `(key, value)` pairs.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "time") (.lit .unit))
                  (.assign "time" (.mcall (.name "self") "timer" []))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "items" (.field (.name "self") "_TLRUCache__items"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "order" (.field (.name "self") "_TLRUCache__order"))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop
                                ">"
                                (.call "len" [(.name "order")])
                                (.binop
                                  "*"
                                  (.call "len" [(.name "items")])
                                  (.field (.name "self") "_TLRUCache__HEAP_CLEANUP_FACTOR")))
                              (.seq
                                (.seq
                                  (.seq
                                    (.assign "tmp0" (.listE []))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.forIn
                                        "item"
                                        (.name "order")
                                        (.seq
                                        (.ifte
                                        (.unop "!" (.unop "!" (.field (.name "item") "removed")))
                                        .cont
                                        .skip)
                                        (.expr (.mcall (.name "tmp0") "append" [(.name "item")]))))
                                        (.assign "tmp2" (.name "tmp0")))))
                                  (.seq
                                    (.setField (.name "self") "_TLRUCache__order" (.name "tmp2"))
                                    (.assign "order" (.name "tmp2"))))
                                (.expr (.mcall (.name "heapq") "heapify" [(.name "order")])))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.assign "expired" (.listE []))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "cache_delitem"
                                      (.fnref "cachetools/__init__.py:<module>.Cache.__delitem__"))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "cache_getitem"
                                        (.fnref "cachetools/__init__.py:<module>.Cache.__getitem__"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.loop
                                        (.binop
                                        "&&"
                                        (.name "order")
                                        (.binop
                                        "||"
                                        (.field (.index (.name "order") (.lit (.int 0))) "removed")
                                        (.unop
                                        "!"
                                        (.binop
                                        "<"
                                        (.name "time")
                                        (.field (.index (.name "order") (.lit (.int 0))) "expires")))))
                                        (.seq
                                        (.assign
                                        "item"
                                        (.mcall (.name "heapq") "heappop" [(.name "order")]))
                                        (.ifte
                                        (.unop "!" (.field (.name "item") "removed"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "expired")
                                        "append"
                                        [ (.tupleE
                                        [ (.field (.name "item") "key")
                                        , (.call
                                        "cache_getitem"
                                        [(.name "self"), (.field (.name "item") "key")]) ]) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "cache_delitem"
                                        [(.name "self"), (.field (.name "item") "key")]))
                                        (.hole "op:delete-index")))
                                        .skip)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ret (.name "expired"))
                                        (.seq .skip (.seq .skip .skip))))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.popitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_popitem : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.popitem"
  , params := []
  , body := (.seq
            (.expr
              (.lit
                (.str "Remove and return the `(key, value)` pair least recently used that\n        has not already expired.\n\n        ")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.field (.name "self") "timer"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.assign "time" (.name "value_tmp0"))
                            (.seq
                              (.expr (.mcall (.name "self") "expire" [(.name "time")]))
                              (.seq
                                (.assign "__else_ok10" (.lit (.bool true)))
                                (.seq
                                  (.tryCatch
                                    (.assign
                                      "key"
                                      (.call
                                        "next"
                                        [ (.call "iter" [(.field (.name "self") "_TLRUCache__items")]) ]))
                                    "__exc"
                                    (.seq
                                      (.assign "__else_ok10" (.lit (.bool false)))
                                      (.raise
                                        (.call
                                        "KeyError"
                                        [ (.binop
                                        "%"
                                        (.lit (.str "%s is empty"))
                                        (.field (.call "type" [(.name "self")]) "__name__")) ]))))
                                  (.ifte
                                    (.name "__else_ok10")
                                    (.ret
                                      (.tupleE
                                        [ (.name "key")
                                        , (.mcall (.name "self") "pop" [(.name "key")]) ]))
                                    .skip)))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache.clear`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache_clear : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache.clear"
  , params := []
  , body := (.seq
            (.expr (.mcall (.name "_TimedCache") "clear" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TLRUCache__items"))
                  (.expr (.mcall (.name "tmp0") "clear" [])))
                (.seq .skip (.hole "op:delete-slice"))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._TLRUCache__getitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__TLRUCache__getitem : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._TLRUCache__getitem"
  , params := ["key"]
  , body := (.seq
            (.assign "value" (.index (.field (.name "self") "_TLRUCache__items") (.name "key")))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp0" (.field (.name "self") "_TLRUCache__items"))
                  (.expr (.mcall (.name "tmp0") "move_to_end" [(.name "key")])))
                (.seq .skip (.ret (.name "value")))))) }

/-- `cachetools/__init__.py:<module>.TLRUCache._TLRUCache__delitem`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__TLRUCache__TLRUCache__delitem : Func :=
  { name := "cachetools/__init__.py:<module>.TLRUCache._TLRUCache__delitem"
  , params := ["key", "cache_delitem"]
  , body := (.seq
            (.seq
              (.assign "__else_ok11" (.lit (.bool true)))
              (.seq
                (.tryCatch
                  (.setField
                    (.mcall (.field (.name "self") "_TLRUCache__items") "pop" [(.name "key")])
                    "removed"
                    (.lit (.bool true)))
                  "__exc"
                  (.seq (.assign "__else_ok11" (.lit (.bool false))) .skip))
                (.ifte
                  (.name "__else_ok11")
                  (.expr (.call "cache_delitem" [(.name "self"), (.name "key")]))
                  .skip)))
            .skip) }

/-- `cachetools/__init__.py:<module>.cached`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached : Func :=
  { name := "cachetools/__init__.py:<module>.cached"
  , params := ["cache", "key", "lock", "condition", "info"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    results in a cache.\n\n    ")))
            (.seq
              (.assign "_wrapper" (.fnref "cachetools/_cached.py:<module>._wrapper"))
              (.seq
                (.assign "decorator" (.closure "cachetools/__init__.py:<module>.cached.decorator"))
                (.seq
                  .skip
                  (.seq
                    (.ret (.name "decorator"))
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/__init__.py:<module>.cached.decorator`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator"
  , params := ["func"]
  , body := (.seq
            (.ifte
              (.name "info")
              (.seq
                (.ifte
                  (.call "isinstance" [(.name "cache"), (.name "Cache")])
                  (.assign
                    "make_info"
                    (.closure
                      "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>0"))
                  (.ifte
                    (.call
                      "isinstance"
                      [(.name "cache"), (.field (.field (.name "collections") "abc") "Mapping")])
                    (.assign
                      "make_info"
                      (.closure
                        "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>1"))
                    (.assign
                      "make_info"
                      (.fnref "cachetools/__init__.py:<module>.cached.decorator.make_info"))))
                (.ret
                  (.call
                    "cachetools/_cachedmethod.py:<module>._wrapper"
                    [ (.name "func")
                    , (.name "cache")
                    , (.name "key")
                    , (.name "lock")
                    , (.name "condition")
                    , (.kwargE "info" (.name "make_info")) ])))
              (.ret
                (.call
                  "cachetools/_cachedmethod.py:<module>._wrapper"
                  [ (.name "func")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "condition") ])))
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>0`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator_make_info_redefined_0 : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>0"
  , params := ["hits", "misses"]
  , body := (.seq
            (.ret
              (.call
                "_CacheInfo"
                [ (.name "hits")
                , (.name "misses")
                , (.field (.name "cache") "maxsize")
                , (.field (.name "cache") "currsize") ]))
            (.seq .skip .skip)) }

/-- `cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>1`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator_make_info_redefined_1 : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator.make_info<redefined>1"
  , params := ["hits", "misses"]
  , body := (.seq
            (.ret
              (.call
                "_CacheInfo"
                [(.name "hits"), (.name "misses"), (.lit .unit), (.call "len" [(.name "cache")])]))
            (.seq .skip (.seq .skip .skip))) }

/-- `cachetools/__init__.py:<module>.cached.decorator.make_info`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cached_decorator_make_info : Func :=
  { name := "cachetools/__init__.py:<module>.cached.decorator.make_info"
  , params := ["hits", "misses"]
  , body := (.seq
            (.ret
              (.call
                "_CacheInfo"
                [(.name "hits"), (.name "misses"), (.lit (.int 0)), (.lit (.int 0))]))
            .skip) }

/-- `cachetools/__init__.py:<module>.cachedmethod`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cachedmethod : Func :=
  { name := "cachetools/__init__.py:<module>.cachedmethod"
  , params := ["cache", "key", "lock", "condition", "info"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a method with a memoizing callable that saves\n    results in a cache.\n\n    ")))
            (.seq
              (.assign "_wrapper" (.fnref "cachetools/_cachedmethod.py:<module>._wrapper"))
              (.seq
                (.assign
                  "decorator"
                  (.closure "cachetools/__init__.py:<module>.cachedmethod.decorator"))
                (.seq
                  .skip
                  (.seq
                    (.ret (.name "decorator"))
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/__init__.py:<module>.cachedmethod.decorator`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cachedmethod_decorator : Func :=
  { name := "cachetools/__init__.py:<module>.cachedmethod.decorator"
  , params := ["method"]
  , body := (.seq
            (.ifte
              (.name "info")
              (.seq
                (.assign
                  "make_info"
                  (.fnref "cachetools/__init__.py:<module>.cachedmethod.decorator.make_info"))
                (.ret
                  (.call
                    "cachetools/_cachedmethod.py:<module>._wrapper"
                    [ (.name "method")
                    , (.name "cache")
                    , (.name "key")
                    , (.name "lock")
                    , (.name "condition")
                    , (.kwargE "info" (.name "make_info")) ])))
              (.ret
                (.call
                  "cachetools/_cachedmethod.py:<module>._wrapper"
                  [ (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "condition") ])))
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))) }

/-- `cachetools/__init__.py:<module>.cachedmethod.decorator.make_info`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module__cachedmethod_decorator_make_info : Func :=
  { name := "cachetools/__init__.py:<module>.cachedmethod.decorator.make_info"
  , params := ["cache", "hits", "misses"]
  , body := (.seq
            (.ifte
              (.call "isinstance" [(.name "cache"), (.name "Cache")])
              (.ret
                (.call
                  "_CacheInfo"
                  [ (.name "hits")
                  , (.name "misses")
                  , (.field (.name "cache") "maxsize")
                  , (.field (.name "cache") "currsize") ]))
              (.ifte
                (.call
                  "isinstance"
                  [(.name "cache"), (.field (.field (.name "collections") "abc") "Mapping")])
                (.ret
                  (.call
                    "_CacheInfo"
                    [ (.name "hits")
                    , (.name "misses")
                    , (.lit .unit)
                    , (.call "len" [(.name "cache")]) ]))
                (.raise
                  (.call "TypeError" [(.lit (.str "cache(self) must return a mutable mapping"))]))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cached.py:<module>._condition_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info"
  , params := ["func", "cache", "key", "lock", "cond", "info"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.lit (.int 0)))
              (.seq (.assign "hits" (.name "tmp0")) (.assign "misses" (.name "tmp0"))))
            (.seq
              (.assign "pending" (.call "set" []))
              (.seq
                (.assign
                  "wrapper"
                  (.closure "cachetools/_cached.py:<module>._condition_info.wrapper"))
                (.seq
                  (.assign
                    "cache_clear"
                    (.closure "cachetools/_cached.py:<module>._condition_info.cache_clear"))
                  (.seq
                    (.assign
                      "cache_info"
                      (.closure "cachetools/_cached.py:<module>._condition_info.cache_info"))
                    (.seq
                      (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                      (.seq
                        (.setField (.name "wrapper") "cache_info" (.name "cache_info"))
                        (.seq
                          .skip
                          (.seq
                            (.ret (.name "wrapper"))
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))) }

/-- `cachetools/_cached.py:<module>._condition_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.hole "scope:nonlocal-write")
            (.seq
              (.assign "k" (.call "key" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.expr
                              (.mcall
                                (.name "cond")
                                "wait_for"
                                [ (.closure
                                    "cachetools/_cached.py:<module>._condition_info.wrapper.<lambda>0") ]))
                            (.tryCatch
                              (.seq
                                (.assign "result" (.index (.name "cache") (.name "k")))
                                (.seq
                                  (.assign "hits" (.binop "+" (.name "hits") (.lit (.int 1))))
                                  (.ret (.name "result"))))
                              "__exc"
                              (.seq
                                (.expr (.mcall (.name "pending") "add" [(.name "k")]))
                                (.assign "misses" (.binop "+" (.name "misses") (.lit (.int 1)))))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    (.tryFinally
                      (.seq
                        (.assign
                          "v"
                          (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                        (.seq
                          (.assign "manager_tmp1" (.name "lock"))
                          (.seq
                            (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                            (.seq
                              (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp1"
                                  (.mcall (.name "manager_tmp1") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.tryCatch
                                      (.setIndex (.name "cache") (.name "k") (.name "v"))
                                      "__exc"
                                      .skip)
                                    (.ret (.name "v")))
                                  (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                      (.seq
                        (.assign "manager_tmp2" (.name "lock"))
                        (.seq
                          (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                          (.seq
                            (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                            (.seq
                              (.assign "value_tmp2" (.mcall (.name "manager_tmp2") "__enter__" []))
                              (.tryFinally
                                (.seq
                                  (.expr (.mcall (.name "pending") "remove" [(.name "k")]))
                                  (.expr (.mcall (.name "cond") "notify_all" [])))
                                (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._condition_info.wrapper.<lambda>0`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_wrapper__lambda_0 : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.wrapper.<lambda>0"
  , params := []
  , body := (.seq (.ret (.inOp true (.name "k") (.name "pending"))) (.seq .skip .skip)) }

/-- `cachetools/_cached.py:<module>._condition_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.cache_clear"
  , params := []
  , body := (.seq
            (.hole "scope:nonlocal-write")
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.expr (.mcall (.name "cache") "clear" []))
                            (.seq
                              (.assign "tmp0" (.lit (.int 0)))
                              (.seq
                                (.assign "hits" (.name "tmp0"))
                                (.assign "misses" (.name "tmp0")))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cached.py:<module>._condition_info.cache_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_info_cache_info : Func :=
  { name := "cachetools/_cached.py:<module>._condition_info.cache_info"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret (.call "info" [(.name "hits"), (.name "misses")]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info"
  , params := ["func", "cache", "key", "lock", "info"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.lit (.int 0)))
              (.seq (.assign "hits" (.name "tmp0")) (.assign "misses" (.name "tmp0"))))
            (.seq
              (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._locked_info.wrapper"))
              (.seq
                (.assign
                  "cache_clear"
                  (.closure "cachetools/_cached.py:<module>._locked_info.cache_clear"))
                (.seq
                  (.assign
                    "cache_info"
                    (.closure "cachetools/_cached.py:<module>._locked_info.cache_info"))
                  (.seq
                    (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                    (.seq
                      (.setField (.name "wrapper") "cache_info" (.name "cache_info"))
                      (.seq
                        (.ret (.name "wrapper"))
                        (.seq
                          .skip
                          (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.hole "scope:nonlocal-write")
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.call "key" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "manager_tmp0" (.name "lock"))
                      (.seq
                        (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                        (.seq
                          (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                          (.seq
                            (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                            (.tryFinally
                              (.tryCatch
                                (.seq
                                  (.assign "result" (.index (.name "cache") (.name "k")))
                                  (.seq
                                    (.assign "hits" (.binop "+" (.name "hits") (.lit (.int 1))))
                                    (.ret (.name "result"))))
                                "__exc"
                                (.assign "misses" (.binop "+" (.name "misses") (.lit (.int 1)))))
                              (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                        (.seq
                          .skip
                          (.seq
                            (.seq
                              (.assign "manager_tmp1" (.name "lock"))
                              (.seq
                                (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                                (.seq
                                  (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                  (.seq
                                    (.assign
                                      "value_tmp1"
                                      (.mcall (.name "manager_tmp1") "__enter__" []))
                                    (.tryFinally
                                      (.tryCatch
                                        (.ret
                                        (.mcall
                                        (.name "cache")
                                        "setdefault"
                                        [(.name "k"), (.name "v")]))
                                        "__exc"
                                        (.ret (.name "v")))
                                      (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info.cache_clear"
  , params := []
  , body := (.seq
            (.hole "scope:nonlocal-write")
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.expr (.mcall (.name "cache") "clear" []))
                            (.seq
                              (.assign "tmp0" (.lit (.int 0)))
                              (.seq
                                (.assign "hits" (.name "tmp0"))
                                (.assign "misses" (.name "tmp0")))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cached.py:<module>._locked_info.cache_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_info_cache_info : Func :=
  { name := "cachetools/_cached.py:<module>._locked_info.cache_info"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret (.call "info" [(.name "hits"), (.name "misses")]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info"
  , params := ["func", "cache", "key", "info"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.lit (.int 0)))
              (.seq (.assign "hits" (.name "tmp0")) (.assign "misses" (.name "tmp0"))))
            (.seq
              (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._unlocked_info.wrapper"))
              (.seq
                (.assign
                  "cache_clear"
                  (.closure "cachetools/_cached.py:<module>._unlocked_info.cache_clear"))
                (.seq
                  (.assign
                    "cache_info"
                    (.closure "cachetools/_cached.py:<module>._unlocked_info.cache_info"))
                  (.seq
                    (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                    (.seq
                      (.setField (.name "wrapper") "cache_info" (.name "cache_info"))
                      (.seq
                        (.ret (.name "wrapper"))
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.hole "scope:nonlocal-write")
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.call "key" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.tryCatch
                      (.seq
                        (.assign "result" (.index (.name "cache") (.name "k")))
                        (.seq
                          (.assign "hits" (.binop "+" (.name "hits") (.lit (.int 1))))
                          (.ret (.name "result"))))
                      "__exc"
                      (.assign "misses" (.binop "+" (.name "misses") (.lit (.int 1)))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                        (.seq
                          .skip
                          (.seq
                            (.tryCatch
                              (.setIndex (.name "cache") (.name "k") (.name "v"))
                              "__exc"
                              .skip)
                            (.seq .skip (.seq (.ret (.name "v")) (.seq .skip (.seq .skip .skip))))))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info.cache_clear"
  , params := []
  , body := (.seq
            (.hole "scope:nonlocal-write")
            (.seq
              .skip
              (.seq
                (.expr (.mcall (.name "cache") "clear" []))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "tmp0" (.lit (.int 0)))
                      (.seq (.assign "hits" (.name "tmp0")) (.assign "misses" (.name "tmp0"))))
                    (.seq .skip .skip)))))) }

/-- `cachetools/_cached.py:<module>._unlocked_info.cache_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_info_cache_info : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked_info.cache_info"
  , params := []
  , body := (.seq
            (.ret (.call "info" [(.name "hits"), (.name "misses")]))
            (.seq .skip (.seq .skip .skip))) }

/-- `cachetools/_cached.py:<module>._uncached_info`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info"
  , params := ["func", "info"]
  , body := (.seq
            (.assign "misses" (.lit (.int 0)))
            (.seq
              (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._uncached_info.wrapper"))
              (.seq
                (.assign
                  "cache_clear"
                  (.closure "cachetools/_cached.py:<module>._uncached_info.cache_clear"))
                (.seq
                  (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                  (.seq
                    (.setField
                      (.name "wrapper")
                      "cache_info"
                      (.closure "cachetools/_cached.py:<module>._uncached_info.<lambda>1"))
                    (.seq (.ret (.name "wrapper")) (.seq .skip (.seq .skip .skip)))))))) }

/-- `cachetools/_cached.py:<module>._uncached_info.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.hole "scope:nonlocal-write")
            (.seq
              .skip
              (.seq
                (.assign "misses" (.binop "+" (.name "misses") (.lit (.int 1))))
                (.seq
                  .skip
                  (.ret (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))))) }

/-- `cachetools/_cached.py:<module>._uncached_info.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info.cache_clear"
  , params := []
  , body := (.seq (.hole "scope:nonlocal-write") (.seq .skip (.assign "misses" (.lit (.int 0))))) }

/-- `cachetools/_cached.py:<module>._uncached_info.<lambda>1`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_info__lambda_1 : Func :=
  { name := "cachetools/_cached.py:<module>._uncached_info.<lambda>1"
  , params := []
  , body := (.seq (.ret (.call "info" [(.lit (.int 0)), (.name "misses")])) (.seq .skip .skip)) }

/-- `cachetools/_cached.py:<module>._condition`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition : Func :=
  { name := "cachetools/_cached.py:<module>._condition"
  , params := ["func", "cache", "key", "lock", "cond"]
  , body := (.seq
            (.assign "pending" (.call "set" []))
            (.seq
              (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._condition.wrapper"))
              (.seq
                (.assign
                  "cache_clear"
                  (.closure "cachetools/_cached.py:<module>._condition.cache_clear"))
                (.seq
                  (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                  (.seq
                    (.ret (.name "wrapper"))
                    (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cached.py:<module>._condition.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._condition.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign "k" (.call "key" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            (.seq
              (.seq
                (.assign "manager_tmp0" (.name "lock"))
                (.seq
                  (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                  (.seq
                    (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                    (.seq
                      (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                      (.tryFinally
                        (.seq
                          (.expr
                            (.mcall
                              (.name "cond")
                              "wait_for"
                              [ (.closure
                                  "cachetools/_cached.py:<module>._condition.wrapper.<lambda>2") ]))
                          (.tryCatch
                            (.seq
                              (.assign "result" (.index (.name "cache") (.name "k")))
                              (.ret (.name "result")))
                            "__exc"
                            (.expr (.mcall (.name "pending") "add" [(.name "k")]))))
                        (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
              (.seq
                (.tryFinally
                  (.seq
                    (.assign
                      "v"
                      (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                    (.seq
                      (.assign "manager_tmp1" (.name "lock"))
                      (.seq
                        (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                        (.seq
                          (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                          (.seq
                            (.assign "value_tmp1" (.mcall (.name "manager_tmp1") "__enter__" []))
                            (.tryFinally
                              (.seq
                                (.tryCatch
                                  (.setIndex (.name "cache") (.name "k") (.name "v"))
                                  "__exc"
                                  .skip)
                                (.ret (.name "v")))
                              (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                  (.seq
                    (.assign "manager_tmp2" (.name "lock"))
                    (.seq
                      (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                      (.seq
                        (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                        (.seq
                          (.assign "value_tmp2" (.mcall (.name "manager_tmp2") "__enter__" []))
                          (.tryFinally
                            (.seq
                              (.expr (.mcall (.name "pending") "remove" [(.name "k")]))
                              (.expr (.mcall (.name "cond") "notify_all" [])))
                            (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._condition.wrapper.<lambda>2`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_wrapper__lambda_2 : Func :=
  { name := "cachetools/_cached.py:<module>._condition.wrapper.<lambda>2"
  , params := []
  , body := (.seq (.ret (.inOp true (.name "k") (.name "pending"))) (.seq .skip .skip)) }

/-- `cachetools/_cached.py:<module>._condition.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___condition_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._condition.cache_clear"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.expr (.mcall (.name "cache") "clear" []))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cached.py:<module>._locked`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked : Func :=
  { name := "cachetools/_cached.py:<module>._locked"
  , params := ["func", "cache", "key", "lock"]
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._locked.wrapper"))
            (.seq
              (.assign
                "cache_clear"
                (.closure "cachetools/_cached.py:<module>._locked.cache_clear"))
              (.seq
                (.setField (.name "wrapper") "cache_clear" (.name "cache_clear"))
                (.seq (.ret (.name "wrapper")) (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cached.py:<module>._locked.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._locked.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign "k" (.call "key" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.name "lock"))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.tryCatch (.ret (.index (.name "cache") (.name "k"))) "__exc" .skip)
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "v"
                      (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                    (.seq
                      .skip
                      (.seq
                        (.seq
                          (.assign "manager_tmp1" (.name "lock"))
                          (.seq
                            (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                            (.seq
                              (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp1"
                                  (.mcall (.name "manager_tmp1") "__enter__" []))
                                (.tryFinally
                                  (.tryCatch
                                    (.ret
                                      (.mcall
                                        (.name "cache")
                                        "setdefault"
                                        [(.name "k"), (.name "v")]))
                                    "__exc"
                                    (.ret (.name "v")))
                                  (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))) }

/-- `cachetools/_cached.py:<module>._locked.cache_clear`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___locked_cache_clear : Func :=
  { name := "cachetools/_cached.py:<module>._locked.cache_clear"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.name "lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.expr (.mcall (.name "cache") "clear" []))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cached.py:<module>._unlocked`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked"
  , params := ["func", "cache", "key"]
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._unlocked.wrapper"))
            (.seq
              (.setField
                (.name "wrapper")
                "cache_clear"
                (.closure "cachetools/_cached.py:<module>._unlocked.<lambda>3"))
              (.seq (.ret (.name "wrapper")) .skip))) }

/-- `cachetools/_cached.py:<module>._unlocked.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign "k" (.call "key" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            (.seq
              .skip
              (.seq
                (.tryCatch (.ret (.index (.name "cache") (.name "k"))) "__exc" .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "v"
                      (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                    (.seq
                      .skip
                      (.seq
                        (.tryCatch
                          (.setIndex (.name "cache") (.name "k") (.name "v"))
                          "__exc"
                          .skip)
                        (.seq .skip (.seq (.ret (.name "v")) .skip))))))))) }

/-- `cachetools/_cached.py:<module>._unlocked.<lambda>3`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___unlocked__lambda_3 : Func :=
  { name := "cachetools/_cached.py:<module>._unlocked.<lambda>3"
  , params := []
  , body := (.seq (.ret (.mcall (.name "cache") "clear" [])) .skip) }

/-- `cachetools/_cached.py:<module>._uncached`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached : Func :=
  { name := "cachetools/_cached.py:<module>._uncached"
  , params := ["func"]
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cached.py:<module>._uncached.wrapper"))
            (.seq
              (.setField
                (.name "wrapper")
                "cache_clear"
                (.fnref "cachetools/_cached.py:<module>._uncached.<lambda>4"))
              (.seq (.ret (.name "wrapper")) .skip))) }

/-- `cachetools/_cached.py:<module>._uncached.wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached_wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._uncached.wrapper"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.ret (.call "func" [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
            .skip) }

/-- `cachetools/_cached.py:<module>._uncached.<lambda>4`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___uncached__lambda_4 : Func :=
  { name := "cachetools/_cached.py:<module>._uncached.<lambda>4"
  , params := []
  , body := (.ret (.lit .unit)) }

/-- `cachetools/_cached.py:<module>._wrapper`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module___wrapper : Func :=
  { name := "cachetools/_cached.py:<module>._wrapper"
  , params := ["func", "cache", "key", "lock", "cond", "info"]
  , body := (.seq
            (.ifte
              (.isOp true (.name "info") (.lit .unit))
              (.ifte
                (.isOp false (.name "cache") (.lit .unit))
                (.assign
                  "wrapper"
                  (.call
                    "cachetools/_cached.py:<module>._uncached_info"
                    [(.name "func"), (.name "info")]))
                (.ifte
                  (.binop
                    "&&"
                    (.isOp true (.name "cond") (.lit .unit))
                    (.isOp true (.name "lock") (.lit .unit)))
                  (.assign
                    "wrapper"
                    (.call
                      "cachetools/_cached.py:<module>._condition_info"
                      [ (.name "func")
                      , (.name "cache")
                      , (.name "key")
                      , (.name "lock")
                      , (.name "cond")
                      , (.name "info") ]))
                  (.ifte
                    (.isOp true (.name "cond") (.lit .unit))
                    (.assign
                      "wrapper"
                      (.call
                        "cachetools/_cached.py:<module>._condition_info"
                        [ (.name "func")
                        , (.name "cache")
                        , (.name "key")
                        , (.name "cond")
                        , (.name "cond")
                        , (.name "info") ]))
                    (.ifte
                      (.isOp true (.name "lock") (.lit .unit))
                      (.assign
                        "wrapper"
                        (.call
                          "cachetools/_cached.py:<module>._locked_info"
                          [ (.name "func")
                          , (.name "cache")
                          , (.name "key")
                          , (.name "lock")
                          , (.name "info") ]))
                      (.assign
                        "wrapper"
                        (.call
                          "cachetools/_cached.py:<module>._unlocked_info"
                          [(.name "func"), (.name "cache"), (.name "key"), (.name "info")]))))))
              (.seq
                (.ifte
                  (.isOp false (.name "cache") (.lit .unit))
                  (.assign
                    "wrapper"
                    (.call "cachetools/_cached.py:<module>._uncached" [(.name "func")]))
                  (.ifte
                    (.binop
                      "&&"
                      (.isOp true (.name "cond") (.lit .unit))
                      (.isOp true (.name "lock") (.lit .unit)))
                    (.assign
                      "wrapper"
                      (.call
                        "cachetools/_cached.py:<module>._condition"
                        [ (.name "func")
                        , (.name "cache")
                        , (.name "key")
                        , (.name "lock")
                        , (.name "cond") ]))
                    (.ifte
                      (.isOp true (.name "cond") (.lit .unit))
                      (.assign
                        "wrapper"
                        (.call
                          "cachetools/_cached.py:<module>._condition"
                          [ (.name "func")
                          , (.name "cache")
                          , (.name "key")
                          , (.name "cond")
                          , (.name "cond") ]))
                      (.ifte
                        (.isOp true (.name "lock") (.lit .unit))
                        (.assign
                          "wrapper"
                          (.call
                            "cachetools/_cached.py:<module>._locked"
                            [(.name "func"), (.name "cache"), (.name "key"), (.name "lock")]))
                        (.assign
                          "wrapper"
                          (.call
                            "cachetools/_cached.py:<module>._unlocked"
                            [(.name "func"), (.name "cache"), (.name "key")]))))))
                (.setField (.name "wrapper") "cache_info" (.lit .unit))))
            (.seq
              .skip
              (.seq
                (.setField (.name "wrapper") "cache" (.name "cache"))
                (.seq
                  .skip
                  (.seq
                    (.setField (.name "wrapper") "cache_key" (.name "key"))
                    (.seq
                      .skip
                      (.seq
                        (.setField
                          (.name "wrapper")
                          "cache_lock"
                          (.cond
                            (.isOp true (.name "lock") (.lit .unit))
                            (.name "lock")
                            (.name "cond")))
                        (.seq
                          .skip
                          (.seq
                            (.setField (.name "wrapper") "cache_condition" (.name "cond"))
                            (.seq
                              .skip
                              (.seq
                                (.ret
                                  (.mcall
                                    (.name "functools")
                                    "update_wrapper"
                                    [(.name "wrapper"), (.name "func")]))
                                (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._warn_classmethod`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___warn_classmethod : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._warn_classmethod"
  , params := ["stacklevel"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "warnings")
                "warn"
                [ (.lit (.str "decorating class methods with @cachedmethod is deprecated"))
                , (.name "DeprecationWarning")
                , (.kwargE "stacklevel" (.name "stacklevel")) ]))
            (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._warn_instance_dict`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___warn_instance_dict : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._warn_instance_dict"
  , params := ["msg", "stacklevel"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "warnings")
                "warn"
                [ (.name "msg")
                , (.name "DeprecationWarning")
                , (.kwargE "stacklevel" (.name "stacklevel")) ]))
            (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._none`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___none : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._none"
  , params := ["_"]
  , body := (.ret (.lit .unit)) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.__init__"
  , params := ["obj", "method", "cache", "key", "lock", "cond"]
  , body := (.seq
            (.ifte
              (.call "isinstance" [(.name "obj"), (.name "type")])
              (.expr
                (.call
                  "cachetools/_cachedmethod.py:<module>._warn_classmethod"
                  [(.kwargE "stacklevel" (.lit (.int 5)))]))
              .skip)
            (.seq
              (.expr
                (.mcall (.name "functools") "update_wrapper" [(.name "self"), (.name "method")]))
              (.seq
                (.setField (.name "self") "_obj" (.name "obj"))
                (.seq
                  (.setField (.name "self") "_WrapperBase__cache" (.name "cache"))
                  (.seq
                    (.setField
                      (.name "self")
                      "_WrapperBase__key"
                      (.mcall (.name "functools") "partial" [(.name "key"), (.name "obj")]))
                    (.seq
                      (.setField
                        (.name "self")
                        "_WrapperBase__lock"
                        (.cond
                          (.isOp true (.name "lock") (.lit .unit))
                          (.name "lock")
                          (.name "_none")))
                      (.seq
                        .skip
                        (.seq
                          (.setField
                            (.name "self")
                            "_WrapperBase__cond"
                            (.cond
                              (.isOp true (.name "cond") (.lit .unit))
                              (.name "cond")
                              (.name "_none")))
                          (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq (.raise (.call "NotImplementedError" [])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_clear"
  , params := []
  , body := (.seq (.raise (.call "NotImplementedError" [])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache"
  , params := []
  , body := (.ret (.mcall (.name "self") "_WrapperBase__cache" [(.field (.name "self") "_obj")])) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_key`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_key : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_key"
  , params := []
  , body := (.ret (.field (.name "self") "_WrapperBase__key")) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_lock : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock"
  , params := []
  , body := (.ret (.mcall (.name "self") "_WrapperBase__lock" [(.field (.name "self") "_obj")])) }

/-- `cachetools/_cachedmethod.py:<module>._WrapperBase.cache_condition`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___WrapperBase_cache_condition : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_condition"
  , params := []
  , body := (.ret (.mcall (.name "self") "_WrapperBase__cond" [(.field (.name "self") "_obj")])) }

/-- `cachetools/_cachedmethod.py:<module>._DescriptorBase.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DescriptorBase___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DescriptorBase.__init__"
  , params := ["deprecated"]
  , body := (.seq
            (.setField (.name "self") "_DescriptorBase__attrname" (.lit .unit))
            (.setField (.name "self") "_DescriptorBase__deprecated" (.name "deprecated"))) }

/-- `cachetools/_cachedmethod.py:<module>._DescriptorBase.__set_name__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DescriptorBase___set_name__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DescriptorBase.__set_name__"
  , params := ["owner", "name"]
  , body := (.seq
            (.ifte
              (.isOp false (.field (.name "self") "_DescriptorBase__attrname") (.lit .unit))
              (.setField (.name "self") "_DescriptorBase__attrname" (.name "name"))
              (.ifte
                (.binop "!=" (.name "name") (.field (.name "self") "_DescriptorBase__attrname"))
                (.raise (.call "TypeError" [(.hole "op:stringExpressionList")]))
                .skip))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._DescriptorBase.__get__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DescriptorBase___get__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DescriptorBase.__get__"
  , params := ["obj", "objtype"]
  , body := (.seq
            (.assign "wrapper" (.mcall (.name "self") "Wrapper" [(.name "obj")]))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "obj") (.lit .unit))
                  .skip
                  (.ifte
                    (.isOp true (.field (.name "self") "_DescriptorBase__attrname") (.lit .unit))
                    (.hole "control:TRY-multiCatch")
                    (.ifte
                      (.field (.name "self") "_DescriptorBase__deprecated")
                      .skip
                      (.seq
                        (.assign
                          "msg"
                          (.lit
                            (.str "Cannot use @cachedmethod instance without calling __set_name__ on it")))
                        (.raise (.call "TypeError" [(.name "msg")]))))))
                (.seq
                  .skip
                  (.seq (.ret (.name "wrapper")) (.seq .skip (.seq .skip (.seq .skip .skip)))))))) }

/-- `cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__init__"
  , params := ["wrapper", "cache_clear"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall (.name "tmp0") "__init__" [(.kwargE "deprecated" (.lit (.bool true)))])))
            (.seq
              (.setField (.name "self") "_DeprecatedDescriptorBase__wrapper" (.name "wrapper"))
              (.seq
                (.setField
                  (.name "self")
                  "_DeprecatedDescriptorBase__cache_clear"
                  (.name "cache_clear"))
                (.seq .skip .skip)))) }

/-- `cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.expr
              (.call
                "cachetools/_cachedmethod.py:<module>._warn_classmethod"
                [(.kwargE "stacklevel" (.lit (.int 3)))]))
            (.seq
              .skip
              (.ret
                (.mcall
                  (.name "self")
                  "_DeprecatedDescriptorBase__wrapper"
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))) }

/-- `cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase.cache_clear"
  , params := ["objtype"]
  , body := (.seq
            (.expr
              (.call
                "cachetools/_cachedmethod.py:<module>._warn_classmethod"
                [(.kwargE "stacklevel" (.lit (.int 3)))]))
            (.seq
              .skip
              (.ret
                (.mcall (.name "self") "_DeprecatedDescriptorBase__cache_clear" [(.name "objtype")])))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info"
  , params := ["method", "cache", "key", "lock", "cond", "info"]
  , body := (.seq
            (.seq
              (.assign
                "Descriptor"
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor<meta>"))
              (.expr
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor<meta>")))
            (.seq (.ret (.alloc "Descriptor" [])) (.seq .skip (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                  , (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock")
                  , (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "cond") ])))
            (.seq
              (.seq
                (.assign "tmp1" (.lit (.int 0)))
                (.seq
                  (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                  (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
              (.seq
                (.setField (.name "self") "_Wrapper__pending" (.call "set" []))
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign "cache" (.field (.name "self") "cache"))
            (.seq
              (.assign "lock" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "cond" (.field (.name "self") "cache_condition"))
                (.seq
                  (.assign
                    "key"
                    (.mcall
                      (.name "self")
                      "cache_key"
                      [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                  (.seq
                    (.seq
                      (.assign "manager_tmp0" (.name "lock"))
                      (.seq
                        (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                        (.seq
                          (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                          (.seq
                            (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                            (.tryFinally
                              (.seq
                                (.expr
                                  (.mcall
                                    (.name "cond")
                                    "wait_for"
                                    [ (.closure
                                        "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__.<lambda>0") ]))
                                (.tryCatch
                                  (.seq
                                    (.assign "result" (.index (.name "cache") (.name "key")))
                                    (.seq
                                      (.setField
                                        (.name "self")
                                        "_Wrapper__hits"
                                        (.binop
                                        "+"
                                        (.field (.name "self") "_Wrapper__hits")
                                        (.lit (.int 1))))
                                      (.ret (.name "result"))))
                                  "__exc"
                                  (.seq
                                    (.seq
                                      (.assign "tmp0" (.field (.name "self") "_Wrapper__pending"))
                                      (.expr (.mcall (.name "tmp0") "add" [(.name "key")])))
                                    (.setField
                                      (.name "self")
                                      "_Wrapper__misses"
                                      (.binop
                                        "+"
                                        (.field (.name "self") "_Wrapper__misses")
                                        (.lit (.int 1)))))))
                              (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                    (.seq
                      (.tryFinally
                        (.seq
                          (.assign
                            "val"
                            (.call
                              "method"
                              [ (.field (.name "self") "_obj")
                              , (.starred (.name "args"))
                              , (.dstarred (.name "kwargs")) ]))
                          (.seq
                            (.assign "manager_tmp1" (.name "lock"))
                            (.seq
                              (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                              (.seq
                                (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                (.seq
                                  (.assign
                                    "value_tmp1"
                                    (.mcall (.name "manager_tmp1") "__enter__" []))
                                  (.tryFinally
                                    (.seq
                                      (.tryCatch
                                        (.setIndex (.name "cache") (.name "key") (.name "val"))
                                        "__exc"
                                        .skip)
                                      (.ret (.name "val")))
                                    (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                        (.seq
                          (.assign "manager_tmp2" (.name "lock"))
                          (.seq
                            (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                            (.seq
                              (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp2"
                                  (.mcall (.name "manager_tmp2") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.seq
                                      (.assign "tmp1" (.field (.name "self") "_Wrapper__pending"))
                                      (.expr (.mcall (.name "tmp1") "remove" [(.name "key")])))
                                    (.expr (.mcall (.name "cond") "notify_all" [])))
                                  (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__.<lambda>0`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call____lambda_0 : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.__call__.<lambda>0"
  , params := []
  , body := (.seq
            (.ret (.inOp true (.name "key") (.field (.name "self") "_Wrapper__pending")))
            (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_clear"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.seq
                          (.assign "tmp0" (.field (.name "self") "cache"))
                          (.expr (.mcall (.name "tmp0") "clear" [])))
                        (.seq
                          (.assign "tmp1" (.lit (.int 0)))
                          (.seq
                            (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                            (.setField (.name "self") "_Wrapper__misses" (.name "tmp1")))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition_info.Descriptor.Wrapper.cache_info"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.call
                          "info"
                          [ (.field (.name "self") "cache")
                          , (.field (.name "self") "_Wrapper__hits")
                          , (.field (.name "self") "_Wrapper__misses") ]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info"
  , params := ["method", "cache", "key", "lock", "info"]
  , body := (.seq
            (.seq
              (.assign
                "Descriptor"
                (.classClosure "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor<meta>"))
              (.expr
                (.classClosure "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor<meta>")))
            (.seq (.ret (.alloc "Descriptor" [])) (.seq .skip (.seq .skip .skip)))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                  , (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock")
                  , (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock") ])))
            (.seq
              (.seq
                (.assign "tmp1" (.lit (.int 0)))
                (.seq
                  (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                  (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign "cache" (.field (.name "self") "cache"))
            (.seq
              (.assign "lock" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign
                  "key"
                  (.mcall
                    (.name "self")
                    "cache_key"
                    [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  (.seq
                    (.assign "manager_tmp0" (.name "lock"))
                    (.seq
                      (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                      (.seq
                        (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                        (.seq
                          (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                          (.tryFinally
                            (.tryCatch
                              (.seq
                                (.assign "result" (.index (.name "cache") (.name "key")))
                                (.seq
                                  (.setField
                                    (.name "self")
                                    "_Wrapper__hits"
                                    (.binop
                                      "+"
                                      (.field (.name "self") "_Wrapper__hits")
                                      (.lit (.int 1))))
                                  (.ret (.name "result"))))
                              "__exc"
                              (.setField
                                (.name "self")
                                "_Wrapper__misses"
                                (.binop
                                  "+"
                                  (.field (.name "self") "_Wrapper__misses")
                                  (.lit (.int 1)))))
                            (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "val"
                        (.call
                          "method"
                          [ (.field (.name "self") "_obj")
                          , (.starred (.name "args"))
                          , (.dstarred (.name "kwargs")) ]))
                      (.seq
                        .skip
                        (.seq
                          (.seq
                            (.assign "manager_tmp1" (.name "lock"))
                            (.seq
                              (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                              (.seq
                                (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                (.seq
                                  (.assign
                                    "value_tmp1"
                                    (.mcall (.name "manager_tmp1") "__enter__" []))
                                  (.tryFinally
                                    (.tryCatch
                                      (.ret
                                        (.mcall
                                        (.name "cache")
                                        "setdefault"
                                        [ (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                                        , (.name "key")
                                        , (.name "val") ]))
                                      "__exc"
                                      (.ret (.name "val")))
                                    (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_clear"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.seq
                        (.seq
                          (.assign "tmp0" (.field (.name "self") "cache"))
                          (.expr (.mcall (.name "tmp0") "clear" [])))
                        (.seq
                          (.assign "tmp1" (.lit (.int 0)))
                          (.seq
                            (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                            (.setField (.name "self") "_Wrapper__misses" (.name "tmp1")))))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked_info.Descriptor.Wrapper.cache_info"
  , params := []
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.field (.name "self") "cache_lock"))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                    (.tryFinally
                      (.ret
                        (.call
                          "info"
                          [ (.field (.name "self") "cache")
                          , (.field (.name "self") "_Wrapper__hits")
                          , (.field (.name "self") "_Wrapper__misses") ]))
                      (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info"
  , params := ["method", "cache", "key", "info"]
  , body := (.seq
            (.seq
              (.assign
                "Descriptor"
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor<meta>"))
              (.expr
                (.classClosure
                  "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor<meta>")))
            (.seq (.ret (.alloc "Descriptor" [])) (.seq .skip .skip))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                  , (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key") ])))
            (.seq
              (.seq
                (.assign "tmp1" (.lit (.int 0)))
                (.seq
                  (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                  (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign "cache" (.field (.name "self") "cache"))
            (.seq
              (.assign
                "key"
                (.mcall
                  (.name "self")
                  "cache_key"
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))]))
              (.seq
                (.tryCatch
                  (.seq
                    (.assign "result" (.index (.name "cache") (.name "key")))
                    (.seq
                      (.setField
                        (.name "self")
                        "_Wrapper__hits"
                        (.binop "+" (.field (.name "self") "_Wrapper__hits") (.lit (.int 1))))
                      (.ret (.name "result"))))
                  "__exc"
                  (.setField
                    (.name "self")
                    "_Wrapper__misses"
                    (.binop "+" (.field (.name "self") "_Wrapper__misses") (.lit (.int 1)))))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "val"
                      (.call
                        "method"
                        [ (.field (.name "self") "_obj")
                        , (.starred (.name "args"))
                        , (.dstarred (.name "kwargs")) ]))
                    (.seq
                      .skip
                      (.seq
                        (.tryCatch
                          (.setIndex (.name "cache") (.name "key") (.name "val"))
                          "__exc"
                          .skip)
                        (.seq .skip (.seq (.ret (.name "val")) (.seq .skip .skip)))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_clear"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.field (.name "self") "cache"))
              (.expr (.mcall (.name "tmp0") "clear" [])))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "tmp1" (.lit (.int 0)))
                  (.seq
                    (.setField (.name "self") "_Wrapper__hits" (.name "tmp1"))
                    (.setField (.name "self") "_Wrapper__misses" (.name "tmp1"))))
                .skip))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_info`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_info : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked_info.Descriptor.Wrapper.cache_info"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "info"
                [ (.field (.name "self") "cache")
                , (.field (.name "self") "_Wrapper__hits")
                , (.field (.name "self") "_Wrapper__misses") ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._condition`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition"
  , params := ["method", "cache", "key", "lock", "cond"]
  , body := (.seq
            (.assign "pending" (.alloc "WeakKeyDictionary" []))
            (.seq
              (.assign
                "wrapper"
                (.closure "cachetools/_cachedmethod.py:<module>._condition.wrapper"))
              (.seq
                (.assign
                  "cache_clear"
                  (.closure "cachetools/_cachedmethod.py:<module>._condition.cache_clear"))
                (.seq
                  (.assign
                    "classmethod_wrapper"
                    (.closure "cachetools/_cachedmethod.py:<module>._condition.classmethod_wrapper"))
                  (.seq
                    (.seq
                      (.assign
                        "Descriptor"
                        (.classClosure
                          "cachetools/_cachedmethod.py:<module>._condition.Descriptor<meta>"))
                      (.expr
                        (.classClosure
                          "cachetools/_cachedmethod.py:<module>._condition.Descriptor<meta>")))
                    (.seq
                      (.ret
                        (.alloc "Descriptor" [(.name "classmethod_wrapper"), (.name "cache_clear")]))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.wrapper"
  , params := ["self", "pending", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign
              "c"
              (.call "cachetools/_cachedmethod.py:<module>._WrapperBase.cache" [(.name "self")]))
            (.seq
              (.assign
                "k"
                (.call
                  "key"
                  [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.call "lock" [(.name "self")]))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.seq
                            (.seq
                              (.assign "tmp0" (.call "cond" [(.name "self")]))
                              (.expr
                                (.mcall
                                  (.name "tmp0")
                                  "wait_for"
                                  [ (.closure
                                      "cachetools/_cachedmethod.py:<module>._condition.wrapper.<lambda>1") ])))
                            (.tryCatch
                              (.ret (.index (.name "c") (.name "k")))
                              "__exc"
                              (.expr (.mcall (.name "pending") "add" [(.name "k")]))))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq
                  .skip
                  (.seq
                    (.tryFinally
                      (.seq
                        (.assign
                          "v"
                          (.call
                            "method"
                            [ (.name "self")
                            , (.starred (.name "args"))
                            , (.dstarred (.name "kwargs")) ]))
                        (.seq
                          (.assign "manager_tmp1" (.call "lock" [(.name "self")]))
                          (.seq
                            (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                            (.seq
                              (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                              (.seq
                                (.assign
                                  "value_tmp1"
                                  (.mcall (.name "manager_tmp1") "__enter__" []))
                                (.tryFinally
                                  (.seq
                                    (.tryCatch
                                      (.setIndex (.name "c") (.name "k") (.name "v"))
                                      "__exc"
                                      .skip)
                                    (.ret (.name "v")))
                                  (.expr (.mcall (.name "manager_tmp1") "__exit__" []))))))))
                      (.seq
                        (.assign "manager_tmp2" (.call "lock" [(.name "self")]))
                        (.seq
                          (.assign "enter_tmp2" (.field (.name "manager_tmp2") "__enter__"))
                          (.seq
                            (.assign "exit_tmp2" (.field (.name "manager_tmp2") "__exit__"))
                            (.seq
                              (.assign "value_tmp2" (.mcall (.name "manager_tmp2") "__enter__" []))
                              (.tryFinally
                                (.seq
                                  (.expr (.mcall (.name "pending") "remove" [(.name "k")]))
                                  (.seq
                                    (.assign "tmp1" (.call "cond" [(.name "self")]))
                                    (.expr (.mcall (.name "tmp1") "notify_all" []))))
                                (.expr (.mcall (.name "manager_tmp2") "__exit__" []))))))))
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.wrapper.<lambda>1`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_wrapper__lambda_1 : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.wrapper.<lambda>1"
  , params := []
  , body := (.seq (.ret (.inOp true (.name "k") (.name "pending"))) (.seq .skip .skip)) }

/-- `cachetools/_cachedmethod.py:<module>._condition.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.cache_clear"
  , params := ["self"]
  , body := (.seq
            (.assign
              "c"
              (.call "cachetools/_cachedmethod.py:<module>._WrapperBase.cache" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.call "lock" [(.name "self")]))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.expr (.mcall (.name "c") "clear" []))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.classmethod_wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_classmethod_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.classmethod_wrapper"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign "p" (.mcall (.name "pending") "setdefault" [(.name "self"), (.call "set" [])]))
            (.seq
              .skip
              (.seq
                (.ret
                  (.call
                    "wrapper"
                    [ (.name "self")
                    , (.name "p")
                    , (.starred (.name "args"))
                    , (.dstarred (.name "kwargs")) ]))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                  , (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock")
                  , (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock")
                  , (.name "cond") ])))
            (.seq
              (.setField (.name "self") "_Wrapper__pending" (.call "set" []))
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.ret
              (.call
                "wrapper"
                [ (.field (.name "self") "_obj")
                , (.field (.name "self") "_Wrapper__pending")
                , (.starred (.name "args"))
                , (.dstarred (.name "kwargs")) ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._condition.Descriptor.Wrapper.cache_clear"
  , params := ["_objtype"]
  , body := (.seq (.ret (.call "cache_clear" [(.field (.name "self") "_obj")])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._locked`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked"
  , params := ["method", "cache", "key", "lock"]
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cachedmethod.py:<module>._locked.wrapper"))
            (.seq
              (.assign
                "cache_clear"
                (.closure "cachetools/_cachedmethod.py:<module>._locked.cache_clear"))
              (.seq
                (.seq
                  (.assign
                    "Descriptor"
                    (.classClosure "cachetools/_cachedmethod.py:<module>._locked.Descriptor<meta>"))
                  (.expr
                    (.classClosure "cachetools/_cachedmethod.py:<module>._locked.Descriptor<meta>")))
                (.seq
                  (.ret (.alloc "Descriptor" [(.name "wrapper"), (.name "cache_clear")]))
                  (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.wrapper"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign
              "c"
              (.call "cachetools/_cachedmethod.py:<module>._WrapperBase.cache" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.call
                    "key"
                    [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.assign "manager_tmp0" (.call "lock" [(.name "self")]))
                      (.seq
                        (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                        (.seq
                          (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                          (.seq
                            (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                            (.tryFinally
                              (.tryCatch (.ret (.index (.name "c") (.name "k"))) "__exc" .skip)
                              (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.call
                            "method"
                            [ (.name "self")
                            , (.starred (.name "args"))
                            , (.dstarred (.name "kwargs")) ]))
                        (.seq
                          .skip
                          (.seq
                            (.seq
                              (.assign "manager_tmp1" (.call "lock" [(.name "self")]))
                              (.seq
                                (.assign "enter_tmp1" (.field (.name "manager_tmp1") "__enter__"))
                                (.seq
                                  (.assign "exit_tmp1" (.field (.name "manager_tmp1") "__exit__"))
                                  (.seq
                                    (.assign
                                      "value_tmp1"
                                      (.mcall (.name "manager_tmp1") "__enter__" []))
                                    (.tryFinally
                                      (.tryCatch
                                        (.ret
                                        (.mcall (.name "c") "setdefault" [(.name "k"), (.name "v")]))
                                        "__exc"
                                        (.ret (.name "v")))
                                      (.expr (.mcall (.name "manager_tmp1") "__exit__" [])))))))
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.cache_clear"
  , params := ["self"]
  , body := (.seq
            (.assign
              "c"
              (.call "cachetools/_cachedmethod.py:<module>._WrapperBase.cache" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.seq
                  (.assign "manager_tmp0" (.call "lock" [(.name "self")]))
                  (.seq
                    (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                    (.seq
                      (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                      (.seq
                        (.assign "value_tmp0" (.mcall (.name "manager_tmp0") "__enter__" []))
                        (.tryFinally
                          (.expr (.mcall (.name "c") "clear" []))
                          (.expr (.mcall (.name "manager_tmp0") "__exit__" [])))))))
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                  , (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache_lock")
                  , (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key")
                  , (.name "lock") ])))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))) }

/-- `cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.ret
              (.call
                "wrapper"
                [ (.field (.name "self") "_obj")
                , (.starred (.name "args"))
                , (.dstarred (.name "kwargs")) ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._locked.Descriptor.Wrapper.cache_clear"
  , params := ["_objtype"]
  , body := (.seq (.ret (.call "cache_clear" [(.field (.name "self") "_obj")])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked"
  , params := ["method", "cache", "key"]
  , body := (.seq
            (.assign "wrapper" (.closure "cachetools/_cachedmethod.py:<module>._unlocked.wrapper"))
            (.seq
              (.assign
                "cache_clear"
                (.closure "cachetools/_cachedmethod.py:<module>._unlocked.cache_clear"))
              (.seq
                (.seq
                  (.assign
                    "Descriptor"
                    (.classClosure
                      "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor<meta>"))
                  (.expr
                    (.classClosure
                      "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor<meta>")))
                (.seq
                  (.ret (.alloc "Descriptor" [(.name "wrapper"), (.name "cache_clear")]))
                  (.seq .skip (.seq .skip (.seq .skip .skip))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.wrapper"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.assign
              "c"
              (.call "cachetools/_cachedmethod.py:<module>._WrapperBase.cache" [(.name "self")]))
            (.seq
              .skip
              (.seq
                (.assign
                  "k"
                  (.call
                    "key"
                    [(.name "self"), (.starred (.name "args")), (.dstarred (.name "kwargs"))]))
                (.seq
                  .skip
                  (.seq
                    (.tryCatch (.ret (.index (.name "c") (.name "k"))) "__exc" .skip)
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "v"
                          (.call
                            "method"
                            [ (.name "self")
                            , (.starred (.name "args"))
                            , (.dstarred (.name "kwargs")) ]))
                        (.seq
                          .skip
                          (.seq
                            (.tryCatch
                              (.setIndex (.name "c") (.name "k") (.name "v"))
                              "__exc"
                              .skip)
                            (.seq .skip (.seq (.ret (.name "v")) .skip))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.cache_clear"
  , params := ["self"]
  , body := (.seq
            (.assign
              "c"
              (.call "cachetools/_cachedmethod.py:<module>._WrapperBase.cache" [(.name "self")]))
            (.seq .skip (.seq (.expr (.mcall (.name "c") "clear" [])) .skip))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__init__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___init__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__init__"
  , params := ["obj"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" []))
              (.expr
                (.mcall
                  (.name "tmp0")
                  "__init__"
                  [ (.fnref "cachetools/_cachedmethod.py:<module>._WrapperBase.cache")
                  , (.name "obj")
                  , (.name "method")
                  , (.name "cache")
                  , (.name "key") ])))
            (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__call__`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___call__ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.__call__"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.ret
              (.call
                "wrapper"
                [ (.field (.name "self") "_obj")
                , (.starred (.name "args"))
                , (.dstarred (.name "kwargs")) ]))
            .skip) }

/-- `cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.cache_clear`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper_cache_clear : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._unlocked.Descriptor.Wrapper.cache_clear"
  , params := ["_objtype"]
  , body := (.seq (.ret (.call "cache_clear" [(.field (.name "self") "_obj")])) .skip) }

/-- `cachetools/_cachedmethod.py:<module>._wrapper`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module___wrapper : Func :=
  { name := "cachetools/_cachedmethod.py:<module>._wrapper"
  , params := ["method", "cache", "key", "lock", "cond", "info"]
  , body := (.seq
            (.ifte
              (.isOp true (.name "info") (.lit .unit))
              (.ifte
                (.binop
                  "&&"
                  (.isOp true (.name "cond") (.lit .unit))
                  (.isOp true (.name "lock") (.lit .unit)))
                (.assign
                  "wrapper"
                  (.call
                    "cachetools/_cachedmethod.py:<module>._condition_info"
                    [ (.name "method")
                    , (.name "cache")
                    , (.name "key")
                    , (.name "lock")
                    , (.name "cond")
                    , (.name "info") ]))
                (.ifte
                  (.isOp true (.name "cond") (.lit .unit))
                  (.assign
                    "wrapper"
                    (.call
                      "cachetools/_cachedmethod.py:<module>._condition_info"
                      [ (.name "method")
                      , (.name "cache")
                      , (.name "key")
                      , (.name "cond")
                      , (.name "cond")
                      , (.name "info") ]))
                  (.ifte
                    (.isOp true (.name "lock") (.lit .unit))
                    (.assign
                      "wrapper"
                      (.call
                        "cachetools/_cachedmethod.py:<module>._locked_info"
                        [ (.name "method")
                        , (.name "cache")
                        , (.name "key")
                        , (.name "lock")
                        , (.name "info") ]))
                    (.assign
                      "wrapper"
                      (.call
                        "cachetools/_cachedmethod.py:<module>._unlocked_info"
                        [(.name "method"), (.name "cache"), (.name "key"), (.name "info")])))))
              (.ifte
                (.binop
                  "&&"
                  (.isOp true (.name "cond") (.lit .unit))
                  (.isOp true (.name "lock") (.lit .unit)))
                (.assign
                  "wrapper"
                  (.call
                    "cachetools/_cachedmethod.py:<module>._condition"
                    [ (.name "method")
                    , (.name "cache")
                    , (.name "key")
                    , (.name "lock")
                    , (.name "cond") ]))
                (.ifte
                  (.isOp true (.name "cond") (.lit .unit))
                  (.assign
                    "wrapper"
                    (.call
                      "cachetools/_cachedmethod.py:<module>._condition"
                      [ (.name "method")
                      , (.name "cache")
                      , (.name "key")
                      , (.name "cond")
                      , (.name "cond") ]))
                  (.ifte
                    (.isOp true (.name "lock") (.lit .unit))
                    (.assign
                      "wrapper"
                      (.call
                        "cachetools/_cachedmethod.py:<module>._locked"
                        [(.name "method"), (.name "cache"), (.name "key"), (.name "lock")]))
                    (.assign
                      "wrapper"
                      (.call
                        "cachetools/_cachedmethod.py:<module>._unlocked"
                        [(.name "method"), (.name "cache"), (.name "key")]))))))
            (.seq
              .skip
              (.seq
                (.setField (.name "wrapper") "cache" (.name "cache"))
                (.seq
                  .skip
                  (.seq
                    (.setField (.name "wrapper") "cache_key" (.name "key"))
                    (.seq
                      .skip
                      (.seq
                        (.setField
                          (.name "wrapper")
                          "cache_lock"
                          (.cond
                            (.isOp true (.name "lock") (.lit .unit))
                            (.name "lock")
                            (.name "cond")))
                        (.seq
                          .skip
                          (.seq
                            (.setField (.name "wrapper") "cache_condition" (.name "cond"))
                            (.seq
                              .skip
                              (.seq
                                (.ret
                                  (.mcall
                                    (.name "functools")
                                    "update_wrapper"
                                    [(.name "wrapper"), (.name "method")]))
                                (.seq .skip (.seq .skip .skip))))))))))))) }

/-- `cachetools/func.py:<module>._UnboundTTLCache.__init__`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___UnboundTTLCache___init__ : Func :=
  { name := "cachetools/func.py:<module>._UnboundTTLCache.__init__"
  , params := ["ttl", "timer"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "TTLCache")
                "__init__"
                [(.name "self"), (.field (.name "math") "inf"), (.name "ttl"), (.name "timer")]))
            (.seq .skip .skip)) }

/-- `cachetools/func.py:<module>._UnboundTTLCache.maxsize`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___UnboundTTLCache_maxsize : Func :=
  { name := "cachetools/func.py:<module>._UnboundTTLCache.maxsize"
  , params := []
  , body := (.ret (.lit .unit)) }

/-- `cachetools/func.py:<module>._cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___cache : Func :=
  { name := "cachetools/func.py:<module>._cache"
  , params := ["cache", "maxsize", "typed"]
  , body := (.seq
            (.assign "decorator" (.closure "cachetools/func.py:<module>._cache.decorator"))
            (.seq (.ret (.name "decorator")) (.seq .skip (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>._cache.decorator`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___cache_decorator : Func :=
  { name := "cachetools/func.py:<module>._cache.decorator"
  , params := ["func"]
  , body := (.seq
            (.assign
              "key"
              (.cond
                (.name "typed")
                (.fnref "cachetools/keys.py:<module>.typedkey")
                (.fnref "cachetools/keys.py:<module>.hashkey")))
            (.seq
              (.assign "wrapper" (.hole "call:computed-callee"))
              (.seq
                (.setField
                  (.name "wrapper")
                  "cache_parameters"
                  (.closure "cachetools/func.py:<module>._cache.decorator.<lambda>0"))
                (.seq
                  .skip
                  (.seq
                    (.ret (.name "wrapper"))
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- `cachetools/func.py:<module>._cache.decorator.<lambda>0`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module___cache_decorator__lambda_0 : Func :=
  { name := "cachetools/func.py:<module>._cache.decorator.<lambda>0"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.dictE []))
              (.seq
                (.setIndex (.name "tmp0") (.lit (.str "maxsize")) (.name "maxsize"))
                (.seq
                  (.setIndex (.name "tmp0") (.lit (.str "typed")) (.name "typed"))
                  (.ret (.name "tmp0")))))
            (.seq .skip (.seq .skip .skip))) }

/-- `cachetools/func.py:<module>.fifo_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__fifo_cache : Func :=
  { name := "cachetools/func.py:<module>.fifo_cache"
  , params := ["maxsize", "typed"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a First In First Out (FIFO)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.ret
                    (.call
                      "cachetools/func.py:<module>._cache"
                      [(.dictE []), (.lit .unit), (.name "typed")]))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret (.hole "call:computed-callee"))
                    (.ret
                      (.call
                        "cachetools/func.py:<module>._cache"
                        [ (.alloc "FIFOCache" [(.name "maxsize")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.lfu_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__lfu_cache : Func :=
  { name := "cachetools/func.py:<module>.lfu_cache"
  , params := ["maxsize", "typed"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Least Frequently Used (LFU)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.ret
                    (.call
                      "cachetools/func.py:<module>._cache"
                      [(.dictE []), (.lit .unit), (.name "typed")]))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret (.hole "call:computed-callee"))
                    (.ret
                      (.call
                        "cachetools/func.py:<module>._cache"
                        [ (.alloc "LFUCache" [(.name "maxsize")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.lru_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__lru_cache : Func :=
  { name := "cachetools/func.py:<module>.lru_cache"
  , params := ["maxsize", "typed"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Least Recently Used (LRU)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.ret
                    (.call
                      "cachetools/func.py:<module>._cache"
                      [(.dictE []), (.lit .unit), (.name "typed")]))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret (.hole "call:computed-callee"))
                    (.ret
                      (.call
                        "cachetools/func.py:<module>._cache"
                        [ (.alloc "LRUCache" [(.name "maxsize")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.rr_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__rr_cache : Func :=
  { name := "cachetools/func.py:<module>.rr_cache"
  , params := ["maxsize", "choice", "typed"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Random Replacement (RR)\n    algorithm.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.ret
                    (.call
                      "cachetools/func.py:<module>._cache"
                      [(.dictE []), (.lit .unit), (.name "typed")]))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret (.hole "call:computed-callee"))
                    (.ret
                      (.call
                        "cachetools/func.py:<module>._cache"
                        [ (.alloc "RRCache" [(.name "maxsize"), (.name "choice")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/func.py:<module>.ttl_cache`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module__ttl_cache : Func :=
  { name := "cachetools/func.py:<module>.ttl_cache"
  , params := ["maxsize", "ttl", "timer", "typed"]
  , body := (.seq
            (.expr
              (.lit
                (.str "Decorator to wrap a function with a memoizing callable that saves\n    up to `maxsize` results based on a Least Recently Used (LRU)\n    algorithm with a per-item time-to-live (TTL) value.\n\n    ")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "maxsize") (.lit .unit))
                  (.ret
                    (.call
                      "cachetools/func.py:<module>._cache"
                      [ (.alloc "_UnboundTTLCache" [(.name "ttl"), (.name "timer")])
                      , (.lit .unit)
                      , (.name "typed") ]))
                  (.ifte
                    (.call "callable" [(.name "maxsize")])
                    (.ret (.hole "call:computed-callee"))
                    (.ret
                      (.call
                        "cachetools/func.py:<module>._cache"
                        [ (.alloc "TTLCache" [(.name "maxsize"), (.name "ttl"), (.name "timer")])
                        , (.name "maxsize")
                        , (.name "typed") ]))))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/keys.py:<module>._HashedTuple.__hash__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___hash__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__hash__"
  , params := ["hash"]
  , body := (.seq
            (.assign "hashvalue" (.field (.name "self") "_HashedTuple__hashvalue"))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.isOp false (.name "hashvalue") (.lit .unit))
                  (.seq
                    (.assign "tmp0" (.call "hash" [(.name "self")]))
                    (.seq
                      (.setField (.name "self") "_HashedTuple__hashvalue" (.name "tmp0"))
                      (.assign "hashvalue" (.name "tmp0"))))
                  .skip)
                (.seq .skip (.ret (.name "hashvalue")))))) }

/-- `cachetools/keys.py:<module>._HashedTuple.__add__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___add__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__add__"
  , params := ["other", "add"]
  , body := (.seq
            (.ret (.alloc "_HashedTuple" [(.call "add" [(.name "self"), (.name "other")])]))
            .skip) }

/-- `cachetools/keys.py:<module>._HashedTuple.__radd__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___radd__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__radd__"
  , params := ["other", "add"]
  , body := (.seq
            (.ret (.alloc "_HashedTuple" [(.call "add" [(.name "other"), (.name "self")])]))
            .skip) }

/-- `cachetools/keys.py:<module>._HashedTuple.__getstate__`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module___HashedTuple___getstate__ : Func :=
  { name := "cachetools/keys.py:<module>._HashedTuple.__getstate__"
  , params := []
  , body := (.seq (.seq (.assign "tmp0" (.dictE [])) (.ret (.name "tmp0"))) .skip) }

/-- `cachetools/keys.py:<module>.hashkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__hashkey : Func :=
  { name := "cachetools/keys.py:<module>.hashkey"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.expr (.lit (.str "Return a cache key for the specified hashable arguments.")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "kwargs")
                  (.ret
                    (.alloc
                      "_HashedTuple"
                      [ (.binop
                          "+"
                          (.binop "+" (.name "args") (.name "_kwmark"))
                          (.call "tuple" [(.call "sorted" [(.mcall (.name "kwargs") "items" [])])])) ]))
                  (.ret (.alloc "_HashedTuple" [(.name "args")])))
                (.seq .skip (.seq .skip .skip))))) }

/-- `cachetools/keys.py:<module>.methodkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__methodkey : Func :=
  { name := "cachetools/keys.py:<module>.methodkey"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.expr (.lit (.str "Return a cache key for use with cached methods.")))
            (.seq
              .skip
              (.ret
                (.call
                  "cachetools/keys.py:<module>.hashkey"
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))) }

/-- `cachetools/keys.py:<module>.typedkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__typedkey : Func :=
  { name := "cachetools/keys.py:<module>.typedkey"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.expr (.lit (.str "Return a typed cache key for the specified hashable arguments.")))
            (.seq
              .skip
              (.seq
                (.ifte
                  (.name "kwargs")
                  (.seq
                    (.assign
                      "sorted_kwargs"
                      (.call "tuple" [(.call "sorted" [(.mcall (.name "kwargs") "items" [])])]))
                    (.seq
                      (.assign
                        "key"
                        (.alloc
                          "_HashedTuple"
                          [ (.binop
                              "+"
                              (.binop "+" (.name "args") (.name "_kwmark"))
                              (.name "sorted_kwargs")) ]))
                      (.assign
                        "key"
                        (.binop "+" (.name "key") (.call "tuple" [(.hole "expr:genExp")])))))
                  (.assign "key" (.alloc "_HashedTuple" [(.name "args")])))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "key"
                      (.binop "+" (.name "key") (.call "tuple" [(.hole "expr:genExp")])))
                    (.seq
                      .skip
                      (.seq
                        (.ret (.name "key"))
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))) }

/-- `cachetools/keys.py:<module>.typedmethodkey`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module__typedmethodkey : Func :=
  { name := "cachetools/keys.py:<module>.typedmethodkey"
  , params := ["self", "args", "kwargs"]
  , vararg := some "args"
  , kwarg := some "kwargs"
  , body := (.seq
            (.expr (.lit (.str "Return a typed cache key for use with cached methods.")))
            (.seq
              .skip
              (.ret
                (.call
                  "cachetools/keys.py:<module>.typedkey"
                  [(.starred (.name "args")), (.dstarred (.name "kwargs"))])))) }

/-- `<module-objects>:<module>`  (from ``) -/
def f__module_objects___module_ : Func :=
  { name := "<module-objects>:<module>"
  , params := []
  , body := (.seq
            (.setGlobal
              "<module>cachetools/__init__.py"
              (.alloc "<module>cachetools/__init__.py" []))
            (.seq
              (.setGlobal
                "<module>cachetools/_cached.py"
                (.alloc "<module>cachetools/_cached.py" []))
              (.seq
                (.setGlobal
                  "<module>cachetools/_cachedmethod.py"
                  (.alloc "<module>cachetools/_cachedmethod.py" []))
                (.seq
                  (.setGlobal "<module>cachetools/func.py" (.alloc "<module>cachetools/func.py" []))
                  (.seq
                    (.setGlobal
                      "<module>cachetools/keys.py"
                      (.alloc "<module>cachetools/keys.py" []))
                    (.seq
                      (.setField
                        (.name "<module>cachetools/__init__.py")
                        "cached"
                        (.fnref "cachetools/__init__.py:<module>.cached"))
                      (.seq
                        (.setField
                          (.name "<module>cachetools/__init__.py")
                          "cachedmethod"
                          (.fnref "cachetools/__init__.py:<module>.cachedmethod"))
                        (.seq
                          (.setField
                            (.name "<module>cachetools/__init__.py")
                            "Cache"
                            (.fnref "cachetools/__init__.py:<module>.Cache<meta>"))
                          (.seq
                            (.setField
                              (.name "<module>cachetools/__init__.py")
                              "FIFOCache"
                              (.fnref "cachetools/__init__.py:<module>.FIFOCache<meta>"))
                            (.seq
                              (.setField
                                (.name "<module>cachetools/__init__.py")
                                "LFUCache"
                                (.fnref "cachetools/__init__.py:<module>.LFUCache<meta>"))
                              (.seq
                                (.setField
                                  (.name "<module>cachetools/__init__.py")
                                  "LRUCache"
                                  (.fnref "cachetools/__init__.py:<module>.LRUCache<meta>"))
                                (.seq
                                  (.setField
                                    (.name "<module>cachetools/__init__.py")
                                    "RRCache"
                                    (.fnref "cachetools/__init__.py:<module>.RRCache<meta>"))
                                  (.seq
                                    (.setField
                                      (.name "<module>cachetools/__init__.py")
                                      "TLRUCache"
                                      (.fnref "cachetools/__init__.py:<module>.TLRUCache<meta>"))
                                    (.seq
                                      (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "TTLCache"
                                        (.fnref "cachetools/__init__.py:<module>.TTLCache<meta>"))
                                      (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_DefaultSize"
                                        (.fnref
                                        "cachetools/__init__.py:<module>._DefaultSize<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_TimedCache"
                                        (.fnref "cachetools/__init__.py:<module>._TimedCache<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_cached"
                                        (.name "<module>cachetools/_cached.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "_cachedmethod"
                                        (.name "<module>cachetools/_cachedmethod.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "func"
                                        (.name "<module>cachetools/func.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/__init__.py")
                                        "keys"
                                        (.name "<module>cachetools/keys.py"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_condition"
                                        (.fnref "cachetools/_cached.py:<module>._condition"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_condition_info"
                                        (.fnref "cachetools/_cached.py:<module>._condition_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_locked"
                                        (.fnref "cachetools/_cached.py:<module>._locked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_locked_info"
                                        (.fnref "cachetools/_cached.py:<module>._locked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_uncached"
                                        (.fnref "cachetools/_cached.py:<module>._uncached"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_uncached_info"
                                        (.fnref "cachetools/_cached.py:<module>._uncached_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_unlocked"
                                        (.fnref "cachetools/_cached.py:<module>._unlocked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_unlocked_info"
                                        (.fnref "cachetools/_cached.py:<module>._unlocked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cached.py")
                                        "_wrapper"
                                        (.fnref "cachetools/_cached.py:<module>._wrapper"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_condition"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._condition"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_condition_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._condition_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_locked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_locked_info"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_none"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._none"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_unlocked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._unlocked"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_unlocked_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._unlocked_info"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_warn_classmethod"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._warn_classmethod"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_warn_instance_dict"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._warn_instance_dict"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_wrapper"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._wrapper"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_DeprecatedDescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_DescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DescriptorBase<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/_cachedmethod.py")
                                        "_WrapperBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "_cache"
                                        (.fnref "cachetools/func.py:<module>._cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "fifo_cache"
                                        (.fnref "cachetools/func.py:<module>.fifo_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "lfu_cache"
                                        (.fnref "cachetools/func.py:<module>.lfu_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "lru_cache"
                                        (.fnref "cachetools/func.py:<module>.lru_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "rr_cache"
                                        (.fnref "cachetools/func.py:<module>.rr_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "ttl_cache"
                                        (.fnref "cachetools/func.py:<module>.ttl_cache"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/func.py")
                                        "_UnboundTTLCache"
                                        (.fnref
                                        "cachetools/func.py:<module>._UnboundTTLCache<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "hashkey"
                                        (.fnref "cachetools/keys.py:<module>.hashkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "methodkey"
                                        (.fnref "cachetools/keys.py:<module>.methodkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "typedkey"
                                        (.fnref "cachetools/keys.py:<module>.typedkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "typedmethodkey"
                                        (.fnref "cachetools/keys.py:<module>.typedmethodkey"))
                                        (.seq
                                        (.setField
                                        (.name "<module>cachetools/keys.py")
                                        "_HashedTuple"
                                        (.fnref "cachetools/keys.py:<module>._HashedTuple<meta>"))
                                        .skip)))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/__init__.py:<module>`  (from `cachetools/__init__.py`) -/
def f_cachetools___init___py__module_ : Func :=
  { name := "cachetools/__init__.py:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "getattr" (.fnref "__builtin.getattr"))
            (.seq
              (.setGlobal "isinstance" (.fnref "__builtin.isinstance"))
              (.seq
                (.setGlobal "iter" (.fnref "__builtin.iter"))
                (.seq
                  (.setGlobal "len" (.fnref "__builtin.len"))
                  (.seq
                    (.setGlobal "next" (.fnref "__builtin.next"))
                    (.seq
                      (.setGlobal "repr" (.fnref "__builtin.repr"))
                      (.seq
                        (.setGlobal "sorted" (.fnref "__builtin.sorted"))
                        (.seq
                          (.setGlobal "staticmethod" (.fnref "__builtin.staticmethod"))
                          (.seq
                            (.setGlobal "super" (.fnref "__builtin.super"))
                            (.seq
                              (.setGlobal "object" (.fnref "__builtin.object<meta>"))
                              (.seq
                                (.setGlobal "property" (.fnref "__builtin.property<meta>"))
                                (.seq
                                  (.setGlobal "set" (.fnref "__builtin.set<meta>"))
                                  (.seq
                                    (.setGlobal "type" (.fnref "__builtin.type<meta>"))
                                    (.seq
                                      (.expr
                                        (.lit
                                        (.str "Extensible memoizing collections and decorators.")))
                                      (.seq
                                        (.setGlobal
                                        "__all__"
                                        (.tupleE
                                        [ (.lit (.str "Cache"))
                                        , (.lit (.str "FIFOCache"))
                                        , (.lit (.str "LFUCache"))
                                        , (.lit (.str "LRUCache"))
                                        , (.lit (.str "RRCache"))
                                        , (.lit (.str "TLRUCache"))
                                        , (.lit (.str "TTLCache"))
                                        , (.lit (.str "cached"))
                                        , (.lit (.str "cachedmethod")) ]))
                                        (.seq
                                        (.setGlobal "__version__" (.lit (.str "7.1.7")))
                                        (.seq
                                        (.setGlobal
                                        "collections"
                                        (.fnref "<absent:external>collections"))
                                        (.seq
                                        (.setGlobal
                                        "collections"
                                        (.fnref "<absent:external>collections"))
                                        (.seq
                                        (.setGlobal
                                        "functools"
                                        (.fnref "<absent:external>functools"))
                                        (.seq
                                        (.setGlobal "heapq" (.fnref "<absent:external>heapq"))
                                        (.seq
                                        (.setGlobal "random" (.fnref "<absent:external>random"))
                                        (.seq
                                        (.setGlobal "time" (.fnref "<absent:external>time"))
                                        (.seq
                                        (.setGlobal "keys" (.name "<module>cachetools/keys.py"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "_DefaultSize"
                                        (.fnref
                                        "cachetools/__init__.py:<module>._DefaultSize<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/__init__.py:<module>._DefaultSize<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Cache"
                                        (.fnref "cachetools/__init__.py:<module>.Cache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.Cache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "FIFOCache"
                                        (.fnref "cachetools/__init__.py:<module>.FIFOCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.FIFOCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "LFUCache"
                                        (.fnref "cachetools/__init__.py:<module>.LFUCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.LFUCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "LRUCache"
                                        (.fnref "cachetools/__init__.py:<module>.LRUCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.LRUCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "RRCache"
                                        (.fnref "cachetools/__init__.py:<module>.RRCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.RRCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "_TimedCache"
                                        (.fnref "cachetools/__init__.py:<module>._TimedCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>._TimedCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "TTLCache"
                                        (.fnref "cachetools/__init__.py:<module>.TTLCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.TTLCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "TLRUCache"
                                        (.fnref "cachetools/__init__.py:<module>.TLRUCache<meta>"))
                                        (.expr
                                        (.fnref "cachetools/__init__.py:<module>.TLRUCache<meta>")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setGlobal
                                        "_CacheInfo"
                                        (.mcall
                                        (.name "collections")
                                        "namedtuple"
                                        [ (.lit (.str "CacheInfo"))
                                        , (.listE
                                        [ (.lit (.str "hits"))
                                        , (.lit (.str "misses"))
                                        , (.lit (.str "maxsize"))
                                        , (.lit (.str "currsize")) ]) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setGlobal
                                        "cached"
                                        (.fnref "cachetools/__init__.py:<module>.cached"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setGlobal
                                        "cachedmethod"
                                        (.fnref "cachetools/__init__.py:<module>.cachedmethod"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/_cached.py:<module>`  (from `cachetools/_cached.py`) -/
def f_cachetools__cached_py__module_ : Func :=
  { name := "cachetools/_cached.py:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "set" (.fnref "__builtin.set<meta>"))
            (.seq
              (.expr (.lit (.str "Function decorator helpers.")))
              (.seq
                (.setGlobal "__all__" (.tupleE []))
                (.seq
                  (.setGlobal "functools" (.fnref "<absent:external>functools"))
                  (.seq
                    (.setGlobal
                      "_condition_info"
                      (.fnref "cachetools/_cached.py:<module>._condition_info"))
                    (.seq
                      (.setGlobal
                        "_locked_info"
                        (.fnref "cachetools/_cached.py:<module>._locked_info"))
                      (.seq
                        (.setGlobal
                          "_unlocked_info"
                          (.fnref "cachetools/_cached.py:<module>._unlocked_info"))
                        (.seq
                          (.setGlobal
                            "_uncached_info"
                            (.fnref "cachetools/_cached.py:<module>._uncached_info"))
                          (.seq
                            (.setGlobal
                              "_condition"
                              (.fnref "cachetools/_cached.py:<module>._condition"))
                            (.seq
                              (.setGlobal
                                "_locked"
                                (.fnref "cachetools/_cached.py:<module>._locked"))
                              (.seq
                                (.setGlobal
                                  "_unlocked"
                                  (.fnref "cachetools/_cached.py:<module>._unlocked"))
                                (.seq
                                  (.setGlobal
                                    "_uncached"
                                    (.fnref "cachetools/_cached.py:<module>._uncached"))
                                  (.seq
                                    (.setGlobal
                                      "_wrapper"
                                      (.fnref "cachetools/_cached.py:<module>._wrapper"))
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))))) }

/-- `cachetools/_cachedmethod.py:<module>`  (from `cachetools/_cachedmethod.py`) -/
def f_cachetools__cachedmethod_py__module_ : Func :=
  { name := "cachetools/_cachedmethod.py:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "isinstance" (.fnref "__builtin.isinstance"))
            (.seq
              (.setGlobal "super" (.fnref "__builtin.super"))
              (.seq
                (.setGlobal "property" (.fnref "__builtin.property<meta>"))
                (.seq
                  (.setGlobal "set" (.fnref "__builtin.set<meta>"))
                  (.seq
                    (.setGlobal "type" (.fnref "__builtin.type<meta>"))
                    (.seq
                      (.expr (.lit (.str "Method decorator helpers.")))
                      (.seq
                        (.setGlobal "__all__" (.tupleE []))
                        (.seq
                          (.setGlobal "functools" (.fnref "<absent:external>functools"))
                          (.seq
                            (.setGlobal "warnings" (.fnref "<absent:external>warnings"))
                            (.seq
                              (.setGlobal "weakref" (.fnref "<absent:external>weakref"))
                              (.seq
                                (.setGlobal
                                  "_warn_classmethod"
                                  (.fnref "cachetools/_cachedmethod.py:<module>._warn_classmethod"))
                                (.seq
                                  (.setGlobal
                                    "_warn_instance_dict"
                                    (.fnref
                                      "cachetools/_cachedmethod.py:<module>._warn_instance_dict"))
                                  (.seq
                                    (.setGlobal
                                      "_none"
                                      (.fnref "cachetools/_cachedmethod.py:<module>._none"))
                                    (.seq
                                      (.seq
                                        (.setGlobal
                                        "_WrapperBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._WrapperBase<meta>")))
                                      (.seq
                                        (.seq
                                        (.setGlobal
                                        "_DescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DescriptorBase<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DescriptorBase<meta>")))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "_DeprecatedDescriptorBase"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase<meta>"))
                                        (.expr
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._DeprecatedDescriptorBase<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "_condition_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._condition_info"))
                                        (.seq
                                        (.setGlobal
                                        "_locked_info"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked_info"))
                                        (.seq
                                        (.setGlobal
                                        "_unlocked_info"
                                        (.fnref
                                        "cachetools/_cachedmethod.py:<module>._unlocked_info"))
                                        (.seq
                                        (.setGlobal
                                        "_condition"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._condition"))
                                        (.seq
                                        (.setGlobal
                                        "_locked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._locked"))
                                        (.seq
                                        (.setGlobal
                                        "_unlocked"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._unlocked"))
                                        (.seq
                                        (.setGlobal
                                        "_wrapper"
                                        (.fnref "cachetools/_cachedmethod.py:<module>._wrapper"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/func.py:<module>`  (from `cachetools/func.py`) -/
def f_cachetools_func_py__module_ : Func :=
  { name := "cachetools/func.py:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "callable" (.fnref "__builtin.callable"))
            (.seq
              (.setGlobal "property" (.fnref "__builtin.property<meta>"))
              (.seq
                (.expr
                  (.lit (.str "`functools.lru_cache` compatible memoizing function decorators.")))
                (.seq
                  (.setGlobal
                    "__all__"
                    (.tupleE
                      [ (.lit (.str "fifo_cache"))
                      , (.lit (.str "lfu_cache"))
                      , (.lit (.str "lru_cache"))
                      , (.lit (.str "rr_cache"))
                      , (.lit (.str "ttl_cache")) ]))
                  (.seq
                    (.setGlobal "math" (.fnref "<absent:external>math"))
                    (.seq
                      (.setGlobal "random" (.fnref "<absent:external>random"))
                      (.seq
                        (.setGlobal "time" (.fnref "<absent:external>time"))
                        (.seq
                          (.setGlobal "Condition" (.fnref "<absent:external>threading"))
                          (.seq
                            (.seq
                              (.setGlobal
                                "FIFOCache"
                                (.fnref "cachetools/__init__.py:<module>.FIFOCache<meta>"))
                              (.seq
                                (.setGlobal
                                  "LFUCache"
                                  (.fnref "cachetools/__init__.py:<module>.LFUCache<meta>"))
                                (.seq
                                  (.setGlobal
                                    "LRUCache"
                                    (.fnref "cachetools/__init__.py:<module>.LRUCache<meta>"))
                                  (.seq
                                    (.setGlobal
                                      "RRCache"
                                      (.fnref "cachetools/__init__.py:<module>.RRCache<meta>"))
                                    (.seq
                                      (.setGlobal
                                        "TTLCache"
                                        (.fnref "cachetools/__init__.py:<module>.TTLCache<meta>"))
                                      (.seq
                                        (.setGlobal
                                        "cached"
                                        (.fnref "cachetools/__init__.py:<module>.cached"))
                                        (.setGlobal "keys" (.name "<module>cachetools/keys.py"))))))))
                            (.seq
                              (.seq
                                (.setGlobal
                                  "_UnboundTTLCache"
                                  (.fnref "cachetools/func.py:<module>._UnboundTTLCache<meta>"))
                                (.expr
                                  (.fnref "cachetools/func.py:<module>._UnboundTTLCache<meta>")))
                              (.seq
                                (.setGlobal "_cache" (.fnref "cachetools/func.py:<module>._cache"))
                                (.seq
                                  (.setGlobal
                                    "fifo_cache"
                                    (.fnref "cachetools/func.py:<module>.fifo_cache"))
                                  (.seq
                                    (.setGlobal
                                      "lfu_cache"
                                      (.fnref "cachetools/func.py:<module>.lfu_cache"))
                                    (.seq
                                      (.setGlobal
                                        "lru_cache"
                                        (.fnref "cachetools/func.py:<module>.lru_cache"))
                                      (.seq
                                        (.setGlobal
                                        "rr_cache"
                                        (.fnref "cachetools/func.py:<module>.rr_cache"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.setGlobal
                                        "ttl_cache"
                                        (.fnref "cachetools/func.py:<module>.ttl_cache"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))))))))))))) }

/-- `cachetools/keys.py:<module>`  (from `cachetools/keys.py`) -/
def f_cachetools_keys_py__module_ : Func :=
  { name := "cachetools/keys.py:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "hash" (.fnref "__builtin.hash"))
            (.seq
              (.setGlobal "sorted" (.fnref "__builtin.sorted"))
              (.seq
                (.setGlobal "tuple" (.fnref "__builtin.tuple<meta>"))
                (.seq
                  (.setGlobal "type" (.fnref "__builtin.type<meta>"))
                  (.seq
                    (.expr (.lit (.str "Key functions for memoizing decorators.")))
                    (.seq
                      (.setGlobal
                        "__all__"
                        (.tupleE
                          [ (.lit (.str "hashkey"))
                          , (.lit (.str "methodkey"))
                          , (.lit (.str "typedkey"))
                          , (.lit (.str "typedmethodkey")) ]))
                      (.seq
                        (.seq
                          (.setGlobal
                            "_HashedTuple"
                            (.fnref "cachetools/keys.py:<module>._HashedTuple<meta>"))
                          (.expr (.fnref "cachetools/keys.py:<module>._HashedTuple<meta>")))
                        (.seq
                          (.setGlobal "_kwmark" (.tupleE [(.name "_HashedTuple")]))
                          (.seq
                            (.setGlobal "hashkey" (.fnref "cachetools/keys.py:<module>.hashkey"))
                            (.seq
                              (.setGlobal
                                "methodkey"
                                (.fnref "cachetools/keys.py:<module>.methodkey"))
                              (.seq
                                (.setGlobal
                                  "typedkey"
                                  (.fnref "cachetools/keys.py:<module>.typedkey"))
                                (.seq
                                  .skip
                                  (.seq
                                    (.setGlobal
                                      "typedmethodkey"
                                      (.fnref "cachetools/keys.py:<module>.typedmethodkey"))
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f__module_objects___module_, f_cachetools___init___py__module_, f_cachetools__cached_py__module_, f_cachetools__cachedmethod_py__module_, f_cachetools_func_py__module_, f_cachetools_keys_py__module_]

/-- Source dialect: `.python` (integer division/modulo convention).

`builtinBases` lists the classes whose base is a builtin type, so that
`Expr.alloc` builds a `Val.bobj` and not an opaque `Val.ref`. -/
def program : Program := { dialect := .python, builtinBases := [("_HashedTuple", .tuple)], funcs := [
  f_cachetools___init___py__module___DefaultSize___getitem__,
  f_cachetools___init___py__module___DefaultSize___setitem__,
  f_cachetools___init___py__module___DefaultSize_pop,
  f_cachetools___init___py__module___DefaultSize_clear,
  f_cachetools___init___py__module__Cache___init__,
  f_cachetools___init___py__module__Cache___repr__,
  f_cachetools___init___py__module__Cache___getitem__,
  f_cachetools___init___py__module__Cache___setitem__,
  f_cachetools___init___py__module__Cache___delitem__,
  f_cachetools___init___py__module__Cache___contains__,
  f_cachetools___init___py__module__Cache___missing__,
  f_cachetools___init___py__module__Cache___iter__,
  f_cachetools___init___py__module__Cache___len__,
  f_cachetools___init___py__module__Cache_get,
  f_cachetools___init___py__module__Cache_pop,
  f_cachetools___init___py__module__Cache_setdefault,
  f_cachetools___init___py__module__Cache_clear,
  f_cachetools___init___py__module__Cache_maxsize,
  f_cachetools___init___py__module__Cache_currsize,
  f_cachetools___init___py__module__Cache_getsizeof,
  f_cachetools___init___py__module__FIFOCache___init__,
  f_cachetools___init___py__module__FIFOCache___setitem__,
  f_cachetools___init___py__module__FIFOCache___delitem__,
  f_cachetools___init___py__module__FIFOCache_popitem,
  f_cachetools___init___py__module__FIFOCache_clear,
  f_cachetools___init___py__module__LFUCache__Link___init__,
  f_cachetools___init___py__module__LFUCache__Link_unlink,
  f_cachetools___init___py__module__LFUCache___init__,
  f_cachetools___init___py__module__LFUCache___getitem__,
  f_cachetools___init___py__module__LFUCache___setitem__,
  f_cachetools___init___py__module__LFUCache___delitem__,
  f_cachetools___init___py__module__LFUCache_popitem,
  f_cachetools___init___py__module__LFUCache_clear,
  f_cachetools___init___py__module__LFUCache__LFUCache__touch,
  f_cachetools___init___py__module__LRUCache___init__,
  f_cachetools___init___py__module__LRUCache___getitem__,
  f_cachetools___init___py__module__LRUCache___setitem__,
  f_cachetools___init___py__module__LRUCache___delitem__,
  f_cachetools___init___py__module__LRUCache_popitem,
  f_cachetools___init___py__module__LRUCache_clear,
  f_cachetools___init___py__module__LRUCache__LRUCache__touch,
  f_cachetools___init___py__module__RRCache___init__,
  f_cachetools___init___py__module__RRCache_choice,
  f_cachetools___init___py__module__RRCache___setitem__,
  f_cachetools___init___py__module__RRCache___delitem__,
  f_cachetools___init___py__module__RRCache_popitem,
  f_cachetools___init___py__module__RRCache_clear,
  f_cachetools___init___py__module___TimedCache__Timer___init__,
  f_cachetools___init___py__module___TimedCache__Timer___call__,
  f_cachetools___init___py__module___TimedCache__Timer___enter__,
  f_cachetools___init___py__module___TimedCache__Timer___exit__,
  f_cachetools___init___py__module___TimedCache__Timer___reduce__,
  f_cachetools___init___py__module___TimedCache__Timer___getattr__,
  f_cachetools___init___py__module___TimedCache___init__,
  f_cachetools___init___py__module___TimedCache___repr__,
  f_cachetools___init___py__module___TimedCache___len__,
  f_cachetools___init___py__module___TimedCache_currsize,
  f_cachetools___init___py__module___TimedCache_timer,
  f_cachetools___init___py__module___TimedCache_get,
  f_cachetools___init___py__module___TimedCache_pop,
  f_cachetools___init___py__module___TimedCache_setdefault,
  f_cachetools___init___py__module___TimedCache_clear,
  f_cachetools___init___py__module___TimedCache_expire,
  f_cachetools___init___py__module__TTLCache__Link___init__,
  f_cachetools___init___py__module__TTLCache__Link___reduce__,
  f_cachetools___init___py__module__TTLCache__Link_unlink,
  f_cachetools___init___py__module__TTLCache___init__,
  f_cachetools___init___py__module__TTLCache___contains__,
  f_cachetools___init___py__module__TTLCache___getitem__,
  f_cachetools___init___py__module__TTLCache___setitem__,
  f_cachetools___init___py__module__TTLCache___delitem__,
  f_cachetools___init___py__module__TTLCache___iter__,
  f_cachetools___init___py__module__TTLCache___setstate__,
  f_cachetools___init___py__module__TTLCache___setstate____lambda_0,
  f_cachetools___init___py__module__TTLCache_ttl,
  f_cachetools___init___py__module__TTLCache_expire,
  f_cachetools___init___py__module__TTLCache_popitem,
  f_cachetools___init___py__module__TTLCache_clear,
  f_cachetools___init___py__module__TTLCache__TTLCache__getlink,
  f_cachetools___init___py__module__TLRUCache__Item___init__,
  f_cachetools___init___py__module__TLRUCache__Item___lt__,
  f_cachetools___init___py__module__TLRUCache___init__,
  f_cachetools___init___py__module__TLRUCache___contains__,
  f_cachetools___init___py__module__TLRUCache___getitem__,
  f_cachetools___init___py__module__TLRUCache___setitem__,
  f_cachetools___init___py__module__TLRUCache___delitem__,
  f_cachetools___init___py__module__TLRUCache___iter__,
  f_cachetools___init___py__module__TLRUCache_ttu,
  f_cachetools___init___py__module__TLRUCache_expire,
  f_cachetools___init___py__module__TLRUCache_popitem,
  f_cachetools___init___py__module__TLRUCache_clear,
  f_cachetools___init___py__module__TLRUCache__TLRUCache__getitem,
  f_cachetools___init___py__module__TLRUCache__TLRUCache__delitem,
  f_cachetools___init___py__module__cached,
  f_cachetools___init___py__module__cached_decorator,
  f_cachetools___init___py__module__cached_decorator_make_info_redefined_0,
  f_cachetools___init___py__module__cached_decorator_make_info_redefined_1,
  f_cachetools___init___py__module__cached_decorator_make_info,
  f_cachetools___init___py__module__cachedmethod,
  f_cachetools___init___py__module__cachedmethod_decorator,
  f_cachetools___init___py__module__cachedmethod_decorator_make_info,
  f_cachetools__cached_py__module___condition_info,
  f_cachetools__cached_py__module___condition_info_wrapper,
  f_cachetools__cached_py__module___condition_info_wrapper__lambda_0,
  f_cachetools__cached_py__module___condition_info_cache_clear,
  f_cachetools__cached_py__module___condition_info_cache_info,
  f_cachetools__cached_py__module___locked_info,
  f_cachetools__cached_py__module___locked_info_wrapper,
  f_cachetools__cached_py__module___locked_info_cache_clear,
  f_cachetools__cached_py__module___locked_info_cache_info,
  f_cachetools__cached_py__module___unlocked_info,
  f_cachetools__cached_py__module___unlocked_info_wrapper,
  f_cachetools__cached_py__module___unlocked_info_cache_clear,
  f_cachetools__cached_py__module___unlocked_info_cache_info,
  f_cachetools__cached_py__module___uncached_info,
  f_cachetools__cached_py__module___uncached_info_wrapper,
  f_cachetools__cached_py__module___uncached_info_cache_clear,
  f_cachetools__cached_py__module___uncached_info__lambda_1,
  f_cachetools__cached_py__module___condition,
  f_cachetools__cached_py__module___condition_wrapper,
  f_cachetools__cached_py__module___condition_wrapper__lambda_2,
  f_cachetools__cached_py__module___condition_cache_clear,
  f_cachetools__cached_py__module___locked,
  f_cachetools__cached_py__module___locked_wrapper,
  f_cachetools__cached_py__module___locked_cache_clear,
  f_cachetools__cached_py__module___unlocked,
  f_cachetools__cached_py__module___unlocked_wrapper,
  f_cachetools__cached_py__module___unlocked__lambda_3,
  f_cachetools__cached_py__module___uncached,
  f_cachetools__cached_py__module___uncached_wrapper,
  f_cachetools__cached_py__module___uncached__lambda_4,
  f_cachetools__cached_py__module___wrapper,
  f_cachetools__cachedmethod_py__module___warn_classmethod,
  f_cachetools__cachedmethod_py__module___warn_instance_dict,
  f_cachetools__cachedmethod_py__module___none,
  f_cachetools__cachedmethod_py__module___WrapperBase___init__,
  f_cachetools__cachedmethod_py__module___WrapperBase___call__,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_clear,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_key,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_lock,
  f_cachetools__cachedmethod_py__module___WrapperBase_cache_condition,
  f_cachetools__cachedmethod_py__module___DescriptorBase___init__,
  f_cachetools__cachedmethod_py__module___DescriptorBase___set_name__,
  f_cachetools__cachedmethod_py__module___DescriptorBase___get__,
  f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___init__,
  f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase___call__,
  f_cachetools__cachedmethod_py__module___DeprecatedDescriptorBase_cache_clear,
  f_cachetools__cachedmethod_py__module___condition_info,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper___call____lambda_0,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___condition_info_Descriptor_Wrapper_cache_info,
  f_cachetools__cachedmethod_py__module___locked_info,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___locked_info_Descriptor_Wrapper_cache_info,
  f_cachetools__cachedmethod_py__module___unlocked_info,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___unlocked_info_Descriptor_Wrapper_cache_info,
  f_cachetools__cachedmethod_py__module___condition,
  f_cachetools__cachedmethod_py__module___condition_wrapper,
  f_cachetools__cachedmethod_py__module___condition_wrapper__lambda_1,
  f_cachetools__cachedmethod_py__module___condition_cache_clear,
  f_cachetools__cachedmethod_py__module___condition_classmethod_wrapper,
  f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___condition_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___locked,
  f_cachetools__cachedmethod_py__module___locked_wrapper,
  f_cachetools__cachedmethod_py__module___locked_cache_clear,
  f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___locked_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___unlocked,
  f_cachetools__cachedmethod_py__module___unlocked_wrapper,
  f_cachetools__cachedmethod_py__module___unlocked_cache_clear,
  f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___init__,
  f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper___call__,
  f_cachetools__cachedmethod_py__module___unlocked_Descriptor_Wrapper_cache_clear,
  f_cachetools__cachedmethod_py__module___wrapper,
  f_cachetools_func_py__module___UnboundTTLCache___init__,
  f_cachetools_func_py__module___UnboundTTLCache_maxsize,
  f_cachetools_func_py__module___cache,
  f_cachetools_func_py__module___cache_decorator,
  f_cachetools_func_py__module___cache_decorator__lambda_0,
  f_cachetools_func_py__module__fifo_cache,
  f_cachetools_func_py__module__lfu_cache,
  f_cachetools_func_py__module__lru_cache,
  f_cachetools_func_py__module__rr_cache,
  f_cachetools_func_py__module__ttl_cache,
  f_cachetools_keys_py__module___HashedTuple___hash__,
  f_cachetools_keys_py__module___HashedTuple___add__,
  f_cachetools_keys_py__module___HashedTuple___radd__,
  f_cachetools_keys_py__module___HashedTuple___getstate__,
  f_cachetools_keys_py__module__hashkey,
  f_cachetools_keys_py__module__methodkey,
  f_cachetools_keys_py__module__typedkey,
  f_cachetools_keys_py__module__typedmethodkey,
  f__module_objects___module_,
  f_cachetools___init___py__module_,
  f_cachetools__cached_py__module_,
  f_cachetools__cachedmethod_py__module_,
  f_cachetools_func_py__module_,
  f_cachetools_keys_py__module_
] }

end Autoform.Generated.Cachetools