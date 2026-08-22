# autoform — turning arbitrary codebases into autoformalized Lean 4

## 0. The central bet

Do **not** translate code directly into Lean definitions and then guess theorems about
them. That is the failure mode of naive "LLM → Lean" pipelines: the translation is
unfaithful, nothing checks the faithfulness, and the theorems are vacuous or trivially
true.

Instead: **formalize the language, not the program.**

1. Build (or import) a **definitional interpreter** for the source language *inside Lean*:
   `Syntax` inductive types + `step : Config → Option Config` / `eval : Env → Expr → Value`.
   This is the semantic kernel. It is written once per language, reviewed hard, and reused.
2. Mechanically **transpile the codebase into a term of that `Syntax` type** — a deep
   embedding. This step is a parser + printer, not an LLM: it is total, deterministic,
   and diff-testable.
3. Every property about the program is then a theorem *about `eval` applied to a
   concrete AST*. Specifications become statable and **checkable against reality** by
   differential-testing `eval` against the real runtime.
4. Layer a **shallow embedding** on top for tractability: prove once that the deep term
   is observationally equivalent to a clean Lean function, then reason in the clean
   world (the Aeneas/`hax` playbook, and the only approach that scales).

The agentic system handles what the compiler cannot: **choosing what to formalize,
inventing the specification, discovering invariants, and driving proof search** — with the
Lean kernel as an unfakeable oracle at every step.

## 1. Why this is now feasible off-the-shelf

Reusable open-source pieces, by layer:

**Front end / parsing (language → AST, no LLM)**
- `tree-sitter` — grammars for ~50 languages, error-tolerant, uniform CST API.
- Language-native: `libclang`, `rustc`/`charon`, `go/ast`, `ast` (Python), `ts-morph`.
- LLVM IR / MLIR as a convergence point for compiled languages.
- WebAssembly as a *universal* target: one small semantics covers everything that
  compiles to Wasm. Wasm semantics exist in Coq (Wasmcert) and K.

**Existing formal semantics to reuse rather than rebuild**
- **K framework**: complete executable semantics for C (`C-semantics`), Java, JavaScript,
  Python, EVM (KEVM), LLVM, x86. The largest single asset in the field.
  Strategy: use K semantics as the *reference oracle* and as the spec ported to Lean.
- **CompCert** (C, Coq), **CakeML** (ML, HOL4), **JSCert/JSExplain** (JS, Coq),
  **Iris/RustBelt** (Rust concurrency, Coq) — port targets, and correctness benchmarks.
- **Aeneas** (Rust → pure functional Lean, via `charon`) — *already emits Lean 4*.
  For Rust, this is steps 1–3 done.
- **hax** (Rust → F*/Coq/**Lean**) — same, different subset, panic-freedom focus.
- **Lampe** (Noir → Lean), **Verus**/**Kani**/**Creusot** (Rust, SMT tier).
- **Lean core**: `Std`, `Mathlib`, `Batteries`; `bv_decide` (bit-blasting to CaDiCaL with
  LRAT-checked certificates) makes bitvector/word-level obligations nearly free.

**Proof automation**
- `aesop` (white-box search), `duper` (superposition), `lean-auto` + `duper` = hammer,
  `lean-smt` / `smt_lean` (cvc5 with proof reconstruction), `polyrith`, `omega`, `decide`,
  `native_decide` (with its trust caveat), `bv_decide`, `simp`+`grind`.
- Neural: **DeepSeek-Prover-V2**, **Kimina-Prover**, **Goedel-Prover-V2**, **InternLM2.5-StepProver**
  — open-weight, all speak Lean 4, all usable as tactic/proof proposers behind a kernel check.
- Retrieval: **LeanDojo/ReProver** (premise selection over Mathlib), **LeanAgent**,
  `Mathlib`'s `exact?`/`apply?`/`loogle`/Moogle.

**Interaction substrate (the agent's hands)**
- **`leanprover-community/repl`** — JSON-in/JSON-out Lean REPL with *proof-state pickling*.
  Load-bearing: it gives snapshot/restore, so tree search over proof states is cheap.
- **Pantograph** — richer goal-level API, designed for ML agents.
- **LeanDojo** — trace a whole repo, extract premises, replay tactics.
- `lake` + `reservoir` for builds; `leanchecker` (ships with the toolchain since v4.28.0;
  the standalone `lean4checker` is deprecated) for external re-verification of `.olean`s;
  `#print axioms` to detect `sorryAx`/`Classical.choice`/`native_decide` leakage.

## 2. Architecture

```
                    ┌──────────────────────────────────────────────┐
                    │  ORCHESTRATOR (planner + budget + ledger)     │
                    └───────────────┬───────────────────────────────┘
   ┌────────────┬──────────────┬────┴─────────┬──────────────┬──────────────┐
   │            │              │              │              │              │
Cartographer  Semanticist  Transpiler    Specifier      Prover        Auditor
(map repo)   (lang kernel) (AST→Lean)  (invent specs) (prove)    (attack results)
   │            │              │              │              │              │
   └────────────┴──────────────┴──────┬───────┴──────────────┴──────────────┘
                                      │
                       ORACLES (non-negotiable ground truth)
             Lean kernel · leanchecker --fresh · differential fuzzing vs real runtime
             · property-based tests · SMT countermodels · #print axioms
```

### Layer 1 — Cartographer (no formalization yet)
Builds the *formalization graph*: modules, call graph, purity/effect classification,
external boundaries (I/O, FFI, network, unsafe, reflection), and a **formalizability
score** per function. Output: a topologically sorted work queue where leaves are pure
total functions and the frontier grows outward. Tools: tree-sitter + language servers +
`cloc` + existing call-graph tools. About 90% deterministic tooling, 10% LLM
(classifying what a module is for).

Product decision: **the whole codebase is never formalized.** A *verified core* is
formalized and machine-checked *boundary contracts* are generated for everything else.

### Layer 2 — Semanticist (per language, one-time, human-reviewed)
Produces `Autoform/Lang/<L>/{Syntax,Semantics,Metatheory}.lean`:
- `inductive Expr | Stmt | Value`
- `Env`, `Heap`, `step`/`eval` (fuel-indexed or well-founded)
- Determinism, progress, preservation lemmas
- A `Decidable`/executable `eval` so `#eval` works — this enables the oracle below.

**The conformance oracle**: extract `eval` to native code (Lean's compiler, or via
`native_decide`-free extraction), then differential-fuzz it against the *real*
interpreter/compiler on a corpus (the language's own test suite — CPython's, V8's
test262, csmith for C). Any divergence is a bug in the semantics, found automatically.
This is what makes an LLM-assisted semantics trustworthy: the semantics is testable
before it is proved.

Agent loop: propose rule → fuzz → shrink counterexample → repair rule → prove
metatheory lemma → repeat. Escalate to a human on repeated failure.

### Layer 3 — Transpiler (deterministic, verified-by-testing)
`source AST → Lean term of type Expr`. Written as ordinary code, not LLM output. Two
correctness checks:
- **Round-trip**: `pretty(parse(s)) ≡ s` modulo formatting, on the whole repo.
- **Behavioral**: `eval (transpile p) input == run p input` on the project's own test
  suite. The project's tests become the transpiler's validation set: every repo ships its
  own conformance suite.

Unsupported constructs are *not* silently dropped; they become `Expr.opaque (name, spec)`
holes that carry an explicit, tracked assumption. The ledger counts them.

### Layer 4 — Specifier (the agentic part)
Given a function's deep-embedded AST, propose Lean statements worth proving. Sources of
specifications, in descending order of trustworthiness:
1. **Existing artifacts**: type signatures, refinement types, assertions, `require`s,
   docstrings, doctests, unit tests, property tests (Hypothesis/QuickCheck strategies map
   almost directly to `∀`-statements), issue trackers, RFCs.
2. **Structural/safety specs, free for all code**: totality, no-panic, no-overflow,
   memory safety, termination, absence of division by zero, resource bounds.
   These need no domain knowledge and supply volume.
3. **Algebraic laws mined from behavior**: Daikon-style invariant detection over
   the test corpus, or fuzzing for candidate equalities (idempotence, commutativity,
   inverse pairs `decode ∘ encode = id`, monotonicity, refinement between two impls).
   Candidates are *conjectures*; the fuzzer prunes the false ones before a prover
   spends time on them.
4. **Cross-implementation equivalence**: the richest specs. `optimized == reference`,
   `new_version == old_version`, `rust_impl == c_impl`. Available from the repo's history.
5. **LLM-invented domain specs** — lowest trust, always fuzz-tested before proof attempt,
   always human-reviewed before being counted as an assurance claim.

**Anti-vacuity gate** (mandatory): every candidate theorem must survive
(a) mutation testing — inject a bug into the implementation; if the theorem still proves,
it is vacuous; (b) `#print axioms` clean; (c) hypothesis satisfiability check — prove the
premises are inhabited, else the theorem is about the empty set. A "proved" theorem
that fails the mutation gate is scored as a *failure*, not a success.

### Layer 5 — Prover (portfolio + search, kernel-gated)
Tiered escalation with a per-goal budget:
1. `rfl` / `decide` / `simp` / `omega` / `bv_decide` / `norm_num` — cheapest.
2. `aesop`, `exact?`, hammer (`lean-auto`+`duper`), `lean-smt`+cvc5.
3. Neural proposer (DeepSeek-Prover-V2 / Kimina) whole-proof sampling, n=8..64.
4. Best-first tree search over REPL proof states (pickled snapshots), premise retrieval
   from ReProver, with the neural model as the tactic policy.
5. Decompose: agent proposes lemmas, recurses. Generalize the goal (often easier).
6. Give up → record as an open obligation.

Everything the prover emits is checked by the Lean kernel; the agent cannot fake a
proof. The reward signal is not LLM-judged, so the system is safe to run unsupervised.

### Layer 6 — Auditor (adversarial)
Independent agent that tries to break the result: hunts `sorry`, `axiom`, `unsafe`,
`native_decide`, `@[implemented_by]` divergence, opaque holes, vacuous hypotheses,
spec/implementation drift (does the theorem talk about the AST that ships?), and
re-verifies all `.olean`s with `leanchecker --fresh` in a clean environment. Produces the
**trust ledger**.

## 3. The trust ledger (the product)

The deliverable is not "your codebase is verified." It is a machine-generated
statement of *what is proved, about what model, under what assumptions*:

```
module payments/ledger.py
  formalized:      412 / 507 LOC  (81%)
  opaque holes:    3   (datetime.now, decimal ctx, network)
  semantics:       Python-subset v0.4  (conformance: 99.2% on CPython test suite,
                                        12 known divergences, listed)
  transpiler:      behavioral-equiv on 1,204/1,204 project tests
  theorems proved: 47   (mutation-gated: 44 survive, 3 flagged vacuous)
    - no unhandled exception on well-typed input   ✔ kernel-checked
    - balance conservation across transfer         ✔ kernel-checked
    - idempotence of settle                        ✔ kernel-checked
  axioms used:     Classical.choice, propext, Quot.sound   (no sorryAx)
  open obligations: 9
```

A reader can locate the trust boundary from this directly.

## 4. Sequencing (what to build in what order)

**Phase 0 — Skeleton (weeks 1–3).** Lean repo + `lake`, REPL harness with pickled state,
theorem/obligation database (SQLite), `#print axioms` + `leanchecker` gate in CI, trust
ledger renderer. No agents yet. Test the plumbing on hand-written examples.

**Phase 1 — Pick one narrow language.** *Recommendation: start with Rust via Aeneas*
(semantics + transpiler already exist and emit Lean 4, so Layers 2–3 are skipped and
Layers 4–6 can be validated immediately) **and** in parallel a **toy imperative
language / Wasm subset** with the whole stack owned end-to-end. Do not start with
Python or C++: dynamic and undefined-behavior-rich languages cost a year.

**Phase 2 — Specifier + anti-vacuity.** The research risk. Build the mutation
gate before the spec generator.

**Phase 3 — Prover portfolio.** Cheap tactics first; measure what fraction each tier
closes. Add the neural tier only once tier-1/2 is exhausted and instrumented — for
safety/structural specs the classical tools close a large majority.

**Phase 4 — Second language (Python or C subset), from K semantics as reference.**
The Semanticist agent and conformance fuzzer become necessary here.

**Phase 5 — Shallow-embedding refinement.** Prove deep ≈ shallow, so proofs scale.

## 5. Failure modes

- **Semantic gap.** A proof about a semantics that does not match the real runtime is
  worthless. The conformance fuzzer is not optional infrastructure.
- **Vacuous theorems.** LLMs readily produce provable-and-useless statements. Mutation
  testing is the counterweight.
- **Concurrency, I/O, FFI, reflection, `eval`, dynamic loading** — no cheap answers.
  Design the opaque-hole mechanism first-class from day one.
- **Proof burden grows superlinearly with program size.** Hence verified core +
  contracts, never whole-repo.
- **Mathlib drift / build times.** Pin toolchains; cache aggressively; expect the
  formalization to bit-rot without CI.

## 6. Minimal viable demo

Take a small, pure Rust crate (a parser, a codec, a data structure), run
`charon`+Aeneas to get Lean, auto-generate: totality + panic-freedom + `decode ∘ encode
= id` + equivalence against a reference implementation, prove them with the portfolio,
mutation-gate them, and emit the trust ledger. If that pipeline runs unattended on 20
crates with an honest ledger, the architecture is validated and every later language is
Layers 2–3 only.

## 7. CSLib (cslib.io / `leanprover/cslib`) — where it fits

**What it is:** "Mathlib for computer science." Lean 4, from de Moura, Barrett, Montesi,
Chaudhuri, Kohli, Grundy, Rademaker, Yingchareonthawornchai (arXiv 2602.04846), with
Amazon / Google DeepMind / Stanford backing. Contains: operational semantics
infrastructure, program equivalences, automata models, linear logic, some verified
sorting/searching. Stated goals include a *program-reasoning toolkit* and
"a shared vocabulary to train models on."

It is load-bearing for Layer 2 and changes the plan.

Do not invent private conventions for `Syntax` / `step` / `eval` / refinement. Build each
language kernel **against CSLib's operational-semantics API** (LTS, bisimulation, program
equivalence):

- **Layer 2 substrate.** CSLib's bundled operational semantics + computable-definition
  discipline is the interface the Semanticist agent should target. Free
  metatheory: determinism/confluence lemmas, bisimulation congruence, equivalence
  combinators.
- **Layer 5 (deep ≈ shallow) becomes reuse, not research.** The refinement step —
  "prove the deep-embedded AST is observationally equivalent to a clean Lean function" —
  is a program-equivalence/bisimulation obligation. That machinery belongs in CSLib,
  not in this repo.
- **Layer 5 retrieval.** ReProver/LeanDojo premise selection is Mathlib-shaped and
  performs badly on CS goals. **CSLibPremiseBench** (arXiv 2605.14549) provides
  structure-guided premise retrieval over CSLib theorems — use it for CS-flavored
  obligations and keep ReProver for the arithmetic/Mathlib tail.
- **Distribution.** Language semantics are generic, reusable, and what CSLib wants.
  Upstream them. That converts a per-language cost center into shared, externally
  reviewed infrastructure; external review of the semantics contributes more to
  trustworthiness than internal work.

**What CSLib is not.** It is a *metatheory and pedagogy* library, not a pipeline for
verifying real codebases. It will not ship a production-grade C, Python, or JS semantics
soon; it says nothing about extracting ASTs from a real repo, inventing specifications,
anti-vacuity, or trust accounting. Layers 1, 3, 4, 6 — Cartographer, Transpiler,
Specifier, Auditor — remain ours. CSLib gives a foundation and a vocabulary, not the
product.

**Risks:** young library, expect API churn (pin revisions, run against `main` in CI);
breadth-first coverage, so depth may be thin where needed; governance/contribution
standards are Mathlib-strict, so upstreaming has latency — vendor locally, upstream
asynchronously.

**Revised Phase 0/1 action:** before writing any semantics, read `Cslib/Semantics`
and the whitepaper, and write the toy-imperative-language kernel *as a CSLib-conformant
development*. If the language kernels cannot be phrased in CSLib's vocabulary, that
indicates either an error on our side or an upstream contribution.

## 8. Build/buy inventory — what is hand-rolled

Default posture: buy or adapt everything; hand-roll only what is irreducible.
Re-audited after CSLib, this is the full component list.

| Component | Verdict | Source |
|---|---|---|
| Parsing / AST extraction | BUY | tree-sitter, `charon`, libclang, `go/ast`, LLVM/MLIR |
| Language semantics | ADAPT | CSLib, K (C/Java/JS/Python/EVM), CompCert, CakeML, Wasmcert |
| Rust front-to-Lean | BUY | Aeneas + charon, hax |
| Conformance corpora | BUY | test262, CPython suite, csmith, Wasm spec tests, AFL++/libFuzzer |
| Dynamic invariant mining | ADAPT | Daikon |
| LLM spec synthesis | ADAPT | SpecGen, Spec-Agent, Quokka, counterexample-guided refinement lineage |
| Mutation-based spec validation | ADAPT | **IronSpec**; MutantChick/MetaCoq (proof-assistant precedent); `universalmutator`, `cargo-mutants`, PIT |
| Vacuity detection | ADAPT | model-checking vacuity literature, ported to Hoare/refinement obligations |
| Proof automation | BUY | aesop, duper, lean-auto, lean-smt/cvc5, bv_decide, omega, grind |
| Neural provers | BUY | DeepSeek-Prover-V2, Kimina, Goedel-V2 |
| Proof-state interaction / search substrate | BUY | `leanprover-community/repl` (pickling), Pantograph |
| Premise retrieval | BUY | ReProver/LeanDojo (Mathlib tail) + CSLibPremiseBench (CS goals) |
| Agent orchestration | BUY | Claude Agent SDK or equivalent — **do not write an agent framework** |
| Build, cache, kernel re-check | BUY | lake, Reservoir, `leanchecker` (in-toolchain), `#print axioms` |
| Attestation / findings format | BUY | in-toto/SLSA predicates, SARIF |
| Sandboxed execution | BUY | containers / nsjail |

**Correction to §4:** the Specifier and the anti-vacuity gate were listed as the research
risk. They are not novel — IronSpec already does mutation-based specification validation,
mutation analysis for Coq exists, and SpecGen/Spec-Agent already do
counterexample-guided LLM spec synthesis validated against a verifier. The work there is
integration and porting to Lean, not invention. Downgrade the risk and reuse the designs.

### What is ours (and where the effort goes)

1. **The transpiler + effect-boundary calculus, per language.** Source AST → deep-embedded
   Lean term, with a principled treatment of what cannot be embedded (I/O, FFI, reflection,
   concurrency, dynamic loading) as tracked `opaque` holes carrying explicit assumptions.
   This is the bulk of the engineering mass and no external project supplies it.
   *Main cost lever:* target **Wasm** and collapse N language front-ends into one semantics
   plus N existing production compilers. The cost is lost source-level structure — the
   shallow-embedding refinement gets harder — so treat it as a per-language decision, not
   a global one.
2. **The Cartographer.** Formalization graph, effect classification, formalizability
   scoring, and the *budget policy* deciding what to formalize and in what order. No prior
   art, because repo-scale is not attempted elsewhere; everyone formalizes a hand-picked
   artifact.
3. **The trust-ledger calculus.** Composing heterogeneous evidence — kernel proof,
   semantics conformance %, transpiler behavioral-equivalence rate, mutation score, hole
   count, axiom set — into one auditable claim with an explicit trust boundary. The
   *format* is in-toto/SARIF; the *composition rules* are ours, and are the product.
4. **Thin oracle harnesses**: differential-fuzz driver, Lean-side mutation-gate driver,
   obligation database.

Everything else is integration. A design discussion concluding "we should build our own
X" where X is not on that list of four is a signal to search harder first.

## 9. Killing #2, and making #4 Lean-native

### #2 Cartographer — mostly buyable

The formalization graph is a **code property graph** plus a policy. The graph is a solved,
commoditized problem:

- **Joern** (`joernio/joern`) — open-source CPG platform, C/C++/Java/JS/Python/Kotlin/binary,
  Scala DSL for queries. Effectively open-source CodeQL. Front-ends: CDT (C/C++), Soot
  (JVM bytecode), Ghidra (binaries). AST + CFG + PDG + call graph in one queryable graph.
- **CodeQL** — better ergonomics and maturity, more restrictive licensing; usable for
  effect/taint classification if terms permit.
- **SCIP** (Sourcegraph) — cross-language symbol/xref index; protobuf, 8× smaller and 3×
  faster than LSIF, with production indexers per language.
- **Glean** (Meta) — repo-scale fact database, ingests SCIP (~550 LoC mapping). Use if
  scale demands it; SCIP alone is enough to start.
- **Stack Graphs** (GitHub) / **tree-sitter-graph** — incremental name resolution.
- Purity/effect classification: LLVM `FunctionAttrs` (`readnone`/`readonly`/`nounwind`) for
  anything with an LLVM path, Rust's own type system, **Infer** for effect/nullability.

**Revised verdict:** the Cartographer is *Joern or SCIP+Glean, plus ~a few hundred lines of
policy*: formalizability scoring, effect classification into the opaque-hole taxonomy, and
the budget/ordering decision. The policy is ours; the graph is not. Drop it from the
"build" list — it is a query layer over a bought index.

That leaves the ours list at **three**: the transpiler + effect-boundary
calculus, the trust-ledger calculus, and the harness.

### #4 harness — build it in Lean

Everything in the harness that touches Lean terms should be written in Lean:

- **Plausible** (`leanprover-community/plausible`) — QuickCheck for Lean 4, integrated into
  the *tactic framework*: given a goal, it derives generators from typeclasses and tries
  to **refute** it with a counterexample. This is the conjecture-pruning and
  anti-vacuity engine, operating on the *same statement object* the prover will attack.
  No serialization layer, no drift between the property fuzzed and the theorem proved.
- **Chamelean** — extends Plausible to auto-derive generators, enumerators, and checkers
  for **inductive relations**. Our semantics *are* inductive relations (`step`, typing
  judgments), so this is the differential-fuzzing engine for Layer 2.
- **LSpec** — Lean test framework with `checkPlausibleIO'` for deferred runtime property
  tests; the CI-facing runner.
- **Lean's own metaprogramming** — Lean beats Coq structurally here: mutation analysis
  needs no MetaCoq analog, because `Lean.Environment` / `ConstantInfo` / `Lean.Meta` are
  first-class in-language. Mutating a definition, re-elaborating dependents, and checking
  whether the proof survives is an ordinary Lean program.
- **Axiom/trust audit** — `#print axioms`, `leanchecker`, environment diffing: all
  in-language. Ledger evidence extraction becomes a Lean `Lake` script, not an external
  scraper parsing logs.
- **`FVSpec`** (arXiv 2606.01008) — 11,039 real-world Python property-based tests scraped
  and 2,772 auto-translated into 9,415 Lean 4 specifications with proof-obligation
  placeholders. Direct evidence for the §4 claim that a repo's own property
  tests are the highest-value spec source, and both a corpus and a benchmark for
  the Specifier. Use it as the evaluation set.

**The resulting pipeline:** candidate spec → Plausible tries to refute it →
survivors go to the proof portfolio → mutation gate re-runs via Lean metaprogramming →
`#print axioms` audit → ledger. One language, one statement representation, end to end.
The only non-Lean glue left is process orchestration, external-runtime differential
testing, and the code-property-graph query layer.

**Where not to use Lean:** orchestration, HTTP, DB, sandboxing, driving external runtimes.
Thin ecosystem, and no benefit — those components never touch a Lean term.

## 10. #3 (trust ledger) — also mostly prior art

The "composition calculus for heterogeneous verification evidence" is the **assurance
case** field, standardized for decades in safety-critical engineering. Do not reinvent it.

- **SACM** (OMG *Structured Assurance Case Metamodel*, v2.1) — the target model. Unifies
  and extends **GSN** (Goal Structuring Notation) and **CAE** (Claims–Arguments–Evidence).
  Models our three concerns: *arguments* (claims + inferential links),
  *artifacts* (evidence: results, techniques, activities, traceability), and *terminology*.
  Provides fine-grained modularity and argument-evidence traceability.
- **Isabelle/SACM** (arXiv 2009.12154) — *integration of mechanized formal proof into
  SACM assurance cases*. The same problem, already solved once for Isabelle;
  SACM claims admit structured expressions, so formal statements embed directly.
  Port the pattern to Lean rather than inventing a ledger format.
- **ACCESS** (arXiv 2403.15236), model-based system assurance tooling (arXiv 1905.02427),
  Adelard/ASCE, AMASS/OpenCert — tooling and metrics, including auto-generated assurance
  case fragments and case metrics, which is what we want to emit per module.
- Transport/provenance envelope stays **in-toto/SLSA** + **SARIF** for findings.
- Domain precedent for arguing *from* formal evidence: **DO-178C / DO-333** (formal
  methods supplement), ISO 26262.

**Revised verdict:** the ledger is *SACM as the model + Isabelle/SACM's proof-integration
pattern + in-toto as the envelope*. Ours is only the domain-specific evidence types
(semantics conformance rate, transpiler behavioral-equivalence rate, hole count, mutation
score, axiom basis) and the rules for combining them into a claim. That is a schema and a
few hundred lines, not a research program.

**The ours list is now two items:**

1. **The transpiler + effect-boundary calculus, per language.**
2. **The domain evidence types and their combination rules** (a SACM profile).

Plus integration glue. That is the scope of this project; everything else is
assembly of existing parts, which is the expected outcome of a build/buy audit.

## 11. FVSpec — the Specifier's corpus, baseline, and leaderboard

**[GaloisInc/fvspec](https://github.com/GaloisInc/fvspec)** — benchmark of **9,415 Lean 4
verification challenges** derived from **2,772 of 11,039 real-world Python property-based
tests** scraped from **333 open-source repositories**. Leaderboard at `fvspec.galois.com`;
corpus on Hugging Face. **Correction, established by fetching the artifacts:** the GitHub
repo ships the generation pipeline, leaderboard and baselines — *not* the formalizations;
`GaloisInc/fvspec-pbt` is the upstream *Python* PBT corpus; the Lean benchmark is a third
artifact, **`GaloisInc/fvspec-fv`** (`train.jsonl`, 235 MB, exactly 9,415 rows).

Relevance:

- **It is a working instance of Layer 4.** The pipeline scrapes GitHub for Hypothesis
  PBTs and uses a **three-agent LLM pipeline** to transpile them to Lean specs,
  autoformalizing each function under test. Each problem ships four artifacts, with
  `sorry` placeholders (~3 formalizations per PBT). Read their agent decomposition before
  writing ours.
- **It corroborates the §4 ordering.** Their highest-yield spec source is the repo's own
  property-based tests — the same conclusion, arrived at independently and at scale.
  Yield: **25%** of scraped PBTs translated. Plan for that hit rate.
- **It is a suitable eval set:** the source PBTs were written by practicing engineers and
  were **never formally verified**, so the resulting theorems are largely absent from
  model training data. Contamination risk is low.
- **It provides baselines** — the paper reports automated and model-based proof
  generation baselines, so the portfolio has a comparison point on day one.
- **It is a target for the anti-vacuity gate.** Their specs are LLM-transpiled
  and *not* mutation-validated. Running the Plausible refutation gate and dependency-vacuity
  check across all 9,415 would (a) exercise the harness at scale and (b) contribute
  back to the benchmark.

**Action:** adopt FVSpec as the Phase-2 evaluation harness, and make "refute/confirm the
FVSpec specification set" the first at-scale run of the harness.

**Revised inventory rows:**

| Component | Verdict | Source |
|---|---|---|
| Spec corpus + eval + leaderboard | BUY | FVSpec, `GaloisInc/fvspec-pbt` |
| PBT→Lean spec transpilation agents | ADAPT | FVSpec's three-agent pipeline |
| Evidence/assurance model | ADAPT | SACM 2.1, Isabelle/SACM, GSN/CAE |

## 12. Built: the CPG as universal front end

The §8 conclusion was that the per-language transpiler is the irreducible cost centre,
with Wasm floated as the way to collapse N front ends into one. A better answer was
already in the Layer 1 tooling: **Joern's code property graph is itself a universal AST.**

C, C++, Java, JavaScript, Python, Kotlin and binaries all normalize to one node
vocabulary — `CALL` / `IDENTIFIER` / `LITERAL` / `CONTROL_STRUCTURE` / `RETURN` / `BLOCK`,
with operators as `<operator>.*` calls. So the transpiler is written **once**:

* `Autoform/Lang/Core/*` — a semantics for that vocabulary, not for any one language.
* `cartographer/export_ast.sc` — CPG → neutral JSON AST.
* `cartographer/render_lean.py` — JSON → Lean.

Unlike the Wasm route, source-level structure survives, so the shallow-embedding
refinement stays tractable. Verified on Python (424 functions of a real repo) and C from
the same code path.

### The dialect lesson

The conformance oracle's first run reported `fmod(6,-9)`: CPython `-3`, Lean `6`. Python
floors integer division and modulo; C and Java truncate toward zero; the semantics had
silently picked one.

Patching the operator is not the fix. The fix is structural: a **universal core language
must be parameterized by the dialects it unifies**, and the transpiler must record which
one produced each program. Otherwise the semantics is right for one language and silently
wrong for the rest — the "semantic gap" failure of §5, and a class of bug that proving
would never surface, because the proofs would be about the wrong `eval`.

Generalization: every place the core language merges constructs that look alike
across languages (string mutability, integer width and overflow, evaluation order, name
resolution, equality) is a latent dialect parameter. Assume there are more, and let the
oracle find them rather than enumerating them up front.

## 13. Gaps remaining — measured, not estimated

Numbers below are from `cachetools` (233 real functions after excluding Joern's
synthetic `<metaClassAdapter>` wrappers).

### Tier 1 — coverage: which gap unblocks the most code

Marginal value = functions whose *only* remaining blockers fall in that group.

| Gap | Newly hole-free | Cumulative |
|---|---|---|
| **Objects** (`fieldAccess` 183, `METHOD_REF` 58, `TYPE_REF` 46, `alloc` 30, non-identifier LHS 58) | **+166** | 176 |
| Exceptions (`TRY` 48, `raise` 12) | +35 | 211 |
| Containers (tuple/list literals, `starredUnpack` 33) + identity (`is`/`in`) | +44 | 255 |
| Iteration (`FOR`) | **+0** | — |

Two conclusions:

* **Objects dominate.** That one gap is worth more than every other gap combined.
  Attribute access, method dispatch, allocation, and assignment-to-non-identifier are one
  feature, and they need a heap, which the Core semantics does not have.
* **`FOR` has zero marginal value.** Every function containing a `FOR` is blocked by
  something else too, so fixing it in isolation would unblock nothing. The marginal metric
  beats the frequency histogram for prioritisation.

Cheap unmapped operators worth closing regardless (`floorDiv` — found by testing and
currently a hole for every Python `//`, `in`/`notIn`, `is`/`isNot`, `+=`/`-=`,
conditional expressions, `pass`, `delete`).

### Tier 2 — fidelity: bugs in what *is* translated

These matter more than coverage, because they are wrong rather than absent.

1. **Integer width is unmodelled.** Confirmed: `mulbig(100000, 100000)` gives
   `1410065408` in C (32-bit wraparound) and `10000000000` in Core. A latent dialect
   parameter of the kind §12 predicted. C/Java/Go need fixed-width wrapping
   integers; Python needs bignums. This silently produces wrong answers.
2. **No short-circuit evaluation.** Confirmed: `b != 0 and a % b == 0` with `b = 0`
   returns `0` in Python, but Core eagerly evaluates both operands and yields
   `hole "mod-by-zero"`. Currently conservative (a hole, not a wrong answer) only
   because Core has no side effects; it becomes a soundness bug once
   assignment-in-expression or effectful calls are modelled.
3. **Differential coverage is thin.** Only module-level, int→int functions are compared.
   `cachetools` yielded **zero** comparable cases. Needed: instance construction for
   methods, comparison of lists/strings/dicts, and — the highest-leverage item, from §3
   and still unimplemented — **driving the differential harness from the repository's own
   test suite** instead of random arguments.
4. **No heap, aliasing, or mutation.** A prerequisite for Tier 1's objects.
5. **Scoping is naive.** `Env.set` conses; no block scope, globals, closures, or
   `nonlocal`.
6. **Strings are conflated.** Python `str` and C `char*` are the same `Val.str`.

### Tier 3 — the verification half does not exist

The system produces *verifiable* code and proves nothing about it.

* No proof portfolio (aesop / lean-auto+duper / lean-smt / bv_decide / neural tier).
* No specification synthesis; the FVSpec run (§11) has not happened.
* The mutation gate is only the **dependency-vacuity** check, which is necessary but not
  sufficient. Source-level mutation — the sufficient test — is unbuilt.
* No SACM ledger schema (§10); the ledger is still ad-hoc text.
* **The deep ≈ shallow refinement has not been started.** Without it, proofs are
  conducted against `evalExpr`/`execStmt` applied to a concrete AST, and will not scale
  past toy functions. This is the largest architectural debt.

### Tier 4 — engineering

No CI; kernel re-check not in the loop; Cartographer scoring weights uncalibrated
(operator dispatch inflates fan-out); build times dominated by Specimen/Plausible.

### If you do one thing next

**Objects + a heap.** It unblocks 166 functions (5% → ~76% on `cachetools`), and it is a
prerequisite for making the differential harness meaningful on real code, which is what
makes every later number trustworthy. Integer width is a close second because it
is actively wrong rather than missing.

## 14. Execution log — Tier 1 spine and Tier 3

### Tier 1: the Core language now has a heap

`Autoform/Lang/Core/{Syntax,Semantics}.lean` were rewritten to add what §13 measured as
the dominant gap:

* **Objects** — `Val.ref`, an explicit `Heap` of `Obj { cls, fields }`, `Expr.field`,
  `Expr.mcall` with dispatch on the receiver's class, `Expr.alloc` running `__init__`,
  `Stmt.setField`. The heap is threaded explicitly through `evalExpr`/`execStmt` rather
  than hidden in a monad, so the fuel recursion stays structural and the
  interpreter remains total.
* **Exceptions** — `EResult.exn` / `Ctl.exn`, `Stmt.raise`, `Stmt.tryCatch`. Division by
  zero and out-of-range indexing now raise `ZeroDivisionError` / `IndexError` / `KeyError`
  instead of being holes.
* **Containers** — `Val.list`/`tuple`/`dict`, `listE`/`tupleE`/`dictE`, `inOp`, `isOp`
  (reference identity for objects, structural for immediates), `cond`.
* **Iteration** — `Stmt.forIn` over any `Val.iterable`, with `break`/`continue`.
* **Name resolution** — `Ctx.resolve` falls back from exact name to *unique* suffix match,
  because Joern emits fully-qualified names while call sites carry short ones. An
  ambiguous match resolves to a hole, not a guess.

`Stmt.setIndex` is deliberately still a hole (`setIndex:immutable-containers`): container
mutation needs boxed containers, and inventing an answer would be the
silent-mistranslation failure this project exists to prevent.

### Tier 3: the mutation gate found real vacuity, and closing it worked

`scripts/mutate.py` scored `evalStmt_sound` at **2 killed / 6 survived (25%, WEAK)**, and
every survivor was a mutation of `evalBExpr`. The diagnosis generalizes:

> `BigStep`'s `iteTrue`/`iteFalse`/`loopTrue`/`loopFalse` side conditions are *themselves*
> stated in terms of `evalBExpr`. Mutating `evalBExpr` therefore mutates both sides of the
> equation at once, and the proof goes through unchanged.

This is the vacuity class `#audit_depends` **cannot** see — `evalStmt_sound` does depend on
`evalBExpr` transitively, it simply says nothing about it. It is the concrete argument for
§4's "dependency vacuity is necessary but not sufficient".

The fix was to pin `evalBExpr` against something not defined in terms of itself — the
integer order and equality on `evalExpr`'s results (`Characterization` section in
`Autoform/Lang/Imp/Semantics.lean`). Re-running the gate: **8 killed / 0 survived, 100%,
HAS TEETH**.

*Caveat on the measurement:* when a mutant makes the module fail to compile, every theorem
in that module is recorded as having killed it, so per-theorem attribution is coarse. The
aggregate claim (these mutants are now caught) is sound; the per-theorem breakdown is not
yet trustworthy and should be refined by isolating theorems into separate modules.

### Tier 3: audit, portfolio, assurance case

* `scripts/audit_all.py` sweeps all **952** declarations: axiom basis is `propext` (225),
  `Quot.sound` (42), `Classical.choice` (15) — **zero** `sorryAx`/`ofReduceBool`/
  `ofReduceNat`, zero project axioms. `Autoform/Lang/Core/*` verified free of
  `sorry`/`partial`/`unsafe`/`native_decide`/`@[implemented_by]`/`@[extern]`, so the
  README's "total, no sorry" claim is checked rather than asserted.
  Two findings: `Autoform/Harness/Audit.lean` uses `partial def transitiveDeps`
  (the audit tool's own walker is unproven-terminating), and at the time **`lean4checker`
  was not installed** — since closed, see §23.
* `Autoform/Tactics/Portfolio.lean` implements the escalation ladder with an honesty
  guard: a rung counts as success only if it closes the goal *and* the proof
  term passes `hasSorry`/`hasExprMVar` screening; on exhaustion it errors with a full
  transcript, and unavailable tiers are printed so "unproved" is distinguishable from
  "not attempted". Open goals are recorded as `Obligation` *data*, never as admitted
  theorems.
* `scripts/sacm.py` + `docs/ledger-schema.md` replace the ad-hoc ledger with a SACM
  profile (Claim / ArgumentReasoning / ArtifactReference / Assumption / typed
  relationships) wrapped in an in-toto Statement. Every hole label becomes a named
  `Assumption` node, so untranslated constructs appear *in the argument* rather than
  vanishing. On Cachetools the top claim comes out **UNDEVELOPED**, which is correct, and
  it caught a provenance defect: `conformance.json` carried no module tag, so
  its numbers could not be attributed and the faithfulness claim was capped at WEAK
  rather than accepted.

## 15. FVSpec results — the anti-vacuity gate at scale

`scripts/fvspec.py` ran the vacuity screen over the **entire** benchmark: 9,415 problems
(9,352 analyzed, 63 with no recognizable theorem declaration reported as `not_analyzed`
rather than passing), **73,046 theorems**, 251 source repos, 78,751 `sorry` placeholders.

| Check | Problems | Theorems |
|---|---|---|
| dependency vacuity (statement names no implementation symbol) | 2,485 | 7,388 |
| opaque subject (subject is a spec-local `axiom`/`sorry` stub) | 1,359 | 3,959 |
| reflexive conclusion (`t = t`, closable by `rfl`) | 920 | 1,221 |
| no `sorry` obligation at all | 328 | 1,028 |
| trivial conclusion (`: True`) | 256 | 444 |
| unsatisfiable hypotheses | 9 | 13 |
| empty quantification | 2 | 2 |

**3,833 of 9,352 analyzed problems (41.0%) are flagged**; 10,699 of 73,046 theorems
(14.6%); 1,047 of the 2,772 canonical formalizations (37.8%).

The dominant pattern is directly relevant to our own Specifier: Python
*determinism* property-tests (`f(x) == f(x)`) transliterated literally into Lean, where
purity makes them `rfl` and therefore contentless. A property meaningful in a
language with mutable state and nondeterminism becomes vacuous when moved
into a pure setting. Spec translation is not spec preservation; §4's anti-vacuity gate
is load-bearing, and this is the empirical evidence.

Two limits carried in the report: survivors are labelled
`clean_static` ("no check that ran fired"), never "passed", with an explicit `not_checked`
list (Lean elaboration, Plausible refutation, mutation gate, axiom audit) — all of which
need Lean and are out of scope for a static screen. And the dataset's own
`actually_invokes_given` flag disagrees with our dependency check on 3,321 problems in
both directions; both are heuristics, and the report states the disagreement instead of
adjudicating it.

## 16. Tier 2: machine integers, and a choice that must be explicit

`Autoform/Lang/Core/Numeric.lean` closes §13 Tier 2 item 1 — the confirmed silent
mistranslation where `mulbig(100000,100000)` gave `10000000000` in Lean against `cc`'s
`1410065408`.

It follows §12's rule (parameterize, don't hardcode): `Width`, `IntType`
(unbounded / signed / unsigned × 8/16/32/64), `NumConfig` with presets for Python, C32,
C64, unsigned, Java, Go, and `Dialect.toNumConfig` as the hook into the interpreter.

The structural choice is that **`NumResult` has four outcomes**, mirroring the
discipline `EResult` already applies to evaluation:

| Outcome | Meaning |
|---|---|
| `ok v` | a defined result |
| `divZero` | division or remainder by zero |
| `trap r` | the language defines this as a runtime fault (Go's `INT_MIN / -1`) |
| **`ub r`** | **the language does not define this at all** |

C's signed overflow, `INT_MIN / -1`, and shifts past the width have *no* correct answer —
the program's meaning depends on the compiler. Returning a number there would be the same
category of error as the original modulo bug, and harder to detect. Wiring
`ub ↦ Expr.hole` keeps undefined behaviour out of proofs: a program that relies on UB
cannot be proved to do anything at that point.

### The configuration that must be recorded, not defaulted

`NumConfig.c32` uses `Policy.undefined` — what the C standard says, so UB *surfaces*.
`NumConfig.c32Wrapv` wraps — what `cc` actually does, so the differential oracle *agrees*.
Both are defensible and they are not interchangeable:

* Verifying with `c32Wrapv` proves things about the compiler that was tested, and
  will bless code whose behaviour another compiler is free to change.
* Verifying with `c32` finds UB, but then the differential harness reports divergences
  against `cc` that are not bugs in the semantics — they are the semantics declining to
  commit.

So this cannot be a hidden default. **The ledger must record which integer policy a
result was obtained under**, as it records the dialect; an assurance claim that
does not name its arithmetic model is not attributable. Current wiring picks `c32Wrapv`
so the conformance oracle stays meaningful; a verification run should flip to `c32`.

Proved: `wrap_inRange`, `wrap_of_inRange`, `wrap_wrap`, `finish_inRange`, and that the
Python config's operations equal plain `Int`/`Int.fdiv`/`Int.fmod`. Left as explicitly
stated open obligations (no `sorry`): the `wrap` ring-homomorphism laws, `shl_eq_mul`,
bitwise identities — closable via a `BitVec` refinement plus `bv_decide`.

## 17. The coverage metric was wrong — twice, in the same direction

Two corrections to the headline number, both found by testing the metric rather than
trusting it. Both moved it **down**.

1. **Synthetic inflation.** The first `cachetools` figure was 130/424 hole-free (30%).
   120 of those were Joern-synthesised `<metaClassAdapter>` wrappers duplicating real
   methods. Excluding them: **12/233 (5%)**.
2. **Static hole-freedom is an upper bound, not a guarantee.** `Func.total` only checks
   that the *AST* contains no holes. The interpreter can introduce holes at runtime:

   ```
   Func.total sneaky = true          -- statically clean
   run sneaky  3 ==> hole "field:attr:non-object"
   run sneaky2 3 ==> hole "call:not_translated"
   run sneaky3 3 ==> hole "index:unsupported"
   ```

   `call:` is the dangerous case. A call to a function that was never translated is, in the
   AST, indistinguishable from a call to one that was — so the metric counted functions as
   verifiable whose behaviour is unknown. Requiring **call closure** (every
   call/method target resolves inside the program) gives **6/233 (2%)**, and the ledger now
   reports a third figure, `dynamic-hole risk` (384 constructs), for the residue that is
   input-dependent and therefore the conformance oracle's business, not the type system's.

The pattern will recur: **a coverage metric computed from the same artifact it
describes will flatter itself.** Static hole-counting over an AST cannot see what the
interpreter does with that AST, exactly as `#audit_depends` cannot see whether a theorem
constrains what it mentions (§14) and as FVSpec's translated determinism properties cannot
see that purity made them vacuous (§15). Three instances of one failure mode: the check
and the thing checked share an assumption.

The defence is an oracle that does not share the artifact's assumptions. For semantics
that is the real runtime; for specifications it is mutation; for coverage it is execution.
Any number reported without one is an upper bound.

## 18. Tier 1 measured: objects closed the gap

Full pipeline on `cachetools` (233 real functions), before and after the Tier 1 work:

| metric | before | after |
|---|--:|--:|
| holes | 745 (20% of nodes) | **102 (2%)** |
| hole-free (upper bound) | 12 (5%) | **166 (71%)** |
| verifiable core (hole-free **and** call-closed) | 6 (2%) | **45 (19%)** |

§13 predicted "+166 from objects", and 166 landed. The marginal-value metric was correct.

### What the exporter work found

The CPG side mattered more than the Lean side, and several of §13's assumptions were
wrong:

* **`FOR` does not exist in a Python CPG.** The frontend pre-desugars every `for` and
  every comprehension into `tmp = e.__iter__()` plus a `WHILE` whose condition is an
  `UNKNOWN` node. §13's measurement of "`FOR` marginal value = +0" was right for the
  wrong reason — it was never a `control:FOR` hole, it was inside `expr:UNKNOWN`.
  Reconstructing `forIn` from that shape unlocked iteration.
* **A latent fidelity bug, removed.** `<operator>.and` / `.or` had been mapped to `&&`/`||`.
  They are **bitwise** `&`/`|` (the logical ones are `logicalAnd`/`logicalOr`), and Core has
  no bitwise operators — so that mapping computed the wrong answer. They are
  now holes. Same for float literals, which were becoming strings. This is the §12 lesson
  recurring: constructs that look alike across languages are the dangerous ones.

  **Update — they are no longer holes; they are bitwise operators.** `Core` now has `"&"`,
  `"|"`, `"^"`, `"<<"`, `">>"` and `">>>"` as operator strings of their own, implemented
  by `NumConfig.band`/`bor`/`bxor`/`shl`/`shr` at the dialect's width. They are *not*
  aliases of `"&&"`/`"||"` and must never become so; the two are separate `applyBinop`
  cases for that reason. `<operator>.not` was mapped to `"!"` by the same mistake
  in unary form — it is `~`, in C, C++, Java **and** Python — and now maps to `"~"`.

  The one place the operand's *type* is still needed is `>>`: it is arithmetic on a signed
  operand and logical on an unsigned one, Joern spells both `arithmeticShiftRight`, and a
  `Val.int` carries no signedness. The exporter chooses from the static type and emits
  `op:shiftRight:unknown-signedness` when it cannot — a hole that names the missing *type*,
  which is a different remedy from a missing semantics.
* **Resolved attribute access is not attribute access.** When Joern resolves `o.m`, it
  prepends the target, so the node has three children rather than two; those are `fnref`,
  not `field`.
* **`<operator>.alloc` is not the construction signal** — it appears only in metaclass
  adapters. Real construction is a call whose `methodFullName` ends in `.__init__`.

### What is deliberately still a hole (102 total)

Each is a case where a faithful translation is not available and inventing one would
be the §12 failure:

* `starredUnpack` (33) — `*args` has no Core representation; splicing it changes arity.
* `try/finally` where the body can `return`/`break` (29) — the non-escaping case *is*
  translated, as `tryCatch(B, e, F; raise e); F`. When control escapes, `ret` bypasses the
  handler and would skip the trailing `F`, so it stays a hole.
* `try/except/else` (11) — `else` must run only when nothing was raised *and* its own
  exceptions must not be caught. One `tryCatch` cannot express that.
* `nonlocal` (8), `del d[k]` (8), multi-`except` (1, the CPG discards exception types).

### The call-closure gap

166 hole-free but only 45 call-closed. The 121-function difference is functions that
contain no holes themselves but call something outside the translated program — mostly
Python builtins and stdlib. That is not a transpiler defect; **a function is only as
analysable as its callees**. The next work item is a modelled standard library, not more
CPG mapping.

## 19. Tier 2 closed, and the oracle caught itself lying

### The short-circuit bug became real, then was fixed

§13 Tier 2 item 2 recorded that `&&`/`||` evaluated both operands eagerly, and called it
conservative — a hole rather than a wrong answer — "only because Core has no side
effects". Adding exceptions removed that condition. With `%0` now raising, the harness
caught:

```
safemod(-11, 0):  cpython = 0,  lean = raised ZeroDivisionError
```

`b != 0 and a % b == 0` divides anyway. That is a wrong answer. `evalExpr` now
short-circuits before evaluating the right operand: **6/6 agree**.

The bug existed all along and was invisible until exceptions were first class. Fidelity
work makes other fidelity bugs findable; the gaps are not independent.

### `hole-free ≠ runnable`, confirmed independently

The harness found two supposedly hole-free `cachetools` functions that hit unresolvable
calls at runtime — `call:_CacheInfo`, `call:info`. This is §17's finding reached from
the other direction, by execution rather than static analysis, and is why the ledger
reports call-closure separately.

### The oracle was reading a stale artifact

A stale `.olean` was answering with the previous semantics. It produced 10 fictitious
divergences and 22 fake inconclusives before being noticed. The harness now runs
`lake build` on the generated module before comparing.

Generalization: this project's trust story rests on oracles that do not share the
artifact's assumptions (§17). An oracle reading a stale cache shares the *old* artifact's
assumptions, which is worse than having no oracle — it produces confident, specific,
wrong findings. **Any oracle must establish that it is reading the current artifact
before it reports anything.** That check belongs in the oracle, not in the caller.

### Measured conformance after Tier 2

| Corpus | functions (total / hole-free / exercised) | compared | agree | diverge | inconclusive |
|---|---|--:|--:|--:|--:|
| cachetools (test-suite driven) | 233 / 166 / 7 | 58 | **42/42 (100%)** | 0 | 16 |
| stress | 6 / 5 / 5 | 25 | 25/25 | 0 | 0 |
| sample | 5 / 2 / 2 | 10 | 10/10 | 0 | 0 |
| ctest (`cc`) | 7 / 6 / 6 | 25 | 25/25 | 0 | 0 |
| shortcircuit | 1 / 1 / 1 | 6 | 6/6 | 0 | 0 |

`cachetools` went from **zero** comparable cases to 42 compared and agreeing, including
method calls against reconstructed receivers, because the harness now drives from the
repository's own test suite (§3), snapshots the receiver into a Lean `Heap` literal, and
compares structured values and exceptions rather than only integers.

Coverage limits: 109 calls skipped because the receiver is a `tuple` subclass (a value,
not an object with fields — Core cannot represent it), 34 skipped for `float` arguments,
2 hole-free methods never reached by the suite.

### Tier 2 status

| item | status |
|---|---|
| 1. integer width | **closed** — `Numeric.lean` wired; `ub ↦ hole` |
| 2. short-circuit | **closed** |
| 3. differential coverage | **closed** — test-suite driven, structured values, exceptions, methods |
| 4. heap / aliasing / mutation | **closed** — done as part of Tier 1 |
| 5. naive scoping | open — no closures, globals, `nonlocal` (8 holes on cachetools) |
| 6. strings conflated | open — Python `str` and C `char*` are one `Val.str` |

## 20. Refinement: the largest debt

§13 called the missing deep≈shallow refinement the largest architectural debt,
because proving anything against `execStmt` applied to a concrete AST does not scale.
`Autoform/Refine.lean` closes it.

```lean
inductive Outcome | ret : Val → Outcome | raise : Val → Outcome
def Refines p name N dom spec : Prop :=
  ∀ args, dom args → ∀ fuel, N ≤ fuel → runFunc p fuel name args = (spec args).toEResult
```

Three design choices make it non-vacuous, each backed by a theorem:

* **`Outcome` has no `hole` and no `outOfFuel` constructor.** A refined function provably
  never reports either (`refines_not_hole`, `refines_terminates`). Exceptions *are*
  refinable — "raises `ZeroDivisionError`" is a specification — but hole and outOfFuel are
  statements about ignorance, so a spec cannot absorb them.
* **Fuel is universally quantified above a concrete bound**, not existential, so the answer
  must be fuel-stable.
* **`refines_unique`**: two shallow specs refining the same entry point agree on the domain.

Proved on real translated functions: `poly`, `clamp`, `cdiv` (C) and `add`, `absval`,
`cmpchain`, `fmod` (Python). `cdiv`/`fmod` are the dialect-sensitive pair — same shape,
`.cLike ↦ Int.tdiv`, `.python ↦ Int.fmod` — both proved.

### The two negative results

* `fdiv_not_refinable` — `ops.py:fdiv` contains `Expr.hole "op:floorDiv"`, and **no**
  shallow spec, at any fuel bound, on any domain containing a nonzero divisor, refines it.
  Holes are provably unspecifiable.
* `poly_not_refinable` — with fixed-width arithmetic wired in, `poly` does **not** refine
  `a*b + c - a` on the unrestricted domain. The witness is `a = b = 100000`, the same
  value that produced the original `1410065408` divergence against `cc`.

A bug found by the differential oracle, fixed by parameterizing the semantics, is now
recorded as a machine-checked impossibility theorem. `poly_refines` holds only under
`Fits32 (a*b) ∧ Fits32 (a*b+c) ∧ Fits32 (a*b+c-a)` — the purpose of the `dom` parameter.

`clamp_deep_idem` shows the payoff: idempotence is proved by `omega` on the plain Lean
function, then transferred to the deep term with no interpreter involved.

All headline theorems: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

Open obligations, stated rather than admitted: general fuel monotonicity for the full
language; loop invariants (`sumto`, `gcdish` are hole-free but need an invariant rule);
heap-mutating methods (need a representation predicate).

## 21. One more silent wrong number, found by the refinement layer

Wiring `Numeric` into `applyBinop` left `applyUnop` untouched, so unary minus still
returned mathematical negation unconditionally. Under `.cLike` that made `-INT_MIN`
evaluate to `2147483648`, a value that does not exist in a 32-bit signed integer.

This is the defect class `Numeric.lean` was built to eliminate, on a path
that was not checked. It was found not by the differential oracle (no test negated
`INT_MIN`) but by the **refinement layer**, which had to state `applyUnop_int_neg` as an
unconditional `rfl`; the unconditionality was the bug.

Now: negation routes through `NumConfig.neg`, and the C equation carries a `Fits32`
hypothesis like every other operator.

```
applyUnop .cLike  "-" (-2147483648)  ==>  -2147483648   (wraps, matching cc -fwrapv)
applyUnop .python "-" (-2147483648)  ==>   2147483648   (bignum, correct)
```

Third distinct oracle, third class of finding: differential testing catches semantics that
disagree with reality, mutation catches specifications that constrain nothing, and
proof catches operations that were never given a specification at all. Each sees a
failure mode the others miss, which is the argument for paying for all three.

## 22. Tier 2 items 5 and 6

### Item 6 — C strings are not Python strings

`Val.str` served both, and `applyBinop` applied Python semantics to both. In C:

* `+` on `char*` is **pointer arithmetic**, not concatenation.
* `<` / `>` compare **addresses**, not contents.
* `==` compares **addresses**, not contents — and `Val.beq` is structural, so this was
  returning the Python answer for C programs.

All three are now dialect-split: correct under `.python`, precise holes under `.cLike`
(`str:pointer-arithmetic-not-modelled`, `str:pointer-compare-not-modelled`,
`str:pointer-equality-not-modelled`). Third instance of the §12 pattern.

### Item 5 — scoping: closures and function values

Two additions:

* `Expr.closure f` builds `Val.clos f ρ`, capturing the enclosing bindings **by value**.
  `applyClosure` uses the captured bindings as the base environment, with parameters
  shadowing them.
* `Expr.name x` now falls back to the function table when `x` is not local, so a
  module-level function referenced as a value resolves to `Val.fn x` instead of `unit`.
  `Expr.call` dispatches through `Val.fn` / `Val.clos` held in variables.

Together these make decorators, factories, callbacks and other higher-order code
translatable rather than holed:

```
def make_adder(n): return inner     # inner(x) = x + n
use() = apply2(make_adder(10), 5)   ==>  15
```

**What is deliberately not done.** `nonlocal` *writes* remain a hole
(`scope:nonlocal-write`). Capture is by value, so a closure cannot mutate a binding in its
enclosing frame. Making that work requires variables to be shared mutable cells — every
scope a heap frame, `Env` becoming a `Ref` — which is a correct design and a large
refactor of the interpreter, and would require re-repairing the 74-theorem
refinement layer. Global *rebinding* (`global x; x = 5`) is unsupported for the same
reason.

The boundary: reads across scopes work and are correct; writes across
scopes are a hole. Implementing writes by copying values back would work on
simple cases and be silently wrong on aliased ones.

### Revised Tier 2 status

| item | status |
|---|---|
| 1. integer width | **closed** — including unary minus (§21) |
| 2. short-circuit | **closed** |
| 3. differential coverage | **closed** |
| 4. heap / aliasing / mutation | **closed** |
| 5. scoping | **closed for reads** — closures, function values, higher-order calls; cross-scope *writes* remain an explicit hole with a stated design for closing them |
| 6. strings conflated | **closed** |

## 23. Kernel re-verification — closed, and a trap avoided

Tier 4's last open gap was that the `.olean` files had never been re-checked by an
independent kernel. It is now closed.

**There was nothing to install.** `lean4checker` is deprecated: it was merged into the
Lean repository and ships as **`leanchecker`** with every toolchain from v4.28.0. We are
on v4.30.0-rc1, so it was already present at
`~/.elan/toolchains/*/bin/leanchecker`. There is no Homebrew formula, and none is needed.

```
lake env leanchecker --fresh Autoform     exit 0,  ~92s,  status VERIFIED
```

### The trap: non-fresh mode can silently pass

`leanchecker <Module>` without `--fresh` **can no-op on a module that has only imports and
no declarations of its own** — the shape of `Autoform.lean`. Demonstrated
directly: a scratch `Bad` module with an env-hacked bogus declaration plus a `Root` module
importing it — `leanchecker Root` exits 0 silently, while `leanchecker Bad` and
`leanchecker --fresh Root` both reject it.

The naive invocation would have produced a VERIFIED that checked nothing.
This is §19's lesson at the last link in the chain: an oracle that
silently passes is worse than no oracle. The audit uses `--fresh` by default
and records *which mode ran* in `audit.json`, because the two are not equally strong.

### Evidence the checker rejects bad input

Two independent demonstrations, since "exit 0" is also the shape of a no-op:

1. **Environment hacking** — `Environment.addDeclCore (doCheck := false)` installing
   `bogusFalse : False := False`. The elaborator writes the `.olean`; `leanchecker`
   exits 1 with `(kernel) declaration type mismatch`.
2. **Tampering this project's own build tree** — a copy of `Autoform/Refine.olean`
   recompiled with an injected bogus declaration. `leanchecker --fresh Autoform` exits 1
   with `while replaying declaration 'Autoform.tamperedFalse': (kernel) declaration type
   mismatch`. The untampered copy of the same scratch setup passes, so the failure is
   caused by the tamper and not by the harness.

Also verified: `LEANCHECKER=/usr/bin/false` → FAILED → VERDICT FAIL; an absent
binary → UNVERIFIED (never a pass), and `--strict` turns that into a failure. CI runs
`audit_all.py --strict`, so a missing checker fails the build rather than downgrading.

Current audit state: **PASS**, axiom sweep clean over 1,696 declarations
(`propext`, `Quot.sound`, `Classical.choice` only), kernel re-verification **VERIFIED**.

## 24. Globals, closures, and a coverage number that moved down

The CPG side of item 5 landed, and the exporter's findings sharpened the design.

### What the CPG says

* **`Method.local` is a *reference*, not a binding.** pysrc2cpg emits a `LOCAL` in the
  *inner* method for every name it closes over and for every module global it reads. A
  free-variable analysis that treats `LOCAL` as a binder concludes nothing ever captures —
  it reported 0 closures on cachetools. Bindings must come from parameters and assignment
  targets, which is Python's own rule.
* **`fullName` is the lexical nesting path**, so the scope chain is recoverable by prefix
  — but it **cannot be split on `.`**, because `cachetools/keys.py:<module>` itself ends in
  the dot-segment `py:<module>`. String surgery classifies module scope as an ordinary
  function and concludes every module-level `def` captures the module.
* **Module-level `def`/`class` are assignments**: `hashkey = def hashkey(...)`,
  `Cache = class Cache<meta>(...)`. So one rewrite of module-scope assignment to
  `setGlobal` makes constants, classes and functions resolvable together.
* **C `typeFullName` gives `char*` directly**, including on literals, so item 6 needed no
  inference.

### The numbers moved down

| | before | after |
|---|--:|--:|
| real functions hole-free | 166 | **148** |
| holes on real functions | 102 | **120** |

The 18 new holes are `scope:class-closure`. `cachetools/_cachedmethod.py` defines classes
*inside* functions, and their methods read the enclosing function's parameters. Those six
functions previously counted as hole-free while returning a class whose methods reference
names that exist nowhere in the translated program. `Expr.closure` names a *function*;
there is no constructor for a class-valued closure, and `fnref` would have been the
silently-wrong answer.

The C string result: on a purpose-built C corpus, **5/5 functions were reported
hole-free before and 1/5 after** — four of the five were being mistranslated,
`s + n` concatenating a pointer and `a < b` comparing contents instead of addresses.

Both movements are the metric becoming more honest, not the tool getting worse. Fourth
instance of §17's rule: a number computed without an oracle that disagrees with the
artifact will flatter itself.

### Open, and deliberately not guessed

* **Cross-file initializer ordering.** The transpiler emits one zero-argument `Func` per
  source module and `runMain` executes them in list order. The CPG does not give a
  cross-file dependency order, so a module reading another module's globals depends on
  list order. Recorded rather than resolved by a guessed topological sort.
* **`Expr.classClosure`** — the constructor that would close the 18 `scope:class-closure`
  holes.
* **`<metaClassCallHandler>` synthetics** pad the function count; the `synthetic` filter
  excludes `<metaClassAdapter>` but not these. Left alone so that this pass's numbers move
  for one reason only.

## 25. The oracle recovered, and found the next silent mistranslation

Adding globals regressed the differential harness to 0/0 — it started from an empty heap,
so every global read resolved to `unit`. Re-integrated via `initGlobals`, with two details:

* **Receiver addresses are computed Lean-side.** The globals frame occupies ref 0, so
  receiver objects must be allocated from `h₀.length` onward. Rather than trust Python
  arithmetic for that offset, the harness emits `Val.ref (base + k)` with
  `base := h₀.length` evaluated in Lean.
* **The harness checks its own setup before reporting.** Each case carries the class name
  Python recorded for every receiver; the runner refuses to compare unless the object at
  `gref` is still `<globals>` and each receiver's class matches, returning
  `harness:receiver-alias` / `harness:globals-frame-clobbered` as INCONCLUSIVE. Verified by
  fault injection: with `base - 1` — the off-by-one that would alias the globals
  frame — it reports the alias rather than a false agreement.

That is §19's rule applied to the oracle itself: an oracle must establish it is measuring
what it thinks it is measuring before it reports anything.

Reach went from 42 compared cases across 7 functions to **87 across 61**.

### The finding: Python private name mangling

All 16 divergences share one root cause. Inside a class body, CPython rewrites `__name` to
`_ClassName__name` at compile time. We emit

    .field (.name "self") "__maxsize"

while CPython stores `_Cache__maxsize`. The read misses and returns `unit`:

    Cache.maxsize():  cpython = 2,  lean = unit

Silently wrong, not absent — the same category as `floorDiv` and the bitwise `and`/`or`
mapping. The *value encoder* was not changed to expose unmangled aliases, which would have
made the numbers agree while leaving the transpiler wrong. Fixing the measurement to match
a broken artifact is what would destroy the conformance number's meaning.

### Ceilings on this corpus

The structural losses are now larger than the fixable ones: `skip_self_not_object` 1,527
(receivers that are `tuple`/`dict` subclasses, which Core cannot represent as objects),
`skip_unencodable_args` 534 (floats, locks, sets), `skip_varargs` 340. The 57 "no instance
reached by the test suite" skips are unrelated to globals and did not move.

Dominant inconclusive labels, i.e. what would buy the most oracle reach next:
`setField:non-object` (49), `call:set` (25), `mcall:__init__:non-object` (20),
`in:non-container` (15).

## 26. Name mangling, and a fix that paid twice

CPython rewrites `__name` to `_ClassName__name` inside a class body, at compile time. The
transpiler did not, so `Cache.maxsize` read a field that does not exist and returned
`unit` where CPython returned `2`. Sixteen divergences, one root cause.

The fix hooks in at two places — `asField` (the single source of the attribute
name for `field`, `setField` *and* `mcall`) and `mangledFullName` (the last segment of a
method's `fullName`) — so references and definitions move together. Fixing only one
side would have converted a silent wrong answer into a silent unresolvable call.
Verified against CPython `__dict__` on a purpose-built
corpus: `__priv`, `___three`, `__trail_` mangle; `__dun__` and `_one` do not; the
mangling class is the *lexically enclosing* class, not the receiver's, which is what makes
`Cache.__getitem__` reach `_Cache__data` even when `self` is an `LRUCache`.

Hole counts are unchanged — mangling is a renaming, not a coverage change.
Divergences went to **zero**.

### The second payoff

The harness recovers qualified names from the source AST (Python 3.9 has no
`co_qualname`), and it was not mangling them — so a traced call to `LFUCache.__touch`
never matched the translated `LFUCache._LFUCache__touch`, and two functions were silently
dropped from the oracle's reach. Applying the same rule there restored them, and one of
the two restored functions produced a new divergence:

    LFUCache._LFUCache__touch(tuple[ref 6]): cpython = unit, lean raised KeyError

The coverage fix and the bug it found were the same change. General shape: the oracle's
blind spots and the artifact's bugs are correlated, because both come from the same
unmodelled language rule. Fixing reach is how defects are found.

### That divergence was the apparatus, not the artifact

`__touch` begins `link = self.__links[key]`. The `key` argument arrives encoded as an
object reference (a `_HashedTuple` — a tuple subclass — snapshotted as a heap object),
while the keys stored inside the receiver's `__links` dict were encoded as tuple *values*.
`Val.beq` cannot equate `.ref n` with `.tuple [...]`, the lookup misses, and Core raises
`KeyError` where CPython succeeds.

The underlying defect is that the representability check applies to top-level arguments but
not to values nested inside a receiver's fields, so an unrepresentable nested value can
surface as a confident divergence. **An oracle must not report a disagreement it caused
itself** — the same discipline as §19's stale `.olean` and the receiver-alias guard of
§25, one level further in.

### Ceilings, restated with current numbers

`skip_self_not_object` 1,527 · `skip_unencodable_args` 521 · `skip_varargs` 340 ·
`skip_no_instance` 57. These dominate, and they bound how much of a real Python
codebase this oracle can reach regardless of translation coverage.

One practical note: `find_tests` did not locate `tests/` when given the repo root, because
the AST paths are relative to `src/`. The `src/`-layout-with-sibling-tests arrangement is
the modern default, so discovery needs to walk up from `src_root`.

## 27. The last divergence was the apparatus — the cause is a scope boundary

Resolved, with a different cause than the encoding inconsistency proposed in §26.

The failing case is `LFUCache.__touch` driven by `test_func.py`, whose helper is:

```python
class RecursiveEquals:
    def __hash__(self):      return hash(self._use_cache)
    def __eq__(self, other): return self._use_cache == other._use_cache
```

The test primes the cache with one instance and then looks up a **different instance that
compares equal**. CPython's dict lookup succeeds through `__hash__`/`__eq__`; Core compares
`Val`s structurally with `.ref` identity, misses, and raises `KeyError`.

**This is a scope boundary, not a bug.** A Python dict keyed by objects with user-defined
equality is outside what a structural `Val` comparison can model. 27 cases are now
refused on that ground and appear in `conformance.json` under `unencodable_reasons`
rather than being compared. Naming the boundary is the deliverable.

A second, independent silent-wrongness source was live in the same case: the encoder
**swallowed** nested representability failures, counting `dropped_fields` and continuing.
A dropped `__links` field reads back as `unit` in Core — an apparatus
artifact becoming a confident divergence. Representability is now recursive and fatal: an
unrepresentable value at any depth aborts the case, which is counted by reason rather than
compared.

Three further apparatus defects surfaced once refusal stopped hiding them:

* The return value was encoded with a **fresh** encoder, so a returned object got a
  colliding `ref`. One memo now spans the whole case, so a given Python object gets the
  same `Val` as receiver, nested field, argument and result.
* `Val.fn` spellings disagreed — CPython says `TTLCache._Link`, Joern says
  `cachetools/__init__.py:<module>.TTLCache._Link`. Now matched by dotted suffix and
  nothing looser, mirroring `Ctx.resolve`. Six more apparatus divergences.
* Callable *instances* were being encoded as `Val.fn`. Only routines, classes, `partial`
  and descriptors are functions; an instance with `__call__` has fields and is an object.
  Recovered 274 previously-refused cases.

### Result

| | before | after |
|---|--:|--:|
| compared cases | 67 | **99** |
| functions exercised | 61 | **79** |
| divergences | 1 | **0** |
| "no instance" skips | 57 | **40** |

Independently re-verified: **99/99 agree (100%), 0 divergences**, and passing the bare
repo root now works — `resolve_src_root` corrects to `<repo>/src` and finds
`<repo>/tests`. Regressions green: stress 30/30, sample 10/10, ctest 25/25 vs `cc`.

### The pattern

Every divergence in this episode was the measurement, not the artifact — and each was
found only because refusing to compare exposed what dropping had hidden. Strictness in
an oracle buys accuracy, not just safety: the stricter the refusal, the more of the
remaining agreements mean something. `MAX_DEPTH` and `MAX_ELEMS` were raised to pay back
the coverage that stricter refusal cost.

### Ceilings, current

`skip_unencodable_args` — dominated by caches wider than 256 entries (15,487) and floats
(6,995, which Core has no type for); `skip_varargs` 13,188; `skip_self_not_object` 1,361.
Top inconclusive labels: `setField:cache_clear:non-object` 49, `mcall:__init__:non-object`
36, `call:super` 30, `call:set` 22.

## 28. Refinement reaches real code shapes

§13 called the missing deep≈shallow refinement the largest architectural debt, and
§20 closed the straight-line case. Two obligations remained: refinement could not touch a
loop or a mutated object. Both are now closed.

### The loop rule

`execStmt_loop_rule` is a Hoare while-rule adapted to the fuel-indexed interpreter. The
invariant `I : Nat → Heap → Env → Prop` is **indexed by a termination measure that must
strictly decrease**, and the fuel bound is derived from it. Partial correctness and
termination are therefore proved together — at measure `0` the step obligation would have
to produce `m' < 0`, so the invariant can only exit. `execFor_rule` is the `for`
counterpart with the remaining sequence as the measure.

Proved on real translated functions:

* `sumto_refines` (C, from `math.c`): `sumto n = n*(n+1)/2`. The per-iteration `Fits32`
  obligations are discharged from a **closed-form** domain via monotonicity of the
  triangular-number function, so the domain reads `0 ≤ n ∧ n ≤ 65535 ∧ Fits32 (n*(n+1)/2)`
  rather than a quantified per-step condition.
* `gcdish_refines` (Python, from `ops.py`): `gcdish a b = Int.gcd a b`. The measure is
  `b.natAbs`; correctness rests on `gcd a b = gcd b (a % b)`, and `%` here is `.python`
  (`Int.fmod`), which agrees with `Int.emod` only because both operands are nonnegative.
  The dialect split reappears inside a loop invariant: §16's parameterization reaches into
  the proof obligations themselves.

### The representation predicate

`HeapRep α` pairs a class name with a **partial** abstraction function, and
`Represents R h r a` says heap object `r` represents abstract value `a`. Two lemmas make it
usable: `Represents.frame` (a write to another address preserves it) and
`Represents.update` (a write to this address re-establishes it), both proved against the
real `Heap.setField` (`List.mapIdx`).

`abs` being partial is the load-bearing choice: an ill-formed object represents *nothing*
rather than something wrong. An instance of a function-local class (one with a
captured frame) returns `none`, so it is not represented rather than
mis-represented.

Proved end to end on a `Counter` class: `bump_step` is a full dispatch of a method that
**mutates its receiver** — receiver evaluation, argument evaluation, `resolveMethod`
dispatch, field read, field write, return — ending in a heap that still represents, now at
`a + k`. `total_run` carries an invariant through `execFor_rule` over an arbitrary list,
through object construction and `__init__`; `total_refines` lands in `Refines` proper, so
§20's non-vacuity theorems apply (no hole, terminates in `|ys| + 13` fuel).

### An incidental finding

**`String.endsWith` does not reduce definitionally** — it goes through `String.Slice`
pattern matching. So `Ctx.resolveMethod`, which resolves by suffix, cannot be discharged by
`rfl` the way `Ctx.resolve` can on an exact name; it needs `simp [String.endsWith]; decide`
per name. Any proof touching method dispatch will hit this.

### Still open

**Loop cost is input-dependent, but `Refines` carries a constant fuel bound.** So the
`Refines` instances need bounded domains (`n ≤ 65535`, `b ≤ 1000000`) while the parametric
`_run` theorems are the sharp statements. Making `Refines` carry an argument-dependent
bound is the correct fix and is not done — a limitation of the refinement
relation, not of these proofs.

Also: `n ≤ 65535` in `sumto`'s domain is *implied* by `Fits32 (n*(n+1)/2)` but stated
rather than derived, because deriving it needs nonlinear arithmetic unavailable without
Mathlib. And representation covers field-mutating objects only; container classes need
boxed containers first.

All headline theorems: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## 29. "Universal" is aspirational: the front end generalizes, the back end does not

Five new languages were run through the unmodified pipeline.

| language | corpus | parses | compiles | hole-free | verifiable core | oracle |
|---|---|:--:|:--:|--:|--:|---|
| Python | cachetools | ✅ | ✅ | 76% | 19% | **CPython** |
| Java | gson | ✅ | ✅ | **52%** | 28% | **none** |
| TypeScript | p-queue | ✅ | ✅ | 51% | 21% | none |
| JavaScript | p-map | ✅ | ✅ | 35% | 7% | none |
| C | antirez/sds | ✅ | ✅ | 29% | 13% | crashed |
| Go | envconfig | ✅ | ✅ | 25% | 7% | none |

**The front end generalizes.** Five languages parsed, exported and type-checked with
*zero* exporter or semantics changes, and Java gave the best hole-free rate measured
anywhere. That is the CPG-as-universal-AST bet paying off.

**The back end does not.** There are two dialects for six languages, `.cLike` means
"32-bit truncating C", and `differential.py` picks its runtime with one line —
`runtime = "cc" if is_c else "cpython"` — so Java, Go, JS, TS and Kotlin are all handed
to CPython, produce zero cases, and print "no comparable cases". The oracle that found
every dialect bug in this project's history does not exist for four of six languages,
so the findings below were found by hand.

### Six silent mistranslations, one in the flagship corpus

1. **`and`/`or` return an operand, not a bool — including Python.** `pick(0,5)` is `0` in
   CPython and was `True` in Core; `both(2,3)` is `3` and was `True`. It survived because
   cachetools only uses them in *conditions*, where truthiness makes the two
   indistinguishable; lodash uses 551 of them in *value* position. **Fixed**, and
   dialect-split: C's `&&`/`||` do yield 0/1.
2. **Unknown extensions silently got the Python dialect.** `infer_dialect` returned
   `.python` when nothing voted, so a `.tsx` file was translated with floored division:
   `-7 % 3` gave `2` where TypeScript gives `-1`. The §12 modulo bug re-entering through
   the extension table. **Fixed** — it now refuses.
3. **JS numbers are doubles; Core gave 32-bit ints.** `2147483647+1` → `-2147483648`
   (JS: 2147483648); `7/2` → `3` (JS: 3.5); `5/0` → `ZeroDivisionError` (JS: Infinity).
4. **JS `==` and `===` are the same Core operator** — `jssrc2cpg` emits
   `<operator>.equals` for both, so the distinction is erased *before* Core sees it.
   Not fixable in the semantics.
5. **Java `long` and Go `int` are 64-bit; Core models 32.** `100000L*100000L` → 1410065408.
   `Numeric.lean` already defines `java32`/`java64`/`go64` — but `Dialect` has only
   `python | cLike`, so they are unreachable dead code.
6. **`.cLike` string rules are C's, applied to Java/JS/TS.** `"a"+"b"` becomes a pointer
   hole instead of `"ab"` — safe, but the inverse of the case §22 fixed.

### The lesson

§22 split strings by dialect and called item 6 closed. It was closed *for C versus
Python*, and then applied C's rules to three languages that are neither. A two-valued
parameter cannot express a six-way distinction, and every dialect axis added to this
project has been under-provisioned: one for integer division, then unary minus, then
strings, now widths and boolean-operator semantics. The right shape is a dialect per
*language*, wired to the `NumConfig`s that already exist, with `infer_dialect` refusing
rather than guessing.

## §30 — The verifiable core survives execution about 40% of the time

`scripts/core_oracle.py` ran the claimed verifiable core and refuted it. The claim was
74 of 238 `cachetools` functions hole-free *and* call-closed. Executed over 1,056 cases
with 100% of the claimed core exercised — 46 of them on arguments recorded from
cachetools' own pytest suite under `sys.settrace` — **30 of 74 never holed**, and **21
were refuted on a real input a CPython test actually passed**. Against the earlier
45-function claim the same harness gave 24/45. The ratio is stable at roughly 40%.

This is §17, measured. §17 said static hole-freedom is an upper bound on runtime
hole-freedom. It is, and the factor is about 2.5x.

Two distinct errors were tangled together:

1. **A bug in the ledger, now fixed.** `Ctx.resolvable` was widened to mirror
   `Ctx.resolveMethod`'s first-match rule — correct for method calls, where `clear` has
   9 candidates and the interpreter dispatches fine. But `Analysis.eCalls` flattened
   `.call` and `.mcall` into one untagged `List String`, so the method rule was applied
   to **free** calls too, which use `Ctx.resolve` and its *unique*-match
   requirement. `_wrapper` and `cache_clear` have several definitions each: the ledger
   called them resolvable, `Ctx.resolve` returns `none` on the ambiguity, and the
   interpreter holes. Calls are now tagged with their dispatch path and answered per
   path. Cachetools' core: **74 → 69**.

   The first version was too strict, understating the core by 14. The
   fix for that overshot into too loose. Both were single-rule answers to a two-path
   question, and a flat `List String` made the second error unstatable rather than
   merely unnoticed.

2. **Not a bug — the remaining gap.** The ambiguity fix accounts for 5 functions; the
   oracle's 44 refutations are mostly something else. `setField:<f>:non-object` (89),
   `mcall:clear:non-object` (90), `in:non-container` (80): setting an attribute on a
   `Val.fn` (decorating a function) is not modelled, and `key in self` has no object
   receiver. These are gaps in the *semantics*, not in the ledger's description of it,
   and no amount of care in `Ledger.lean` would have found them. Only execution did.

The recurring rule holds a fourth time: a metric computed from the same artifact it
describes will flatter itself. `verifiableCore` is computed from the AST and the program
table; only running the program refuted it.

Two apparatus defects caught in the harness itself, both of which would have produced a
better-looking number: `differential.py`'s `parse_result` rejects `Val.clos`, which would
have turned three genuine closure results into fake INCONCLUSIVEs; and a synthetic
receiver with no fields makes every attribute access hole for reasons that are the
harness's, not the program's, so `harness:` holes are excluded from the evidence entirely.

## §30.2 — Fuel monotonicity (`Autoform/FuelMono.lean`)

*(Appended as a second "## 20." by mistake and renumbered here. It sits between §30 and
§31 chronologically. Nothing outside this file cited it under the old number.)*

*(Numbering note: this section is numbered 20 in the source and collides with the earlier
§20 on refinement. Both numbers are preserved as written.)*

Open obligation #1 of `Refine.lean` §5 is closed, with one exclusion that is not a proof
artefact. All seven mutually recursive interpreter functions (`evalExpr`, `applyFunc`,
`applyClosure`, `evalList`, `evalPairs`, `execStmt`, `execFor`) satisfy
`f k … = (h', r) → r ≠ outOfFuel → f (k+1) … = (h', r)`, and the `k ≤ k'` form follows;
the proof is one induction on fuel over a seven-way conjunction, since every recursive
call in the interpreter is at `k`.

The exclusion is `Stmt.tryFinally`, the only construct that does **not** propagate an
out-of-fuel sub-result: when the body exhausts fuel and the finalizer exits abnormally,
the finalizer's outcome discards the body's, so the statement returns an ordinary result
computed from a partially-mutated heap, and more fuel mutates that heap further.
`tryFinally_breaks_fuel_mono` is a machine-checked counterexample (`return 1` at fuel 4,
`return 2` at fuel 5, neither `outOfFuel`). The theorems therefore carry `tfFreeS`
side conditions; `tfFree_of_table` discharges them from a table-wide check, and
`(Generated.program.table.all fun p => tfFreeS p.2.body) = true` holds by `rfl`, so the
cachetools corpus is inside the covered fragment.

### §30.1 — Naming the language, so the approximation can be read

Four of six supported languages have no conformance oracle, and commissioning one
surfaced a prerequisite: nothing in the build ever named a language. `Dialect` has two
constructors, so Java, Go, JavaScript, TypeScript and Kotlin were all run as `.cLike`.
That is right about `and`/`or` for Java, Go and Kotlin — they yield a bool — and **wrong**
for JavaScript and TypeScript, where `0 || 5` is `5`, as in Python.

`Lang` (in `Numeric.lean`) names the language and states, per language, the dialect it is
evaluated under, its `NumConfig`, its file extensions, and whether that pairing is
`approximated` — known-wrong rather than unknown. `Lang.known_wrong` currently evaluates
to `[javascript, typescript]`. This also wires `java64` and `go64`, written months ago
and never connected to anything, because nothing named a language.

This is deliberately *not* the constructor-per-language split §29 calls for. About 110
sites still `match` on `Dialect` directly, so adding constructors makes all of them
non-exhaustive simultaneously — and four agents are mid-build. The split is the right end
state; it is blocked on those sites, not on this type. What `Lang` buys now is that a
divergence found by the new oracle can be attributed: caused by the transpiler, or caused
by an approximation the build already admits to.

## §31 — 104 nodes were silently wrong

The exporter pass that closed `control:TRY-finally-escaping` (31 → 0) and
`scope:class-closure` (18 → 0) found **104 call nodes with an empty callee name**.
`{"k":"call","f":""}` is well-typed. It rendered, it type-checked, it counted as
*translated*, and at run time it resolved to nothing. Holes are admissions of ignorance
the ledger can count; these were not holes. They were translated code that did nothing,
inflating the coverage number in the one direction the ledger cannot detect, because a
hole-free function is what the ledger looks for.

Ninety of them were the `with` statement. `pysrc2cpg` lowers `with cm as x:` into
`manager_tmp0 = cm; enter_tmp0 = manager_tmp0.__enter__; value_tmp0 = enter_tmp0()`, so
the invocation carries no name — but both halves of the method's identity are present,
split across two statements: the receiver on the call, the attribute name on the
assignment that made the temporary. Rejoining them made `with` translatable, and it is why
the `_TimedCache`/`TTLCache`/`TLRUCache` timer methods stopped being calls into nothing.

Six were inexpressible — `cached(...)(func)`, a *computed* callee, where
`Expr.call` is by name and Core has no "apply this value". Those six functions were
counted hole-free and are not. Coverage went down for the right reason, the third time
on this project.

Two further results from the same pass:

* **Verifiable core 74 → 97, with no Lean change.** The exporter was discarding Joern's
  resolved `fullName` and emitting the short name, so `Ctx.resolve`'s unique-suffix
  fallback could not separate `_cached.py:_wrapper` from `_cachedmethod.py:_wrapper`.
  Emitting the `fullName` makes the *exact* match fire. This interacts with §30: the
  ledger fix made the free-call path correctly strict, and this makes the exporter supply
  the name that strictness needs. Neither alone was enough.

* **18 "hole-free" functions were padding.** `<metaClassCallHandler>` synthetics: 30
  functions removed, of which 18 had counted as hole-free. Denominator and numerator both
  fell, and none of it was coverage. On the common 208-function basis the real movement is
  hole-free **147 → 159**, holes **106 → 78**.

### The decision: no inheritance from builtin types

`class _HashedTuple(tuple)` translates to an ordinary class, so instances are opaque
`Val.ref`s. CPython's instance *is* a tuple: `hashkey(0) == (0,)` is `True`. `Val.beq`
cannot equate a `.ref` with a `.tuple`, and `hashkey` is cachetools' cache-key function,
so this is a behavioural gap, not an encoding artifact. It was verified against the
*pre-change* 238-function program, which returns the same `ref 1`, so it predates the
exporter work and was exposed when the harness stopped skipping varargs.

**Decision: it stays a DIVERGENCE.** An oracle-side representability rule reclassifying it
INCONCLUSIVE — "we cannot encode this comparison" — would be false. The semantics computes
a different answer from CPython, and calling that "unrepresentable" would convert a
known-wrong result into a not-measured one: the §17/§30 failure, an artifact that makes a
metric look better by narrowing what it measures. A real fix is a Core notion of builtin
base classes, or `alloc` producing a tagged value for such classes. Until then the
divergence is the honest output.

*(§33 and §34 revise this section; see below. §33 attributed the five divergences to
mutation contamination; §34 established that the `_HashedTuple` divergence is real and
independent of mutation, i.e. §31's finding stands.)*

### An apparatus hazard that generated phantom results

`scripts/differential.py` writes its harness to a fixed `/tmp/autoform_diff.lean`. With
several agents running it concurrently they overwrite each other mid-run, so a run can
report conformance for *another agent's program*. This was live for every concurrent run
that day. The apparatus was not measuring the intended artifact.

## §32 — Velvet/Loom: take the DSL, refuse the oracle

`verse-lab/velvet` is a Dafny-style auto-active verifier for Lean 4, built on `verse-lab/loom`,
with `requires`/`ensures`/`invariant`/`decreasing` macros, cvc5 and z3 wired in, and
property-based testing in the same environment. It resembles the tier-2 hammer §5 asks
for and this build does not have.

It is not one, because of `Loom/SMT.lean:215`:

```lean
axiom trust_smt : ∀ (p : Prop), p
```

closed by `mkApp (mkConst ``trust_smt) goalType`. This is not "assume the solver is
right about this formula". It is a proof of every proposition. Checked directly in this
build:

```
'two_eq_three' depends on axioms: [trust_smt]     -- (2 : Nat) = 3
'false_holds'  depends on axioms: [trust_smt]     -- False
```

Adopting it would let `portfolio` close all 89 open obligations immediately, and every
one would be worthless. `scripts/audit_all.py` allows exactly
`{propext, Quot.sound, Classical.choice}`, so the sweep rejects it — the first time the
gate has been tested against a real external tool rather than a hypothetical.

This supports `#smt_evidence`. §5 wanted SMT at tier 2; the design instead reaches
cvc5/z3 through `scripts/prover/smt.py` and records the verdict as an **open obligation
carrying the solver's answer as evidence**, because no Lean proof can be reconstructed
from it. Velvet shows the alternative and its cost: an axiom that makes the logic
inconsistent, in exchange for a green checkmark. `bv_decide` is the counterexample
that proves the rule — SAT-backed *and* LRAT-replayed in the kernel, hence a real rung.

What is worth taking, none of which costs trust:

* **The specification DSL.** `requires`/`ensures`/`invariant`/`decreasing` as syntax over
  an existing semantics. `Autoform/Contracts.lean` builds `Contract` values by hand and
  `execStmt_loop_rule` takes its invariant and decreasing measure as explicit arguments;
  both would read better as macros, and macros carry no soundness weight.
* **Angelic vs demonic non-determinism.** Vocabulary for something already
  built: `RefinesUnder` quantifies over *every* implementation consistent with the
  contract, which is demonic non-determinism, and `refinesUnder_of_unsatisfiable`
  is the degenerate angelic case. Naming it connects the hole mechanism to existing
  literature instead of inventing terms.
* **Partial vs total correctness kept apart, with termination separate.** The fuel-indexed
  interpreter already draws this line — `outOfFuel` is ignorance, not divergence — but the
  ledger reports one number. Velvet's separation is the cleaner presentation.

What Velvet does **not** help with: the remaining holes. `op:starredUnpack` (36),
`import:module-value` (15), `scope:nonlocal-write` (8), `op:delete-index`/`-slice` (8),
`call:computed-callee` (6) and the `_HashedTuple` builtin-base gap are all missing
*language modelling* in Core, not missing proof automation. No verifier closes them.

## §33 — Correction to §31: contamination in the measurement

§31 attributed five `cachetools` conformance divergences to `class _HashedTuple(tuple)`
and Core's lack of inheritance from builtin types. That attribution was recorded as wrong
here, and had reached the README before being checked. (§34 revises this correction:
see below.)

The claim made here was that all five were contamination. A **concurrent mutation run**
held `Autoform/Generated/Cachetools.lean` while the differential harness read it, and
`_DefaultSize.pop` was a live mutant returning `0` instead of `1`. Corroborated by an
independent artifact rather than by the same agent that found it:
`f_cachetools___init___py__module___DefaultSize_pop` appears in `mutation-Cachetools.json`'s
`decls` list. Reproducing against a rebuilt module returns `1`. Two earlier divergences
(`Cache.__contains__` inverted) were the same thing.

The oracle was measuring a program nobody had written.

§27 concluded the last divergence was the apparatus, and §31 quoted that rule while
committing the same error one level down. The exporter agent's reasoning was careful and
its evidence was real — it evaluated `hashkey` on the pre-change build and got `ref 1` —
but "this gap exists" and "this gap caused those five divergences" are different claims,
and only the first was established. A true fact adjacent to a failure is not an
explanation of it.

Three defences now exist:

* `scripts/differential.py` detects the `.mutate-backup` sentinel, warns, and sets
  `build_stable: false` / `mutation_in_progress: true`. A measurement taken over a mutant
  is labelled as one.
* The harness copies the compiled `Autoform/Lang` tree and the generated `.olean` into a
  private directory and points `LEAN_PATH` at it, so a concurrent rebuild cannot change
  the program mid-run.
* Every scratch path is under one `mkdtemp`. The fixed `/tmp/autoform_diff.lean` meant
  concurrent agents overwrote each other's harness and could report conformance for
  *another agent's program*.

### The `_HashedTuple` gap, restated

It is real. This section classified it as not a divergence: Core has no inheritance from
builtin types, so `_HashedTuple` instances are opaque `Val.ref`s while CPython's instance
*is* a tuple, and the harness rules this a counted `representation:value-vs-object`
INCONCLUSIVE. (§34 reverses this classification: the divergence is real and independent
of mutation.)

§31 argued that reclassifying a divergence as "unrepresentable" would be a flattering
lie. That argument stands as a principle and was applied here to facts believed to show
there was no divergence to reclassify. The distinction that matters is whether the class
is **counted and named** — an INCONCLUSIVE bucket with a label and a number is an
admission, while one that quietly absorbs disagreements is not.

### The headline was overstated in the other direction

`0 divergences` on `cachetools` is true and nearly uninformative: **30 of 208 functions**
are compared. The rest are INCONCLUSIVE. Reach is the binding constraint, not agreement,
and a conformance rate quoted without its coverage is the metric shape §17, §30
and §31 keep catching.

## §34 — Correction to §33: the same inferential error, repeated

§31 attributed five conformance divergences to `_HashedTuple` and Core's lack of builtin
inheritance. §33 corrected that, saying all five were mutation contamination. **§33 was
an over-correction, reached by the reasoning §33 itself records as invalid.**

The evidence offered for §33 was that `f_..._DefaultSize_pop` appears in
`mutation-Cachetools.json`'s `decls` list. That establishes `_DefaultSize.pop` *was being
mutated*. It does not establish that it *caused those divergences* — the "true fact
adjacent to the failure" error §33 was written to record.

Settled by direct execution rather than by agent report. `hashkey` is **not** in the
mutation `decls` list and its body is untouched by the live mutant, so it can be evaluated
even with the gate running:

```
Lean:    hashkey (tuple [int 0])  =  Val.ref 0          -- an opaque reference
CPython: hashkey((0,))            =  ((0,),)            -- type _HashedTuple
         isinstance(r, tuple)     =  True
         r == ((0,),)             =  True
```

So the `_HashedTuple` divergence is **real, and independent of mutation**. §31 was right.

The contamination is *also* real — in the current tree
`_DefaultSize.__getitem__` evaluates to `int 1` where the pristine body returns `int 0`,
because that decl is live-mutated.

Both are true because they are **different runs**. Two agents each reported "5
divergences" from separate invocations at separate times, one against a pristine subject
in an isolated copy and one against the main repo mid-mutation. Neither report was wrong
about its own run; the error was assuming two reports of the same *count* were reports of
the same *event*.

The standing rule needs a clause. "The last divergence was the apparatus" (§27) is a
prior, not a verdict — applying it reflexively produced a wrong correction to a right
finding. A report is evidence about the run that produced it, and two runs are not
comparable unless something ties them together. `conformance.json` now carries
`measurement_basis`, `build_stable` and `mutation_in_progress` so that a
future comparison can check whether it is entitled to compare.

### Standing hazard while agents run concurrently

`Autoform/Generated/Cachetools.lean` currently has **238** functions while
`ast-Cachetools.json` has **208**: a concurrent pipeline re-rendered the module from an
AST that is not the checked-in one, three separate times. Any `cachetools` conformance or
ledger number produced in that state describes a build that does not correspond to the
committed AST. `scripts/check_docs.py` reports this as STALE and should keep failing
until the module is re-rendered from the AST and both are committed together.

## §35 — Closing the `_HashedTuple` gap: the payload has to be in the value

§34 settled that the divergence is real: `hashkey (tuple [int 0])` was `Val.ref 0` where
CPython's `hashkey(0)` is `(0,)`, of type `_HashedTuple`, and `== (0,)` is `True`. This
section is the fix, and why the cheaper version is not available.

### The representation, and why the other one is not available

The cheap option is `Obj.builtin : Option Val` — leave the instance a `Val.ref` and
have equality consult the heap. It is not implementable without a larger change
than the alternative, for structural reasons: `Val.beq`,
`applyBinop`, `valIn` and `Val.truthy` are pure functions of values and do not take a
`Heap`. They are also the functions that have to agree with the builtin. Making
an `Obj` payload visible to them means threading a heap through `Val.beq` — which is the
`BEq Val` instance, is called from `Val.beqL`/`beqP`, from `Stdlib`'s association-list
helpers, and from dozens of `Refine.lean` theorems — and it leaves every one of those call
sites able to *forget* to consult the heap. That is the silent-wrong shape this project
keeps finding, at a higher price than the alternative.

So the payload lives in the value: `Val.bobj : String → Val → Val`, the class name plus
the underlying `tuple`/`list`/`dict`/`str`. There is exactly one copy of the state and no
way for a value and a heap object to disagree about it.

The predicted cost of a new `Val` constructor — every existing match going non-exhaustive
at once — was **not** what the change cost. Lean flagged four matchers, all of which had
catch-alls that were already honest. The actual costs were:

* Making `Val.truthy`, `Val.iterable` and `Stdlib.elems` *recursive* (`| .bobj _ v => f v`)
  compiles them through `brecOn`, and that broke ~30 `Refine.lean` proofs and the
  `whnf`-based proof of `Stdlib.builtin_heap_unchanged`. Writing the four base cases out
  by hand keeps them plain matchers that reduce by `rfl`. The same constraint forced
  `Val.beq`'s twelve explicit `bobj` cases: every recursive call has to be on a subterm of
  the *first* argument or the definition falls off structural recursion into well-founded
  recursion, and a well-founded `Val.beq` is not reducible by `decide` — which
  `beq_float_nan_self` and much of `Refine.lean` depend on.
* One case did not fit: `len` of a builtin-based instance. Adding it to
  `Stdlib.builtinCore` defeats the brute-force branch enumeration in
  `builtin_heap_unchanged`, and raising `maxHeartbeats` does not help. It is a **hole**
  with a test pinning it (`excluded_len`), not a silent `none`. `list`, `tuple`, `sorted`,
  `sum`, `min` and `max` all reach the base through `Stdlib.elems` and do work.

`FuelMono.lean` needed two new cases and no weakening: `alloc` splits on
`Ctx.builtinBase` before the existing proof (the builtin branch is a fuel-free
computation, so there is nothing to induct on), and `mcall` gains a `bobj` receiver case
mirroring the `ref` one. `fuelMonoExclusions` is unchanged at `["Stmt.tryFinally"]`.

### The refusals

`Val.beq` compares a `bobj` by contents and **ignores the class**, because CPython does:
`A((0,)) == B((0,))` is `True` for two distinct subclasses of `tuple`. That is only sound
for a class that does not override `__eq__`, so `allocBuiltin` **refuses** to build a
`bobj` for a class that defines its own `__eq__` or `__init__`, emitting
`alloc:builtin-base:<cls>:own-__eq__`. A refusal is a counted hole; honouring the class
while ignoring the override would be a silent wrong answer. Same for `str(x)` of a
non-string, `dict(pairs)`, a non-iterable argument, and more than one constructor argument.

The feature is **opt-in per class**: `Program.builtinBases` is empty by default, so a
class the exporter did not record behaves as before — an opaque `Val.ref`. Every
existing corpus is byte-for-byte unaffected, which is what makes the 113 `Refine.lean` and
79 `SpecsGen` theorems a meaningful regression check.

### What is still open: the exporter

`cartographer/export_ast.sc` now reads `TypeDecl.inheritsFromTypeFullName` and emits a
`classBases` map on the module initializer; `render_lean.py` turns it into
`Program.builtinBases`. **Neither has been run**: this environment has no Joern and no
corpus source, so `ast-Cachetools.json` still carries no `classBases` and the shipped
`Autoform/Generated/Cachetools.lean` therefore still has an empty `builtinBases`. The Lean
side is demonstrated against the *committed* `hashkey` body with the one base supplied at
the test site (`Autoform/BuiltinBase.lean`). Until the exporter is re-run, the capability
exists and the corpus does not use it.

`Autoform/Generated/Cachetools.lean` is also still stale against its AST (238 functions
against 208, §34's standing hazard). Re-rendering it would delete declarations
`Autoform/SpecsGen/Cachetools.lean` depends on, so it stays a separate change and
`scripts/check_render.py` keeps failing on exactly that one module, as it did before.

## §36 — `op:starredUnpack` closed: a calling convention, not a hole-filler

`f(*args, **kwargs)` and `def f(*args, **kwargs)` had no translation. `Expr.call` took a
fixed list of expressions and `Func.params` was a `List String`, so every starred call
became `Expr.hole "op:starredUnpack"` — **36 holes on `cachetools`, the largest single
category**, 46% of all holes in the corpus.

### What was added

Three `Expr` constructors and two `Func` fields:

| addition | meaning |
|---|---|
| `Expr.starred e` | `*e` in an argument list: splice an iterable into the positional arguments |
| `Expr.kwargE k e` | `k = e`: one keyword argument |
| `Expr.dstarred e` | `**e`: splice a `dict` into the keyword arguments |
| `Func.vararg : Option String` | which parameter is `*args` |
| `Func.kwarg : Option String` | which parameter is `**kwargs` |

Both `Func` fields default to `none`, so every already-rendered corpus keeps its exact
meaning (`bindParams_plain` is the compatibility equation, proved).

**Argument forms rather than a new call constructor, deliberately.** Replacing
`List Expr` with an `Arg` type would have made every one of the ~110 dialect matches and
every `Expr` recursion non-exhaustive at once; three leaf constructors disturbed only the
four matches that are exhaustive over `Expr` (`Contracts.substE`, its `substE_nil` proof,
`FuelMono`'s `evalExpr` case split, `Overflow`'s inexact-operator list).

The interpreter change is confined to two places: `evalList` now returns *positional
values plus keyword bindings* and dispatches on the argument's syntax before evaluating
it, and `bindParams` — an ordinary total function, not part of the mutual recursion —
implements CPython's binding rule. `applyFunc`/`applyClosure` gained a `kws` argument.

### Result

| label | before | after |
|---|--:|--:|
| `op:starredUnpack` | **36** | **0** |
| `import:module-value` | 15 | 15 |
| `scope:nonlocal-write` | 8 | 8 |
| `op:delete-index` | 6 | 6 |
| `call:computed-callee` | 6 | 6 |
| `expr:genExp` | 2 | 2 |
| `op:delete-slice` | 2 | 2 |
| `op:stringExpressionList` | 1 | 1 |
| `control:TRY-multiCatch` | 1 | 1 |
| `import:unresolved` | 1 | 1 |
| **total** | **78** | **42** |

Hole-free **159 → 179** of 208; verifiable core **94 → 100**. No other label rose — the
outcome §29/§31 warn about (a category that moves rather than closes) did not occur.

`Autoform/Contracts.lean`'s `methodkey_refinesUnder_value` is now
**`methodkey_refines`, unconditional** (`Γ = []`, an ordinary `Refine.Refines`), on
`[propext, Classical.choice, Quot.sound]`. The contract machinery is kept and re-pointed
at `keysProgramHoled` — `methodkey` *as the transpiler used to emit it* — so the
worked example is explicitly historical.

### Nine arguments were being dropped in silence

`**kwargs` and `k = v` arrive from `pysrc2cpg` with `ARGUMENT_INDEX = -1` and an
`ARGUMENT_NAME`. The exporter selected arguments with `argumentIndex >= 1`, so **every
keyword argument in the corpus was discarded without a hole and without a count** — the
§31 category: well-typed output that type-checked, counted as translated, and did
the wrong thing. Nine sites, including `sorted(..., key = ...)` in `TTLCache.__setstate__`
(sorted by the wrong key, silently) and `_wrapper(..., info = make_info)` in both
`cached.decorator` and `cachedmethod.decorator`, where `_wrapper` does have an
`info` parameter and never received it.

Those nine are now expressed. Two consequences are losses, not gains: a keyword
argument to a *modelled builtin* is now the named hole `call:<f>:keyword-to-builtin`
rather than a silent drop, and `Consistent` gained a clause forbidding a hole
implementation from being a bare argument form (see below), which narrows `RefinesUnder`.

### An exporter precondition that fails loudly

`pysrc2cpg` marks `*args` with `IS_VARIADIC` and marks `**kwargs` with **nothing at all** —
its parameter node is indistinguishable from an ordinary one by any graph property. What
is present is `OFFSET`, so the exporter reads the source text at that offset and counts
the `*`s. That makes `export_ast.sc` require the source tree the CPG was built from, and
it `sys.error`s rather than falling back, because the fallback would be treating
`**kwargs` as a positional parameter, which is a silent mistranslation.

### Fuel monotonicity: no new exclusion

`FuelMono` still proves all seven functions, with `Stmt.tryFinally` remaining the only
exclusion. The starred forms propagate `outOfFuel` like every other argument, so the
seven-way induction extends mechanically (three new `evalExpr` leaf cases, three new
`evalList` head cases, and one `if` split in `applyFunc`/`applyClosure`).

### One place the mechanism could not be stretched

An `Impl` may not replace a hole with `starred`/`kwargE`/`dstarred`. Those are not
expressions that produce a value — `f(*xs)` passes several arguments and `f(**d)` passes
none positionally — so substituting one changes a call's *arity*, and a `Contract.post`,
being a predicate on `evalExpr`'s single `Heap × EResult`, cannot describe that.
`Consistent` therefore carries `∀ l e, σ.lookup l = some e → e.plainArg`. This makes
`RefinesUnder` quantify over strictly fewer implementations than before, i.e. every
contract-relative theorem now says slightly less. Admitting the forms instead would have
been unsound, not merely imprecise.

### Still unexpressible after this

* **Default parameter values.** `def k(a=None, **kw)` binds `a` to `None`; Core leaves it
  unbound and reads `unit`. Not modelled, and `unit` is not `None`.
* **Under-supplied calls.** `f(1)` into `def f(a,b)` is a `TypeError` in CPython; Core
  leaves `b` unbound and reads `unit`. It stays accepted because Core has no default
  values and so cannot tell a missing argument from a defaulted one — rejecting it would
  reject calls CPython accepts. (The *surplus* direction, `f(1,2,3)`, used to truncate and
  now raises: `posRejected`, `surplusPositional_now_agrees_with_cpython`.)
* **Keyword-only parameters** (`def f(*, a)`) are not distinguished from positional ones.
* **A starred form outside an argument list** (`a, *b = xs`) is the narrower hole
  `op:starred-outside-call`. It does not occur in `cachetools`; the label exists so that
  when it does occur it is counted rather than guessed at.
* **Keyword arguments to modelled builtins** — `Stdlib.builtin`/`Stdlib.method` take
  positional arguments only, so these are the named holes `call:<f>:keyword-to-builtin`
  and `mcall:<m>:keyword-to-builtin`.
* **One measured divergence left, recorded as a theorem rather than omitted.**
  `h(1, a=2)` where `a` is also positional is
  `TypeError: got multiple values for argument 'a'` in CPython, while Core lets the
  keyword shadow the positional (`duplicate_argument_is_not_detected`). The other one
  recorded here is closed: `Val.iterable` now has a `str` case, so `g(*"ab")` is
  `('a','b')` and `for c in "ab"` iterates one-character strings, as in CPython
  (`str_is_iterable`, `str_iteration_is_not_empty`, both pinned with `#guard_msgs`).

### The anti-vacuity evidence

`Autoform/CallingConvention.lean` is 31 `#eval`s against CPython 3.9.6, each carrying the
value CPython printed — seven of them pinned with `#guard_msgs` so a regression fails the
build — plus 15 kernel-checked theorems. It covers `f(*[1,2])`,
`f(1,*[2])`, `def g(*a)` at 0/1/3 arguments, `def h(a,*rest)` (the interaction with a
positional parameter, including the empty remainder), `k(**{'a':1})` vs `k(**{'z':9})`,
all four forms in one call, `*` on a tuple and on a dict (which iterates keys), and the
four `TypeError` cases. Every one agrees. Without it, a construct that always returned
`unit` would have produced the same hole table.

### The blast radius of making surplus positional arguments raise, measured

Turning a silent truncation into an exception can only be an improvement if the sites it
newly rejects were already wrong. So they were counted, not assumed. Over every free-call
site whose argument list has no starred or keyword form (where the positional count is
statically exact), resolving the callee with `Ctx.resolve` and asking `posRejected`:

| corpus | free-call sites | resolve in-program | now raise |
|---|---|---|---|
| V8Base | 2,822 | 460 | 0 |
| Cachetools | 139 | 36 | 6 |
| LinuxLib | 15,449 | 4,530 | 257 |
| Ansible | 7,527 | 2,605 | 439 |

Every rejected site falls into one of two classes, and neither was correct before:

* **The resolution is right and the arity is genuinely wrong** — then CPython raises too,
  and Core now agrees where it used to invent a result.
* **The resolution is wrong** — then Core was already executing the wrong function, and
  the arity mismatch is the *symptom* that says so. Both large numbers are this class,
  and each points at a real defect the truncation was hiding:
  - `LinuxLib`: `static int __bpf_fill_ja(struct bpf_test *self, unsigned int len,
    unsigned int plen)` renders as `params := ["len", "plen"]`. The exporter's
    receiver-stripping heuristic fires on a **C** function whose first parameter happens
    to be named `self`, and the call site passes three arguments. Truncation bound
    `len := self` and `plen := len` and ran the body on garbage.
  - `Ansible`: `type(x)`, `list(x)` and `main(x)` suffix-resolve to the *methods*
    `PluginLoader.type`, `SshAgentClient.list` and `__main__.main`, so the builtin is
    never reached — `Ctx.resolve` is consulted before `Stdlib.builtin`.

Both are pre-existing and neither is fixed here (`cartographer/export_ast.sc` and the
resolution rule are separate changes); what changed is that they are now loud.

### The same two fixes, run rather than argued

`scripts/core_oracle.py` executes the ledger's claimed core against synthetic inputs. It
was run twice on `Cachetools` — once with `Val.iterable`'s `str` case and `posRejected`
reverted, once with them — 2,424 cases each, same inputs, same fuel:

| | claimed core | exercised | never holed | holes at runtime |
|---|---|---|---|---|
| before | 101 | 101 | 39 | 62 |
| after | 101 | 101 | **41** | 60 |

No function that executed hole-free before stops doing so; two start
(`_condition_info.Descriptor.Wrapper.__call__`, `_unlocked.cache_clear`), and three hole
labels fall (`field:_obj:non-object` 24 → 0, `field:__enter__:non-object` 370 → 351,
`binop:+` 66 → 61). No new label appears.

Read that gain narrowly. Both functions are in `_cachedmethod.py`, which is where all six
of the corpus' newly-rejected call sites are, so the likeliest cause is that `posRejected`
raises `TypeError` *before* the body reaches the construct that used to hole — an
exception is not a hole, and the oracle counts holes. That is a real improvement in
faithfulness (CPython raises there too, on a call Core was mis-resolving) but it is not
two more functions' worth of coverage, and it is not claimed as such.

This run also required fixing `scripts/core_oracle.py`, which had been emitting a harness
that did not elaborate — see the commit; it reported "0 executed" where it should have
reported a type error.

### What is *not* established

`scripts/differential.py` on this corpus produced **0 COMPARED cases** — the recorded
test suite yielded nothing and 142 hole-free methods had no reachable instance. So there
is no conformance evidence either way from that oracle for this change, and none is
claimed. The evidence for the semantics is the CPython-paired `#eval`s above; the evidence
for the exporter is that a re-export reproduces the committed AST byte-for-byte and
`scripts/check_render.py` passes on all 10 modules.


## §37 — The first theorem about something other than `cachetools`

`Autoform/Specs/V8Spec.lean` proves a property of `v8::base::bits::SignedMod32`, from
`v8/src/base/bits.cc`, translated by the pipeline with no holes.

V8's own header states the contract:

> `SignedMod32(lhs, rhs)` … **If either `|rhs|` is zero or `|lhs|` is minint and `|rhs|`
> is -1, it returns zero.**

On x86, `INT_MIN % -1` raises `#DE` — the same trap as division by zero — so the property
worth proving is that the guard covers the trapping inputs for *every* `lhs`, not for a
sample.

```lean
theorem signedMod32_zero_divisor (lhs : Int) (k : Nat) :
    (applyFunc C (k+9) [] smod32 none [.int lhs, .int 0] []).2 = .val (.int 0)
```

Universally quantified over `lhs` **and** over any fuel budget at least 9, so it is
neither a statement about sampled inputs nor about one budget. Axiom basis
`[propext, Classical.choice, Quot.sound]`, `#audit_axioms` clean, and `#audit_depends`
confirms the proof mentions the translated function rather than proving something
about nothing. The context carries an empty function table — `SignedMod32` calls nothing —
which makes the theorem independent of the other 1,734 functions in the module.

### What is *not* proved, and why it is a `def`

The `rhs = -1` half is an open obligation, stated as a `Prop`-valued `def`. The `rhs = 0`
case reduces because `0` is a literal; `-1` is `Expr.unop "-" (lit 1)`, so the guard's
second disjunct routes through `NumConfig.c32Wrapv.neg` and `simp` did not close it with
the numeric model unfolded. The *behaviour* is pinned at three inputs including `INT_MIN`
via `#guard_msgs` (which fails the build on change and, unlike `native_decide`, adds no
axiom). Pinning three points is a weaker claim than a universally quantified proof, and
the two must not be confused.

### A structural limit this exposed — and its removal

**Only one generated corpus could be in a single import graph.** Every
`Autoform/Generated/<M>.lean` defined `Autoform.Generated.program`, so importing two of
them failed with "environment already contains 'Autoform.Generated.program'". `V8Spec`
therefore built standalone (`lake build Autoform.Specs.V8Spec`) and was deliberately NOT
in `Autoform.lean`'s import list — along with `BuiltinBase`, `Contracts`,
`Specs/CachetoolsSpec` and `SpecsGen/Cachetools`. That was acceptable for one corpus and
blocked the goal for many: a repository that proves things about V8 *and* cachetools
could not put those proofs in one build. It also meant `leanchecker --fresh`, which
replays the `Autoform` root graph, never saw those five modules.

**Fixed (2026-08-21).** `cartographer/render_lean.py` now emits
`namespace Autoform.Generated.<Module>`, so each corpus owns its own `program`
(`Autoform.Generated.Cachetools.program`, `Autoform.Generated.V8Base.program`, ...) and
any number of corpora coexist. Every spec that named `program` was re-pointed, every
corpus was re-rendered (the diff is exactly the two namespace lines), and all five
previously-gated modules are now imported from `Autoform.lean`. Theorems about a Python
library and theorems about a C++ engine are in one build, kernel-checked together and
replayed together by `leanchecker --fresh`.

### An error that produced a theorem

An `open ... in` scoped to only the first declaration left the second unable to resolve
its identifier. Lean reported the error **and admitted the theorem anyway**, so
`#print axioms` showed `sorryAx` in the basis of a theorem that looked proved. The build
was red, so nothing shipped — but in one file among many with its output scrolled past,
only the axiom check would have caught it. That is the third time this session a
green-looking result was false, after the mutation-gate regex and the conflict-marked
module that built from a cached `.olean`.


## §38 — C: `for`, aggregate initializers, bitwise arithmetic, tail `goto`, and a data model

*(Written as a second "§36" and renumbered here. Commit `f6085ce` cites it as §36; the
`op:starredUnpack` section above is the other §36.)*

*(Numbering note: this is the second section numbered §36 in the source. Both are
preserved as written.)*

Five C-shaped gaps closed against the Linux kernel 7.1-rc3 (`lib/`, `crypto/`), V8
`src/base`, and — for the two that are not C-specific — Ansible.

* **`for (init; cond; step) body`** becomes `init; while (cond) { body; step }`. The
  subtlety is `continue`, which in C jumps to the **step**, not to the test: the textbook
  desugaring turns `for (i=0;i<n;i++) { if (p) continue; ... }` into an infinite loop that
  type-checks. Each `continue` belonging to *this* loop is therefore emitted as
  `step; continue` — an exact rewrite, not an approximation, so no hole is needed. The
  negative control is in `Semantics.lean`: the naive desugaring of the same loop is
  pinned as `outOfFuel` while the real one is pinned as the value `cc` prints. A `for`
  with a clause elided is `control:FOR:elided-clause`, because Joern omits absent clauses
  and nothing in the graph says which of the three the survivor was.

* **Brace initializers.** `{1,2,3}` is `Expr.listE`; `{ .a = 1, .b = 2 }` is `Expr.dictE`
  keyed by the field names, with `Dialect.fieldsOnDicts` making `s.a` read it back under a
  C-family dialect only (in Python `{'a':1}.a` is an `AttributeError` and stays a hole).
  A struct literal is a finite map from field names to values and C copies structs
  by value, so value semantics is the right semantics. `{ [IDX] = v }` — an *index*
  designator — is refused (`op:arrayInitializer:index-designator`): reading it
  positionally would put the right value in the wrong place. `T x[N]` in declaration
  position wears the same CPG operator and is not an initializer at all; it is now
  `op:arrayDecl:size`, still a hole, because modelling it needs a size model this
  project does not have.

* **Bitwise operators.** `&`, `|`, `^`, `<<`, `>>`, `>>>` and `~` are now real
  operations on `NumConfig`, not holes and not the logical operators. See the
  §-note above on `<operator>.and`. `>>` needs the operand's *type*: it is
  arithmetic on a signed operand and logical on an unsigned one, Joern spells both
  `arithmeticShiftRight`, and a `Val.int` has no signedness — so the exporter chooses from
  the static type and emits `op:shiftRight:unknown-signedness` when it cannot.

* **`goto`, partially.** A *forward* jump to a *single* label that is a *direct child of
  the function body*, with no jump inside a loop or switch, is `while (true) { prefix;
  break } suffix` — structured control flow with an unstructured spelling. Everything
  else keeps `control:GOTO`. On `crypto/` that is 114 of 434; on `lib/`, 83 of 402. Each
  condition is load-bearing and each one, dropped, gives a wrong answer rather than a
  hole: a `break` inside a real loop leaves *that* loop.

* **`long` is not 32 bits.** `intTypeNames` mapped `long -> i32`, so `(long)x` truncated
  to 32 bits on LP64 — Linux and macOS on x86-64 and arm64, which is what both C corpora
  are built for. That is the worst category the project has, because a hole-free function
  is what the ledger counts as good. The fix is not to write `i64`: `long` is 64 bits under
  LP64 and 32 under LLP64, so its width is a property of the **target data model**, not of
  the language. `dataModelTable` tabulates `lp64` / `llp64` / `ilp32` for the whole
  family — `long`, `size_t`, `ssize_t`, `ptrdiff_t`, `intptr_t`, `uintptr_t` — the model
  is an explicit `--param dataModel` (default `lp64`, printed by the exporter on every
  run), and an unknown model makes every one of them the hole
  `op:cast:model-dependent` rather than a silent guess. The choice is legible in the
  output as well as in this file: the emitted operator names the width it picked, so
  `(long)x` is `unop "cast:i64"` under LP64 and `"cast:i32"` under LLP64.

  The exactly-sized kernel spellings `s8`..`u64` and `__s8`..`__u64` were added to the
  model-*independent* table, since those names exist to be target-invariant.
  `__le32`/`__be32` were **not**: their value is byte-swapped as well as narrowed, and
  modelling only the narrowing would be half a translation.

**What this does not fix.** `Dialect.cLike` is still 32-bit signed for *arithmetic*, so a
`cast:i64` value that then takes part in `+` is wrapped back to 32 bits. The cast is now
right; the arithmetic around it is still under the two-constructor `Dialect` §29 records.

## §39 — Reconciling the `cachetools` figures

Sections above quote the verifiable core as 45, 69, 74, 94, 97, 100 and 101, and the
function count as 208, 209, 233 and 238. They are consistent as a sequence and confusing
as a set, because both the numerator and the denominator moved, sometimes in the same
revision. This section states the current values and what moved.

**Current, from `ledger-Cachetools.json`, regenerated after the last exporter change:**

    functions        209
    hole-free        180
    verifiable core  101
    holes            40

What moved the denominator: `<metaClassCallHandler>` synthetics were excluded (§31),
removing 30 functions of which 18 had counted as hole-free — padding in both the numerator
and the denominator, and no real coverage either way.

What moved the numerator, in order: `Ctx.resolvable` was split by dispatch path so free
calls use `Ctx.resolve`'s unique-match rule (§30, core down to 69); the exporter began
emitting Joern's resolved `fullName` so the exact match fires (§31, up to 97);
`op:starredUnpack` closed (§36); module objects and import resolution closed most of the
Python import holes.

**A figure in an earlier section is a snapshot, not a claim about today.** Only
`ledger-Cachetools.json` is authoritative, `scripts/check_docs.py` compares eight
documented figures against it and fails on a mismatch, and `scripts/check_render.py`
verifies the module those figures describe is a render of the checked-in AST.

Two smaller discrepancies remain unreconciled and are recorded rather than fixed:
`skip_unencodable_args` is 534 in §25 and 521 in §26 with no stated cause, and §27 reports
that category on a different basis again. Whether §34's 238-vs-208 hazard is still live is
answered by running `scripts/check_render.py`, which now verifies 15/15 against
`artifact-manifest.json` (§40).


## §40 — The merge that found the theorems had not been checked

Eleven branches merged into one state. The build is clean, `scripts/audit_all.py` prints
PASS, `scripts/check_render.py` verifies 15 of 15, `scripts/check_docs.py` matches 8 of 8,
`fuelMonoExclusions` is still exactly `["Stmt.tryFinally"]`, and `tests/` is 130 green.
None of that is the finding.

### The finding

**No `Autoform/SpecsGen/*.lean` module was in the build, and the headline theorem count
was a `grep`.**

`lake build` roots the `Autoform` library at `Autoform.lean`, which imported no SpecsGen
module. `audit_all.py`'s `leanchecker` replay walks that same import closure, so it never
saw one either. CI's proof-inventory step counted `^ *theorem ` with `grep -c`. Three
independent green signals, none of them looking at the artifact they were about.

Under that cover, `Autoform/SpecsGen/Cachetools.lean` — the home of the 79 theorems this
project has been quoting — stopped elaborating at some point after
`Autoform/SpecsGen/Basis.lean` changed shape underneath it, and nothing anywhere said so.
This is §17 again in its purest form: every metric in sight was computed from something
other than the thing it described.

The mutation branch found the same wall independently and, to its credit, recorded it
correctly: `mutation-SpecsGenCachetools.json` is not a kill rate but

    "status": "BASELINE_FAILED",
    "reason": "the module under test does not build before any mutation is applied;
               no mutation verdict is possible"

A mutation gate whose baseline does not build could have reported a 100% kill rate — every
mutant "dies" because everything dies. It refused to, and that refusal is the only reason
the breakage was written down anywhere before this merge.

`Autoform/SpecsGen/Basis.lean` is now imported from `Autoform.lean`, so its 21 theorems go
through the kernel on every build and through `leanchecker` in the audit. The corpus
modules are too slow for the gating build, so `scripts/check_specs.py` elaborates them and
reports per module; a missing module, an unbuilt dependency, a timeout and a `--quick`
skip are each a FAILURE with a reason, and an empty run exits 2.

### What the semantics fix cost, and why the cost is the point

The surplus-positional change (`applyFunc` now raises `TypeError` instead of truncating)
made 47 generated theorems **false**, not merely unprovable. They were stated as

    Refines P "f" N (fun _ => True) (fun _ => .ret v)

— for *every* argument list — and were true only because surplus arguments were silently
dropped. The repair is the exact domain, `fun args => posRejected f args = false`, in
`scripts/synth_specs.py` and in the modules it had already emitted; the same hypothesis
went onto Basis's two accessor lemmas, where it is discharged by `rfl` at every call site.
For a callee with `*args` the hypothesis is identically true, so nothing variadic lost
anything. `LinuxLib`, `LinuxLibSample` and `V8BaseSample` elaborate again.

That a semantics fix falsified 47 theorems and no build noticed is the strongest available
argument for putting the proofs in the build.

### What is still broken, precisely

`Autoform/SpecsGen/Cachetools.lean` does not elaborate. Its `C_tfFree` premise — *every
body in the function table is `tryFinally`-free* — is what every fuel-transported theorem
in the module rests on, and it is now false: `Autoform/Generated/Cachetools.lean` contains
49 `.tryFinally` nodes, because the exporter learned to translate `try/finally` after the
module was generated. This is not repairable by hand; it needs regeneration, and
`synth_specs.py`'s trace step currently records zero calls on cachetools — inside
`scripts/differential.py`, owned by another branch. The failure is pinned in CI, which
also fails if it starts passing, so the pin cannot go stale in silence.

`fuelMonoExclusions` was not touched. The right response to a table that is no longer
`tryFinally`-free is a narrower context, not a wider exclusion list.

### The renders were all behind their ASTs

`check_render` went red the moment the V8Base evidence branch landed its `ast-V8Base.json`,
and pulling that thread showed every large corpus in the same state: the committed
`Autoform/Generated/*.lean` were older than the neutral ASTs — Ansible by 42,094 lines,
LinuxCrypto by 26,714, V8Base by 2,105. Anything measured from them described a program
nobody wrote. All five were re-rendered, type-checked and re-pinned in
`artifact-manifest.json`.

### Coverage: unchanged, and independently reconfirmed

| corpus | functions | hole-free | holes |
|---|---|---|---|
| v8 `src/numbers` | 157 | 109 (69%) | 210 |
| v8 `src/base` | 1920 | 1189 (62%) | 2055 |
| linux `lib/` | 3368 | 1168 (35%) | 10106 |
| linux `crypto/` | 1955 | 692 (35%) | 5884 |
| ansible | 5546 | 3304 (60%) | 8060 |

No corpus regressed and none improved. That is the correct result and not a null one: no
branch in this workflow touched `cartographer/export_ast.sc` or
`cartographer/render_lean.py`, so re-exporting could only reproduce the same ASTs. The
numbers above were recomputed from `/tmp/final-*.json` by a walk that counts `hole` and
`holeS` nodes, independent of the ledger and of the documents that quote it, and they
agree exactly with the figures this workflow started from.

### What this workflow closed

* CI runs `check_render`, `check_docs`, `pytest` and `check_specs`, and the previously-red
  Cachetools render is green.
* The artifact policy: the AST is tracked, the render is a build product, both pinned by
  sha256 in `artifact-manifest.json`. 33 MB left the index.
* Evidence artifacts — trust ledger, SACM assurance case, execution oracle — for V8Base,
  LinuxLib, LinuxCrypto and Ansible. Four of the five large corpora now have some.
* ~8,000 lines of Python tooling have a test suite, with a regression test per silent
  failure. It is 130 green and it caught two of its own fixtures going stale during this
  merge.
* Four branches independently discovered that `core_oracle.py` called `applyFunc` without
  its keyword-argument list, so every case failed to elaborate and every run reported
  INCONCLUSIVE. The merged file keeps the smoke gate that fails before spending hours, the
  all-cases-unanswered backstop, and the per-depth error print.
* Theorems about V8 `base/` and Linux `lib/` — the first about anything other than
  cachetools — and they elaborate.

### What it did not

* The 108-theorem figure. Measured by elaboration rather than by `grep`, the inventory is:

  | module | theorems | verdict |
  |---|---|---|
  | `SpecsGen/Basis.lean` | 21 | **proved** — imported from `Autoform.lean`, kernel-checked every build |
  | `SpecsGen/LinuxLib.lean` | 12 | **proved** (`check_specs`, 30 s) |
  | `SpecsGen/V8BaseSample.lean` | 9 | **proved** (`check_specs`, 5 s) |
  | `SpecsGen/LinuxLibSample.lean` | 7 | **proved** (`check_specs`, 11 s) |
  | `SpecsGen/V8Base.lean` | 229 | **does not elaborate** (21 errors, 2420 s) |
  | `SpecsGen/Cachetools.lean` | 79 | **does not elaborate** (14 errors) |

  So **49 theorems prove and 308 do not**, against a `grep` count of 357. The gap is the
  whole point of this section.

  `SpecsGen/V8Base.lean` fails for a *different* reason from Cachetools, and the reason is
  instructive. Re-rendering V8Base from its AST split an overloaded C++ name differently:
  `f_v8_base_AddressRegion___init__` is now the empty stub (`params := []`, `body := .skip`)
  and the real two-argument constructor is `f_v8_base_AddressRegion___init__'`. Every
  theorem generated against the old numbering is now a theorem about the wrong function.
  Nothing here is repairable by editing a proof; both modules need `synth_specs.py` run
  again against the current render, and the domains it mines have to come with them.
* Provenance. `scripts/check_provenance.py` reports 0 of 12 artifacts attributed to a
  pinned Joern. That is the honest baseline it was built to establish, not a pass.
* `scripts/differential.py`'s trace step on cachetools, which is what blocks the
  regeneration above.

## §41 — `op:addressOf` is a corpus-boundary problem, not a location-model problem

The largest remaining hole label was recorded as needing a location model — `Val.ptr` with
a base object and access path, arrays as heap objects, a size model, estimated at roughly
three times the `Val.bobj` change and touching `Semantics`, `FuelMono`, `Refine`,
`Overflow`, the renderer and the ledger. That estimate is right about the work and wrong
about the problem.

Measured over Linux `lib/`, for every `op:addressOf:local:unknown-type` site:

    passed to a call defined IN the analysed program      64   ( 2%)
    passed to an EXTERNAL call                          2,724  (98%)
    not a direct call argument                              0   ( 0%)

`kstrtoul(s, 0, &n)` is the shape. The callee is not in `lib/`, so it is not translated,
so **what it does to the pointer is unknowable whatever the pointer model is**. A location
model would let Core represent `&n`; it would not let Core say what happens to `n`,
because the function that writes it does not exist in the program.

The same measurement on the other corpora:

    linux crypto/   94 sites: 32% in-program, 52% external, 16% other
    v8 src/base      3 sites: 100% external

So the remedy is not a pointer model but a **wider corpus**. Parsing the callees — the
rest of `lib/`'s dependencies, or the kernel with its headers — converts the 98% into the
2% case, and only then does a location model buy anything. Building the model first would
be building the expensive half of a two-part fix, in the wrong order, and the 2% figure
says how little it would return on its own.

This also explains why the earlier syntactic type-recovery pass moved the number by only
66. It was inferring types for variables whose *use* is outside the corpus; there was
nothing local left to infer from.

The honest statement of the caveat is therefore: **`op:addressOf` is blocked on corpus
coverage, and a location model is the second step, not the first.** The label should say
so; it currently says `unknown-type`, which points at type inference — the one remedy the
measurement rules out.

## §42 — Three caveats that were one construct each

§41 established that `op:addressOf` is a corpus-boundary problem rather than a
pointer-model one. Following the same method on the next two largest labels found the same
shape three times running: a caveat recorded as needing a large subsystem was dominated by
a single family of constructs with **no runtime semantics at all**.

| caveat, as recorded | what it actually was | fix |
|---|---|---|
| `op:addressOf` needs a location model (~3x `Val.bobj`) | 90% `&lock` passed to `spin_lock`/`mutex_lock`/`rcu_read_lock` | 35-entry set, one `case` arm |
| `import:absent:external` needs module semantics | 546 were `from __future__ import annotations` | one branch |
| `stmt:UNKNOWN` needs a preprocessed kernel build | ~490 were `MODULE_LICENSE`-family metadata | 18-entry set |

Each rests on the same argument, and it is an argument about what Core *is* rather than an
approximation of what it is not:

* Core is a **sequential** interpreter — no threads, no scheduler. An uncontended
  acquire/release changes nothing a program can read, so `Stmt.skip` is the exact
  translation.
* `from __future__ import annotations` is a **compiler directive**. It binds a `_Feature`
  object nobody reads.
* `MODULE_LICENSE("GPL")` writes a string into an **ELF section**. It compiles to no
  instructions.

In every case the construct was a hole for a reason unrelated to its own difficulty: `&l`
could not be represented, so a `mutex_lock` made its whole function unanalysable; a
file-scope macro made its module initialiser unanalysable. The cost was never in the
construct, it was in what the construct dragged down with it.

What is given up is stated at each site and is narrow: no data race, deadlock or missing
critical section is detectable — which was already true, Core has no threads to race. The
boundaries are drawn where behaviour becomes observable: `spin_trylock` is excluded because
it returns a value the program branches on, and `module_param` is excluded because it binds
a variable from the command line.

Combined effect across all five corpora:

    session start   12,947 functions   ~3,900 hole-free (30%)   40,581 holes
    now             12,947 functions    7,586 hole-free (59%)   18,428 holes

**The remaining caveats should be assumed mischaracterised until measured.** That has now
been the outcome three times in a row, and the measurement each time cost minutes while the
design work it displaced was estimated in weeks. The one place the method found a genuine
gap is worth naming too: 574 `static … __init …` declarations in Linux `lib/` are entire
FUNCTION DEFINITIONS that Joern's parser drops because of GCC attributes. Those are not
holes — they are functions missing from the corpus, and no amount of Core work reaches them.
That is the real content of "needs a preprocessed build".

## §43 — 571 Linux functions were never in the corpus, and the front end never said so

§42 named the one genuine gap the measurement method found: `static … __init …`
declarations that Joern's C parser drops. This closes it, and the shape of the failure is
worth recording because it is not a hole and does not appear in any hole count.

Joern parses C **without running the preprocessor**, so

    static int __init setup_early_mem_profiling(char *str) { … }

fails to parse and the whole FUNCTION is dropped. Not translated into a hole — absent.
Nothing in the ledger showed it, because the ledger counts what the exporter produced, and
a function the front end never emitted has no row anywhere. The only visible trace was a
`stmt:UNKNOWN` on the surrounding declaration.

`scripts/strip_kernel_attrs.py` removes the attributes that defeat the parser from a
**staging copy**: `__init`/`__exit` (ELF section placement), `__user`/`__iomem`/`__rcu`
(sparse annotations, no codegen), `__weak`/`__visible` (linkage), `__cold`/`__pure`/
`__must_check` (optimiser and warning hints), and the parametrised
`__printf(m,n)`/`__section(…)`/`__attribute__((…))`. None of them changes what a function
body computes, which is the only thing the translation models — so this removes text the
semantics never depended on rather than approximating anything.

    linux lib/   functions  3,368 -> 3,939   (+571)
                 hole-free  1,669 -> 1,978   (50% -> 50%)
                 holes      6,727 -> 7,280
                 stmt:UNKNOWN:CASTProblemDeclaration  1,183 -> 509

The hole *count* rose and the hole-free *ratio* held. That is the honest result: 571 more
functions bring their own holes, and coverage per function is unchanged. A metric that
improved here would have meant the new functions were being counted differently from the
old ones.

This is **not** a substitute for a real preprocessed build. Macros that expand to *code* —
`MODULE_LICENSE`, `TEST_SPINLOCK_COMMON`, `DEFINE_SPINLOCK` — are untouched and remain
`stmt:UNKNOWN` at 509. Those need cpp with the kernel's own headers and config.

**Provenance**: any AST exported from a stripped tree is from modified sources, and that
has to travel with the figures. The script says so on every run, next to the standing
requirement to record the Joern version.

Across all five corpora after this: **13,518 functions, 7,895 hole-free (58%)**, against
12,947 / ~3,900 (30%) at the start of the session.

## §44 — The conformance oracle was dark, and every other gate was green

`scripts/differential.py` reported **534 of 534 cases INCONCLUSIVE (`lean-no-answer`)** on
`cachetools` — the corpus this project knows best. It was not deciding anything. Meanwhile
`lake build` (472 jobs), `audit_all.py`, `check_render` (17/17), `check_docs` (8/8),
`check_specs_fresh` (7/7) and 131 tests were all passing.

Four separate faults, three of them introduced by work done the same day:

1. **`applyFunc` arity.** Modelling Python's calling convention gave `applyFunc` a `kws`
   parameter. The harness's generated Lean kept five arguments, so `drun` failed to
   elaborate — but the `@@meta@@` line above it only mentions `base`/`gref` and still
   printed, so the harness saw a live Lean process and recorded every case as
   "lean did not answer". **An arity change disabled the only oracle that compares the
   semantics to a real runtime, and looked like the semantics abstaining.**
2. **Per-corpus namespaces.** The harness did `open Autoform.Generated` and referred to
   bare `program`, which after §-namespacing lives in `Autoform.Generated.<M>`.
3. **`json.load` recursion.** Ansible's AST blew the 1000-frame default *while decoding*.
   Third instance of that defect class here, after `render_lean.py` and `has_hole`.
4. **`os.path.exists` where `isfile` was meant.** An AST entry with an empty `file` — a
   module-level initialiser — joins to the source ROOT, which exists and is a directory.

Restored: **38 functions compared, 133/166 agree (80%), 33 divergences.**

### Why it stayed dark

An oracle that *cannot run* reported identically to an oracle that *ran and abstained*.
`lean-no-answer` was counted as INCONCLUSIVE, which is a legitimate outcome, so the
headline read "0 divergences" — the best possible number — while nothing was being checked.

The harness now prints the first line of Lean's stderr when it fails to reach the first
case. That is the whole fix for the class: **a check with nothing to say and a check that
cannot speak must not look the same.** Four instances now — the mutation-gate regex that
never matched, the doc checker comparing against a stale artifact, the cross-check that
went quiet on a fresh clone, and this.

**Conformance is not in CI.** Everything that is in CI stayed green throughout. That is the
concrete lesson: the only oracle that tests the semantics against reality rather than
against itself is the one nothing was guarding.

### The 33 divergences, diagnosed

All are `lean raised TypeError` where CPython succeeds, and all have one cause.
`LRUCache.__getitem__` calls `cache_getitem(self, key)` — passing `self` **positionally**
to a function value. The exporter strips `self` from `params` (right for method dispatch,
since `applyFunc` binds the receiver separately), so `Cache.__getitem__` has
`params = ['key']` and receives two positional arguments. Surplus positional arguments now
raise `TypeError` rather than being truncated, so the stricter rule turned a silent
truncation into a loud wrong answer.

That is progress, not regression — the old behaviour was wrong too and said nothing — but
it is not yet right. A `Val.fn` called directly needs its first positional argument bound
to `self` when the referent is a method. Recorded, not fixed.

## §45 — The oracle needed four fixes before it could see one bug

§44 restored conformance from 534/534 `lean-no-answer` to 38 compared. Pushing further
found three more faults, all the same kind: **Core was fixed, and the harness that checks
Core was not told.**

* `Val.bobj cls payload` takes two arguments — the only `Val` constructor that does.
  Parsed as one-argument, it consumed the class name and left the payload dangling, so
  every `_HashedTuple` result was "unparsable" and counted INCONCLUSIVE.
* The harness built `Ctx` as `{ dialect, table, globals }` and never carried
  `builtinBases`, so `Expr.alloc` could not know the class had a builtin base and produced
  a plain `Val.ref`. The oracle then reported `representation:value-vs-object` — refusing
  to look at a value it had itself prevented Core from producing.
* `same`/`shape_clash` had no `bobj` case.

    compared      38 -> 40 functions, 166 -> 186 cases
    agree        133 -> 138
    divergences   33 -> 48        rate 80% -> 74%

**The rate fell and that is the honest direction.** The newly comparable cases contain real
disagreements that were previously hidden behind "unparsable". A rate that improved here
would have meant the oracle was still refusing the hard cases.

### The remaining divergences, both diagnosed

**27 are the `self`-positional bug** (§44): a `Val.fn` called directly needs its first
positional argument bound to `self` when the referent is a method.

**15 are a double pack, and the fault is in the harness.** Core answers
`bobj "_HashedTuple" (tuple [tuple [int 0], dict []])` where CPython answers `(0,)`. The
harness records its cases by tracing CPython, and what it captures is the *frame's*
`args`/`kwargs` — for `hashkey(*args, **kwargs)` called as `hashkey(0)` that is
`args = (0,)`, `kwargs = {}`. It then passes those two packed values as positional
arguments to a function that packs again.

This was invisible before varargs were modelled, because `vararg` did not exist and the
packed tuple was simply bound to the first parameter — the same wrong answer, arrived at
by a different route, and reported as agreement. The fix is to spread the recorded packed
values back into positionals when the callee has a `vararg`/`kwarg`.

### The pattern

Every one of these four faults reported as INCONCLUSIVE or as a divergence in Core, never
as a fault in the checker. **An oracle reports its own defects in the vocabulary of the
thing it is checking**, which is why they survived: each one looked like a limitation of
the semantics, and the semantics was innocent in all four cases.

## 46. The unbound-method rule, and a denominator that moved on its own

`applyFunc` binds a receiver separately from the positional arguments, which is right for a
`.`-call, where Python supplies the receiver implicitly. It is wrong for a method reached as
a VALUE. `LRUCache.__getitem__(self, key, cache_getitem)` calls `cache_getitem(self, key)`,
and cachetools passes `Cache.__getitem__` in that slot. There the receiver is an ordinary
first positional -- that is all `self` ever is. Core bound it to `self`'s successor instead
and reported a spurious arity `TypeError`, on 27 of the 38 divergences then outstanding.

The fix is Python's actual rule, applied at the one call path that was wrong -- a variable
holding `.fn g` -- and guarded so it is a no-op everywhere else:

    if fn.isMethod && fn.vararg.isNone && vs.length == fn.params.length + 1

C++ functions have no `self`, so V8 and Linux are untouched; exactly one proof in the whole
corpus needed repair (`FuelMono`, which is indifferent to WHICH arguments are passed but
still has to take the branch). Divergences fell 38 -> 5, agreement 79% -> 96%.

`Func.isMethod` reads the EXPORTER'S NAMING CONVENTION (`<module>.Class.method`), which is a
coupling between Core and the front end, not a semantic property. The right shape is a
`receiver` field on `Func`. That changes `Func`, which re-generates every AST and breaks the
hand-written `CachetoolsSpec` and `Contracts` proofs -- a larger change than is wise while
the conformance number is still moving. A stated shortcut, not a hidden one.

### The part that was not a win

The same run's denominator FELL: 107 exercised / 40 compared before, 82 / 28 after. A
semantics change cannot do that. `cases` is built by tracing CPython and is complete before
Lean is invoked once; `random` is seeded at a fixed value; two consecutive runs agreed
exactly. So the harness is deterministic and the drop came from an input.

The obvious suspect was the corpus. It was not: re-parsing the current checkout and
re-running the exporter produced an AST BYTE-IDENTICAL to the committed one, all 209
functions, no name added or lost. So `ast-Cachetools.json` and the sources do match.

Which leaves the checkout the EARLIER run traced, three days and one `/tmp` clearing ago,
and that state cannot be reconstructed. The honest position is that the 96% and the 79% were
measured over different case sets, and only the 96% has a recorded provenance.

So the response is not an argument, it is a pin. `--depth 1` tracked upstream HEAD, meaning
the coverage denominator could move with no commit in this repository -- the drifting-corpus
trap, which this project has already been caught by once (the 15 false V8 laws in section 31
were a stale corpus, not a generator defect). CI now checks out a fixed commit, and
`conformance.json` records `corpus_commit` for every run. The next such gap is a diff.

Coverage remains the honest weak number: 28 of 180 hole-free functions. 250 INCONCLUSIVE
are runtime holes with named causes -- `call:set`, `setField:cache_clear:non-object`,
`mcall:warn:keyword-to-builtin` -- each one unmodelled construct, not a mystery.

## 47. Function objects: specified, then made

The largest single block of INCONCLUSIVE cases is `setField:<f>:non-object` -- six functions
in `cachetools/_cached.py`, thirty cases. The construct is the decorator epilogue:

    wrapper.cache_clear = clear

In Python a function IS a heap object with a `__dict__`, so this is an ordinary attribute
write. In Core, `Val.fn` is a bare `String` with no identity, `Stmt.setField` requires a
`.ref`, and the write holes. `Val.ref` already exists and already carries the reference
identity `is` compares, so nothing new is needed in the heap -- only in what a function value
IS.

The change, in the order it has to happen:

1. `Stmt.setField` on a receiver that evaluates to `.fn`/`.clos`: allocate a heap object
   carrying the function, REBIND the receiver variable to the new `.ref`, then write the
   field. `execStmt` already returns `.normal ρ`, so the rebinding has somewhere to go. This
   only works when the receiver is a `.name`; a function value reached any other way has no
   place to rebind and must keep holing, which is correct rather than convenient.
2. The call path must dispatch through a `.ref` whose object carries a function -- the same
   site as the unbound-method rule in section 46.
3. `FuelMono` has a `setField` case and the call case; both need the branch taken, the same
   mechanical repair as section 46.

What makes this bigger than section 46 is that section 46 was GUARDED to be a no-op
everywhere else -- C++ has no `self`, so exactly one proof moved. This one changes what a
function value is, on every path that handles one, in every corpus. It was made, with the
gates run at each step rather than at the end.

Two proof sites moved, both in `FuelMono` and both mechanically: the call path (boxed objects
dispatch where the case used to be inert) and `setField` (boxing evaluates the right-hand
side IN THE POST-ALLOCATION HEAP, so the recursion is at `(boxFn h₁ _).1` and the proof has
to generalize over it rather than name `h₁`).

### Three more faults in the oracle, not in Core

Core was right after the first edit and the measurement still got worse before it got better,
in three stages -- worth recording, because each stage LOOKED like the change had failed:

1. Coverage rose 28 -> 34 as predicted, and divergences jumped 5 -> 35. The new divergences
   read `cpython=fn '_locked_info.<locals>.wrapper'` against `lean=ref 6`. Those are the same
   value: CPython reports the function, Core reports the object carrying it. A shape clash.
2. Unboxing in the harness -- reporting a boxed function as the function it carries, the same
   move `unwrap_bobj` already makes -- sent all 30 straight back to INCONCLUSIVE. A
   decorator's `wrapper` is a CLOSURE, so unboxing exposed `Val.clos`, which the parser had
   never had a case for. It read as unparsable, which is indistinguishable from abstaining.
3. With `Val.clos` parsed, the names still disagreed: CPython's `__qualname__` writes
   `<locals>` for function scope, Joern's qualified name writes `<module>` for file scope.
   Neither segment names anything a program can refer to. Dropping both before the
   dotted-suffix match closed it.

    compared    28 -> 34 of 180 hole-free (16% -> 19%)
    agree       135/140 (96%) -> 165/170 (97%)
    divergences 5 -> 5

So the coverage gain cost nothing in agreement, and the three faults were all in the
oracle -- the eighth, ninth and tenth found there this session, against one in Core. That
ratio is itself the finding: the measuring apparatus has been consistently less correct than
the thing it measures, and every one of those faults failed CLOSED, reporting abstention or
disagreement rather than false agreement. That is the direction an oracle should fail, and it
is not an accident -- it is what `shape_clash` and the liveness gate were built to force.

Still open: `call:set` (3 functions) needs a `Val.set`, a second and independent value-model
addition. `mcall:warn:keyword-to-builtin`, `expr:genExp`, `in:non-container` and
`mcall:clear:unboxed-container` are each one construct.

## 48. The largest blocker was not a semantics gap, and its stated cause was false

Ranking the report by what blocks each function put `set` seventh. First, at 54 functions --
MORE THAN WERE BEING COMPARED -- was:

    no live instance and constructor rejected ()/(1)/(2,1)

That cause was false for 48 of them. Three things were wrong, each hidden by the one above it:

1. **The constructor search never ran.** `find_class` returned `None`, so no argument shape
   was ever tried. The message named three shapes anyway.
2. **The class lookup could not have worked.** `import cachetools` loads `cachetools.keys`
   and nothing else -- `_cached` and `_cachedmethod` are imported lazily inside functions --
   so tracing the suite never put them in `sys.modules`. Importing a submodule of a package
   the suite already imported is not fabricating state; it is loading code the corpus ships
   and the AST was exported from.
3. **Some of those names are not classes at all.** `_condition.wrapper` and
   `_locked_info.cache_info` are nested FUNCTIONS -- closures returned by a factory -- which
   a split on the last dot had classified as `Class.method`. They need their factory called
   and its result captured, which is a different piece of work from constructing an instance.

After fixing all three the bucket is gone and the causes are true: 9 `unencodable
receiver/arguments: callable`, 6 varargs, 5 nested-function-needs-factory. `COMPARED` moved
only 34 -> 35, and that is the honest outcome: the win here is not coverage, it is that the
largest category in the report stopped lying about why it was blocked. A wrong cause is worse
than a coarse one -- it sends the next person to widen a constructor search that was never
reached.

The remaining 9 are self-inflicted and recorded as such: the widened search fabricates a
`lambda` for parameters named `func`/`key`, and a fabricated lambda has no counterpart in the
AST, so the encoder correctly refuses it. Drawing those from corpus functions instead
(`cachetools.keys.hashkey` for `key`) is the next step.

### Why `set` is not next

`Val.set` looked like the biggest remaining item at 9 functions. It is not worth doing yet.
LFUCache builds a set and then MUTATES it (`link.keys.add(key)`, `.remove(key)`), and Core's
containers are value-semantics, so mutation has to hole exactly as `setIndex` already does.
Adding the constructor would move those 9 functions from `blocked (value model): set` to
`runtime holes mcall` and compare nothing new, while obliging an audit of every catch-all
`match` on `Val` -- the risk the `bobj` note in `Syntax.lean` already spells out. The real
blocker underneath is mutable containers on the heap, which is also what
`mcall:clear:unboxed-container` and `setIndex:immutable-containers` are.

### 48a. A fix that was measured and reverted

The 9 `unencodable receiver/arguments: callable` cases looked self-inflicted -- the widened
constructor search fabricates a `lambda`, and a fabricated lambda has no counterpart in the
AST -- so the obvious repair was to draw those arguments from functions the corpus defines.

It was implemented, measured, and reverted. `COMPARED` went 35 -> 34 and the 9 cases did not
move, because the premise was wrong: a lambda HAS a `__qualname__` (`<lambda>`) and encodes
fine. The unnamed callables are `functools.partial` objects, which have neither `__name__`
nor `__qualname__` and which the change never touched. It made constructors reject arguments
they had been accepting, and fixed nothing.

Recorded because the reasoning is more re-derivable than the result: the next person to read
`unencodable ...: callable` will suspect the fabricated lambdas too. They are not the cause.

## 49. `self` was stripped from functions that were not methods

`applyFunc` binds a receiver itself, so the exporter drops the `self` parameter. It dropped
it from EVERY function whose first parameter was named `self`, and that is not the same set:

    def methodkey(self, *args, **kwargs):      # module scope, cachetools/keys.py
        return hashkey(*args, **kwargs)

`methodkey` is a module-level function. Its `self` is an ordinary positional -- Python does
not treat the name specially, only the binding does. With it stripped, `methodkey(10, -4)`
put both arguments into `*args` and Core computed `hashkey(10, -4)` where CPython computes
`hashkey(-4)`. It surfaced as `cpython=tuple[int -4]` against a `_HashedTuple` carrying two
elements, which reads as a builtin-subclass representation problem and is nothing of the
kind: a parameter was missing.

The first fix used `astParentType == "TYPE_DECL"`, which is not what pythonsrc marks methods
with. It stripped nothing and changed 140 functions -- caught by diffing the re-export
against the committed AST before installing it, which is the only reason it did not land.
The working signal is one this exporter already computes: `classNames` holds every real
`class` statement, so a function is a method exactly when the segment before its own name is
one of them. Nine functions changed, and all nine are genuinely not methods -- `methodkey`,
`typedmethodkey`, and the `wrapper`/`cache_clear`/`classmethod_wrapper` closures that
decorators build inside a factory.

    agree         169/174 (97%) -> 174/174 (100%)
    divergences   5 -> 0
    compared      35 of 180 hole-free, unchanged

### 100% is the number this project distrusts

A dead oracle reports zero divergences, and so does a perfect one. The liveness gate in CI
only checks `COMPARED > 0`, which this passes at 35 -- necessary, not sufficient. So the
claim was tested directly: `_DefaultSize.__getitem__` was edited to return `2` where CPython
returns `1`, the module rebuilt, and the oracle re-run.

    DIVERGENCE ..._DefaultSize.__getitem__(int -1): cpython=int 1 lean=int 2

It found it, on every case, and the fault was reverted and the build re-verified. The 100% is
an oracle that adjudicated 174 cases and agreed, not one that abstained. Note what the check
is worth: it proves the pipeline can still report a disagreement end to end -- encoder, Lean
harness, parser, comparison. It does not prove the semantics are right about anything the
oracle never reaches, which is still 145 of 180 hole-free functions.

## 50. A loader bug that looked like unreachable code

`load_module` loaded a corpus file BY PATH, which gives it a synthetic top-level name
(`cachetools__init___py`). Every RELATIVE import inside such a module then fails: `from . import
keys` has no package to be relative to. `load_module` caught the exception and returned
`None`, the caller did `continue`, and the functions in that file got no cases.

That is not an edge case. It is every package `__init__.py`, which is where a library puts
its public API. Here it cost `cached`, `cachedmethod` and `_cache` -- and the report called
them "hole-free, no case built", which reads as "the harness could not think of an argument"
rather than "the file never loaded".

Asking for the module by package name first, and keeping the path loader as the fallback for
a corpus that is not an importable package:

    compared    35 -> 38 of 180 hole-free (19% -> 21%)
    cases       174 -> 189
    agree       189/189 (100%), 0 divergences

Fifteen new cases, all agreeing. This is the third distinct failure this session where the
oracle reported a SEMANTIC blocker for something that was purely mechanical -- after the
false "constructor rejected" cause (section 48) and the lazily-imported submodules that made
`find_class` return `None` for 48 functions. The pattern is consistent enough to state as a
rule: when the report says a function is unreachable, check that the harness can load and
call it AT ALL before believing anything about the semantics.

## 51. Reaching closures through their factory: reach up, coverage flat

A decorator's `wrapper`, and the `Descriptor.Wrapper` classes cachetools builds inside
`_condition`/`_locked`/`_unlocked`, do not exist until their factory runs. They are closures,
not module attributes. Splitting the qualified name on the last dot classified them as
`Class.method`, so the report said "class not found" -- true, and useless: nothing is wrong
with the class, it has not been created yet.

`resolve_via_factory` calls the factory with synthesized arguments and then walks the
remaining name segments, accepting three shapes: an attribute of the result
(`wrapper.cache_clear`), the result ITSELF when the factory returns the thing being named
(`_locked` returns `wrapper`), or a nested class to construct.

    exercised    85 -> 91
    COMPARED     38 -> 38, unchanged
    cases        189 -> 189 compared, INCONCLUSIVE 236 -> 266

**The headline did not move, and that is the honest result.** All six newly reached
functions produce cases that Core cannot answer: they land in `runtime holes mcall` (20 ->
21), `call` (15 -> 16) and `field` (6 -> 10). What changed is the ATTRIBUTION. Those six were
being counted against the harness's inability to construct a receiver; they are now counted
against holes in the semantics, which is where the work actually is.

Kept rather than reverted -- unlike section 48a, which cost a compared function and fixed
nothing -- because it costs nothing measured and it stops six functions being blamed on the
wrong component. The capability pays off when those holes close, not before.

## 52. One unmodelled import destroyed a module's entire global scope

Ranking the report by HOLE LABEL rather than by bucket put `set` fifth. First was
`field:__enter__:non-object` at 9 functions, second `mcall:__init__:non-object` at 6 -- every
subclass constructor in the corpus. Neither is a container problem.

`LRUCache.__init__` starts `Cache.__init__(self, maxsize, getsizeof)`: an unbound method
reached through the CLASS, where Python passes the receiver as an ordinary first positional.
That is the same rule as section 46, never applied to `Expr.mcall`. Adding it did NOT fix the
6 functions, and the failure is what found the real bug: a direct probe of the harness
globals showed `Cache bound: false`, 42 fields, all of them from `keys.py`. The receiver was
not a class value. It was nothing.

The exporter binds an absent module to a HOLE VALUE. `execStmt` stops at a hole, so one
`import time` aborted `cachetools/__init__.py`'s initialiser and every `class` statement
after it never ran. `__version__` and `__all__` were bound because they precede the imports;
everything after was lost.

A hole in a value should be LOCAL, not fatal. The name really is bound in Python -- to a
module object Core cannot model -- so it is now bound to an opaque marker that no source
language can spell. Every USE of it still holes, carrying the same information, without
destroying the rest of the file.

    AST functions changed      4   (only the module initialisers)
    holes in ast-Cachetools   40 -> 26
    globals fields            42 -> 102
    hole-free functions      180 -> 184
    COMPARED                  38 -> 41 of 184 (21% -> 22%)
    cases                    189 -> 204, still 0 divergences

Two judgements inside this worth keeping:

* The class-value dispatch uses `classDefines`, NOT `resolveMethod`. The latter falls back to
  any free function of the same name, and with opaque modules now reachable, `time.monotonic`
  would have invented a method out of an unrelated global.
* `classNameOfValue` is a named Core function rather than an inline expression, because the
  inline version was unmanageable in `FuelMono`. Code a proof cannot talk about is code that
  resists checking.

### A caveat I raised and then had to withdraw

I recorded that V8, Linux and Ansible were left carrying the old `import:absent:*` holes and
were now inconsistent with the exporter. **That was wrong, and checking took one command:**

    for f in ast-*.json; do grep -c "import:absent" $f; done   # every one: 0

No committed AST contains an absent-import hole. `import` is a PYTHON construct; V8 and Linux
are C and C++, and the `Lang*` corpora are Java, Go, JS, TS and C. The only Python corpus with
a committed AST is cachetools, which was re-exported. Ansible's AST is not committed at all --
the ~2,400 figure comes from a measurement run whose artifact was never checked in.

Recorded because the failure mode is the project's own, pointed the other way. The rule here
has been that a metric computed from the artifact it describes will flatter itself, so claims
get checked against the artifact. A CAVEAT is a claim too. Stating an unverified one is not
the safe direction -- it is the same error with the sign flipped, and it sends the next person
to re-export three corpora that never needed it.

The real outstanding item is narrower: Ansible is a Python corpus where this fix should help,
and it has never had a committed AST. That is new measurement, not a repair.

### 52a. The same fix, measured on Ansible

Ansible is the largest Python corpus and the one where absent imports were worst. Re-exported
with the fix, from the CPG already in `workspace/`:

    functions            5,547
    holes            5,101 -> 3,131   (-39%)
    absent-import holes  1,970 -> 0
    hole-free        3,753 -> 4,017   (68% -> 72%)
    functions recovered    264

The 1,970 figure is exact rather than inferred: every opaque marker in the new AST is one
hole that the old exporter emitted in that position, so the two are countable against each
other in the same artifact.

264 functions became hole-free because their ONLY hole was an import. Those were not hard
constructs, and nothing about them was ever unanalysable -- the module they lived in simply
stopped executing at its first `import`. This is the same shape as the 571 Linux functions in
section 43, which were absent from the corpus rather than untranslatable: the biggest wins so
far have come from finding out that something was never reached, not from modelling something
difficult.

Not committed: `ast-Ansible.json` has never been a tracked artifact, and adding a 5,547
-function corpus to the repository is a separate decision from fixing the exporter.

