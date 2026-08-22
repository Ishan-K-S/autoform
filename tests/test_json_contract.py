"""The JSON contract between `cartographer/export_ast.sc` (Scala) and the Python side.

The Scala exporter belongs to another workstream; this file does not test it. It tests
the *contract*: every committed `ast-*.json` must be something `render_lean.py` can turn
into Lean without inventing anything, and the facts the exporter promises about literals,
holes and varargs must hold on the artifacts that are actually in the tree.

Every test here fails loudly when there is nothing to inspect. "No AST files found" is
not a pass.
"""
from __future__ import annotations

import glob
import json
import os
import re
import sys
import threading

import pytest

from conftest import ROOT

AST_GLOB = os.path.join(ROOT, "ast-*.json")


def ast_paths():
    return sorted(glob.glob(AST_GLOB))


@pytest.fixture(scope="module")
def corpora():
    paths = ast_paths()
    if not paths:
        pytest.fail("no ast-*.json in %s — this suite inspected nothing, which is a "
                    "failure, not a pass. Re-run the exporter or point ROOT at the "
                    "repository." % ROOT)
    return _load_on_a_big_stack(paths)


def _load_on_a_big_stack(paths):
    """`json.load` recurses once per nesting level, and a translated function body nests
    as deeply as the source did. CPython's default 1000-frame limit is reached by the
    real corpora -- Ansible and LinuxLib both blow it -- so the decode runs on a thread
    with a large stack, exactly as `differential.py` and `render_lean.py` already do.

    This suite was passing only because those ASTs are gitignored build products and were
    absent from the tree. A test that inspects the small corpora and errors on the large
    ones is not testing "every committed AST"; it is testing the ones that fit."""
    out, err = {}, []

    def main():
        try:
            for path in paths:
                out[os.path.basename(path)] = json.load(open(path))
        except Exception as exc:                            # noqa: BLE001
            err.append(exc)

    sys.setrecursionlimit(300_000)
    threading.stack_size(512 * 1024 * 1024)
    thread = threading.Thread(target=main)
    thread.start()
    thread.join()
    if err:
        raise err[0]
    return out


def walk(node):
    """Every dict in the tree. ITERATIVE: `yield from` recursion costs a frame per level
    and per element, which the large corpora exceed even with a raised limit."""
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, dict):
            yield cur
            stack.extend(cur.values())
        elif isinstance(cur, list):
            stack.extend(cur)


# ---------------------------------------------------------------------------

class TestTopLevelShape:
    def test_each_ast_is_a_list_of_functions(self, corpora):
        for name, funcs in corpora.items():
            assert isinstance(funcs, list) and funcs, name

    def test_required_fields(self, corpora):
        for name, funcs in corpora.items():
            for f in funcs:
                assert isinstance(f.get("name"), str) and f["name"], name
                assert isinstance(f.get("file"), str), (name, f.get("name"))
                assert isinstance(f.get("params"), list), (name, f["name"])
                assert all(isinstance(p, str) for p in f["params"]), (name, f["name"])
                assert isinstance(f.get("body"), dict), (name, f["name"])

    def test_every_corpus_can_infer_a_dialect(self, corpora, render_lean):
        """An extension the renderer cannot map is a hard stop at render time (by
        design — defaulting gave a `.tsx` file Python's floored division). Catch it at
        the artifact instead of at the next render."""
        for name, funcs in corpora.items():
            try:
                d = render_lean.infer_dialect(funcs)
            except SystemExit as e:
                pytest.fail("%s: %s" % (name, e))
            assert d in (".python", ".cLike"), (name, d)

    # Was a strict xfail recording that `.cc` was absent from render_lean.DIALECT:
    # ast-V8Numbers.json is 104 `.cc` against 53 `.h`, so the dialect was decided by the
    # HEADERS alone and a pure-`.cc` corpus aborted the render. That is no longer
    # hypothetical — extracting a 4-function V8 sample produced exactly such a corpus and
    # the renderer refused. `.cc`/`.cxx`/`.hh`/`.hpp` were added; the xfail was strict, so
    # it failed the moment the gap closed, which is how this test came to be a real one.
    def test_all_extensions_present_in_the_dialect_table(self, corpora, render_lean):
        for name, funcs in corpora.items():
            exts = {os.path.splitext(f.get("file", ""))[1] for f in funcs}
            unknown = {e for e in exts if e and e not in render_lean.DIALECT}
            assert not unknown, "%s: %s" % (name, sorted(unknown))


class TestLiteralContract:
    def test_ints_are_exact(self, corpora):
        """`v` is a JSON number when |v| <= 2^53 and a decimal *string* beyond it.
        A number past 2^53 means the exporter let a double round the value."""
        seen = 0
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") != "int":
                    continue
                seen += 1
                v = n["v"]
                assert isinstance(v, (int, str)) and not isinstance(v, bool), (name, v)
                if isinstance(v, int):
                    assert abs(v) <= 2 ** 53, (
                        "%s: integer %d is past 2^53 and was carried as a JSON number, "
                        "which is a double — emit it as a string" % (name, v))
                else:
                    assert re.fullmatch(r"-?\d+", v), (name, v)
        assert seen > 0, "no integer literals in any corpus — nothing was checked"

    @pytest.mark.xfail(strict=True, reason=(
        "KNOWN GAP, reported not hidden: the exporter promises `k:int` carries a JSON "
        "number up to 2^53 and a decimal *string* beyond it, but ast-V8Numbers.json "
        "encodes 218 small integers as strings (92 of them plain \"0\"). Nothing is "
        "lost — render_lean.lean_int accepts both and emits the same Lean — but the "
        "artifact is non-canonical, so a byte comparison of two ASTs of the same code "
        "can differ for no semantic reason. Strict xfail: it fails once fixed."))
    def test_int_encoding_is_canonical(self, corpora):
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") == "int" and isinstance(n["v"], str):
                    assert abs(int(n["v"])) > 2 ** 53, (
                        "%s: %s is small enough to be a JSON number" % (name, n["v"]))

    def test_big_ints_render_without_loss(self, corpora, render_lean):
        """The VALUE must round-trip, sign included.

        This compared `lean_int(v).strip("()")` against `v.lstrip("-")`, which strips the
        sign from the expected side only -- so it demanded that `-6` render as `6`. It
        passed for as long as every string-encoded integer in the tree happened to be a
        large positive one, and failed the moment a corpus containing a negative one was
        inspected. `lean_int` was right all along: it emits `(-6)`, parenthesised because
        Lean needs it in argument position."""
        bigs = [n["v"] for fs in corpora.values() for n in walk(fs)
                if n.get("k") == "int" and isinstance(n["v"], str)]
        for v in bigs:
            assert int(render_lean.lean_int(v).strip("()")) == int(v)

    def test_hex_and_suffixed_literals_did_not_become_holes(self, corpora):
        """`0xFFFFFFFF`, `1ULL`, `0b10000`, `0x0010'0000'0000'0000` all used to fall
        through to a `lit:unquoted` hole. If a C-family corpus is present, its
        unquoted-literal holes must not be dominated by plain integers."""
        offenders = []
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") in ("hole", "holeS") and n.get("label") == "lit:unquoted":
                    offenders.append(name)
        # `lit:unquoted` is legitimate for things Core genuinely cannot model (chars,
        # user-defined literals). What must not happen is the count exploding: pin it.
        counts = {k: offenders.count(k) for k in set(offenders)}
        for name, c in counts.items():
            total = sum(1 for _ in walk(corpora[name]))
            assert c < total * 0.02, (
                "%s: %d `lit:unquoted` holes out of %d nodes — the integer-literal "
                "parser has regressed" % (name, c, total))

    def test_bool_literals_are_real_bools(self, corpora):
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") == "bool":
                    assert isinstance(n["v"], bool), name

    def test_string_literals_are_strings(self, corpora):
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") == "str":
                    assert isinstance(n["v"], str), name


class TestHoleContract:
    """A hole is the honest form of "not translated". An *unlabelled* hole is not:
    it makes the gap uncountable, and every downstream ledger counts by label."""

    def test_every_hole_carries_a_nonempty_label(self, corpora):
        seen = 0
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") in ("hole", "holeS"):
                    seen += 1
                    assert isinstance(n.get("label"), str) and n["label"].strip(), name
        assert seen > 0, "no holes anywhere — either 100% translation or a broken walk"

    def test_labels_are_namespaced(self, corpora):
        """`<family>:<detail>` so a ledger can group them. A bare word means somebody
        added a hole without deciding what family it belongs to."""
        bad = set()
        for funcs in corpora.values():
            for n in walk(funcs):
                if n.get("k") in ("hole", "holeS"):
                    if not re.fullmatch(r"[A-Za-z][\w.-]*(:[\w.<>+-]+)+", n["label"]):
                        bad.add(n["label"])
        assert not bad, sorted(bad)

    def test_import_holes_use_the_documented_vocabulary(self, corpora):
        """The import resolver reports a hole under a closed vocabulary, and each label
        names *why* the import was not translated. The set below is the whole of it;
        a label outside it means somebody widened the resolver without saying so.

        `import:absent:*` are the three-way split of what `import:unresolved` used to
        conflate (see cartographer/export_ast.sc `absentModule`): a relative import
        whose target is not in the CPG, one whose *prefix* is in the CPG (so more
        exporter work could resolve it), and one that is simply external. Widening this
        set is fine when the exporter genuinely gains a label -- but it must be a
        deliberate edit here, not a silent pass."""
        # Widened when the module-object work replaced `import:module-value` /
        # `import:unresolved` with a taxonomy that says WHY resolution failed. The point
        # of the test is that the vocabulary is CLOSED, not that it never grows: a label
        # outside this set means the exporter invented a category nobody documented.
        allowed = {"import:module-value", "import:unresolved",
                   "import:absent:relative", "import:absent:prefix-in-cpg",
                   "import:absent:external", "import:member-not-found",
                   "import:operand"}
        seen = set()
        for funcs in corpora.values():
            for n in walk(funcs):
                lab = n.get("label")
                if isinstance(lab, str) and lab.startswith("import:"):
                    seen.add(lab)
        assert seen <= allowed, sorted(seen - allowed)

    def test_a_resolved_import_is_a_reference_not_a_hole(self, corpora):
        """`from ._cached import _wrapper` names a function of this program; it must
        come out as `fnref`/`closure`. If a Python corpus is present and *every* import
        is a hole, the resolver has stopped resolving."""
        py = {k: v for k, v in corpora.items()
              if any(f.get("file", "").endswith(".py") for f in v)}
        if not py:
            pytest.skip("no Python corpus in the tree")
        refs = sum(1 for fs in py.values() for n in walk(fs)
                   if n.get("k") in ("fnref", "closure"))
        assert refs > 0, ("every import in every Python corpus is a hole; the resolver "
                          "resolved nothing")


class TestRenderability:
    """The strongest contract statement available without running Lean: every node in
    every committed AST is one `render_lean.py` knows how to print."""

    def test_every_node_has_a_shape(self, corpora, render_lean):
        checked = 0
        for name, funcs in corpora.items():
            for f in funcs:
                self._walk_stmt(render_lean, f["body"], name, f["name"])
                checked += 1
        assert checked > 0

    @classmethod
    def _walk_stmt(cls, rl, n, corpus, fname):
        try:
            _, kids = rl.stmt_shape(n)
        except ValueError as e:
            pytest.fail("%s / %s: %s" % (corpus, fname, e))
        cls._kids(rl, kids, corpus, fname)

    @classmethod
    def _walk_expr(cls, rl, n, corpus, fname):
        try:
            _, kids = rl.expr_shape(n)
        except ValueError as e:
            pytest.fail("%s / %s: %s" % (corpus, fname, e))
        cls._kids(rl, kids, corpus, fname)

    @classmethod
    def _kids(cls, rl, kids, corpus, fname):
        for tag, val in kids:
            if tag == "e":
                cls._walk_expr(rl, val, corpus, fname)
            elif tag == "s":
                cls._walk_stmt(rl, val, corpus, fname)
            elif tag == "es":
                for x in val or []:
                    cls._walk_expr(rl, x, corpus, fname)
            elif tag == "ps":
                for p in val or []:
                    assert isinstance(p, list) and len(p) == 2, (corpus, fname)
                    for x in p:
                        cls._walk_expr(rl, x, corpus, fname)

    def test_class_bases_are_modelled(self, corpora, render_lean):
        base_ctor = {"tuple", "list", "dict", "str"}
        for name, funcs in corpora.items():
            for f in funcs:
                for cls, base in (f.get("classBases") or {}).items():
                    assert base in base_ctor, "%s: %s(%s)" % (name, cls, base)
