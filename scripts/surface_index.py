#!/usr/bin/env python3
"""Surface index for crnt-lean: a real parser for the `CRNT/` + `Scaffold/` sources.

Why this exists
---------------
`scripts/decl_index.py` answers "is there already a theorem like this one?".  It
cannot answer the questions the swarm actually has, which are structural:

* which declarations sit on a path from one of the two open holes to a consumer;
* which modules are load-bearing and which are decorative;
* which obligations are stated twice under different names;
* what the docstrings actually cite, so the theorem index can be cross-referenced.

So this module parses the sources properly: it tracks `namespace`/`section` nesting,
attributes, `variable` binders, doc comments and string literals, and splits each
declaration into a *signature* (everything up to the first top-level `:=`/`by`/
`where`) and a *body* (everything after it).  Bodies are normalized and hashed, which
is what makes the duplication map machine-generated rather than anecdotal.

The output is consumed by `scripts/gen_docs.py`.  Nothing here writes files.

Design notes
------------
* We never parse Lean with a full grammar.  We tokenize just enough to know whether a
  character is inside a comment, a string, or an identifier, and we use indentation
  (column 0 = top level) to delimit top-level declarations.  That is exactly the
  convention the repo follows in all 870 modules, and `check_imports.py` keeps it true.
* `fullname` is the namespace stack joined with the declaration name.  This is what
  makes the *collision* analysis possible: two declarations with the same short name in
  different namespaces are genuinely different Lean names, and the short name is what a
  reader is most likely to collide on.
"""

from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass, field
from typing import Iterable

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------------------
# lexer-ish helpers
# ---------------------------------------------------------------------------

_IDENT_START = re.compile(r"[A-Za-z_]")


def strip_comments_keep_lines(text: str) -> str:
    """Blank out line comments, block comments (incl. `/--` docstrings) and string
    literal interiors, preserving every character position (so offsets stay valid)."""
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0  # >0 inside a block comment
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        elif depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif depth == 0 and text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif depth == 0 and text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append(text[i:j])
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def doc_comment_blocks(text: str) -> list[tuple[int, str]]:
    """Every `/-- ... -/` block, as `(line_of_opening_delimiter, body)`.

    `/--` is the declaration docstring form; `/-!` is the module header and is
    deliberately excluded — it is attributed to the module, not to a declaration.
    """
    out: list[tuple[int, str]] = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("/--", i):
            j = text.find("-/", i + 3)
            if j == -1:
                break
            body = text[i + 3 : j]
            out.append((text.count("\n", 0, i) + 1, body))
            i = j + 2
        elif text.startswith("/-", i):
            j = text.find("-/", i + 2)
            i = n if j == -1 else j + 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        else:
            i += 1
    return out


def module_header_doc(text: str) -> str:
    """The `/-! ... -/` module header, if any."""
    m = re.search(r"/-!(.*?)-/", text, re.S)
    return m.group(1).strip() if m else ""


# ---------------------------------------------------------------------------
# declaration records
# ---------------------------------------------------------------------------

DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive",
              "instance", "class", "opaque", "axiom", "example", "where")

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+)*"
    r"(?P<kind>" + "|".join(DECL_KINDS) + r")\s+"
    r"(?P<name>[^\s:({\[]+)"
)

NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)")
END_RE = re.compile(r"^end\b")
SECTION_RE = re.compile(r"^(?:protected\s+)?section\b")
VARIABLE_RE = re.compile(r"^variable\s")


@dataclass
class Decl:
    module: str                    # dotted module name
    path: str                      # repo-relative source path
    line: int                      # 1-based line of the `theorem`/`def` keyword
    kind: str
    name: str                      # short name as written
    fullname: str                  # namespace-qualified Lean name
    signature: str                 # normalized single-line binder+type text
    body: str                      # raw body text (after `:=` / `by` / `where`)
    body_norm: str                 # whitespace/comment-normalized body
    doc: str                       # docstring text (newlines collapsed)
    has_sorry: bool = False
    sorry_count: int = 0
    locals_: tuple[str, ...] = ()  # `variable` binders in scope
    section: str = ""
    # filled in from the Lean environment dump when available
    axioms: tuple[str, ...] = ()
    env_type: str = ""

    @property
    def body_hash(self) -> str:
        return hashlib.sha256(self.body_norm.encode("utf-8")).hexdigest()[:16]

    @property
    def stmt_norm(self) -> str:
        """Binder-erased, whitespace-free rendering of the signature.

        Binder names are the *only* thing allowed to differ between two declarations
        that state the same obligation, so we canonicalize them away: every
        identifier immediately followed by `:` inside a binder group becomes `_`.
        """
        s = re.sub(r"\s+", " ", self.signature)
        s = re.sub(r"@\[[-\w.]+(\s+[^\]]*)?\]", "", s)  # attributes
        # binder erasure: `x y : T` / `{x : T}` / `(x : T)`
        s = re.sub(r"\(([^()]*)\)", lambda m: "(" + _erase_binders(m.group(1)) + ")", s)
        s = re.sub(r"\{([^{}]*)\}", lambda m: "{" + _erase_binders(m.group(1)) + "}", s)
        s = re.sub(r"\[([^\[\]]*)\]", lambda m: "[" + _erase_binders(m.group(1)) + "]", s)
        return re.sub(r"\s+", "", s)


def _erase_binders(g: str) -> str:
    """Replace every `ident (: | := | ?)` head inside a binder group by `_`."""
    g = re.sub(r"\b([A-Za-z_][A-Za-z0-9_'.]*)(\s*)(?=[:?=])", "_ ", g)
    g = re.sub(r"(\s*)\b([A-Za-z_][A-Za-z0-9_'.]*)(\s*)(\()", r"\1_\3\4", g)
    return g


def normalize_body(body: str) -> str:
    """Whitespace- and comment-free rendering of a proof body."""
    b = strip_comments_keep_lines(body)
    b = re.sub(r"\s+", " ", b)
    return b.strip()


# ---------------------------------------------------------------------------
# the parser
# ---------------------------------------------------------------------------

@dataclass
class Module:
    name: str
    path: str
    text: str
    code: str
    imports: list[str] = field(default_factory=list)
    header: str = ""
    decls: list[Decl] = field(default_factory=list)

    @property
    def relpath(self) -> str:
        return self.path


def lean_files(*dirs: str) -> list[str]:
    out: list[str] = []
    for d in dirs:
        base = os.path.join(ROOT, d)
        if not os.path.isdir(base):
            continue
        for dp, _, fs in os.walk(base):
            for f in sorted(fs):
                if f.endswith(".lean"):
                    out.append(os.path.join(dp, f))
    return sorted(out)


def parse_module(path: str) -> Module:
    rel = os.path.relpath(path, ROOT)
    name = rel[:-5].replace(os.sep, ".")
    with open(path, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    code = strip_comments_keep_lines(text)
    lines = code.split("\n")
    raw_lines = text.split("\n")
    docs = doc_comment_blocks(text)

    mod = Module(name=name, path=rel, text=text, code=code, header=module_header_doc(text))
    mod.imports = [m.group(1) for m in
                   (re.match(r"import\s+([A-Za-z0-9_.]+)", l.strip()) for l in raw_lines) if m]

    ns: list[str] = []            # namespace stack
    locals_: list[str] = []
    sections: list[str] = []

    # Single stateful pass: declarations *and* namespace/section/variable bookkeeping in
    # source order, so each declaration sees the namespace it was actually written in.
    # `variable` lines are not declarations but they do change the binder context, and
    # `end` closes either a namespace or a section, so we cannot do two independent
    # passes.
    events: list[tuple[int, str, object]] = []
    for i, line in enumerate(lines):
        if not line or line[0].isspace():
            continue
        m = DECL_RE.match(line)
        if m:
            events.append((i, "decl", m))
            continue
        m = NAMESPACE_RE.match(line)
        if m:
            events.append((i, "ns", m.group(1)))
            continue
        if END_RE.match(line):
            events.append((i, "end", None))
            continue
        m = SECTION_RE.match(line)
        if m:
            sections.append(line.strip())
            events.append((i, "sec", None))
            continue
        if VARIABLE_RE.match(line):
            locals_.append(line.strip())
            continue

    # `open_stack` records what is open, because Lean writes `end` identically for a
    # namespace and for a section.
    open_stack: list[str] = []
    for idx, (i, kind, payload) in enumerate(events):
        if kind == "decl":
            m: re.Match = payload  # type: ignore[assignment]
        elif kind == "ns":
            ns.append(payload)  # type: ignore[arg-type]
            open_stack.append("ns:" + str(payload))
            continue
        elif kind == "sec":
            sections.append("")
            open_stack.append("sec")
            continue
        elif kind == "end":
            # `end` closes a namespace or a section and Lean writes both identically,
            # so we pop whichever opener is innermost.
            while open_stack:
                top = open_stack.pop()
                if top.startswith("ns:"):
                    ns.pop()
                elif sections:
                    sections.pop()
                break
            continue
        else:
            continue
        # find the next *declaration* event to bound this block
        nxt = len(lines)
        for j in range(idx + 1, len(events)):
            if events[j][1] == "decl":
                nxt = events[j][0]
                break
        block = "\n".join(lines[i:nxt])
        sig, body = split_signature(block)
        norm_body = normalize_body(body)
        ns_count = len(re.findall(r"(?<![A-Za-z_.'\"])\bsorry\b(?![A-Za-z_])", norm_body))
        short = m.group("name")
        full = ".".join(ns + [short]) if ns else short
        doc, doc_line = "", -1
        for dline, dtext in docs:
            if dline < i + 1 and i + 1 - dline < 40 and dline > doc_line:
                doc, doc_line = dtext.strip(), dline
        mod.decls.append(Decl(
            module=name, path=rel, line=i + 1, kind=m.group("kind"),
            name=short, fullname=full, signature=sig, body=body,
            body_norm=norm_body, doc=re.sub(r"\s+", " ", doc).strip(),
            has_sorry=ns_count > 0, sorry_count=ns_count,
            locals_=tuple(locals_),
            section=sections[-1] if sections else "",
        ))

    return mod



def split_signature(block: str) -> tuple[str, str]:
    """Split a declaration into (signature, body) at the first top-level `:=`, `by`,
    or `where`.  Depth tracking is parenthesis/bracket/brace/angle-aware and
    string-aware, so a `:=` inside a term (`fun x => (y := z)`) is not mistaken for
    the definition boundary."""
    depth = 0
    i, n = 0, len(block)
    in_str = False
    while i < n:
        c = block[i]
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            if block.startswith(":= ", i) or block.startswith(":=\n", i) or block.startswith(":=\t", i):
                return block[:i].rstrip(), block[i + 2 :]
            if re.match(r"^:=[^\s:=]", block[i:]):
                return block[:i].rstrip(), block[i + 2 :]
            if re.match(r"^(by|where)\b", block[i:]):
                # `by`/`where` only terminates when it is preceded by whitespace and
                # the statement is already closed
                if i == 0 or block[i - 1] in " \t\n)}":
                    return block[:i].rstrip(), block[i:]
        i += 1
    return block.rstrip(), ""


def parse_all(*dirs: str) -> list[Module]:
    return [parse_module(p) for p in lean_files(*dirs)]


# ---------------------------------------------------------------------------
# import graph
# ---------------------------------------------------------------------------

def import_graph(mods: Iterable[Module]) -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """`(forward, backward)` module-level dependency maps.

    Only edges between modules that exist on disk are kept; an `import` of a module
    outside `CRNT/`+`Scaffold/` (Mathlib, Batteries) is dropped because it carries no
    information about *this* repository's layering."""
    mods = list(mods)
    names = {m.name for m in mods}
    fwd: dict[str, set[str]] = {m.name: set() for m in mods}
    bwd: dict[str, set[str]] = {m.name: set() for m in mods}
    for m in mods:
        for imp in m.imports:
            if imp in names and imp != m.name:
                fwd[m.name].add(imp)
                bwd[imp].add(m.name)
    return fwd, bwd


def transitive(bwd: dict[str, set[str]], start: str) -> set[str]:
    """Everything that transitively depends on `start` (its *dependents*)."""
    seen: set[str] = set()
    stack = list(bwd.get(start, ()))
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        stack.extend(bwd.get(x, ()))
    return seen


def transitive_deps(fwd: dict[str, set[str]], start: str) -> set[str]:
    """Everything `start` transitively depends on (its *dependencies*)."""
    seen: set[str] = set()
    stack = list(fwd.get(start, ()))
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        stack.extend(fwd.get(x, ()))
    return seen


def shortest_path(bwd: dict[str, set[str]], start: str, target: str) -> list[str] | None:
    """A shortest module-level path `start -> ... -> target` along the reverse graph."""
    if start == target:
        return [start]
    prev: dict[str, str] = {}
    seen = {start}
    frontier = [start]
    while frontier:
        nxt = []
        for x in frontier:
            for y in bwd.get(x, ()):
                if y in seen:
                    continue
                seen.add(y)
                prev[y] = x
                if y == target:
                    path = [y]
                    while path[-1] != start:
                        path.append(prev[path[-1]])
                    return list(reversed(path))
                nxt.append(y)
        frontier = nxt
    return None


# ---------------------------------------------------------------------------
# citation harvesting
# ---------------------------------------------------------------------------

PAPERS: dict[str, str] = {
    "craciun-gac": "Craciun, *Toric differential inclusions and a proof of the global attractor conjecture* (arXiv:1501.02860)",
    "craciun-2023": "Craciun, *Toric differential inclusions ...* v3 (arXiv:2306.03055)",
    "shinar-feinberg": "Shinar–Feinberg, *Structural at-systems of the complex plane*",
    "craciun-fiebig-singleton": "Craciun–Fiebig–Singleton, *Toric-differential inclusions and a proof of the global attractor conjecture*",
    "anderson-shiu": "Anderson–Shiu, *A lock-in region for a differential inclusion*",
    "feinberg-horn-jackson": "Feinberg–Horn–Jackson, *The theory of differential inclusions for chemical reaction networks*",
    "gunnells": "Gunnells, general-complex-balanced (2012)",
    "horn-jackson": "Horn–Jackson, *General mass action kinetics*",
    "andrews-craciun": "Andrews–Craciun, *The graphical criterion for complex balanced equilibria*",
    "soules": "Soules, *A graphical approach to the global attractor conjecture*",
    "craciun-b Announces": "Craciun, *Which reaction networks are weakly reversible?*",
    "monk": "Monk–Gunnells, *A Newton–Puiseux theorem for Pfaffian functions*",
    "deoliveira": "de Oliveira–van den Dries, *Theory of semiflows*",
    "craciun-r Translational": "",
    "craciun-singleton-2020": "Craciun–Singleton, *Toric differential inclusions and a proof of the global attractor conjecture*",
    "shiu-nagumo": "Shiu, *Nonnegative solutions of systems of differential equations*",
    "craciun-2024": "",
    "robbins": "Robbins–Savage, *A Bayesian approach to the global attractor conjecture*",
}

# Ordered: the first matching pattern wins, so `arXiv:1501.02860` is attributed to the
# GAC paper and not to the (same-author) v3 note.
CITE_PATTERNS: list[tuple[str, str]] = [
    (r"arXiv:1501\.02860", "craciun-gac"),
    (r"\bv3\b.{0,40}Craciun|Craciun.{0,40}\bv3\b|arXiv:2306\.03055", "craciun-2023"),
    (r"Shinar[-–]Feinberg|Shinar & Feinberg", "shinar-feinberg"),
    (r"Craciun[-–]Fiebig[-–]Singleton|Fiebig[-–]Singleton", "craciun-fiebig-singleton"),
    (r"Anderson[-–]Shiu", "anderson-shiu"),
    (r"Feinberg[-–]Horn[-–]Jackson|Horn[-–]Jackson", "feinberg-horn-jackson"),
    (r"Gunnells", "gunnells"),
    (r"Andrews[-–]Craciun", "andrews-craciun"),
    (r"de Oliveira[-–]van den Dries|de\s*Oliveira", "deoliveira"),
    (r"Soules", "soules"),
    (r"Shiu", "shiu-nagumo"),
    (r"Robbins[-–]Savage", "robbins"),
]

# Locators: `Lemma 9.5`, `Theorem B`, `§7.4.3`, `Definition 4.6`, `Prop. 5.4`, `Thm 3.2`.
LOCATOR_RE = re.compile(
    r"(?:Lemma|Theorem|Definition|Prop(?:osition)?|Thm|Def|Corollary|Remark|Step|"
    r"Figure|Fig)\s+[A-Z]?\d+(?:\.\d+)*[a-z]?"
    r"|§+\s?\d+(?:\.\d+)*"
    r"|Theorem\s+[A-Z]"
    r"|arxiv:\d{4}\.\d{4,5}v?\d*"
)


def citations(text: str) -> dict[str, list[str]]:
    """Extract `(paper_key, [locators])` from a docstring or comment block.

    Locators are de-duplicated, order-preserving, and capped at six per declaration so
    a long module header does not dominate the index."""
    t = text
    found: dict[str, list[str]] = {}
    for pat, key in CITE_PATTERNS:
        if re.search(pat, t, re.I):
            found.setdefault(key, [])
    for m in LOCATOR_RE.finditer(t):
        loc = re.sub(r"\s+", " ", m.group(0)).strip()
        for key in found:
            found[key].append(loc)
    return {k: list(dict.fromkeys(v))[:6] for k, v in found.items()}


def module_citations(mod: Module) -> dict[str, list[str]]:
    """Citations from a module's own header plus its declaration docstrings."""
    out: dict[str, list[str]] = {}
    for text in [mod.header] + [d.doc for d in mod.decls]:
        for k, v in citations(text).items():
            out.setdefault(k, [])
            for loc in v:
                if loc not in out[k]:
                    out[k].append(loc)
    return {k: v[:12] for k, v in out.items()}


# ---------------------------------------------------------------------------
# declaration-level dependency edges (source-level)
# ---------------------------------------------------------------------------

# Names of CRNT declarations we are willing to resolve.  A mention of one of these
# short names inside a declaration's signature or body is, to a very good
# approximation, a use of that declaration.  The approximation is honest: Lean
# namespaces can be reopened, and a local `variable` can shadow a global name.  The
# exact graph comes from `scripts/surface/DumpEnv.lean` when its JSON is present; see
# `load_env_edges`.
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def decl_mentions(decl: Decl, short_index: dict[str, list[Decl]]) -> list[Decl]:
    """Declarations whose short name appears in `decl`'s signature or body.

    Lean writes a reference to a declaration in a namespace as a *single dotted token*
    (`N.exists_positive_omegaPoint_of_highCodimension_siphonFace`), so matching whole
    identifier tokens would miss every qualified use — which is most uses.  We resolve
    each dotted token against the short index at every suffix boundary, so
    `Network.foo` resolves to `foo` and `foo` resolves to `foo`.
    """
    text = decl.signature + " " + decl.body_norm
    out: list[Decl] = []
    seen: set[str] = set()
    for tok in IDENT_RE.findall(text):
        parts = tok.split(".")
        for k in range(1, len(parts) + 1):
            for cand in short_index.get(".".join(parts[k - 1:]), ()):
                if cand.fullname in seen or cand.fullname == decl.fullname:
                    continue
                seen.add(cand.fullname)
                out.append(cand)
    return out


def build_short_index(mods: Iterable[Module]) -> dict[str, list[Decl]]:
    idx: dict[str, list[Decl]] = {}
    for m in mods:
        for d in m.decls:
            if d.kind in ("example", "where"):
                continue
            idx.setdefault(d.name, []).append(d)
    return idx


def load_env_edges(path: str) -> dict[str, list[str]] | None:
    """Read the exact constant-level dependency graph produced by
    `scripts/surface/DumpEnv.lean`.  Returns `None` when the dump is absent, in which
    case the caller falls back to the source-level approximation above."""
    import json

    if not os.path.isfile(path):
        return None
    with open(path, encoding="utf-8") as fh:
        data = json.load(fh)
    g: dict[str, list[str]] = {}
    for a, b in data.get("edges", []):
        g.setdefault(a, []).append(b)
    return g


def load_env_decls(path: str) -> dict[str, dict] | None:
    """Read the exact `name -> {mod, kind, type, doc, axioms}` map from the dump."""
    import json

    if not os.path.isfile(path):
        return None
    with open(path, encoding="utf-8") as fh:
        data = json.load(fh)
    return {d["name"]: d for d in data.get("decls", [])}


__all__ = [
    "ROOT", "Decl", "Module", "lean_files", "parse_module", "parse_all",
    "import_graph", "transitive", "transitive_deps", "shortest_path",
    "strip_comments_keep_lines", "normalize_body", "doc_comment_blocks",
    "citations", "module_citations", "PAPERS", "CITE_PATTERNS",
    "build_short_index", "decl_mentions", "load_env_edges", "load_env_decls",
]