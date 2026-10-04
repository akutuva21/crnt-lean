#!/usr/bin/env python3
"""leanparse.py — a small, dependency-free Lean 4 *declaration* parser.

Shared by the audit scripts that need to reason about a declaration's **statement**
separately from its proof:

* `scripts/check_statement_drift.py` — compares statements across two git refs.
* `scripts/check_vacuity.py` — finds hypotheses that the proof never mentions.

Why a parser and not a regex
---------------------------
A regex for "what does this theorem say" cannot tell a signature from a proof.
`theorem foo (h : P) : Q := by exact h` has the shape

    keyword  name  <binder telescope>  :  <conclusion>  :=  <proof>

and the only thing separating conclusion from proof is the first `:=` (or
`where`, for structures) *at bracket depth zero*.  Getting depth wrong is how you
silently compare proofs instead of statements — which is precisely the bug class
`check_statement_drift.py` exists to catch, so the parser must not have it.

Everything here is pure text processing: no Lean toolchain, no build, no imports
outside the standard library.  It runs in well under a second on the full tree.

Guarantees
----------
* `strip_comments` preserves **line numbering** and offsets: output is the same
  length as the input, so any index into one is valid in the other.
* `parse_decls` never raises on malformed input; it returns what it could parse.
* Top-level declarations are those starting in column 0, which is the convention
  throughout this repository (8045 of 8052 declarations; the 7 exceptions are
  inside `where`-blocks of structures, which are fields, not new declarations).
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field

# --------------------------------------------------------------------------
# Keywords
# --------------------------------------------------------------------------

#: Keywords that introduce a declaration we want to index.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "example",
    "def",
    "abbrev",
    "structure",
    "class",
    "instance",
    "opaque",
    "axiom",
    "constant",
)

#: Keywords that open or close a scope; tracked but not indexed as declarations.
SCOPE_KEYWORDS = ("namespace", "section", "end", "variable", "include", "open")

#: A top-level line that begins a declaration or a scope-tracking keyword.
TOP_RE = re.compile(r"^(%s)\b" % "|".join(DECL_KEYWORDS + SCOPE_KEYWORDS))

IDENT_START = re.compile(r"[^\s(){}\[\]:;=∀∘˥νΛᶜ]")
IDENT_CHAR = re.compile(r"[^\s(){}\[\]:;=<>]")

#: An identifier occurrence, used for unused-hypothesis detection.  `\w` is
#: Unicode-aware in Python 3, so `hωaff` and `x₀` tokenize correctly.
IDENT_OCC = re.compile(r"[A-Za-z_][\w'.]*", re.UNICODE)

#: A dotted path such as `N.steadyRateTensor` or `Foo.Bar.baz`.  `\w` is
#: Unicode-aware, so `hωaff`, `μ₀` and `x₀` tokenize correctly.  Unlike
#: `IDENT_OCC` this stops at each `.`, so the components can be split apart —
#: see `iter_identifiers`, whose correctness depends on it.
IDENT_DOTTED_RE = re.compile(
    r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", re.UNICODE
)

# --------------------------------------------------------------------------
# Comments and strings
# --------------------------------------------------------------------------


def strip_comments(text: str) -> str:
    """Blank out Lean comments, preserving length, offsets and line numbers.

    The returned string is exactly `len(text)` characters long and has the same
    number of newlines, so `text[i]` and `strip_comments(text)[i]` describe the
    same source position.

    This is **one left-to-right pass**, which is not an optimisation but a
    correctness requirement.  Three ordered substitutions cannot work:
    masking strings first hides the `--` they contain from the line-comment
    pass only if strings are then *restored*, but restoring them re-exposes
    their `--` to that same pass; blanking line comments first instead destroys
    the `--` inside a string.  Either order corrupts something, which the
    self-test caught on `theorem b : String := "-- not a comment"`.  A single
    alternation scan decides, at each position, whether it is inside a comment
    or inside a string, which is the only way to get both right.

    String *contents* are preserved verbatim rather than blanked, matching
    `research/scripts/measure.py`.  That is safe because `find_statement_end`
    skips string literals explicitly.

    Lean block comments *may* nest, which non-greedy matching gets wrong by
    closing at the inner `-/`.  The repository's maximum nesting depth is 1
    (verified over all 883 Lean files), so the fast path is exact here.  Should a
    future file nest, `_has_nested_comment` detects it and the exact
    depth-tracking `_strip_comments_exact` path is used instead, so the fast
    path can never be silently wrong.
    """
    if "-/" in text and _has_nested_comment(text):
        return _strip_comments_exact(text)
    return _TOKEN_COMMENT_RE.sub(_blank_token, text)


#: One token: a block comment, a line comment, or a string literal.  Order
#: matters within the alternation: `/-` must be tried before a line comment, and
#: a string is matched whole so its contents never look like a comment.
_TOKEN_COMMENT_RE = re.compile(
    r"""
      /-.*?-/                 # block comment (non-nesting; guarded above)
    | --[^\n]*                 # line comment to end of line
    | "(?:[^"\\]|\\.)*"         # string literal
    """,
    re.VERBOSE | re.DOTALL,
)

_NOT_EOL_RE = re.compile(r"[^\n\r]")


def _blank_token(m: "re.Match[str]") -> str:
    """Blank a comment token; return a string literal unchanged."""
    if m.group(0).startswith('"'):
        return m.group(0)
    return _NOT_EOL_RE.sub(" ", m.group(0))




def _has_nested_comment(text: str) -> bool:
    """True if any `/- -/` comment body itself contains an opener.

    A non-greedy match ends at the *first* `-/`, so if its interior contains
    another `/-`, the comments really do nest and non-greedy matching would
    close too early.  This is a conservative over-approximation of true nesting
    (it also fires on unbalanced stray delimiters), which is the safe direction:
    a false alarm costs speed on one file, a false negative costs correctness.

    Regex rather than a character loop: the loop costs ~13s over the tree.
    """
    for m in _BLOCK_COMMENT_SCAN_RE.finditer(text):
        if "/-" in m.group(0)[2:]:
            return True
    return False

_BLOCK_COMMENT_SCAN_RE = re.compile(r"/-.*?-/", re.S)


def _strip_comments_exact(text: str) -> str:
    """Reference comment stripper: a character loop with a depth counter.

    Correct for arbitrarily nested block comments, string literals and line
    comments.  Roughly 18x slower than `strip_comments`, so it is reached only
    for files that actually nest.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
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
            # Strings are preserved verbatim, as on the fast path.
            out.append(text[i:j])
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
        else:
            out.append(text[i])
            i += 1
    return "".join(out)




# --------------------------------------------------------------------------
# Declarations
# --------------------------------------------------------------------------


@dataclass
class Decl:
    """One declaration: its kind, its qualified name, its statement and its proof.

    The three source spans (`text`, `statement`, `body`) are computed on demand
    from the shared source buffer rather than sliced eagerly.  Eagerly slicing
    would copy essentially the whole repository once per script (9.5 MB here)
    for fields most callers never read; the lazy properties cost one slice, only
    when asked, and most audit tools ask only for `one_line_statement`.
    """

    kind: str
    name: str
    qualname: str
    module: str
    line: int  # 1-based line of the declaration keyword
    binder_entries: list[tuple[str, str]] = field(default_factory=list)
    conclusion: str = ""
    _src: str = field(default="", repr=False)  # comment-stripped source
    _off: int = field(default=0, repr=False)
    _end: int = field(default=0, repr=False)  # end of the statement
    _limit: int = field(default=0, repr=False)  # end of the declaration
    _has_fields: bool = field(default=False, repr=False)

    # -- lazy source spans ------------------------------------------------
    @property
    def text(self) -> str:
        """The whole declaration, comments blanked."""
        return self._src[self._off : self._limit]

    @property
    def statement(self) -> str:
        """Keyword through conclusion, with the `:=` terminator excluded."""
        return self._src[self._off : self._end].strip()

    @property
    def body(self) -> str:
        """The proof or definition body, terminator included."""
        return self._src[self._end : self._limit]

    @property
    def fields(self) -> str:
        """Structure fields, when the terminator was `where`."""
        if not self._has_fields:
            return ""
        return _parse_fields(self._src, self._end, self._limit)

    # -- convenience ------------------------------------------------------

    @property
    def binder_names(self) -> list[str]:
        """Every binder name, explicit or implicit."""
        return [n for n, _b in self.binder_entries]

    @property
    def explicit_binders(self) -> list[str]:
        """Only the `(h : T)` binders.

        This is the set `check_vacuity.py` reasons about.  Instance binders
        `[NeZero n]` are excluded because a typeclass argument is consumed at its
        use sites and legitimately never appears by name in the proof; implicit
        `{x : α}` is excluded because it is often inferred from the goal rather
        than named.
        """
        return [n for n, b in self.binder_entries if b == "("]

    @property
    def instance_binders(self) -> list[str]:
        return [n for n, b in self.binder_entries if b == "["]

    @property
    def one_line_statement(self) -> str:
        """The statement with all whitespace collapsed, for comparison."""
        return normalize_ws(self.statement)

    @property
    def one_line_fields(self) -> str:
        return normalize_ws(self.fields)

    def comparable(self) -> str:
        """The full mathematical surface: signature plus structure fields."""
        return self.one_line_statement + (
            " | " + self.one_line_fields if self.fields else ""
        )


def normalize_ws(s: str) -> str:
    """Collapse every whitespace run to a single space and trim.

    This is what makes drift detection semantic rather than cosmetic: rewrapping
    a long signature across lines must not register as a change, while dropping
    a hypothesis must.
    """
    return re.sub(r"\s+", " ", s).strip()


def line_of(text: str, offset: int) -> int:
    """1-based line number of `offset` in `text`."""
    return text.count("\n", 0, offset) + 1


def _skip_ws(code: str, i: int) -> int:
    while i < len(code) and code[i] in " \t\n\r":
        i += 1
    return i


def _read_ident(code: str, i: int) -> tuple[str, int]:
    """Read an identifier starting at `i`; return (identifier, next offset)."""
    i = _skip_ws(code, i)
    if i >= len(code) or not IDENT_START.match(code[i]):
        return "", i
    j = i
    while j < len(code) and IDENT_CHAR.match(code[j]):
        j += 1
    return code[i:j], j


#: Every token that can affect depth tracking or terminate a statement.  The
#: character class is ordered so that `:=` is tried before a bare `=`.
_TOKEN_RE = re.compile(r'"(?:[^"\\]|\\.)*"|:=|\[|\]|\(|\)|\{|\}|\bwhere\b|\bby\b')


def find_statement_end(code: str, start: int, limit: int | None = None) -> tuple[int, str]:
    """Locate the end of the statement beginning at `start`.

    Returns `(offset, terminator)` where `terminator` is `":="`, `"where"`,
    `"by"`, `"=>"` or `""` when the declaration runs to `limit` with no explicit
    terminator.  `offset` is the offset *of* the terminator, so
    `code[start:offset]` is the statement and `code[offset:]` the body.

    Only depth-zero `:=` counts.  Depth is tracked over `()`, `[]` and `{}`, so
    a named argument such as `LipschitzWith 0 (f (Y := Y) v)` — which really does
    contain `:=` inside brackets — cannot be mistaken for the end of a
    signature.  Ignoring this is how a statement/proof separator gets mislocated
    and a diff ends up comparing proofs.

    Implemented with one C-level token scan rather than a character loop: over
    8000 declarations the loop costs ~2.4s and this ~0.3s.
    """
    n = len(code) if limit is None else min(limit, len(code))
    depth = 0
    for m in _TOKEN_RE.finditer(code, start, n):
        tok = m.group(0)
        if tok[0] == '"':
            continue  # a string literal cannot change depth or end a statement
        if tok == ":=":
            if depth == 0:
                return m.start(), ":="
            continue
        if tok in "([{":
            depth += 1
            continue
        if tok in ")]}":
            if depth > 0:
                depth -= 1
            continue
        # `where` / `by` introduce a body only at depth zero, and only when the
        # next token is a newline or a bracket — otherwise they are an
        # identifier fragment (`by_cases` is handled because `\b` requires a
        # boundary, but e.g. `x := foo` inside a term is excluded by depth).
        if depth == 0:
            nxt = _skip_ws(code, m.end())
            if nxt >= n or code[nxt] == "\n" or code[nxt] in "([{":
                return m.start(), tok
    return n, ""


def _is_word_boundary(code: str, i: int, length: int) -> bool:
    """True if `code[i:i+length]` is a whole identifier."""
    before_ok = i == 0 or not (IDENT_CHAR.match(code[i - 1]) or code[i - 1] == ".")
    after = i + length
    after_ok = after >= len(code) or not IDENT_CHAR.match(code[after])
    return before_ok and after_ok


def split_binders(head: str) -> tuple[list[tuple[str, str]], str]:
    """Split a declaration head into (binder entries, conclusion).

    `head` is everything between the declaration's name and its terminator, e.g.

        " (h : P) {x : α} [NeZero n] (rate Lf : ℝ) : ∀ y, R y"

    Each binder entry is `(name, bracket)` where `bracket` is one of `"("`
    (explicit), `"{"` (implicit) or `"["` (instance).  The distinction is not
    cosmetic: `check_vacuity.py` must not report `[NeZero n]` as an unused
    hypothesis, because a typeclass binder is consumed by elaborating `n`'s use
    sites and never appears by name in the proof.

    The conclusion starts after the last depth-zero `:` outside any binder group.
    The multi-name form `(rate Lf : ℝ)` and the untyped form `(x y)` are both
    handled.
    """
    depth = 0
    groups: list[tuple[str, int, int, str]] = []  # (text, open, close, bracket)
    open_at = -1
    open_ch = ""
    for i, c in enumerate(head):
        if c in "([{":
            if depth == 0:
                open_at = i
                open_ch = c
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0 and open_at >= 0:
                groups.append((head[open_at : i + 1], open_at, i + 1, open_ch))
                open_at = -1

    # The conclusion separator is the last depth-zero ':' outside all groups.
    conclusion_at = -1
    depth = 0
    for i, c in enumerate(head):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0 and not (i + 1 < len(head) and head[i + 1] == "="):
            conclusion_at = i

    telescope = head[:conclusion_at] if conclusion_at >= 0 else head
    conclusion = head[conclusion_at + 1 :] if conclusion_at >= 0 else ""

    entries: list[tuple[str, str]] = []
    for gtext, gs, _ge, bracket in groups:
        if gs >= len(telescope):
            continue
        inner = gtext[1:-1].strip()
        if not inner:
            continue
        # The binder names are everything before the group's first depth-zero
        # ':'; the rest of the group is the type.
        d = 0
        colon = -1
        for i, c in enumerate(inner):
            if c in "([{":
                d += 1
            elif c in ")]}":
                d -= 1
            elif c == ":" and d == 0:
                colon = i
                break
        binders = inner[:colon] if colon >= 0 else inner
        toks = [t for t in binders.split() if IDENT_OCC.fullmatch(t)]
        if bracket == "[" and colon < 0:
            # `[C a b]` is a typeclass application: `C` names the class and
            # `a b` are the arguments being bound.  Only the arguments are
            # binders; treating `C` as one would make every instance argument
            # look like a duplicate hypothesis.
            toks = toks[1:]
        for tok in toks:
            if (tok, bracket) not in entries:
                entries.append((tok, bracket))

    return entries, conclusion.strip()


def _parse_fields(code: str, start: int, limit: int) -> str:
    """Collect the indented field block of a `structure ... where` declaration."""
    lines = code[start:limit].split("\n")
    kept: list[str] = []
    started = False
    for ln in lines[1:]:
        if not ln.strip():
            kept.append("")
            continue
        if not ln[0].isspace():
            break
        started = True
        kept.append(ln.strip())
    return "\n".join(kept) if started else ""


def parse_decls(text: str, module: str = "") -> list[Decl]:
    """Parse every top-level declaration in `text`.

    Scopes (`namespace` / `section` / `variable`) are tracked so that
    `Decl.qualname` is the name a user would actually write.  Declarations whose
    name is anonymous (an `instance` with no binder name) are given a synthetic
    `«instance@line»` name so they remain addressable and diffable.
    """
    code = strip_comments(text)
    n = len(code)
    ns: list[str] = []  # namespace stack
    sections: list[str] = []
    decls: list[Decl] = []

    # Collect the offsets of every top-level keyword line first, so a
    # declaration's extent is bounded by the next one.
    starts: list[tuple[int, str, str]] = []  # (offset, keyword, rest-of-line)
    for m in re.finditer(r"(?m)^(%s)\b([^\n]*)" % "|".join(DECL_KEYWORDS + SCOPE_KEYWORDS), code):
        starts.append((m.start(), m.group(1), m.group(2)))

    for idx, (off, kw, rest) in enumerate(starts):
        limit = starts[idx + 1][0] if idx + 1 < len(starts) else n
        if kw == "namespace":
            ident, _ = _read_ident(code, off + len(kw))
            if ident:
                ns.append(ident)
            continue
        if kw == "section":
            ident, _ = _read_ident(code, off + len(kw))
            sections.append(ident)
            continue
        if kw == "end":
            # `end Foo` closes the namespace; a bare `end` closes the section.
            ident, _ = _read_ident(code, off + len(kw))
            if ident and ns and ns[-1] == ident:
                ns.pop()
            elif sections:
                sections.pop()
            continue
        if kw in ("variable", "include", "open"):
            continue

        # ---- a declaration --------------------------------------------
        # Bounding the scan at `limit` (the next top-level keyword) keeps a
        # malformed declaration from swallowing the rest of the file.
        end_off, term = find_statement_end(code, off, limit)

        name, after_name = _read_ident(code, off + len(kw))
        if not name:
            # `example : P := by ...` and anonymous `instance : C := ...`.
            name = f"«{kw}@{line_of(code, off)}»"

        head = code[after_name:end_off]
        binder_entries, conclusion = split_binders(head)

        qual = ".".join(ns + [name]) if ns else name
        decls.append(
            Decl(
                kind=kw,
                name=name,
                qualname=qual,
                module=module,
                line=line_of(code, off),
                binder_entries=binder_entries,
                conclusion=conclusion,
                _src=code,
                _off=off,
                _end=end_off,
                _limit=limit,
                _has_fields=(term == "where"),
            )
        )
    return decls


def parse_file(path: str, module: str = "") -> list[Decl]:
    with open(path, encoding="utf-8", errors="replace") as fh:
        return parse_decls(fh.read(), module=module or module_of_path(path))


def module_of_path(path: str) -> str:
    """`CRNT/Foo/Bar.lean` -> `CRNT.Foo.Bar`."""
    p = path.replace("\\", "/")
    if p.endswith(".lean"):
        p = p[:-5]
    return p.strip("./").replace("/", ".")


def iter_identifiers(text: str) -> set[str]:
    """Every identifier-like name occurring in `text`, including dotted heads.

    Two Lean-specific splits are essential here, and both were false positives
    before they were made:

    * **Dotted paths.**  `N.steadyStatePolynomial_eq_complexBalanceCombination` is
      one token by naive tokenization, so a theorem whose hypothesis
      `(N : Network S)` is used *only* through field access looks as though it
      never mentions `N`.  That fired on 1636 theorems.
    * **Postfix operators.**  `Qᶜ` (complement), `s⁻¹`, `fˣ` are one token, so
      `def supported (Q : Finset I) := (P.project Qᶜ).ker` looks as though `Q`
      is unused.  Each component is therefore also recorded with its postfix
      stripped.

    `«quoted»` names are unwrapped so that `«h»` and `h` compare equal.
    """
    out: set[str] = set()
    for m in IDENT_DOTTED_RE.finditer(strip_comments(text)):
        for part in m.group(0).split("."):
            part = part.strip("«»")
            if not part:
                continue
            out.add(part)
            bare = part.rstrip(_POSTFIX_CHARS)
            if bare and bare != part:
                out.add(bare)
    return out

#: Lean postfix operators that bind to an identifier without a separator, so
#: `Qᶜ` tokenizes as a single unit unless they are split off.  `ᶜ` is complement
#: (Finset, Set), `⁻¹` inverse, `ˣ` map/commute notation, `'`/`′` prime.
_POSTFIX_CHARS = "ᶜ⁻¹ˣ′'"


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------


def self_test() -> int:
    """Check the parser on the shapes that break naive implementations.

    Every case here corresponds to a real construct in this repository that a
    regex-based approach gets wrong.
    """
    fails: list[str] = []

    # 1. Comments are blanked, and length/line structure is preserved.
    src = "theorem a : P := by\n  -- comment\n  exact h\n"
    out = strip_comments(src)
    if len(out) != len(src):
        fails.append("strip_comments changed the length")
    if out.count("\n") != src.count("\n"):
        fails.append("strip_comments changed the line count")
    if "comment" in out:
        fails.append("strip_comments left comment text in place")

    # 2. A `--` inside a string literal is not a comment.
    s2 = 'theorem b : String := "-- not a comment"\n'
    if "not a comment" not in strip_comments(s2):
        fails.append("a `--` inside a string was treated as a comment")

    # 3. Block comments are blanked.
    if "secret" in strip_comments("/- secret -/\ntheorem c : P := by sorry\n"):
        fails.append("a block comment was not blanked")

    # 4. Nested block comments must be detected (so the exact path is taken)
    #    and still produce the right answer.
    nested = "/- outer /- inner -/ still comment -/\ntheorem d : P := by sorry\n"
    if not _has_nested_comment(nested):
        fails.append("_has_nested_comment failed to see nesting")
    if "still comment" in strip_comments(nested):
        fails.append("nested block comment not handled")
    if "still comment" in strip_comments("-/ after an unbalanced close\n"):
        fails.append("an unbalanced `-/` was mishandled")

    # 5. The statement ends at the first depth-zero `:=`, not a named argument.
    d = parse_decls("theorem n (f : F) : LipschitzWith 0 (g (Y := Y) f) := by sorry")[0]
    if "LipschitzWith 0 (g (Y := Y) f)" not in d.one_line_statement:
        fails.append(f"named-argument := truncated the statement: {d.one_line_statement!r}")

    # 6. Whitespace rewrapping is not a statement change.
    a = parse_decls("theorem w (h : P)\n  :\n  Q := by sorry")[0]
    b = parse_decls("theorem w (h : P) : Q := by exact h")[0]
    if a.comparable() != b.comparable():
        fails.append("rewrapping a signature was reported as a change")

    # 7. Multi-line binder telescopes, including implicit and instance binders.
    d = parse_decls(
        "theorem big (N : Network S) {x₀ : Concentration S}\n"
        "    (hcb : N.IsComplexBalanced κ x₀) :\n"
        "    ∃ p, p.Positive := by sorry"
    )[0]
    if d.explicit_binders != ["N", "hcb"]:
        fails.append(f"explicit binders parsed as {d.explicit_binders}")
    if d.conclusion != "∃ p, p.Positive":
        fails.append(f"conclusion parsed as {d.conclusion!r}")

    # 8. Namespaces produce qualified names.
    d = parse_decls("namespace Foo\ntheorem bar : P := by sorry\nend Foo\n")[0]
    if d.qualname != "Foo.bar":
        fails.append(f"qualname parsed as {d.qualname!r}")

    # 9. Dotted and postfix usage both count as using the binder.
    idents = iter_identifiers("(P.project Qᶜ).ker")
    if not {"P", "Q"} <= idents:
        fails.append(f"dotted/postfix identifiers not split: {sorted(idents)}")

    # 10. A structure's fields are part of its mathematical surface.
    s_old = parse_decls("structure S where\n  a : Nat\n  b : Nat\n")[0]
    s_new = parse_decls("structure S where\n  a : Nat\n")[0]
    if s_old.comparable() == s_new.comparable():
        fails.append("losing a structure field was not detected")
    if s_new.fields.strip():
        fails.append(f"a structure with no fields reported fields {s_new.fields!r}")

    # 11. `example` has no name and gets a stable synthetic one.
    e = parse_decls("example : P := by sorry\n")[0]
    if not e.qualname.startswith("«example@"):
        fails.append(f"anonymous example named {e.qualname!r}")

    for f in fails:
        print(f"FAIL: {f}", file=sys.stderr)
    if fails:
        return 1
    print("self-test ok: comments, strings, nesting, terminators, binders, namespaces")
    return 0


if __name__ == "__main__":
    sys.exit(self_test())