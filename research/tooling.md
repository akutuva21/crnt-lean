# Audit tooling (`scripts/`)

Tooling that finds the ways a formalization can be *wrong without failing to
compile*. Everything here is Python 3 standard library only, needs no Lean
toolchain, and runs in seconds.

Read this before adding a script: the existing gates already cover a lot, and
extending one of them is almost always better than adding a sixth.

| script | what it catches | runtime | gates? |
|---|---|---|---|
| [`check_stubs.py`](check_stubs.py) | hollow definitions: `:= True`, `dummy : True`, `isTrue` | <1s | yes (existing) |
| [`check_imports.py`](check_imports.py) | imports of modules that do not exist | <1s | yes (existing) |
| [`check_undefined_names.py`](check_undefined_names.py) | identifiers used but never declared | <1s | yes (existing) |
| [`check_exclusions.py`](check_exclusions.py) | ledger drift; lakefile not generated | <1s | yes (existing) |
| [`leanparse.py`](leanparse.py) | *shared parser*: statements vs. proofs | 2.6s | — (library) |
| [`check_vacuity.py`](check_vacuity.py) | unused hypotheses, `True` conclusions, closing proofs | 3.0s | **yes** (new) |
| [`check_statement_drift.py`](check_statement_drift.py) | **a theorem's statement changed between two refs** | 3.3s | advisory (new) |
| [`axiom_scan.py`](axiom_scan.py) | `sorryAx` reachable via imports; axiom-set pins | 1.0s | — (new) |
| [`measure_diff.py`](measure_diff.py) | objective delta between two refs | ~7s | — (new) |
| [`run_selftests.py`](run_selftests.py) | runs every `--self-test` above | 0.3s | **yes** (new) |

Run everything:

```sh
python3 scripts/run_selftests.py          # 5/5 self-tests, ~0.3s
```

---

## `leanparse.py` — the shared parser

Everything else needs to tell a **statement** from a **proof**, and a regex
cannot:

```lean
theorem foo (h : P) : Q := by exact h
```

The only thing separating conclusion from proof is the first `:=` *at bracket
depth zero*. Getting depth wrong is exactly how a diff ends up comparing proofs
instead of statements — the bug `check_statement_drift.py` exists to catch — so
the parser cannot have it.

Verified properties (all machine-checked, see `--self-test`):

- Over **all 882 Lean files** in the repo, **0** declarations are mis-terminated
  (a statement never contains a depth-zero `:=`).
- `strip_comments` is **byte-identical** to `research/scripts/measure.py`'s
  reference implementation on all 882 files, while running ~20x faster.
- A named argument inside a binder type — `LipschitzWith 0 (g (Y := Y) f)` —
  does not truncate the statement. This is a real occurrence in the tree.
- Block comments may nest in Lean; the repository's maximum depth is 1, so a
  fast non-greedy path is exact here, and `_has_nested_comment` routes any file
  that *does* nest to an exact depth-tracking path. The fast path can never be
  silently wrong.

### Two tokenization bugs worth knowing about

Both were found by running the tool on the real tree, and both were producing
**thousands of false positives**:

- `N.steadyStatePolynomial_eq_complexBalanceCombination` tokenizes as *one*
  identifier, so a theorem using `(N : Network S)` only through field access
  looks like it never mentions `N`. → 1636 false positives.
- `Qᶜ` (complement), `s⁻¹`, `fˣ` are postfix operators, so `Q` looks unused in
  `def supported (Q : Finset I) := (P.project Qᶜ).ker`.

---

## `check_vacuity.py` — is the theorem vacuous?

A theorem whose hypothesis is never used still compiles. So does one whose
conclusion is `True`, or whose proof is one closing tactic. This generalizes
`check_stubs.py` beyond the specific shapes it already lists.

```sh
python3 scripts/check_vacuity.py --report          # ranked findings
python3 scripts/check_vacuity.py                   # gate (CI)
python3 scripts/check_vacuity.py --lint-log build.log
```

Three signals, ranked by risk:

1. **unused hypothesis** — an explicit `(h : T)` binder absent from the proof.
   `WEAK` normally, `VACUOUS` if the conclusion is also trivial.
2. **trivial conclusion** — `True`, `1 = 1`. Satisfied by *any* hypothesis.
3. **closing proof** — the body is just `trivial` / `decide` / `simp` / `norm_num`.

### What it deliberately does *not* claim

This is a heuristic, and an unsound one in the direction of false accusations, so
two guards are built in:

- **Instance binders `[NeZero n]` are excluded.** A typeclass argument is
  consumed at its use sites and legitimately never appears by name.
- **Searching tactics downgrade the finding to `INDETERMINATE`.** `aesop`,
  `simp_all`, `linarith`, `omega`, `rfl` and friends can consume a hypothesis
  without naming it. A body containing one is *never* reported as confident
  vacuity — the self-test asserts this explicitly, because
  `theorem coordinatePrimeContains_target_iff (N) (P) (r) : ... := Iff.rfl` is
  good mathematics whose three binders never appear by name.

Lean's own `unused variable` linter is authoritative when a build log is
available; pass it with `--lint-log` to fold those in.

**Gating.** Shrink-only baseline (`scripts/vacuity_baseline.txt`, currently 1576
entries), exactly like `check_stubs.py`. It fails only on *new* findings — the
direction that matters — and reports baseline entries that disappeared.

---

## `check_statement_drift.py` — did a theorem's *statement* change?

This is the tool that would have caught the silent-hypothesis-weakening failure
mode. A proof-editing pass can quietly make a theorem **weaker** — drop a
hypothesis, weaken a conclusion — and the new version still compiles and still
discharges its goal, so nothing downstream breaks and nothing looks wrong.
`git diff` cannot see this, because the diff is full of legitimate proof churn.

```sh
python3 scripts/check_statement_drift.py --base holes --head HEAD
python3 scripts/check_statement_drift.py --base holes --head HEAD --fail
python3 scripts/check_statement_drift.py --base holes --head HEAD --json
```

Every difference is classified by *direction*:

| kind | meaning |
|---|---|
| `WEAKENED` | a hypothesis was removed — the statement now admits strictly more arguments |
| `STRENGTHENED` | a hypothesis was added |
| `CHANGED` | conclusion or binder types differ |
| `ADDED` / `REMOVED` | declaration is new / gone |
| `ADDED_MODULE` / `REMOVED_MODULE` | whole file added / deleted |

**Whitespace rewrapping is not drift** — statements are normalised before
comparison, so reformatting a long signature is silent while dropping a
hypothesis is not. Structure fields count as part of a declaration's
mathematical surface, so silently dropping a field is caught.

**It does not guess.** Deciding whether `h : P ∧ Q` is weaker than `h : P` needs
type comparison, which is undecidable from text. The tool prints the evidence —
the hypothesis set-difference plus a word-level diff of both signatures — and
leaves the judgment to the reader. A tool that guesses wrong about the direction
of weakening would be worse than one that shows both.

**Module churn is collapsed.** Deleting a file is normal but its 30 declarations
would otherwise bury a real signature edit; they are reported as one line.

Verified end-to-end on real refs in this repo. On `holes` → `gac-deep` (7 files
changed) it reports 22 genuine removals and collapses 59 others into 3 module
deletions, in 3.3s.

**In CI** this runs *advisory* (never blocking) against the merge base, because
the direction of weakening is not decidable from text. Reviewers should read it.

---

## `axiom_scan.py` — `sorryAx` reachability

`test/AxiomAudit.lean` pins a hand-written list of headline results with
`#print axioms` + `#guard_msgs`. That list is valuable but static: it covers
only the declarations somebody remembered to add, and it says nothing about
what a *new file* pulls in.

```sh
python3 scripts/axiom_scan.py --closure CRNT.Dynamics.GlobalAttractorTheorem
python3 scripts/axiom_scan.py --generate --out test/AxiomScan.lean
python3 scripts/axiom_scan.py --check   --out test/AxiomScan.lean
python3 scripts/axiom_scan.py --lean     # actually run Lean (slow)
```

**`--closure` is the valuable half.** It walks the transitive `import` closure of
a module and reports every executable `sorry` inside it. This is the question
that actually bites: a theorem that transitively imports a module containing a
`sorry` still *compiles*, still runs, and is silently unsound.

On `holes` today:

```
$ python3 scripts/axiom_scan.py --closure CRNT.Dynamics.GlobalAttractorTheorem
import closure of CRNT.Dynamics.GlobalAttractorTheorem: 189 module(s) on disk
  1 executable `sorry` reachable:
    CRNT.Dynamics.HighCodimensionSiphonFace:135  in
      CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace
```

1.0s, no Lean. This is the check Hole B's port must satisfy: a new module that
imports `TrueChemistrySRCriterion` drags `sorryAx` into its own footprint even
though the file itself is hole-free. **A clean file is not a clean closure.**

`scripts/axiom_targets.txt` holds the 132 declarations already pinned by
`AxiomAudit.lean`; `--generate` emits a Lean module pinning any list in that
form, and `--check` fails if the emitted file is stale.

> The generated module is **not** committed here, because it cannot be
> elaborated without a build and an unverified `.lean` file would be a liability.
> Regenerate it, build it, then commit.

---

## `measure_diff.py` — score a change, not a tree

`research/scripts/measure.py` is the swarm's frozen objective and answers "how
big is this tree", which is the wrong question when reviewing a *change*. This
compares two refs on `holes`, `frontier_mods`, `scaffold_mods`, `lean_lines`,
`declared_axioms` and `score`, and adds what `measure.py` does not track: **which
specific `sorry` appeared or disappeared**.

```sh
python3 scripts/measure_diff.py --base holes --head HEAD
python3 scripts/measure_diff.py --base holes --head HEAD --json
```

A ref is materialised with `git archive` (only `CRNT/`, `Scaffold/`, `scripts/`,
`research/` — extracting the whole tree costs ~6s more). **The current
`measure.py` always scores both sides**, even when a ref predates the script:
the objective is frozen, so both sides must use the same yardstick.

Exits non-zero if a branch **opens** a `sorry` or declares an axiom, regardless
of the scalar score.

---

## Adding a script

Every audit script follows the same shape, so `run_selftests.py` picks it up
for free:

1. `--self-test` exercises the decision logic on **synthetic** inputs — no git
   history, no dependence on repository contents, so it cannot be broken by a
   merge.
2. Baselines are keyed on `(kind, module, name, detail)`, **never** line numbers
   or declaration text, which churn on every edit.
3. Default mode gates; `--report` prints and exits 0.
4. Comment the *why*, especially every place the tool is deliberately imprecise.
   A silent heuristic is worse than no heuristic, because it gets trusted.

Add the new script to `TOOLS` in `run_selftests.py` and to the table above.