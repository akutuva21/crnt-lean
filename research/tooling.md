## Ledger semantics — the trap worth writing down

`scripts/unverified_modules.txt` is **not** a registry of interesting modules, of frontier
candidates, or of things you want built. It is a list of modules **Lean has never
successfully elaborated**, and it becomes `excludeGlobs` of the `CRNT` library.

So listing a hole-free module there *removes it from `lake build CRNT`*, and it stops being
elaborated by `CRNTFrontier` too. Nothing fails loudly: you have taken a working module out
of every build target in the tree and the build is still green.

What happens for free, with no ledger edit and no generator run:

* A new file under `CRNT/` is picked up automatically. The verified library's globs are
  `["CRNT", "CRNT.+"]` — pattern-based, not enumerated — so a new module is in
  `lake build CRNT` the moment it exists.
* Not appearing in `CRNTFrontier.lean` is **not** lost coverage. That target is the set of
  modules that have ever failed to elaborate; it is a diagnostic, not a build.
* To reach the verified **umbrella**, add an `import` line to `CRNT.lean`. That is an
  import, not a ledger line.
* `scripts/gen_lakefile.py --add M` is correct in exactly one case: you added a module and
  `lake build` genuinely cannot elaborate it yet (a stub, or it depends on an unproved hole).
  It refuses to write if the entry would transitively hide anything.

### The corollary that matters more

**The ledger cannot detect holes.** A hole-bearing module still *elaborates* — it elaborates
*with* `sorryAx`. Both holes are off-ledger by construction, and have been all along.

Three consequences, all of which the tooling is built around:

1. **`lake build` green is not evidence of anything on this tree.** Every module elaborates;
   two of them carry `sorryAx`.
2. **Frontier membership is not evidence about elaboration either**, in either direction.
   "It's on the frontier, so it doesn't build" and "it's on the frontier, so it carries a
   sorry" are both invalid inferences. The frontier is "modules the `CRNTFrontier` target has
   ever covered".
3. **The real signals are `scripts/dump_sorries.py` and the transitive `#print axioms`
   check.** `#print axioms` reports the whole axiom closure of a declaration, not just its
   own proof, so it is also the strong version of the hole check: it catches a module that is
   clean in isolation but imports something unverified. That is exactly the trap
   `CRNT.Multistationarity.TrueChemistrySRCriterion` sets for any file that must not import
   it (ledger entry B-11).

`close_hole.sh` treats `dump_sorries.py` as the primary signal and the ledger step as the
follow-up, for this reason.

---
