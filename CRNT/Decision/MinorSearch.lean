import CRNT.Basic.Network
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.List.Sublists

/-!
# Searching for a nonsingular stoichiometric minor

The computable engine behind the argument-free `crnt_deficiency_zero`: given explicit element lists
for the reaction and species types, find a `k × k` stoichiometric minor with nonzero rational
determinant. `findMinorWitness` returns the chosen positions as index lists into the supplied
element lists, so the search and the proof term it feeds agree on element order by construction.

Determinants here run under compiled evaluation, which has no trouble with the permutation sum that
kernel `decide` cannot reduce; the witness it finds is then discharged on the kernel path by the
tactic. Entries use `List.get?` (no `Inhabited` on the carrier), defaulting out-of-range positions to
`0`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Basic.Network`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The `(i, j)` entry of the stoichiometric minor selected by reaction list `rs` and species list
`ss`: the reaction-vector coefficient `target − source` of reaction `rs[j]` at species `ss[i]`,
or `0` if either index is out of range. -/
def minorEntry (N : Network S) (rs : List N.R) (ss : List S) (i j : ℕ) : ℚ :=
  match rs[j]?, ss[i]? with
  | some r, some s => ((N.reaction r).target s : ℚ) - ((N.reaction r).source s : ℚ)
  | _, _ => 0

/-- The determinant of the `k × k` stoichiometric minor selected by `rs` (reactions, columns) and
`ss` (species, rows). -/
def minorDet (N : Network S) (rs : List N.R) (ss : List S) (k : ℕ) : ℚ :=
  (Matrix.of fun i j : Fin k => N.minorEntry rs ss i.val j.val).det

/-- **Search for a nonsingular `k × k` minor.** Over `k`-subsets of the reaction list `rs` and the
species list `ss`, return the first pair whose minor determinant is nonzero, as index lists into `rs`
and `ss`. Returns `none` if no such minor exists. -/
def findMinorWitness (N : Network S) (rs : List N.R) (ss : List S) (k : ℕ) :
    Option (List ℕ × List ℕ) := Id.run do
  let rIdx := (List.range rs.length).sublistsLen k
  let sIdx := (List.range ss.length).sublistsLen k
  for ri in rIdx do
    let rsub := ri.filterMap (fun t => rs[t]?)
    for si in sIdx do
      let ssub := si.filterMap (fun t => ss[t]?)
      if N.minorDet rsub ssub k ≠ 0 then
        return some (ri, si)
  return none

end Network

end CRNT
