import CRNT.Graph.WeakReversibility

/-!
# Certificate checking

A core purpose of `crnt-lean` is to *check* structural claims emitted by external
tools rather than recompute them. This module realizes the path-certificate pattern
for directed reachability: an external tool emits, for a reachability claim `c ⇝ d`,
an explicit walk (a list of complexes), and Lean verifies it with a computable
`Bool` check whose `true` value soundly implies `Reaches`.

Because `DirectlyReacts` is decidable, `reachesWalk` reduces by `decide` on concrete
networks, so generated certificates close their goals automatically.

This module is **stable**. Depends on: `CRNT.Graph.WeakReversibility`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Checks that the complexes in `l`, starting from `c`, form a directed walk in the
reaction graph: each consecutive pair is connected by a reaction. The endpoint of the
walk is the last element of `l` (or `c` itself when `l` is empty). -/
def reachesWalk (N : Network S) (c : Complex S) : List (Complex S) → Bool
  | [] => true
  | d :: rest => decide (N.DirectlyReacts c d) && N.reachesWalk d rest

/-- Soundness of the walk checker: a verified directed walk from `c` through `l`
witnesses that the walk's endpoint is reachable from `c`. -/
theorem reaches_getLastD_of_reachesWalk (N : Network S) :
    ∀ (c : Complex S) (l : List (Complex S)), N.reachesWalk c l = true →
      N.Reaches c (l.getLastD c)
  | c, [], _ => by simpa using Reaches.refl N c
  | c, d :: rest, h => by
    rw [reachesWalk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcd, hrest⟩ := h
    have ih := N.reaches_getLastD_of_reachesWalk d rest hrest
    rw [List.getLastD_cons]
    exact (Reaches.single hcd).trans ih

/-- A directed walk from `c` to an explicitly named endpoint `d` certifies
`Reaches c d`. This is the form a generated certificate uses: supply the intermediate
walk `l` ending at `d`, discharge the `Bool` check by `decide`, and obtain reachability. -/
theorem reaches_of_walk (N : Network S) (c d : Complex S) (l : List (Complex S))
    (hend : l.getLastD c = d) (h : N.reachesWalk c l = true) : N.Reaches c d :=
  hend ▸ N.reaches_getLastD_of_reachesWalk c l h

end Network

end CRNT
