#!/usr/bin/env python3
"""offcycle_negflux_search.py — counterexample search for Hole B's residual proposition.

TARGET
------
`CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean:202`

    def no_offCycle_negFlux (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) : Prop :=
      ∀ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ →
        0 ≤ N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b)

Its negation is exactly the datum `research/routes/HoleB-Residue-Reduction.md` names as the
missing input for the `sorry` at `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:9435`:

    ∃ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ ∧
      trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0

HYPOTHESIS SET UNDER TEST
-------------------------
Exactly the context that is in scope at the residue (read off
`TrueChemistrySRCriterion.lean:8715-8758` and `StrongConcordance.lean:26-61`):

  hsep   : N.ReactantProductSeparated
  hflow  : N.ZeroComplexReactionsAreFlows
  hSR    : N.TrueSRStrongCriterion                (see the CAVEAT below)
  W      : N.fullyOpen.StrongConcordanceWitness α σ   -- how α and σ are obtained at the
  C      : N.TrueSRCycle n ;  hCeven : C.Even        residue (`by_contra hnot;
  hcausal: ∀ i, 0 < flux α (C.reaction i) (C.species (i+1 mod n)) * σ (C.species (i+1 mod n))
                                                      obtain ⟨α, σ, W⟩ := hnot`)
  (optionally hopp : ∀ k, flux α (C.reaction k) (C.species k) * σ (C.species k) < 0)

CAVEAT ABOUT `TrueSRStrongCriterion`'s SECOND CONJUNCT  (a finding, not a modelling choice)
--------------------------------------------------------------------------------------------
`TrueChemistrySRGraph.lean:271-274`

    def TrueSRStrongCriterion (N : Network S) : Prop :=
      (∀ {n : ℕ} (C : N.TrueSRCycle n), C.Even → C.SCycle) ∧
      (∀ {m n : ℕ} (C : N.TrueSRCycle m) (D : N.TrueSRCycle n),
        C.Even → D.Even → ¬ Nonempty (C.SToRIntersection D))

The second conjunct quantifies over *all* pairs, including `C = D`, which invites the suspicion
that `hSR` is unsatisfiable (a cycle obviously shares an S-to-R path with itself).  That
suspicion is WRONG, and the self-test is what caught it: `Nonempty (C.SToRIntersection C)` is
IMPOSSIBLE for every SR cycle `C`, so the `C = D` instances hold vacuously and the literal and
`C ≠ D` readings of the conjunct coincide.  Counting argument: `covers_common` + `edge_simple` +
`components_separated` force the listed components to be a vertex-disjoint path decomposition of
the whole common-edge graph, which for `C = D` is `C`'s own `2n`-edge cycle, so `Σ_c L_c = 2n`
with every `L_c` odd (a component starts at a species vertex and ends at a reaction vertex,
alternating).  Each component then holds `(L_c+1)/2` species vertices, so the decomposition uses
`Σ_c (L_c+1)/2 = n + k/2 > n` distinct species vertices, while `C` has exactly `n`.  Contradiction.

The conjunct therefore has real content (it bites on genuinely distinct even cycles that share
an S-to-R path -- see the `B -> C`, `A -> C`, `A + B -> C` witness in
`TrueSRCPairThirdEdge.lean:228-236`).  This script evaluates it on the LITERAL reading, all pairs
included (`check_hSR(..., literal_hsr2=True)`, the default); `--distinct-hsr2` restricts to
`C ≠ D`.  The self-test reports how many cycles were found with `Nonempty (C.SToRIntersection C)`
computed `True` (expected: none -- any nonzero count would refute the counting argument above).

CERTIFICATION DISCIPLINE (mirrors `research/scripts/holeA_refute_search.py`)
---------------------------------------------------------------------------
No conclusion is ever drawn from a floating-point residual.

  * `σ` is drawn from `{−1,0,+1}^S \ {0}`.  This is COMPLETE for the propositions tested, because
    `Promotes`/`Opposes`/`hcausal`/`hopp` and the target inequality only ever read
    `SignType.sign (σ s)` and `σ s = 0`.  So no float ever enters `σ`.
  * `α` is *proposed* by a float LP inside the exact rational kernel of the `InKerL` matrix
    (`trueInternalClassFlux` and every witness clause are linear in `α`), then **snapped to
    `fractions.Fraction` in the kernel coordinates** and **every hypothesis plus the target
    inequality is re-verified exactly with `Fraction` arithmetic**.  A candidate is accepted only
    if that exact re-verification passes; a float residual of any size is irrelevant.
  * `fractions.Fraction` is used for the stoichiometry, the c-pair parity, the s-cycle products,
    `InKerL`, the flux sums and all sign tests.  There is no floating-point comparison anywhere
    in a predicate.
  * What is NOT certified: an LP stage that reports "infeasible" is *not* a proof of
    infeasibility (floating-point LP has no infeasibility certificate here).  Negative results are
    therefore reported as "no counterexample found in range R", never as "no counterexample
    exists".  For the smallest cases a genuinely exhaustive **exact integer** search over a
    finite box of `α` is run as well, which *is* complete within that box.

Usage
-----
    python3 offcycle_negflux_search.py            # all phases
    python3 offcycle_negflux_search.py selftest
    python3 offcycle_negflux_search.py 1          # exhaustive phase
    python3 offcycle_negflux_search.py 2 20261010 4096   # random phase, seed, iters
"""

import itertools
import random
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

ZERO = Fraction(0)


# --------------------------------------------------------------------------
# Exact rational linear algebra
# --------------------------------------------------------------------------

def rref_nullspace(A):
    """Exact rational nullspace basis of an integer matrix A (list of rows).

    Returns a list of integer columns B (len = nullity), so `A @ B == 0` exactly.
    """
    M = [[Fraction(x) for x in row] for row in A]
    rows, cols = len(M), (len(M[0]) if M else 0)
    piv = []
    r = 0
    for c in range(cols):
        pivrow = None
        for i in range(r, rows):
            if M[i][c] != 0:
                pivrow = i
                break
        if pivrow is None:
            continue
        M[r], M[pivrow] = M[pivrow], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == rows:
            break
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * cols
        v[f] = Fraction(1)
        for i, pc in enumerate(piv):
            v[pc] = -M[i][f]
        basis.append(v)
    # scale each basis vector to integers
    out = []
    for v in basis:
        den = 1
        for x in v:
            den = den * x.denominator // _gcd(den, x.denominator)
        out.append([int(x * den) for x in v])
    return out


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


def matvec(B, y):
    """alpha = B . y with Fractions, exactly."""
    m = len(B[0]) if B else 0
    out = [ZERO] * m
    for col, yj in zip(B, y):
        if yj == 0:
            continue
        for i in range(m):
            if col[i]:
                out[i] += col[i] * yj
    return out


# --------------------------------------------------------------------------
# Encoding of the Lean structures
# --------------------------------------------------------------------------
#
# S           finite species, modelled as {0, ..., ns-1}      (S = Fin ns)
# Complex S   S → ℕ, modelled as a tuple of ns natural numbers
#             Complex.zero = all zeros; singletonComplex s = 1 at s
# N.R         finite channels, modelled as a list `recs` of (source, target) complexes
#             (N.reaction r) = (recs[r].source, recs[r].target)
# reactionVector r s = target(s) - source(s)                  [CRNT/Stoich/Vector.lean:23]
# IsFlowChannel r = source = 0 or target = 0                  [TrueChemistrySRGraph.lean:71]
# nonflowOriginalChannels = { r : ¬ IsFlowChannel r }        [TrueChemistrySRCriterion.lean:1590]
# SameTrueReaction r q  <=> {source, target} equal as unordered pairs  [TrueChemistrySRGraph.lean:31]
# TrueReaction = Quotient of N.R by SameTrueReaction          [TrueChemistrySRGraph.lean:57-67]
#               modelled as the canonical sorted pair (min(src,tgt), max(src,tgt))
# TrueSREdge e = (species, reaction-class, endpoint, representative)   [TrueChemistrySRGraph.lean:108]
#               with endpoint = source(rep) or target(rep) and endpoint[species] ≠ 0,
#               and the class internal (has a non-flow representative).
#               ONLY (species, class, endpoint) is retained: the `representative` field enters
#               no predicate tested here (`coeff = endpoint[species]`, `SameIncidence`, `isCPair`
#               all read only those three).  `netCoeff` does read the representative, but under
#               `hsep` `TrueSRCycle.sCycleNet_iff_sCycle_of_separated` derives it from `SCycle`,
#               which is what we use.
# TrueSRCycle C  [TrueChemistrySRGraph.lean:137]
#               species : Fin n → S injective; reaction : Fin n → TrueReaction injective;
#               leftEdge i  at (species i,  reaction i,  endpointL i)
#               rightEdge i at (species i+1, reaction i, endpointR i)
#               endpointL i / endpointR i ∈ {complexes of reaction i}, with the coefficient at the
#               edge's species nonzero.
# isCPair i = endpointL i == endpointR i                     [TrueChemistrySRGraph.lean:153]
# numCPairs / Even = that number is even                     [TrueChemistrySRGraph.lean:158-165]
# SCycle = ∏ coeff(leftEdge i) = ∏ coeff(rightEdge i)        [TrueChemistrySRGraph.lean:169]
# TrueSRCycle.HasReaction ρ = ∃ t, C.reaction t = ρ          [TrueSRMinimalChord.lean:21]
# trueInternalClassFlux α ρ s
#               = Σ_{r non-flow, trueReaction r = ρ} α (inl r) * reactionVector r s
#                                                             [TrueChemistrySRCriterion.lean:4423]
# TrueInternalAggregateCausalEdge (inl s) (inr ρ)  <->  flux ρ s * σ s < 0
#                                                             [TrueChemistrySRCriterion.lean:4693]
#   -- i.e. the target inequality IS the causal-edge condition, so `no_offCycle_negFlux` says
#      "no causal edge leaves a cycle species towards an off-cycle class".
# fullyOpen    R := N.R ⊕ S ⊕ S                              [CRNT/Open/Augmentation.lean:49]
#              reaction (inl r) = reaction r
#              reaction (inr (inl s)) = inflowReaction s  = (0, e_s)
#              reaction (inr (inr s)) = outflowReaction s = (e_s, 0)
#              reactionVector of the inflow  is  +e_s, of the outflow  -e_s
#              (Augmentation.lean:65-82)
# InKerL α  = ∑ q, α q • reactionVector q = 0               [Concordance.lean:47]
# stoichSubspace of the fully open extension is ⊤            [Augmentation.lean:85], so
#              `mem_stoich` is automatic and `σ` is an arbitrary non-zero vector.
# reactionDirectionSign r s = source(s) - target(s)         [StrongConcordance.lean:31]
# Promotes r σ s : sign(σ s) = sign(dirSign r s) ∧ dirSign r s ≠ 0
# Opposes  r σ s : sign(σ s) = -sign(dirSign r s) ∧ dirSign r s ≠ 0
# StrongConcordanceWitness α σ                              [StrongConcordance.lean:46-57]
#              mem_kerL, mem_stoich, sigma_ne,
#              positive_reaction / negative_reaction / zero_reaction
# ZeroComplexReactionsAreFlows N                             [TrueChemistrySRCriterion.lean:368]
#              ∀ r, IsFlowChannel r → (∃ s, reaction r = inflowReaction s)
#                                      ∨ (∃ s, reaction r = outflowReaction s)
# ReactantProductSeparated N                                 [StrongConcordance.lean:26]
#              ∀ r s, source r s ≠ 0 → target r s = 0

class Net:
    """A network: `ns` species, `recs` a list of (source, target) complexes."""

    __slots__ = ("ns", "recs", "zero", "cls", "cls_list", "cls_complices",
                 "nonflow", "internal_cls", "m", "kerB")

    def __init__(self, ns, recs):
        self.ns = ns
        self.recs = [tuple((tuple(a), tuple(b))) for a, b in recs]
        self.zero = tuple([0] * ns)
        self.cls = []
        for a, b in self.recs:
            self.cls.append((a, b) if a <= b else (b, a))
        self.cls_list = sorted(set(self.cls))
        cc = {}
        for (a, b), c in zip(self.recs, self.cls):
            cc.setdefault(c, set()).add(a)
            cc.setdefault(c, set()).add(b)
        self.cls_complices = {c: sorted(v) for c, v in cc.items()}
        self.nonflow = [i for i, (a, b) in enumerate(self.recs)
                        if a != self.zero and b != self.zero]
        self.internal_cls = sorted({self.cls[i] for i in self.nonflow})
        self.m = len(self.recs) + 2 * ns          # |N.fullyOpen.R|
        self.kerB = None                          # filled lazily

    # ---- alpha index layout -------------------------------------------
    def i_ch(self, r):
        return r

    def i_in(self, t):
        return len(self.recs) + t

    def i_out(self, t):
        return len(self.recs) + self.ns + t

    def dirsign(self, q, s):
        """reactionDirectionSign of fullyOpen channel q at species s."""
        n = len(self.recs)
        if q < n:
            a, b = self.recs[q]
            return a[s] - b[s]
        if q < n + self.ns:
            return -1 if (q - n) == s else 0
        return 1 if (q - n - self.ns) == s else 0

    def source_of(self, q, s):
        n = len(self.recs)
        if q < n:
            return self.recs[q][0][s]
        if q < n + self.ns:
            return 0
        return 1 if (q - n - self.ns) == s else 0

    def has_identity(self):
        return any(a == b for a, b in self.recs)


def vec(net, r, s):
    """reactionVector r s as an exact integer."""
    a, b = net.recs[r]
    return b[s] - a[s]


def kerL_matrix(net):
    """Rows = species, columns = fullyOpen channels.  `A . alpha = 0` is `mem_kerL`."""
    ns, n = net.ns, len(net.recs)
    A = [[0] * net.m for _ in range(ns)]
    for r in range(n):
        for s in range(ns):
            A[s][r] = vec(net, r, s)
    for s in range(ns):
        A[s][net.i_in(s)] += 1
        A[s][net.i_out(s)] -= 1
    return A


def ker_basis(net):
    if net.kerB is None:
        net.kerB = rref_nullspace(kerL_matrix(net))
    return net.kerB


# --------------------------------------------------------------------------
# Hypotheses
# --------------------------------------------------------------------------

def hsep(net):
    for a, b in net.recs:
        for s in range(net.ns):
            if a[s] != 0 and b[s] != 0:
                return False
    return True


def singleton(ns, s):
    v = [0] * ns
    v[s] = 1
    return tuple(v)


def hflow(net):
    for a, b in net.recs:
        if a != net.zero and b != net.zero:
            continue
        ok = False
        for s in range(net.ns):
            if a == net.zero and b == singleton(net.ns, s):
                ok = True
            if b == net.zero and a == singleton(net.ns, s):
                ok = True
        if not ok:
            return False
    return True


class Cycle:
    __slots__ = ("n", "species", "rxn", "eL", "eR", "net")

    def __init__(self, net, species, rxn, eL, eR):
        self.net, self.n = net, len(species)
        self.species, self.rxn, self.eL, self.eR = species, rxn, eL, eR

    def key(self):
        return (tuple(self.species), tuple(self.rxn), tuple(self.eL), tuple(self.eR))

    def coeff_L(self, i):
        return self.eL[i][self.species[i]]

    def coeff_R(self, i):
        return self.eR[i][self.species[(i + 1) % self.n]]

    def is_even(self):
        return sum(1 for i in range(self.n) if self.eL[i] == self.eR[i]) % 2 == 0

    def is_scycle(self):
        p = 1
        for i in range(self.n):
            p *= self.coeff_L(i)
        q = 1
        for i in range(self.n):
            q *= self.coeff_R(i)
        return p == q

    def has_reaction(self, c):
        return c in self.rxn

    def edges(self):
        """The 2n graph edges as (species, class, endpoint)."""
        out = []
        for i in range(self.n):
            out.append((self.species[i], self.rxn[i], self.eL[i]))
            out.append((self.species[(i + 1) % self.n], self.rxn[i], self.eR[i]))
        return out

    def __repr__(self):
        return ("C(n=%d, species=%s, rxn=%s, eL=%s, eR=%s)"
                % (self.n, self.species, self.rxn, self.eL, self.eR))


def enumerate_cycles(net, minlen=2, maxlen=None):
    """Every TrueSRCycle of `net`, deduplicated up to representative choice."""
    if maxlen is None:
        maxlen = net.ns
    cl = net.internal_cls
    seen = set()
    for n in range(minlen, maxlen + 1):
        if n > len(cl) or n > net.ns:
            break
        for species in itertools.permutations(range(net.ns), n):
            for rxn in itertools.permutations(cl, n):
                # per-index endpoint options
                optL = []
                for i in range(n):
                    sp = species[i]
                    optL.append([c for c in net.cls_complices[rxn[i]] if c[sp] != 0])
                if any(not o for o in optL):
                    continue
                optR = []
                for i in range(n):
                    sp = species[(i + 1) % n]
                    optR.append([c for c in net.cls_complices[rxn[i]] if c[sp] != 0])
                if any(not o for o in optR):
                    continue
                for eL in itertools.product(*optL):
                    for eR in itertools.product(*optR):
                        cy = Cycle(net, species, rxn, eL, eR)
                        k = cy.key()
                        if k in seen:
                            continue
                        seen.add(k)
                        yield cy


# ---------------- S-to-R intersection -------------------------------------

def s_to_r_intersection_exists(C, D):
    """`Nonempty (C.SToRIntersection D)` decided exactly.

    `covers_common` + `edge_simple` + `components_separated` force the component list to be a
    vertex-disjoint decomposition of the *whole* common-edge subgraph into simple paths, each of
    odd length >= 1, starting at a species vertex and ending at a reaction vertex.
    """
    ce = set(C.edges())
    de = set(D.edges())
    common = ce & de
    if not common:
        return False
    # graph on nodes: ('s', species) | ('r', class)
    adj = {}
    for (sp, cl, ep) in common:
        u, v = ("s", sp), ("r", cl)
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    nodes = sorted(adj)

    # cheap sound filter: each connected component must have equal #species and #reaction nodes
    seen = set()
    for st in nodes:
        if st in seen:
            continue
        stack, comp = [st], []
        seen.add(st)
        while stack:
            x = stack.pop()
            comp.append(x)
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        ns_ = sum(1 for x in comp if x[0] == 's')
        nr_ = sum(1 for x in comp if x[0] == 'r')
        if ns_ != nr_:
            return False

    # enumerate all qualifying simple paths (as edge sets + node sets)
    paths = []
    for st in nodes:
        if st[0] != 's':
            continue

        def dfs(cur, nodeset, edgeset, used_nodes):
            for nxt in adj[cur]:
                if nxt in nodeset:
                    continue
                ne = tuple(sorted((cur, nxt)))
                ne2 = edgeset | {ne}
                nn = nodeset | {nxt}
                if nxt[0] == 'r' and len(ne2) % 2 == 1:
                    paths.append((frozenset(ne2), frozenset(nn)))
                dfs(nxt, nn, ne2, used_nodes | {nxt})

        dfs(st, {st}, set(), {st})

    if not paths:
        return False

    # A graph edge (species, class, endpoint) is determined by its two endpoint nodes, and the
    # DFS above labels its steps by exactly those node pairs; index on the node pair.
    edgelist = sorted({tuple(sorted((("s", sp), ("r", cl)))) for (sp, cl, _ep) in common})
    idx = {e: i for i, e in enumerate(edgelist)}
    bit = {}
    for pe, _ in paths:
        m = 0
        for e in pe:
            m |= 1 << idx[e]
        bit[pe] = m
    full = (1 << len(edgelist)) - 1
    by_edge = {i: [] for i in range(len(edgelist))}
    for pe, pn in paths:
        m = bit[pe]
        while m:
            b = m & -m
            i = b.bit_length() - 1
            by_edge[i].append((pe, pn))
            m ^= b


    def cover(rem, used):
        if rem == 0:
            return True
        i = (rem & -rem).bit_length() - 1
        for pe, pn in by_edge[i]:
            if (bit[pe] & rem) != bit[pe]:
                continue
            if (pn & used) != 0:
                continue
            if cover(rem & ~bit[pe], used | pn):
                return True
        return False

    return cover(full, frozenset())


def check_hSR(net, cycles, literal_hsr2=True):
    """`TrueSRStrongCriterion` for `net`, given its full cycle list.

    `literal_hsr2=True` evaluates the second conjunct exactly as stated at
    `TrueChemistrySRGraph.lean:271-274`, i.e. over every ordered pair of even cycles including
    `C = D`.  (The `C = D` instances are vacuous: see the CAVEAT in the module docstring, and the
    self-test's `selfint` count, which must stay 0.)

    Returns (ok, self_intersects_count).
    """
    evens = [c for c in cycles if c.is_even()]
    for c in evens:
        if not c.is_scycle():
            return False, 0
    n_self = sum(1 for c in cycles if s_to_r_intersection_exists(c, c))
    pairs = itertools.product(evens, evens) if literal_hsr2 else \
        itertools.combinations(evens, 2)
    for C, D in pairs:
        if s_to_r_intersection_exists(C, D):
            return False, n_self
    return True, n_self


# ---------------- witness -----------------------------------------------

def flux_vec(net, c, s):
    """Row vector (over kernel basis coords) of `flux alpha c s`, plus the constant part."""
    B = ker_basis(net)
    cols = [ZERO] * len(B)
    for r in range(len(net.recs)):
        if net.cls[r] != c:
            continue
        v = vec(net, r, s)
        if v == 0:
            continue
        for j, col in enumerate(B):
            if col[r]:
                cols[j] += col[r] * v
    return cols


def flux_exact(net, alpha, c, s):
    tot = ZERO
    for r in range(len(net.recs)):
        if net.cls[r] != c:
            continue
        tot += alpha[r] * vec(net, r, s)
    return tot


def sign(x):
    return (x > 0) - (x < 0)


def sign_sets(net, sigma):
    """P, M, Z subsets of fullyOpen channel indices for a given σ (values in {-1,0,1})."""
    P, M = set(), set()
    for q in range(net.m):
        ds = {s: net.dirsign(q, s) for s in range(net.ns)}
        pv = any(sigma[s] != 0 and ds[s] != 0 and sign(sigma[s]) == sign(ds[s])
                 for s in range(net.ns))
        mv = any(sigma[s] != 0 and ds[s] != 0 and sign(sigma[s]) == -sign(ds[s])
                 for s in range(net.ns))
        if pv:
            P.add(q)
        if mv:
            M.add(q)
    Z = set(P) & set(M)
    for q in range(net.m):
        if all(sigma[s] == 0 for s in range(net.ns) if net.source_of(q, s) != 0):
            Z.add(q)
    return P, M, Z


def witness_ok(net, alpha, sigma):
    """Exact check of `N.fullyOpen.StrongConcordanceWitness alpha sigma` (mem_stoich automatic)."""
    if all(v == 0 for v in sigma):
        return False, "sigma = 0"
    for s in range(net.ns):
        tot = ZERO
        for r in range(len(net.recs)):
            if alpha[r]:
                tot += alpha[r] * vec(net, r, s)
        tot += alpha[net.i_in(s)] - alpha[net.i_out(s)]
        if tot != 0:
            return False, "mem_kerL at species %d" % s
    P, M, Z = sign_sets(net, sigma)
    for q in range(net.m):
        a = alpha[q]
        if a > 0 and q not in P:
            return False, "positive_reaction fails at %d" % q
        if a < 0 and q not in M:
            return False, "negative_reaction fails at %d" % q
        if a == 0 and q not in Z:
            return False, "zero_reaction fails at %d" % q
    return True, ""


def causal_ok(net, alpha, sigma, C):
    """`hcausal`: flux (C.reaction i) (C.species (i+1 mod n)) * sigma > 0 for every i."""
    for i in range(C.n):
        s = C.species[(i + 1) % C.n]
        if flux_exact(net, alpha, C.rxn[i], s) * sigma[s] <= 0:
            return False, ("hcausal", i)
    return True, ""


def hopp_ok(net, alpha, sigma, C):
    """`hopp`: flux (C.reaction i) (C.species i) * sigma < 0 for every i."""
    for i in range(C.n):
        s = C.species[i]
        if flux_exact(net, alpha, C.rxn[i], s) * sigma[s] >= 0:
            return False, ("hopp", i)
    return True, ""


def find_target(net, alpha, sigma, C):
    """The negation of `no_offCycle_negFlux`: (b, rho) with rho off-cycle and flux*sigma < 0."""
    for b in range(C.n):
        s = C.species[b]
        if sigma[s] == 0:
            continue
        for c in net.cls_list:
            if C.has_reaction(c):
                continue
            if flux_exact(net, alpha, c, s) * sigma[s] < 0:
                return (b, c)
    return None


# --------------------------------------------------------------------------
# LP proposal in exact kernel coordinates
# --------------------------------------------------------------------------

def sigma_patterns(ns):
    """All sigma sign patterns in {-1,0,+1}^S \\ {0}.

    Complete for every proposition tested: `Promotes`, `Opposes`, `hcausal`, `hopp` and the
    target inequality read only `SignType.sign (sigma s)` and `sigma s = 0`."""
    for v in itertools.product((-1, 0, 1), repeat=ns):
        if any(v):
            yield list(v)


def off_cycle_classes(net, C):
    """Classes rho with `not C.HasReaction rho` -- the `rho` the target quantifies over."""
    return [c for c in net.cls_list if not C.has_reaction(c)]



def exact_strict_ok(net, alpha, sigma, rows):
    for (c, s, neg) in rows:
        if sigma[s] == 0:
            return False
        v = flux_exact(net, alpha, c, s) * sigma[s]
        if neg and not v < 0:
            return False
        if (not neg) and not v > 0:
            return False
    return True

def examine(net, C, want_hopp, rng, stats):
    """Try to refute `no_offCycle_negFlux` for one (network, even cycle) pair."""
    B = ker_basis(net)
    d = len(B)
    if d == 0:
        return None
    off = off_cycle_classes(net, C)
    for sigma in sigma_patterns(net.ns):
        if any(sigma[C.species[k]] == 0 for k in range(C.n)):
            continue                      # hcausal forces sigma != 0 on the cycle
        P, M, Z = sign_sets(net, sigma)
        # feasibility of the hypothesis cone alone (informative count)
        base_rows = [(C.rxn[i], C.species[(i + 1) % C.n], False) for i in range(C.n)]
        if want_hopp:
            base_rows += [(C.rxn[i], C.species[i], True) for i in range(C.n)]
        for target in [None] + [(c, C.species[b], True)
                               for c in off for b in range(C.n)]:
            rows = base_rows + ([] if target is None else [target])
            a = lp_once(net, B, d, sigma, rows, rng)
            if a is None:
                continue
            stats["proposals"] += 1
            ok, why = witness_ok(net, a, sigma)
            if not ok:
                continue
            if not causal_ok(net, a, sigma, C)[0]:
                continue
            if want_hopp and not hopp_ok(net, a, sigma, C)[0]:
                continue
            tg = find_target(net, a, sigma, C)
            if tg is None:
                continue
            stats["certified"] += 1
            return {"net": net, "C": C, "alpha": a, "sigma": sigma,
                    "target": tg, "hopp": want_hopp}
    return None


def lp_once(net, B, d, sigma, rows, rng):
    """One float-LP proposal snapped back into exact kernel coordinates."""
    P, M, Z = sign_sets(net, sigma)
    A_ub, b_ub = [], []
    for q in range(net.m):
        row = [float(B[j][q]) for j in range(d)]
        if q not in M:
            A_ub.append([-x for x in row]); b_ub.append(0.0)
        if q not in P:
            A_ub.append(row); b_ub.append(0.0)
    strict = []
    for (c, s, neg) in rows:
        if sigma[s] == 0:
            return None
        cols = flux_vec(net, c, s)
        sg = -sigma[s] if neg else sigma[s]
        strict.append([sg * float(cols[j]) for j in range(d)])
    if not strict:
        return None
    Aub = [r + [-1.0] for r in strict] + A_ub
    bub = [0.0] * len(strict) + b_ub
    try:
        res = linprog([0.0] * d + [-1.0], A_ub=np.array(Aub), b_ub=np.array(bub),
                      bounds=[(None, None)] * d + [(0, None)], method="highs")
    except Exception:
        return None
    if not res.success or res.x is None or res.x[d] <= 1e-9:
        return None
    yf = res.x[:d]
    for Dc in (10 ** 6, 10 ** 9, 10 ** 4, 10 ** 12, 10 ** 3):
        y = [Fraction(int(round(v * Dc)), Dc) for v in yf]
        a = matvec(B, y)
        if exact_strict_ok(net, a, sigma, rows):
            return a
    return None


# --------------------------------------------------------------------------
# Phases
# --------------------------------------------------------------------------

def candidate_channels(ns, maxsize=2, maxcoef=2):
    """All complexes of size 1..maxsize with entries in 0..maxcoef, then all ordered pairs."""
    cplx = []
    for size in range(1, maxsize + 1):
        for combo in itertools.combinations_with_replacement(range(ns), size):
            for mult in itertools.product(range(1, maxcoef + 1), repeat=size):
                v = [0] * ns
                for sp, m in zip(combo, mult):
                    v[sp] += m
                t = tuple(v)
                if t not in cplx:
                    cplx.append(t)
    zero = tuple([0] * ns)
    chans = []
    for a in cplx:
        for b in cplx:
            if a == b:
                continue
            chans.append((a, b))
    return chans, zero


def phase1(ns_list=(2, 3), nchan=(2, 3), maxsize=2, maxcoef=2, verbose=True):
    hits = []
    stats = {"nets": 0, "nets_sep": 0, "nets_flow": 0, "nets_hSR": 0,
             "cycles": 0, "even_cycles": 0, "pairs": 0, "proposals": 0,
             "certified": 0, "selfint": 0}
    for ns in ns_list:
        chans, zero = candidate_channels(ns, maxsize, maxcoef)
        sep_chans = []
        for (a, b) in chans:
            ok = all(not (a[s] != 0 and b[s] != 0) for s in range(ns))
            if ok:
                sep_chans.append((a, b))
        if verbose:
            print("  ns=%d: %d candidate channels, %d pass hsep" % (ns, len(chans), len(sep_chans)))
        for k in nchan:
            for combo in itertools.combinations(sep_chans, k):
                stats["nets"] += 1
                net = Net(ns, combo)
                if not hflow(net):
                    continue
                stats["nets_flow"] += 1
                cycles = list(enumerate_cycles(net))
                stats["cycles"] += len(cycles)
                if not any(c.is_even() for c in cycles):
                    continue
                stats["even_cycles"] += sum(1 for c in cycles if c.is_even())
                ok, nself = check_hSR(net, cycles)
                stats["selfint"] += nself
                if not ok:
                    continue
                stats["nets_hSR"] += 1
                rng = random.Random(12345)
                for C in cycles:
                    if not C.is_even():
                        continue
                    stats["pairs"] += 1
                    for hopp in (False, True):
                        hit = examine(net, C, hopp, rng, stats)
                        if hit:
                            hits.append(hit)
                            if verbose:
                                print("  *** COUNTEREXAMPLE (ns=%d, k=%d, hopp=%s)"
                                      % (ns, k, hopp))
                                print_report(hit)
                            return hits, stats
    return hits, stats


def random_network(rng, ns, nchan, maxsize=2, maxcoef=2):
    chans, _ = candidate_channels(ns, maxsize, maxcoef)
    sep = [(a, b) for (a, b) in chans
           if all(not (a[s] != 0 and b[s] != 0) for s in range(ns))]
    if len(sep) < nchan:
        return None
    return Net(ns, rng.sample(sep, nchan))


def phase2(seed, iters, ns_list=(3, 4), nchan=(3, 4, 5), verbose=True):
    rng = random.Random(seed)
    hits = []
    stats = {"nets": 0, "nets_flow": 0, "nets_hSR": 0, "cycles": 0,
             "even_cycles": 0, "pairs": 0, "proposals": 0, "certified": 0,
             "selfint": 0}
    for it in range(iters):
        ns = rng.choice(ns_list)
        k = rng.choice(nchan)
        net = random_network(rng, ns, k)
        if net is None:
            continue
        stats["nets"] += 1
        if not hflow(net):
            continue
        stats["nets_flow"] += 1
        cycles = list(enumerate_cycles(net))
        stats["cycles"] += len(cycles)
        evens = [c for c in cycles if c.is_even()]
        stats["even_cycles"] += len(evens)
        if not evens:
            continue
        ok, nself = check_hSR(net, cycles)
        stats["selfint"] += nself
        if not ok:
            continue
        stats["nets_hSR"] += 1
        for C in evens:
            stats["pairs"] += 1
            for hopp in (False, True):
                hit = examine(net, C, hopp, rng, stats)
                if hit:
                    hits.append(hit)
                    if verbose:
                        print("  *** COUNTEREXAMPLE at iteration %d (ns=%d, k=%d, hopp=%s)"
                              % (it, ns, k, hopp))
                        print_report(hit)
                    return hits, stats, it
        if verbose and (it + 1) % 500 == 0:
            print("  iter %d: %s" % (it + 1, stats))
    return hits, stats, None


# --------------------------------------------------------------------------

def print_report(hit):
    net, C, a, sigma = hit["net"], hit["C"], hit["alpha"], hit["sigma"]
    print("  species          : %s" % (list(range(net.ns)),))
    for i, (x, y) in enumerate(net.recs):
        print("  channel %d        : %s -> %s   (class %s, %s)"
              % (i, x, y, net.cls[i],
                 "flow" if i not in net.nonflow else "non-flow"))
    print("  cycle            : %r" % (C,))
    print("  numCPairs        : %d  (Even = %s)"
          % (sum(1 for i in range(C.n) if C.eL[i] == C.eR[i]), C.is_even()))
    print("  SCycle           : %s" % C.is_scycle())
    print("  sigma            : %s" % sigma)
    print("  alpha (fullyOpen): %s" % a)
    print("  kerL             : %s"
          % [str(sum(a[r] * vec(net, r, s) for r in range(len(net.recs)))
                 + a[net.i_in(s)] - a[net.i_out(s)]) for s in range(net.ns)])
    b, c = hit["target"]
    s = C.species[b]
    print("  TARGET b=%d (species %d), off-cycle class %s" % (b, s, c))
    print("  flux             : %s" % flux_exact(net, a, c, s))
    print("  flux * sigma     : %s   (STRICTLY NEGATIVE -> target)"
          % (flux_exact(net, a, c, s) * sigma[s]))
    print("  C.HasReaction c  : %s" % C.has_reaction(c))
    print("  hcausal / hopp   : %s / %s"
          % (causal_ok(net, a, sigma, C)[0], hopp_ok(net, a, sigma, C)[0]))
    print("  witness          : %s" % (witness_ok(net, a, sigma),))


def self_test():
    """Validate the encoder on the machine-checked example `CRNT/Scaffold/Cycle3TrueSRWitness.lean`."""
    print("Self-test on `cycle3Net` (A -> B -> C -> A, plus inflow A):")
    ns = 3
    recs = [((1, 0, 0), (0, 1, 0)),
            ((0, 1, 0), (0, 0, 1)),
            ((0, 0, 1), (1, 0, 0)),
            ((0, 0, 0), (1, 0, 0))]
    net = Net(ns, recs)
    assert hsep(net), "cycle3Net should be reactant/product separated"
    assert hflow(net), "cycle3Net should satisfy ZeroComplexReactionsAreFlows"
    cycles = list(enumerate_cycles(net))
    tri = [c for c in cycles if c.n == 3]
    assert tri, "the triangle cycle should be found"
    evens = [c for c in tri if c.is_even()]
    assert evens, "the triangle cycle has 0 c-pairs and is even"
    assert all(c.is_scycle() for c in evens)
    print("  hsep, hflow: OK")
    print("  cycles of length 3 found: %d, even: %d, all s-cycles: %s"
          % (len(tri), len(evens), all(c.is_scycle() for c in evens)))
    # Channel 3 is `inflowReaction 0`, a flow channel in its own class; channels 0..2 are the
    # three internal classes of the triangle (no reversals present).
    assert len(net.cls_list) == 4, net.cls_list
    assert len(net.internal_cls) == 3, net.internal_cls
    # hand check of `trueInternalClassFlux`: class of channel 0 is ({A},{B}); at species B the
    # vector is 1, at A it is -1, elsewhere 0.
    c0 = net.cls[0]
    assert flux_exact(net, [1] + [0] * (net.m - 1), c0, 1) == 1
    assert flux_exact(net, [1] + [0] * (net.m - 1), c0, 0) == -1
    print("  classes: %d total, %d internal; class-flux signs checked by hand: OK"
          % (len(net.cls_list), len(net.internal_cls)))
    # Exact check of the CAVEAT: `C` shares no S-to-R path with ITSELF, so the `C = D` instances of
    # `TrueSRStrongCriterion`'s second conjunct are vacuously satisfied.
    C = evens[0]
    nself = sum(1 for c in cycles if s_to_r_intersection_exists(c, c))
    assert nself == 0, ("counting argument says Nonempty (C.SToRIntersection C) is impossible, "
                        "but %d cycles self-intersect" % nself)
    print("  Nonempty (C.SToRIntersection C) over all %d cycles: %d  (must be 0)"
          % (len(cycles), nself))
    # kerL basis sanity
    B = ker_basis(net)
    A = kerL_matrix(net)
    for col in B:
        for s in range(net.ns):
            assert sum(A[s][i] * col[i] for i in range(net.m)) == 0
    print("  nullspace basis of the InKerL matrix: %d columns, verified exactly" % len(B))
    # sigma sign-pattern completeness note
    assert len(list(sigma_patterns(2))) == 8
    print("  sigma sign patterns for ns=2: 8 (3^2 - 1)  OK")
    print("Self-test passed.")


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    print(__doc__)
    print("=" * 78)
    if which in ("selftest", "all"):
        self_test()
        print("-" * 78)
    if which in ("1", "all"):
        print("PHASE 1 — exhaustive: ns in {2,3}, |R| in {2,3}, complexes of size <= 2, coeff <= 2")
        hits, st = phase1()
        print("  stats: %s" % st)
        print("  counterexamples: %d" % len(hits))
        print("-" * 78)
    if which in ("2", "all"):
        seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20261010
        iters = int(sys.argv[3]) if len(sys.argv) > 3 else 4096
        print("PHASE 2 — random: seed=%d, iters=%d, ns in {3,4}, |R| in {3,4,5}" % (seed, iters))
        hits, st, it = phase2(seed, iters)
        print("  stats: %s" % st)
        print("  counterexamples: %d" % len(hits))
    return 0


if __name__ == "__main__":
    sys.exit(main())
