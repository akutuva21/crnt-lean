# Transcription — Anderson, *A proof of the global attractor conjecture in the single linkage class case*

**Source actually read this session:** `https://arxiv.org/pdf/1101.0761` fetched to `/tmp/a1101.pdf`,
`file` reports `PDF document, version 1.4, 23 pages`. Text extracted and read **end to end**
(pages 1–23, §1.1 through the reference list). Header line of page 1 (`a1101.pdf:3`) and the arXiv
stamp on page 3 (`a1101.pdf:19`, `arXiv:1101.0761v6 [math.DS] 17 May 2011`) fix the identity.
Every quotation below is from that file; page markers are the `<!-- Page n -->` comments.

This is the **same paper** the repository already names at
`CRNT/Dynamics/SingleLinkageGAC.lean:24-25` ("Anderson, _A proof of the global attractor conjecture
in the single linkage class case_, 2011") and at
`research/README.md:176-181` ("`relEntropy` + tiers + Stiemke is Anderson, arXiv:1101.0761").
**`CRNT/Dynamics/TierPersistence.lean` is a different paper** — its own header at `:10-12` says
"the Anderson–Cappelletti–Kim–Nguyen tier route" — although it formalises the same *tier*
primitive (Definition 4.1 below).

---

## 1. The headline claim of the repository's residue is NOT in this paper

`CRNT/Dynamics/SiphonDimensionDescent.lean:25-27` calls the residue

> "The single genuinely analytic ingredient — Anderson's comparable-growth Lyapunov-family
> estimate, which forbids the trajectory from cycling among boundary faces and forces each
> boundary excursion to strip away at least one species"

and `:120-122`

> "the strict shrinking is forced by comparing the growth of the relative-entropy Lyapunov family
> across an escape from the face `SiphonFace P`".

**I read all 23 pages. There is no siphon-cardinality descent in this paper, no iteration over
siphons, and no clause of the shape "the zero set strictly shrinks".** The word "siphon" occurs
exactly once in the body, in the historical background at `a1101.pdf:41`:

> "those associated with a semi-locking set (using the terminology of [1]), which is a subset of
> the species whose absence is forward invariant. (Semi-locking sets were termed siphons in the
> earlier paper in which their concept was formally introduced.)"

Anderson's actual mechanism is a **single global dichotomy**, proved once, with **no iteration**.
The "comparable growth" language in `SiphonDimensionDescent` corresponds to two genuinely
different objects in the paper, which the repository's docstring fuses:

* the **tier partition** (Definition 4.1 / Lemma 4.2) — a comparable-growth decomposition of the
  complexes along a *subsequence*; and
* the **family of Lyapunov functions** `V_x`, `x ∈ ℝ^N_{>0}` (eq. 4.5, page 15), of which condition
  **C1** of Lemma 4.7 says *the whole family* strictly decreases.

The conjunction of the two does produce a strong conclusion, but it is **"the ω-limit set is a
single point"** (Lemma 4.9) — not "the siphon shrinks".

---

## 2. The pieces, transcribed

### 2.1 Projected dynamics — §3.1, eq. (3.2), `a1101.pdf:126-134`

For `U ⊂ {1,…,N}` nonempty, `M = |U|`, the projected dynamics is the `M`-dimensional system

> ẋ|<sub>U,1</sub>(t) = f₁(κ, x|<sub>U,1</sub>(t),…,x|<sub>U,M</sub>(t), x<sub>M+1</sub>(t),…,x<sub>N</sub>(t)) = f₁(κ̂(t), x|<sub>U</sub>(t))
> … ẋ|<sub>U,M</sub>(t) = f<sub>M</sub>(…) = f<sub>M</sub>(κ̂(t), x|<sub>U</sub>(t)),

> "where `κ̂(t) = (κ, x_{M+1}(t),…,x_N(t))` and `f̂_i` … are defined via the above equalities."

> "That is, they are now viewed as inputs, or perhaps forcing, to the system."

### 2.2 Reduced reaction network — Definition 3.1, `a1101.pdf:153-160`

`{S_U, C_U, R_U}` is built by:

> "1. Set `S_U = {S_i ∈ S : i ∈ U}`.
> 2. Set `C_U = {y|<sub>U</sub> : y ∈ C}`. We say the complex `y` *reduces to* the complex `y|<sub>U</sub>`.
> 3. Set `R_U = {y|<sub>U</sub> → y′|<sub>U</sub> : y → y′ ∈ R, and for which `y|<sub>U</sub> = y′|<sub>U</sub>`}.
> 4. If a resulting linkage class consists of a single complex, we delete that complex from `C_U`."

Two structural lemmas:

* **Lemma 3.3** (`a1101.pdf:169`): "the reduced reaction network `{S_U,C_U,R_U}` has less than or
  equal to the number of linkage classes as `{S,C,R}`."
* **Lemma 3.4** (`a1101.pdf:169`): "Suppose that `{S,C,R}` … is weakly reversible and that
  `U ⊂ {1,…,N}` is nonempty. Then `{S_U,C_U,R_U}` is weakly reversible."

### 2.3 Projected kinetics — eq. (3.7), `a1101.pdf:180`

> "for `y_k|<sub>U</sub> → y′_k|<sub>U</sub> ∈ R_U`,  `κ_k(t) = Σ_{z_i→z_i′∈R : y_k|<sub>U</sub> = z_i|<sub>U</sub> and y′_k|<sub>U</sub> = z_i′|<sub>U</sub>} κ_i (x(t)|<sub>U</sub>^c)_{<sub>i′</sub>}`"

> "It is important to note that the variables `κ̂_k(t)` … are always non-negative as they consist
> of positive linear combinations of non-negative monomials of the variables `x_j` for which
> `j ∉ U`."

And **Definition 2.7** (bounded mass-action kinetics), `a1101.pdf:99-103`:

> "We say that the non-autonomous system `{S,C,R,K(t)}` has bounded mass-action kinetics if there
> exists an `η > 0` such that for each `k ∈ {1,…,|R|}`: `R_k(x,t) = κ_k(t) x^{y_k}`, where
> `η < κ_k(t) < 1/η` for all `t ≥ 0` and `k ∈ {1,…,|R|}`."

### 2.4 Tiers — Definition 4.1, `a1101.pdf:192-205`

For a finite `C ⊂ ℤ^N` and a sequence `x_n ∈ ℝ^N_{>0}`, `C` is **partitioned along `{x_n}`** if there
are tiers `T_1,…,T_P` (a partition of `C`) and a constant `C > 1` with

> (i) if `y_j, y_k ∈ T_i` for some `i`, then for all `n`, `1/C · x_n^{y_j} ≤ x_n^{y_k} ≤ C · x_n^{y_j}`
> (ii) if `y_k ∈ T_i` and `y_j ∈ T_{i+m}` for some `m ∈ {1,…,P−i}`, then `x_n^{y_k} / x_n^{y_j} → ∞` as `n → ∞`.

> "Therefore, we have a natural ordering of the tiers: `T_1 ≻ T_2 ≻ ⋯ ≻ T_P`, and we say `T_1` is
> the 'highest' tier, whereas `T_P` is the 'lowest' tier."

> "**Lemma 4.2.** Let `C` denote a finite set of vectors in `ℝ^N`. Let `x_n` be a sequence of
> points in `ℝ^N_{>0}`. Then, there exists a subsequence of `{x_n}` along which `C` is partitioned."

Lemma 4.2's proof (`a1101.pdf:207-229`) is a finite pigeonhole on the `r!` orderings of `C`
followed by monotone (`lim inf < ∞`) subdivision of the ratio functions
`ψ_i(x) = x^{y_i}/x^{y_{i+1}}`. It is a compactness argument, not a CRNT argument.

### 2.5 Stiemke — Lemma 4.3, `a1101.pdf:231`

> "**Lemma 4.3 (Stiemke's Theorem, [32]).** For `i = 1,…,n`, let `u_i ∈ ℝ^m`. Either there exists an
> `α ∈ ℝ^n` such that `Σ_i α_i u_i ≤ 0` … and such that at least one of the inequalities is
> strict, or there is a `w ∈ ℝ^m_{>0}` such that `w · u_i = 0` for each `i ∈ {1,…,n}`."

### 2.6 Tier-respecting conservation relations — Definitions 4.4/4.5 and Theorem 4.6

> "**Definition 4.4.** Let `w ∈ ℝ^N`. The set `{i ∈ {1,…,N} : w_i = 0}` is called the *support* of `w`."

> "**Definition 4.5.** … We say that the vector `w ∈ ℝ^N_{≥0}` is a *non-negative conservation
> relation that respects the pair* `(U, {T_i})` if: 1. `w_i > 0` iff `i ∈ U` … 2. Whenever
> `y_j, y_ℓ ∈ T_i` for some `i`, we have that `w · (y_j − y_ℓ) = 0`."

> "**Theorem 4.6.** Let `C` denote a finite set of vectors in `ℝ^N`. Let `x_n ∈ ℝ^N_{>0}` denote a
> sequence of points with `x_n → z ∈ ∂ℝ^N_{≥0}`, as `n → ∞`. Let `U = U(z) = {i : z_i = 0}`.
> Finally, suppose that `C` is partitioned along `{x_n}` with tiers `T_i`, `i = 1,…,P`, and constant
> `C > 0`. Then, there is a non-negative conservation relation `w ∈ ℝ^N_{≥0}` that respects the
> pair `(U, {T_i})`."

> "Note that if `C = T_1`, then the type of conservation relation described above is the usual
> concept in chemical reaction network theory." (`a1101.pdf:239`)

### 2.7 The Lyapunov family — eq. (4.5), `a1101.pdf:258-262`

> "For any `x ∈ ℝ^N_{>0}`, define `V_x : ℝ^N_{>0} → ℝ_{≥0}` by
> `V_x(x) = Σ_{i=1}^N [ x_i (ln(x_i) − ln(x) − 1) + x_i ]`. … For `x ∈ ∂ℝ^N_{≥0}`, define `V_x(x)`
> via the continuous extension of (4.5). … **Note that `∇V_x(x) = ln x − ln x`.** It is relatively
> straightforward to show that for any `x ∈ ℝ^N_{>0}`, `V_x` is convex with a global minimum of zero
> at `x`. Note that in the current setting `x` need not be a complex balanced equilibrium."

(Notation collision in the paper's own text: `V_x` is indexed by a reference `x̄ ∈ ℝ^N_{>0}` and
evaluated at a state `x`; the extracted text has lost the distinction. The intended reading is
`V_{x̄}(x) = Σ_i [ x_i(ln x_i − ln x̄_i − 1) + x̄_i ]`.)

### 2.8 The dichotomy — Lemma 4.7, `a1101.pdf:264-275`

> "**Lemma 4.7.** Let `{S,C,R,K(t)}`, with `S = {S_1,…,S_N}`, be a weakly reversible,
> non-autonomous mass-action system with bounded kinetics. For `t ≥ 0`, let `x(t) = φ(t,x_0)` be the
> solution … Suppose `x_0 ∈ ℝ^N_{>0}` is such that `φ(t,x_0)` remains bounded and
> `dist(φ(t,x_0), ∂ℝ^N_{≥0}) → 0`, as `t → ∞`. Then at least one of the following two conditions
> hold for this trajectory:
>
> **C1**: For any `x ∈ ℝ^N_{>0}`, there exists a `T = T_x > 0` such that `t > T` implies
> `d/dt V_x(x(t)) = Σ_k κ_k(t) x(t)^{y_k} (y_k′ − y_k) · (ln(x(t)) − ln x) < 0`.
>
> **C2**: There exists a sequence of times, `t_n → ∞`, such that `x_n = φ(t_n,x_0) ∈ ℝ^N_{>0}`
> converges to a point `z ∈ ω(φ(·,x_0)) ∩ ∂ℝ^N_{≥0}`, and (i) `C` is partitioned along `x_n` with
> tiers `{T_i}^P_{i=1}`, and constant `C`, and (ii) **`T_1` consists of a union of linkage classes**."

**Lemma 4.7's proof is the "comparable-growth estimate".** Its shape, in full:

* `¬C1` gives `x̄ ∈ ℝ^N_{>0}` and `t_n → ∞` with the sum in C1 `≥ 0` (eq. 4.6, `a1101.pdf:275`).
* Boundedness + `dist → 0` gives a convergent subsequence `x_n → z ∈ ω ∩ ∂` (paper says `∂ℝ^N_{>0}`;
  this is a typo for `∂ℝ^N_{≥0}`, cf. the later identical usage at `a1101.pdf:345`).
* Lemma 4.2 partitions `C` along a further subsequence.
* The C1 sum is split into three blocks by tier (eqs. 4.8/4.9, `a1101.pdf:284-294`):
  `∑_i ∑_{i→i}` (within a tier, **all negative** by (i)), `∑_i ∑_{m≥1} {i→i+m}` (**all negative** by
  (ii)), and `∑_i ∑_{m≥1} {i→i−m}` (**all positive**).
* `¬C2` ⟹ `T_1` is not a union of linkage classes ⟹ **weak reversibility** gives a reaction
  `y_{k_1} → y'_{k_1}` with `y_{k_1} ∈ T_1`, `y'_{k_1} ∈ T_j`, `j ≥ 2`; that single negative term
  dominates every term of `∑_{i→i}` — eq. (4.10), `a1101.pdf:304`, with `q_{1,n} → ∞`.
* For each term of `∑_{i→i−m}`, weak reversibility supplies a **directed path**
  `y_0 → y'_0, y'_0 → … → y_0` with no repeated reaction, from which a sub-path
  `r_1,…,r_b` is cut satisfying conditions 1–5 (`a1101.pdf:308-312`): every source is in a
  strictly higher tier than its product; the product of `r_b` is in tier `≥ i`; every source of
  the `r_ℓ` is in tier `< i`. Triangle inequality gives eq. (4.12) with a product of `b` factors each
  `→ +∞` (using the **bounded kinetics bound `η`**, `a1101.pdf:325`), against eq. (4.13) bounded
  below uniformly — eq. (4.14) with `q_{2,n} → ∞`. Summing: eq. (4.15), the whole sum is `< 0`,
  contradicting (4.6).

  **The rate is therefore explicit and qualitative: `q_{1,n}, q_{2,n} → ∞`, i.e. the domination is
  as strong as one wants for all sufficiently large `n`, with no uniform rate over the choice of
  reference `x̄`.**

### 2.9 Killing C2 — Lemma 4.8, `a1101.pdf:341-345`

> "**Lemma 4.8.** Let `{S,C,R,K(t)}` … be a non-autonomous mass-action system with bounded kinetics
> and **a single linkage class**. Suppose `x_0 ∈ ℝ^N_{>0}` is such that `φ(t,x_0)` remains bounded
> and `dist(φ(t,x_0),∂ℝ^N_{≥0}) → 0` as `t → ∞`. Then, there does **not** exist a subsequence of
> times `t_n → ∞` such that `C` is partitioned along `x_n = φ(t_n,x_0)` in which `T_1` consists of
> a union of linkage classes."

Proof: "in the one linkage class case `T_1` can only consist of a union of linkage classes if
`T_1 ≡ C`" — i.e. there is **one single tier**. Then Theorem 4.6 gives `w ≥ 0` with `supp w = U`
and `w·(y'_k − y_k) = 0` for all reactions, so `w · φ(t,x_0)` is constant in `t` by (2.2), while
`w · φ(t_n,x_0) → 0` since `φ_i(t_n,x_0) → 0` for all `i ∈ U`. Contradiction.

### 2.10 The family forces a single point — Lemma 4.9, `a1101.pdf:345-357`

> "**Lemma 4.9.** Let `{S,C,R,K(t)}` … be a non-autonomous system with bounded mass-action kinetics.
> Suppose `x_0 ∈ ℝ^N_{>0}` is such that for any `x ∈ ℝ^N_{>0}`, there exists a `T = T_x > 0` such
> that `t > T` implies `d/dt V_x(x(t)) < 0` … Then `ω(φ(·,x_0))` is a single point."

Proof: each `V_x(φ(t,x_0))` is bounded below by 0 and decreasing, so `V_x(φ(t,x_0)) → c_x`. For
`z_1, z_2 ∈ ω`, `V_{x̄_1}(z_1) − V_{x̄_1}(z_2) − (V_{x̄_2}(z_1) − V_{x̄_2}(z_2)) = (z_1 − z_2)·(ln x̄_2 − ln x̄_1)`
for arbitrary `x̄_1, x̄_2 ∈ ℝ^N_{>0}`; hence `z_1 = z_2`.

### 2.11 The theorem — Theorem 4.10, Corollary 4.11, `a1101.pdf:357-385`

> "**Theorem 4.10.** Let `{S,C,R,K}` … be a weakly reversible, single linkage class chemical
> reaction network with mass-action kinetics. We assume that for `x_0 ∈ ℝ^N_{>0}` the trajectory
> `φ(t,x_0)` satisfies the following two conditions
>
> 1. `φ(t,x_0)` is bounded (in `t`), and
> 2. `ω(φ(·,x_0))` is either completely contained in `∂ℝ^N_{≥0}` or completely contained within
>    the interior of `ℝ^N_{>0}`.
>
> Then `ω(φ(·,x_0)) ∩ ∂ℝ^N_{≥0} = ∅`, and the trajectory is persistent."

**Proof structure** (`a1101.pdf:367-383`):

* Assume `∃ z ∈ ω ∩ ∂`. Set `U = {i : z_i = 0 for some z ∈ ω}` (all indices whose concentration
  approaches zero along *some* subsequence) — nonempty.
* Equivalence (4.16): `i ∈ U ⟺ lim inf φ_i(t) = 0 ∧ lim sup φ_i(t) < ∞`; for `j ∉ U`,
  `0 < lim inf φ_j(t) ≤ lim sup φ_j(t) < ∞`.
* Reduce: `{S_U,C_U,R_U}` + projected `K(t)`. By (4.16) and (3.7), `η < κ_k(t) < 1/η` — eq. (4.17),
  **bounded mass-action kinetics**.
* By Lemmas 3.3/3.4 the reduced network is weakly reversible **and has one linkage class**.
* "By condition 2., above, which pertains to the original system, and by the construction of `U`,
  the set of ω-limit points of the trajectory of the reduced system must exist on `∂ℝ^N_{≥0}`."
  ← **this is the *only* use of condition 2 in the proof.**
* Lemmas 3.3, 4.7, 4.8, 4.9 ⟹ the reduced ω-limit set is a **single point**. By construction of `U`
  it must be the origin `0 ∈ ℝ^N`.
* "However, we also know by Lemmas 4.7, 4.8, and 4.9 that `d/dt V_x(x(t)) < 0` for `t` large
  enough, where `x ∈ ℝ^N_{>0}` is arbitrary. Therefore, because the origin is a local maximum of
  `V_x`, we can not have that `x(t) → 0 ∈ ℝ^N`." **Contradiction.**

> "**Corollary 4.11.** Let `{S,C,R,K}` denote a complex-balanced system with one linkage class. Then,
> any complex-balanced equilibrium contained in the interior of a positive compatibility class is a
> global attractor of the interior of that positive class."

And Anderson's own closing caveat (`a1101.pdf:389`):

> "Note that the single linkage class assumption in Theorem 4.10, and hence Corollary 4.11, was
> only used in conjunction with Theorem 4.6 in the proof of Lemma 4.8 to guarantee that the top
> tier, `T_1`, could not consist of a union of linkage classes. **If it can be guaranteed in any
> other way that the top tier, in the construction detailed in the previous lemmas, can not consist
> of a union of linkage classes, then the conclusions of Theorem 4.10 and Corollary 4.11 … will
> still hold.** Also, note that if it can be shown that condition 2 of Theorem 4.10 is always
> satisfied by weakly reversible networks with mass-action kinetics, something we believe to be
> true, then the Persistence Conjecture … will also be proven in the single linkage class case by
> the arguments in this paper."

---

## 3. What I could NOT access

* Nothing in §§1–5 or the reference list: the PDF above is complete and I read all 23 pages.
* Anderson, *Global asymptotic stability for a class of nonlinear chemical equations*, SIAM J. Appl.
  Math. **68** (2008), 1464–1476 (reference [1], `a1101.pdf:408-410`) — the "entry-time" paper. I
  did **not** fetch it in this session. `research/README.md:175-176` already records the same gap.
  Everything I say about it below is **not** sourced and is flagged where used.
* Anderson–Shiu, *The dynamics of weakly reversible population processes near facets*, SIAM J. Appl.
  Math. **70** (2010), 1840–1858, arXiv:0903.0901 — referenced by this paper as [3] but **not read
  this session**; the repository's use of it is at
  `CRNT/Dynamics/FacetRepulsionAndersonShiu.lean:22-24`, which I did not read this session.