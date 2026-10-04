import CRNT.Dynamics.HighCodimensionSiphonFace
import CRNT.Multistationarity.TrueChemistrySRCriterion
import CRNT

open Lean

namespace AxiomSweep

/-- Axioms Mathlib/Lean itself legitimately introduces. -/
def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The axiom `sorry` introduces. -/
def sorryAx : Name := `sorryAx

/-- Every constant mentioned in `e`. -/
partial def exprConsts (e : Expr) (acc : Array Name := #[]) : Array Name :=
  match e with
  | .const n _ => acc.push n
  | .app f a => exprConsts a (exprConsts f acc)
  | .lam _ t b _ => exprConsts b (exprConsts t acc)
  | .forallE _ t b _ => exprConsts b (exprConsts t acc)
  | .letE _ t v b _ => exprConsts b (exprConsts v (exprConsts t acc))
  | .mdata _ b => exprConsts b acc
  | .proj _ _ b => exprConsts b acc
  | .lit _ => acc

/-- Constants directly depended on by a `ConstantInfo`'s value. -/
def valueDeps : ConstantInfo → Array Name
  | .thmInfo v _ => exprConsts v
  | .defnInfo v _ _ _ => exprConsts v
  | .opaqueInfo v _ => exprConsts v
  | .ctorInfo v _ => exprConsts v
  | .axiomInfo _ => #[]
  | _ => #[]

/-- Transitive constant closure of `roots` in `env`, via an explicit-stack BFS with an
`Std.HashSet`-backed seen-set (a quadratic `Array.contains` walk is far too slow over a
~50k-constant environment). -/
def closure (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  let mut out : Array Name := #[]
  let mut stack : Array Name := roots
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    out := out.push n
    if let some ci := env.find? n then
      for d in valueDeps ci do
        if !seen.contains d then
          stack := stack.push d
  return out

/-- The theorem/lemma constants in `names`: those whose `ConstantInfo` is a `thmInfo`. -/
def theoremsIn (env : Environment) (names : Array Name) : Array Name :=
  names.filter fun n => match env.find? n with
    | some (.thmInfo _ _) => true
    | _ => false

/-- Is this constant part of this repository's own development (not Mathlib, not core)? -/
def isLocal (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "CRNT." || s.startsWith "ODE." || s.startsWith "Scaffold."

/-- Names of constants in `env` introduced by this repository, i.e. plausibly ours. -/
def localNames (env : Environment) : Array Name :=
  env.constants.fold (fun acc n => if isLocal n then acc.push n else acc) #[]

structure Report where
  /-- Every distinct axiom set occurring, with the declarations exhibiting it. -/
  buckets : Array (String × Array Name)
  /-- Local declarations resting on an axiom outside `allowed ∪ {sorryAx}`. -/
  offenders : Array (Name × Array Name)
  /-- Local declarations depending on `sorryAx`. -/
  sorryInfected : Array Name
  /-- Local constants in the closure at all. -/
  localTotal : Nat
  /-- Local theorems in the closure. -/
  localTheoremTotal : Nat
  /-- Size of the whole constant closure, Mathlib included. -/
  closureSize : Nat

/-- Union of two name sets, in a canonical (sorted) order so keys compare by string. -/
def unionNames (a b : Array Name) : Array Name :=
  let mut s : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  for x in a do s := s.insert x
  for x in b do s := s.insert x
  s.toArray.qsort (fun x y => x.toString < y.toString)

/-- Propagate axiom sets through the closure in one reverse pass.

`closure` pushes a constant's dependencies *after* popping it, so in the returned array every
dependency appears strictly later than its dependent.  Walking that array backwards visits each
constant only after all of its dependencies, which makes a single pass enough — no topological
sort and, unlike calling `collectAxioms` per theorem, no re-walk of the environment per theorem. -/
def run (env : Environment) (roots : Array Name) : ReportCoreM Report := do
  let out := closure env roots
  let mut ax : Std.HashMap Name (Array Name) := Std.HashMap.emptyWithCapacity
  let mut bucketMap : Std.HashMap String (Array Name) := Std.HashMap.emptyWithCapacity
  let mut offenders : Array (Name × Array Name) := #[]
  let mut sorryInfected : Array Name := #[]
  let mut localTotal := 0
  let mut localTheoremTotal := 0
  for i in [0:out.size] do
    let n := out[out.size - 1 - i]!
    let ci := env.find? n
    let mut acc : Array Name :=
      match ci with
      | some (.axiomInfo _) => #[n]
      | _ => #[]
    match ci with
    | some c =>
      for d in valueDeps c do
        if let some v := ax.get? d then
          acc := unionNames acc v
    | none => pure ()
    ax := ax.insert n acc
    if isLocal n then
      localTotal := localTotal + 1
      if (match ci with | some (.thmInfo _ _) => true | _ => false) then
        localTheoremTotal := localTheoremTotal + 1
        let key := String.intercalate ", " (acc.toList.map Name.toString)
        bucketMap := match bucketMap.get? key with
          | some v => bucketMap.insert key (v.push n)
          | none => bucketMap.insert key #[n]
        let extra := acc.filter fun a => !(allowed.contains a) && a != sorryAx
        if !extra.isEmpty then
          offenders := offenders.push (n, extra)
        if acc.contains sorryAx then
          sorryInfected := sorryInfected.push n
  let mut buckets : Array (String × Array Name) := #[]
  for (k, v) in bucketMap.toList do
    buckets := buckets.push (k, v)
  return {
    buckets := buckets.qsort (fun a b => a.1 < b.1),
    offenders := offenders,
    sorryInfected := sorryInfected,
    localTotal := localTotal,
    localTheoremTotal := localTheoremTotal,
    closureSize := out.size }

/-- Whole-environment census: every *local* theorem anywhere in `env` that rests on `sorryAx`.

This is what tests the claim in `CRNT/Dynamics/HighCodimensionSiphonFace.lean`: "so do exactly its
downstream consumers `Network.complexBalanced_genuinePermanent`, `Network.complexBalanced_permanent`,
and `Network.complexBalanced_globalAttractor`.  No other declaration in the tree does."
The claim is a statement about the *whole* environment, so it needs a whole-environment scan. -/

end AxiomSweep

/-- Every constant in `env` whose *transitive* dependency closure mentions `sorryAx`.

One forward pass: `sorryAx` is a leaf, so a constant is tainted iff it mentions `sorryAx`
directly or mentions a tainted constant.  Iterating to a fixed point keeps the pass linear in the
number of rounds, and each round is a single sweep, so this is far cheaper than re-walking every
local theorem's full closure. -/
def sorryAxSet (env : Environment) : Std.HashSet Name := Id.run do
  let mut tainted : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  let mut changed := true
  while changed do
    changed := false
    for (n, ci) in env.constants.map₂.toList do
      if tainted.contains n then continue
      if ci matches .axiomInfo _ then
        if n == sorryAx then
          tainted := tainted.insert n
          changed := true
        continue
      for d in valueDeps ci do
        if d == sorryAx || tainted.contains d then
          tainted := tainted.insert n
          changed := true
          break
  return tainted

open AxiomSweep in
def main : IO Unit := do
  let env ← Lean.getEnv
  let holeA := `CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace
  let holeB := `CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion
  IO.println "=== ROOT CHECK ==="
  for h in #[holeA, holeB] do
    match env.find? h with
    | some ci => IO.println s!"root {h} : present ({ci.kindName})"
    | none => IO.println s!"root {h} : MISSING"
  IO.println ""
  IO.println "=== WHOLE-ENVIRONMENT sorryAx CENSUS ==="
  let tainted := sorryAxSet env
  let mut localTainted : Array Name := tainted.toArray.filter isLocal
  localTainted := localTainted.qsort (fun a b => a.toString < b.toString)
  IO.println s!"constants in env resting on sorryAx : {tainted.size}"
  IO.println s!"of which local (CRNT./ODE./Scaffold.) : {localTainted.size}"
  for n in localTainted do
    IO.println s!"  {n}"
  IO.flush
  -- `import CRNT` together with the two hole modules is the largest environment this repository
  -- can produce, so "no other declaration in the tree does [report sorryAx]" is testable here:
  -- anything in `env` is in the tree.
  for (tag, roots) in #[("A", #[holeA]), ("B", #[holeB]), ("A+B", #[holeA, holeB])] do
    IO.println ""
    IO.println s!"=== CHAIN {tag} ==="
    IO.flush
    let r ← run env roots
    IO.println s!"closure size (all consts): {r.closureSize}"
    IO.println s!"local constants in closure : {r.localTotal}"
    IO.println s!"local theorems in closure   : {r.localTheoremTotal}"
    IO.println s!"distinct axiom sets        : {r.buckets.size}"
    for (key, ns) in r.buckets do
      IO.println s!"  [{key}]  x{ns.size}"
      if key != "Classical.choice, Quot.sound, propext" then
        for n in ns do IO.println s!"      {n}"
    IO.flush
    IO.println s!"-- offenders (axiom outside allowed ∪ sorryAx): {r.offenders.size}"
    for (n, xs) in r.offenders do
      IO.println s!"  {n} :: {xs.toList}"
    IO.println s!"-- sorryAx-tainted local theorems: {r.sorryInfected.size}"
    for n in r.sorryInfected do
      IO.println s!"  {n}"
    IO.flush
