import CRNT

/-!
# `DumpEnv` — machine-readable dump of the whole `CRNT` environment.

Run (from the repo root, against the shared olean cache):

```
LEAN_PATH="$CRNT_ROOT/.lake/build/lib/lean" lake env lean scripts/surface/DumpEnv.lean \
  > /tmp/crnt-env.json
```

Emits a single JSON object:

```
{ "modules": [...], "decls": [ {...}, ... ], "edges": [[from, to], ...] }
```

* `decls[i]` = `{ name, mod, kind, type, doc, axioms }` where `doc` is the `/** ... */`
  docstring with newlines flattened, `type` is the Lean pretty-printer rendering of the type,
  and `axioms` is the list reported by `Lean.collectAxioms`.
* `edges` is the *constant-level* dependency DAG: `[from, to]` means `from`'s type or value
  mentions `to`.  This is what `scripts/gen_docs.py` consumes to compute the exact set of
  declarations on every path from a hole to a downstream consumer, and to find the
  (statement, body-hash) near-duplicates across modules.

This file lives under `scripts/` and is never part of the `CRNT` or `Scaffold` surface, so
it cannot perturb `research/scripts/measure.py`.
-/

open Lean

private def jsonEscape (s : String) : String :=
  let hex := "0123456789abcdef"
  let enc (c : Char) : String :=
    if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else if c.toNat < 32 then
      "\\u00" ++ String.singleton hex[c.toNat / 16] ++ String.singleton hex[c.toNat % 16]
    else c.toString
  String.mk (s.data.toList.map enc)

/-- Wrap a pretty-printer rendering so it is safe inside a JSON string. -/
private def flatten (s : String) : String :=
  s.replace "\n" " " |>.replace "\r" " " |>.replace "\t" " "

/-- Map a declaration kind to a stable lowercase tag. -/
private def kindTag : ConstInfo → String
  | .thm _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .cdecl _ => "class"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .instInfo _ => "instance"
  | _ => "other"

namespace DumpEnv

/-- Constants mentioned by a declaration's type and, when it has one, its value. -/
def depsOf (info : ConstInfo) : Array Name := Id.run do
  let mut acc : Std.HashSet Name := {}
  for c in info.type.getUsedConstants do
    unless c.isInternal do
      acc := acc.insert c
  match info.value? with
  | some v =>
    for c in v.getUsedConstants do
      unless c.isInternal do
        acc := acc.insert c
  | none => pure ()
  return acc.toArray

end DumpEnv

open Elab Command in
elab "#dump_surface " outPath:str : command => do
  let env ← getEnv
  let modNameOf (n : Name) : String :=
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames.get! i
    | none => "<builtin>"
  let mut names := env.constants.toList.filterMap fun (n, _) =>
    if n.isInternal then none else some n
  let mut decls : Array String := #[]
  let mut edges : Array String := #[]
  let mut mods : Std.HashSet String := {}
  names := names.qsort fun a b =>
    (modNameOf a, a.toString) < (modNameOf b, b.toString)
  for n in names do
    let some info := env.constants.find? n | pure ()
    let m := modNameOf n
    mods := mods.insert m
    let ty ← withOptions (fun o => o.setBool `pp.fullNames true) do
      pure (← ppExpr info.type)
    let doc := match (← env.getDocString? n) with
      | some ds => ds.value
      | none => ""
    let axs ← Lean.collectAxioms info
    decls := decls.push
      ("{\"name\":\"" ++ jsonEscape n.toString ++ "\"," ++
       "\"mod\":\"" ++ jsonEscape m ++ "\"," ++
       "\"kind\":\"" ++ kindTag info ++ "\"," ++
       "\"type\":\"" ++ jsonEscape (flatten ty.pretty) ++ "\"," ++
       "\"doc\":\"" ++ jsonEscape (flatten doc) ++ "\"," ++
       "\"axioms\":[" ++ String.intercalate "," (axs.toList.map fun a => "\"" ++ a.toString ++ "\"") ++ "]}")
    for d in DumpEnv.depsOf info do
      if d != n then
        edges := edges.push ("[\"" ++ n.toString ++ "\",\"" ++ d.toString ++ "\"]")
  let modList := mods.toList.qsort (· < ·)
  let out :=
    "{\"modules\":[" ++ String.intercalate "," (modList.map fun m => "\"" ++ jsonEscape m ++ "\"") ++
    "],\"decls\":[" ++ String.intercalate "," decls.toList ++
    "],\"edges\":[" ++ String.intercalate "," edges.toList ++ "]}"
  IO.FS.writeFile outPath out
  logInfo m!"wrote {decls.size} decls, {edges.size} edges, {modList.length} modules"