# tools

External code generators that emit Lean certificate files against the `CRNT` API live
here. They are independent of the Lean package and impose no runtime dependency on it.

The intended layout (not yet populated):

```text
tools/
├── python/   # JSON/SBML → Lean certificate generator
├── rust/
└── julia/
```

A generator reads a network description (JSON, SBML, SBOL-derived, BioCRNpyler/Catalyst
output) and writes a `.lean` file following the emission contract in
[`../docs/generated-certificates.md`](../docs/generated-certificates.md): a `Species`
type, complex definitions, a `Rxn` type, a `reaction` map, the `Network` value, and the
property checks. Lean then verifies the emitted certificate.
