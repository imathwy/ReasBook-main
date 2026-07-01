import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Definition 9.20.6:
- primary domain: trace pairings for finite field extensions;
- sampled owner declarations: `Algebra.traceForm`, `Algebra.traceForm_apply`,
  `Algebra.traceForm_isSymm`, `Algebra.traceForm_toMatrix`;
- best owner abstraction:
  - `source-facing`: the trace pairing `Q_{L/K}` of the finite field extension `L / K`;
  - `core/canonical`: the bilinear form `Algebra.traceForm K L`;
  - `bridge/view`: the evaluation formula `Algebra.traceForm_apply`, symmetry
    `Algebra.traceForm_isSymm`, and basis-matrix presentation `Algebra.traceForm_toMatrix`;
- primitive data: only the canonical owner bilinear form `Algebra.traceForm K L`;
- derived API: its pointwise trace formula, symmetry, and matrix expressions in a basis.

This item is therefore already at the correct `core/canonical` owner layer, so refinement should
stay as direct recall/use rather than introducing any local trace-pairing wrapper.
-/

/- Definition 9.20.6: for a finite field extension `L/K`, the trace pairing is the symmetric
`K`-bilinear form `Algebra.traceForm K L`, i.e. the form sending `(α, β)` to
`Trace_{L/K}(α * β)`. -/
recall Algebra.traceForm

/- Companion recall: the defining formula for the trace pairing is the existing theorem
`Algebra.traceForm_apply`, identifying `Algebra.traceForm K L α β` with `Algebra.trace K L (α * β)`.
-/
recall Algebra.traceForm_apply

/- Companion recall: the trace pairing is symmetric by the existing theorem
`Algebra.traceForm_isSymm`. -/
recall Algebra.traceForm_isSymm
