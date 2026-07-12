import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/- Domain-style sampling for Definition 11.2.1:
- primary domain: finiteness of algebras over a field, expressed through the underlying module;
- sampled owner declarations:
  `FiniteDimensional`,
  `Module.finrank`,
  `Module.Finite`;
- best owner abstraction: `FiniteDimensional k A`, the canonical field-specialized owner matching
  the source definition of a finite `k`-algebra;
- primitive data: none beyond the ambient `k`-algebra structure on `A`;
- derived API: the degree invariant `Module.finrank k A`;
- bridge/view: the underlying finitely generated-module spelling `Module.Finite k A`.

Source/core/bridge triage:
- `source-facing`: the textbook notion that a `k`-algebra is finite over `k`, namely
  `FiniteDimensional k A`;
- `core/canonical`: the same owner `FiniteDimensional k A`, whose mathlib implementation is the
  finitely generated-module condition;
- `bridge/view`: `Module.finrank k A` for the degree notation `[A : k]`, and `Module.Finite k A`
  for finitely generated-module arguments.

Since this item only recalls a canonical owner already present in mathlib, the public surface
should stay recall-first rather than introducing any chapter-local alias or wrapper. -/

/- Definition 11.2.1: a `k`-algebra `A` is finite over `k` when it is finite-dimensional as a
vector space over `k`. This is exactly the canonical owner `FiniteDimensional k A`. -/
recall FiniteDimensional

/- Companion recall: when `A` is finite over `k`, the degree `[A : k]` is represented by the
canonical derived natural-number invariant `Module.finrank k A`. -/
recall Module.finrank

/- Bridge recall: mathlib implements `FiniteDimensional k A` as the underlying finitely
generated-module condition `Module.Finite k A`, which remains available for downstream module-level
arguments. -/
recall Module.Finite

end
