import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Tactic.Recall

open scoped Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Text 1.2 names the translate of a subset by a fixed vector.
- `core/canonical`: the owner abstraction is the pointwise `VAdd` action `Set.vaddSet`, exposed by
  the notation `a +ᵥ M` on `Set β`.
- `bridge/view`: `Set.image_vadd`, `Set.singleton_vadd`, `Set.vadd_singleton`, and
  `Set.mem_vadd_set` give the textbook image/singleton/membership presentations of that owner
  action.
- Domain-style sampling used here: `Set.vaddSet`, `Set.image_vadd`, `Set.singleton_vadd`,
  `Set.vadd_singleton`, and `Set.mem_vadd_set`.
- Primitive data vs derived API: the translated set itself is primitive through the owner action;
  the displayed image, singleton, and membership formulas are derived bridge theorems.
- Layer target: keep the owner at `core/canonical`; expose source-facing formulas through
  owner-first bridge theorem surfaces, while reusing exact canonical bridge owners directly when
  they already match the intended source view.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the owner at generic `VAdd α β`; no additive/group specialization.
- Scalar check: no scalar structure is mathematically relevant in this item, so none is exposed.
- Owner check: keep canonical owner `Set.vaddSet` (notation `+ᵥ`), avoid a parallel local owner.
- Topology check: not a topology-facing statement, so no ambient/intrinsic topology refactor.
- Owner-name check: keep standard short owner names from `Set` namespace.
- Notation check: use textbook-primary notation `a +ᵥ M` on theorem surfaces.
- Upstream/downstream migration:
  upstream owner bridge is `Set.mem_vadd_set`; downstream source-facing theorem surfaces below
  reuse `Set.mem_vadd_set`, `Set.image_vadd`, `Set.singleton_vadd`, and
  `Set.vadd_singleton` directly rather than restating them as local wrapper theorems.
-/

/- Text 1.2: for a subset `M` of a `VAdd`-space and a vector `a`, the translate of `M` by `a` is
the canonical pointwise action on sets, provided by `Set.vaddSet` and written `a +ᵥ M`. -/
recall Set.vaddSet

/- The image description `{a + x | x ∈ M}` is the canonical bridge theorem `Set.image_vadd`. -/
recall Set.image_vadd

/- The singleton-set descriptions of the same translation are the owner-level bridge theorems
`Set.singleton_vadd` and `Set.vadd_singleton`. -/
recall Set.singleton_vadd
recall Set.vadd_singleton

/- The textbook membership form `x ∈ a +ᵥ M ↔ ∃ y ∈ M, a +ᵥ y = x` is the canonical bridge theorem
`Set.mem_vadd_set`. -/
recall Set.mem_vadd_set
