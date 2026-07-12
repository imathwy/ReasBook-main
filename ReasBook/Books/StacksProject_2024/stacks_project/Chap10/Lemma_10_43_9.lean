import StacksProject_2024.Chap10.Definition_10_43_1
import StacksProject_2024.Chap10.Lemma_10_43_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

open scoped TensorProduct

variable {k : Type u} {k' : Type v} {A : Type w}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
variable [Algebra.IsSeparable k k']

/- Domain triage:
- `source-facing`: invariance of geometric reducedness under a separable algebraic change of the
  ground field.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyReduced`.
- `bridge/view`: Definition `10.43.1` provides the owner-level reformulation in terms of reduced
  tensor products, and Lemma `10.43.6` supplies the separable-algebraic reducedness input used in
  the proof.

Primitive data are the field-extension hypotheses and the ambient `k'`-algebra `A`; geometric
reducedness itself stays in the owner class rather than being repackaged by a local wrapper.
-/
/-- Lemma 10.43.9 (Tag 0C2Y): for a separable algebraic field extension `k' / k`, a `k'`-algebra
`A` is geometrically reduced over `k` if and only if it is geometrically reduced over `k'`. -/
@[stacks 0C2Y]
theorem isGeometricallyReduced_iff_of_isSeparable :
    IsGeometricallyReduced k A ↔ IsGeometricallyReduced k' A := by
  constructor
  · intro h
    -- Owner-level strategy: compare the `k'`-geometric test object
    -- `AlgebraicClosure k' ⊗[k'] A` with the larger `k`-base-changed tensor product, and use
    -- reducedness of the latter coming from `h`.
    sorry
  · intro h
    -- Owner-level strategy: `AlgebraicClosure k ⊗[k] k'` is reduced by Lemma `10.43.6`; after
    -- tensoring over `k'` with `A`, the canonical tensor reassociation identifies this with the
    -- `k`-geometric test object for `A`.
    sorry

end

end Algebra
