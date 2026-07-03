import Mathlib
import StacksProject_2024.Chap10.Lemma_10_166_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {k : Type u} {k' : Type v} {A : Type w}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
variable [Algebra.IsSeparable k k']

/- Domain triage:
- `source-facing`: invariance of geometric regularity under a separable algebraic extension of the
  ground field.
- `core/canonical`: the owner abstraction is `IsGeometricallyRegular`.
- `bridge/view`: the sampled owner-style declarations are
  `IsGeometricallyRegular`,
  `isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing`,
  `isGeometricallyRegular_of_directed_iSup_subfields`,
  and the parallel owner-level separable-base-change theorems
  `isGeometricallyReduced_iff_of_isSeparable` and
  `isGeometricallyNormal_iff_of_isSeparable`.

Primitive data are only the field-extension hypotheses and the ambient `k'`-algebra `A`.
Geometric regularity stays in the owner class, while the tensor-product regularity tests, the
finite-stage reduction from Lemma `10.166.5`, and the smoothness step through the multiplication
map remain derived API rather than primitive fields of a local wrapper.
-/
-- Proof sketch: if `A` is geometrically regular over `k'`, then for any finite purely
-- inseparable extension `K / k`, the tensor product `K ⊗[k] k'` is a field and
-- `K ⊗[k] A ≃ (K ⊗[k] k') ⊗[k'] A`, so regularity over `k'` implies regularity over `k`.
-- Conversely, write the separable algebraic extension `k' / k` as a filtered colimit of finite
-- separable subextensions, reduce to the finite separable case by Lemma `10.166.5`, note that
-- `A ⊗[k] k'` is geometrically regular over `k'`, and then apply Lemma `10.166.4` to the smooth
-- map `A ⊗[k] k' → A` induced by the étale multiplication map `k' ⊗[k] k' → k'`.
/-- Lemma 10.166.6: for a separable algebraic field extension `k' / k`, a `k'`-algebra `A` is
geometrically regular over `k` if and only if it is geometrically regular over `k'`. -/
theorem isGeometricallyRegular_iff_of_isSeparable :
    IsGeometricallyRegular k A ↔ IsGeometricallyRegular k' A := sorry

end

end Algebra
