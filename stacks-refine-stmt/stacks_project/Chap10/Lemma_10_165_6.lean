import Mathlib
import stacks_project.Chap10.Definition_10_165_2
import stacks_project.Chap10.Lemma_10_165_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {k : Type u} {k' : Type v} {A : Type w}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
variable [Algebra.IsSeparable k k']

/- Domain triage:
- `source-facing`: invariance of geometric normality under a separable algebraic extension of the
  ground field.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyNormal`.
- `bridge/view`: the sampled owner-style declarations are:
  `Definition_10_165_2` for the owner predicate itself,
  `IsGeometricallyNormal.of_isLocalization` from Lemma `10.165.3`,
  `isNormalRing_tensorProduct_of_isGeometricallyNormal` from Lemma `10.165.5`,
  and the parallel owner-level separable-base-change theorem
  `isGeometricallyReduced_iff_of_isSeparable` from Lemma `10.43.9`.

Primitive data are only the field-extension hypotheses and the ambient `k'`-algebra `A`.
Geometric normality stays in the owner class, and the localization/tensor-product normality facts
remain derived API rather than primitive fields of a parallel wrapper.
-/
/-- Lemma 10.165.6: for a separable algebraic field extension `k' / k`, a `k'`-algebra `A` is
geometrically normal over `k` if and only if it is geometrically normal over `k'`. -/
-- Proof sketch: for `→`, every field extension of `k'` is in particular a field extension of `k`,
-- so the required normality statement is immediate from the owner definition. For `←`, any field
-- extension of `k` can be tensored with `k'`; separability makes the intermediate tensor product
-- geometrically normal over the larger field, and Lemmas `10.165.5` and `10.165.3` provide the
-- tensor-product and localization steps needed to descend normality back to the original
-- base-changed ring.
theorem isGeometricallyNormal_iff_of_isSeparable :
    IsGeometricallyNormal k A ↔ IsGeometricallyNormal k' A := sorry

end

end Algebra
