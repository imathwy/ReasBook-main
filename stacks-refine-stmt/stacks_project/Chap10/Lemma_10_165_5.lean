import Mathlib
import stacks_project.Chap10.Definition_10_165_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w x

/-
Domain triage:
- `source-facing`: normality of the tensor product with one geometrically normal factor.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyNormal`.
- `bridge/view`: the tensor-product normality statement is derived API yielding an
  `IsNormalRing` instance; there is no extra wrapper object.

Sampled declarations in this domain:
- `Algebra.IsGeometricallyNormal` from `Definition_10_165_2`,
- `isReduced_tensorProduct_of_geometricallyReduced` from `Lemma_10_43_5`,
- `IsGeometricallyNormal.of_isLocalization` from `Lemma_10_165_3`.

Primitive data are only the field `k`, the two `k`-algebras `A` and `B`, and the hypotheses
`[IsGeometricallyNormal k A]` and `[IsNormalRing B]`. Normality of `A ⊗[k] B` is derived API and
should not be duplicated by a parallel local instance wrapper.
-/
section

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable [IsGeometricallyNormal k A] [IsNormalRing B]

/-- Lemma 10.165.5: if `A` is geometrically normal over the field `k` and `B` is a normal
`k`-algebra, then `A ⊗[k] B` is a normal ring. -/
-- Proof sketch: localize at a prime of `A ⊗[k] B` and reduce to the case where both factors are
-- domains. Approximate `B` by finite type normal `k`-subalgebras, reduce by filtered colimits to
-- finite type, and then embed the tensor product into the intersections `Frac(A) ⊗[k] B` and
-- `A ⊗[k] Frac(B)`. The geometric normality of `A` makes the first overring normal after passing
-- through finitely generated subextensions of `Frac(A)`, so integral elements over `A ⊗[k] B`
-- already lie in the tensor product itself.
@[instance]
theorem isNormalRing_tensorProduct_of_isGeometricallyNormal :
    IsNormalRing (A ⊗[k] B) := sorry

end
