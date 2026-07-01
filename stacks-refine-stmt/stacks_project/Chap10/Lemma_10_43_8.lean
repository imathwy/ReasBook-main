import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable [Algebra.IsSeparable k K]

/-
Layer note:
- `source-facing`: the existence of a localization presentation for the multiplication map
  `K ⊗[k] K → K`;
- `core/canonical`: separability is owned upstream by `Algebra.FormallyEtale` /
  `Algebra.FormallyUnramified`, organized around the tensor-product multiplication map `lmul'`;
- `bridge/view`: this lemma keeps the Stacks source conclusion that the diagonal map is a
  localization, with the submonoid as derived witness data rather than primitive structure.
-/
/-- Lemma 10.43.8 (Tag 0C2X): for a separable algebraic extension `K / k`, the tensor-product
multiplication map `K ⊗[k] K →ₐ[k] K` is a localization map at some multiplicative subset of
`K ⊗[k] K`. -/
-- Proof sketch: the owner abstraction is the formally étale / formally unramified structure
-- attached to a separable field extension. In the finite separable case, choose a primitive
-- element, identify `K ⊗[k] K` with `K[X] / (P)` for the minimal polynomial `P`, factor
-- `P = (X - α) Q`, and localize away from the image of `Q`. For a general separable algebraic
-- extension, write `K` as the directed union of its finite separable subextensions and take the
-- union of the corresponding multiplicative subsets.
@[stacks 0C2X]
theorem exists_submonoid_tensorProduct_self_isLocalization :
    ∃ S : Submonoid (K ⊗[k] K),
      S.IsLocalizationMap (lmul' k) := sorry

end
