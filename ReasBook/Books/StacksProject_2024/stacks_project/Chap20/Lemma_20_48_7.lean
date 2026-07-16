import StacksProject_2024.stacks_project.Chap20.Lemma_20_48_5

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable {a b c d : ℤ}

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
variable {K L : DMod}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules X))]

/-
Domain-style sampling for Lemma 20.48.7:
- primary domain: tor-amplitude in `DMod` and its behavior under the canonical derived tensor
  product;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn`,
  `AlgebraicGeometry.RingedSpace.stalkDerived`,
  `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_iff_forall_stalk`;
- best owner abstraction:
  `source-facing`: the ringed-space tensor-closure statement below;
  `core/canonical`: `HasTorAmplitudeIn` together with the derived tensor owner `K ⊗^L L`;
  `bridge/view`: the stalkwise companion theorem `stalkDerived_hasTorAmplitudeIn_tensor`, which
    expresses the source argument at the canonical stalk bridge from Lemma `20.48.5`.

This file keeps only the source-facing theorem and its stalkwise bridge. The previous local
point-space and site-point wrapper layer was redundant once `stalkDerived` already existed as the
canonical Chapter 20 owner. -/

-- Proof sketch: identify the stalk of `K ⊗^L L` with the derived tensor product of the stalks
-- over the local ring `𝒪_{X, x}`, then apply the module-category
-- additivity theorem for tor-amplitude under derived tensor product.
/-- Stalkwise form of Lemma 20.48.7: if the derived stalks `((stalkDerived x).obj K)` and
`((stalkDerived x).obj L)` have tor-amplitude in `[a, b]` and `[c, d]`, then the stalk of
`K ⊗^L L` has
tor-amplitude in `[a + c, b + d]`. -/
theorem stalkDerived_hasTorAmplitudeIn_tensor
    (x : X)
    (hK : CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj K) a b)
    (hL : CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj L) c d) :
    CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj (K ⊗^L L)) (a + c) (b + d) := by
  sorry

namespace HasTorAmplitudeIn

-- Proof sketch: apply the stalkwise criterion from Lemma `20.48.5` and use the preceding
-- stalkwise tensor statement at each point.
/-- Lemma 20.48.7: if `K` has tor-amplitude in `[a, b]` and `L` has tor-amplitude in `[c, d]`,
then `K ⊗^L L` has tor-amplitude in `[a + c, b + d]`. -/
@[stacks 09J4]
theorem tensor
    {K L : DMod} {a b c d : ℤ}
    (hK : HasTorAmplitudeIn K a b)
    (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗^L L) (a + c) (b + d) := by
  have hK' : ∀ x : X, CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj K) a b :=
    HasTorAmplitudeIn.forall_stalk hK
  have hL' : ∀ x : X, CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj L) c d :=
    HasTorAmplitudeIn.forall_stalk hL
  refine hasTorAmplitudeIn_of_forall_stalk fun x ↦
    stalkDerived_hasTorAmplitudeIn_tensor x (hK' x) (hL' x)

end HasTorAmplitudeIn

end

end AlgebraicGeometry.RingedSpace
