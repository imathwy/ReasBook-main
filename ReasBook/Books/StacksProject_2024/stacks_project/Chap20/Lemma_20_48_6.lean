import StacksProject_2024.Chap15.Lemma_15_67_5
import StacksProject_2024.Chap20.Lemma_20_48_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable {a b : ℤ}

local notation "DMod" => DerivedCategory (Modules X)

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

/- Domain-style sampling for Lemma 20.48.6:
- primary domain: tor-amplitude in the derived category of module sheaves on a ringed space and
  its behavior under distinguished triangles;
- sampled owner declarations:
  `CategoryTheory.HasTorAmplitudeIn`,
  `CategoryTheory.hasTorAmplitudeIn_obj₃_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₂_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₁_of_distinguishedTriangle`,
  `hasTorAmplitudeIn_iff_forall_stalk`,
  `stalkDerived`;
- best owner abstraction: the chapter owner is
  `CategoryTheory.HasTorAmplitudeIn` on stalkwise derived module categories, with
  `hasTorAmplitudeIn_iff_forall_stalk` as the canonical ringed-space bridge;
- primitive vs. derived:
  primitive data are the ringed-space tor-amplitude predicate `HasTorAmplitudeIn` and the derived
  stalk functor `stalkDerived`;
  derived API are the three distinguished-triangle closure statements below, obtained by applying
  the canonical module-category theorem stalkwise;
- source/core/bridge triage:
  `source-facing`: the three ringed-space closure statements below;
  `core/canonical`: `CategoryTheory.HasTorAmplitudeIn` together with the Chapter 15
    distinguished-triangle theorem;
  `bridge/view`: `stalkDerived` and `hasTorAmplitudeIn_iff_forall_stalk`, which transport between
    ringed-space objects and the canonical stalkwise module-category owner.

This file keeps the Stacks ringed-space statements as the public surface, but removes the parallel
proof wheel by deriving them directly from the canonical module-category owner theorem through the
stalk bridge. -/

-- Proof sketch: apply `- ⊗^L_{𝒪_X} ℱ[0]` to the distinguished triangle for an arbitrary module
-- sheaf `ℱ`, use that derived tensor preserves
-- distinguished triangles, and read off the vanishing range for the third term from the
-- associated long exact homology sequence.
/-- Lemma 20.48.6 (1): in a distinguished triangle in `D(𝒪_X)`, if the first term has
tor-amplitude in `[a + 1, b + 1]` and the second term has tor-amplitude in `[a, b]`, then the
third term has tor-amplitude in `[a, b]`. -/
@[stacks 08CJ]
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := by
  refine hasTorAmplitudeIn_of_forall_stalk fun x ↦ ?_
  exact
    CategoryTheory.hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
      ((stalkDerived x).mapTriangle.obj T)
      ((stalkDerived x).map_distinguished T hT)
      (h₁.forall_stalk x) (h₂.forall_stalk x)

-- Proof sketch: tensor with an arbitrary module sheaf placed in degree `0`, use the long exact
-- homology sequence of the distinguished triangle, and apply two-out-of-three for vanishing in
-- degrees outside `[a, b]`.
/-- Lemma 20.48.6 (2): in a distinguished triangle in `D(𝒪_X)`, if the first and third
terms have tor-amplitude in `[a, b]`, then the second term has tor-amplitude in `[a, b]`. -/
@[stacks 08CJ]
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := by
  refine hasTorAmplitudeIn_of_forall_stalk fun x ↦ ?_
  exact
    CategoryTheory.hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
      ((stalkDerived x).mapTriangle.obj T)
      ((stalkDerived x).map_distinguished T hT)
      (h₁.forall_stalk x) (h₃.forall_stalk x)

-- Proof sketch: rotate the distinguished triangle and reduce to part `(1)`, which shifts the
-- tor-amplitude interval on the first vertex by one exactly as required.
/-- Lemma 20.48.6 (3): in a distinguished triangle in `D(𝒪_X)`, if the second term has
tor-amplitude in `[a + 1, b + 1]` and the third term has tor-amplitude in `[a, b]`, then the
first term has tor-amplitude in `[a + 1, b + 1]`. -/
@[stacks 08CJ]
theorem hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := by
  refine hasTorAmplitudeIn_of_forall_stalk fun x ↦ ?_
  exact
    CategoryTheory.hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
      ((stalkDerived x).mapTriangle.obj T)
      ((stalkDerived x).map_distinguished T hT)
      (h₂.forall_stalk x) (h₃.forall_stalk x)

end

end AlgebraicGeometry.RingedSpace
