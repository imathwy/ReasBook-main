import StacksProject_2024.stacks_project.Chap20.Definition_20_48_1_Core
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable {a b : ℤ}

variable [CategoryWithHomology (Modules X)]
variable [MonoidalCategory (DerivedCategory (Modules X))]

/- Domain-style sampling for Lemma 20.48.8:
- primary domain: tor-amplitude on `D(𝒪_X)` and its direct-summand stability;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn`,
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction:
  `source-facing`: the Chapter 20 direct-summand statements for tor-amplitude on a ringed space;
  `core/canonical`: the object property `TorAmp := fun E : D(𝒪_X) ↦
    HasTorAmplitudeIn E a b` together with its retract-stability instance;
  `bridge/view`: transport of a retract through tensoring by `ℱ[0]` and the homology
    functor, then application of the generic retract-stability owner for `IsZero`.
- primitive data: the source-facing tor-amplitude predicate `HasTorAmplitudeIn E a b`;
- derived API: retract stability and the left/right biproduct consequences below.

This file therefore stays source-facing, but removes the ad hoc biproduct proof wheel in favor of
the canonical owner-level retract-stability abstraction already used for the analogous ringed-site
statement. -/

local notation "DMod" => DerivedCategory (Modules X)
local notation "ModX" => Modules X
local notation "H" => DerivedCategory.homologyFunctor ModX
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)
local notation "TorAmp" => fun E : DMod ↦ HasTorAmplitudeIn E a b

/-- Helper for Lemma 20.48.8: tor-amplitude descends along retracts in `D(𝒪_X)`. -/
lemma hasTorAmplitudeIn_of_retract {K L : DMod} (h : Retract K L)
    (hL : HasTorAmplitudeIn L a b) : HasTorAmplitudeIn K a b := by
  intro ℱ i hi
  let F : DMod ⥤ DMod := (tensoringRight DMod).obj ((single0).obj ℱ)
  -- Route correction: descend the Chapter 20 vanishing condition directly instead of
  -- changing to the later Chapter 21 ringed-site theorem.
  -- Tensor the retract by `ℱ[0]`, apply homology, and use retract-stability of `IsZero`.
  simpa [F] using
    prop_of_retract IsZero (h.map (F ⋙ H i)) (by simpa [F] using hL ℱ i hi)

/-- Helper for Lemma 20.48.8: tor-amplitude in `[a, b]` is stable under retracts/direct
summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hL := by
    -- Reuse the local retract-descent lemma so the biproduct theorem is dependency-closed.
    exact hasTorAmplitudeIn_of_retract (a := a) (b := b) h hL

/-- Lemma 20.48.8: if `K ⊞ L` has tor-amplitude in `[a, b]`, then both summands have
tor-amplitude in `[a, b]`. -/
@[stacks 08CK]
theorem hasTorAmplitudeIn_summands_of_biprod
    (K L : DMod) (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b ∧ HasTorAmplitudeIn L a b := by
  -- Each biproduct summand is a retract, so the generic owner-level API gives both conclusions.
  exact ⟨of_biprod_left TorAmp hKL, of_biprod_right TorAmp hKL⟩

/-- The left-projection companion to `hasTorAmplitudeIn_summands_of_biprod`. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod) (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b := by
  -- Project the left summand from the already-proved direct-summand statement.
  exact (hasTorAmplitudeIn_summands_of_biprod (X := X) (a := a) (b := b) K L hKL).1

/-- The right-projection companion to `hasTorAmplitudeIn_summands_of_biprod`. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod) (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b := by
  -- The right summand is the other projection of the same direct-summand statement.
  exact (hasTorAmplitudeIn_summands_of_biprod (X := X) (a := a) (b := b) K L hKL).2

end

end AlgebraicGeometry.RingedSpace
