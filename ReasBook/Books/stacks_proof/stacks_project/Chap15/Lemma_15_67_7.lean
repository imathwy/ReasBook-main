import stacks_proof.stacks_project.Chap13.Lemma_13_6_2
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open ObjectProperty.IsStableUnderRetracts
open DerivedCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {a b : ℤ}

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)
local notation "H" => homologyFunctor (ModuleCat R)
local notation "TorAmp" => fun K : DMod ↦ HasTorAmplitudeIn K a b

/- Domain-style sampling for Lemma 15.67.7:
- primary domain: tor-amplitude as an object property on `D(R)`, together with the generic
  retract/direct-summand API for object properties in additive categories;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the owner layer is the object property
  `fun K : DMod ↦ HasTorAmplitudeIn K a b` together with its retract-stability instance; the
  biproduct/summand statements are derived API from the canonical generic lemmas `of_biprod_left`
  and `of_biprod_right`;
- primitive vs. derived:
  primitive data are the tor-amplitude owner predicate `HasTorAmplitudeIn`;
  derived API is its retract stability and the direct-summand consequences.

Source/core/bridge triage:
- `source-facing`: the textbook direct-summand consequences for tor-amplitude;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts` on
  `fun K : DMod ↦ HasTorAmplitudeIn K a b`;
- `bridge/view`: the specialization of the generic owner lemmas `of_biprod_left` and
  `of_biprod_right` to this tor-amplitude predicate.

This file therefore keeps the genuinely new owner instance and derives the textbook biproduct
clauses directly from the canonical owner API instead of maintaining parallel local copies.
-/

/-- Helper for Lemma 15.67.7: tor-amplitude in `[a, b]` is stable under retracts. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hK M i hi :=
    -- Transport the retract through derived tensor product and homology, then descend
    -- the vanishing statement along retract-stability of `IsZero`.
    prop_of_retract IsZero (h.map (derivedTensorProduct ((single₀).obj M) ⋙ H i)) (hK M i hi)

/-- Lemma 15.67.7: if `K ⊞ L` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. -/
@[stacks 066G]
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  -- The left summand is a retract of the biproduct, so the generic retract-stable owner API
  -- gives the tor-amplitude conclusion immediately.
  of_biprod_left TorAmp hKL

/-- Helper for Lemma 15.67.7: if `K ⊞ L` has tor-amplitude in `[a, b]`, then the right summand
`L` has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  -- The same retract argument applies to the right summand through the canonical biproduct maps.
  of_biprod_right TorAmp hKL

end

end CategoryTheory
