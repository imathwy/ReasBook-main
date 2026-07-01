import stacks_project.Chap13.Lemma_13_6_2
import stacks_project.Chap15.Definition_15_67_1

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

-- Proof sketch: unfold tor-amplitude, transport a retract `K ↪ L ↠ K` through tensoring with a
-- degree-zero module and then through the homology functor, and use retract-stability of the
-- zero-object property on `ModuleCat R`.
/-- Objects of `D(R)` with tor-amplitude in `[a, b]` are stable under retracts/direct summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hK M i hi :=
    prop_of_retract IsZero (h.map (derivedTensorProduct ((single₀).obj M) ⋙ H i)) (hK M i hi)

/- Lemma 15.67.7 (1): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. This is the canonical direct-summand lemma
`ObjectProperty.IsStableUnderRetracts.of_biprod_left`, specialized to the tor-amplitude owner
predicate. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  of_biprod_left TorAmp hKL

/- Lemma 15.67.7 (2): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `L` has tor-amplitude in
`[a, b]`. This is the canonical direct-summand lemma
`ObjectProperty.IsStableUnderRetracts.of_biprod_right`, specialized to the tor-amplitude owner
predicate. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  of_biprod_right TorAmp hKL

end

end CategoryTheory
