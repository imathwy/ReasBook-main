import Mathlib
import stacks_project.Chap15.Lemma_15_67_7
import stacks_project.Chap20.Lemma_20_48_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

variable {a b : ℤ}

local notation "DMod" => ModuleDerived X
local notation "TorAmp" => fun E : DMod ↦ HasTorAmplitudeIn E a b

/- Domain-style sampling for Lemma 20.48.8:
- primary domain: retract-stable object properties in derived categories, with ringed-space
  tor-amplitude as the source-facing predicate and module-category tor-amplitude as the canonical
  owner abstraction;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`,
  `CategoryTheory.hasTorAmplitudeIn_isStableUnderRetracts`,
  `hasTorAmplitudeIn_iff_forall_stalk`;
- best owner abstraction: the source-facing predicate remains
  `fun E : DMod ↦ HasTorAmplitudeIn E a b`, but its retract-stability is derived from the
  canonical Chapter 15 owner instance for `CategoryTheory.HasTorAmplitudeIn` via the stalk bridge
  `hasTorAmplitudeIn_iff_forall_stalk`;
- primitive vs. derived:
  primitive data are the ringed-space tor-amplitude predicate and the canonical derived stalk
  functors;
  the retract-stability instance and the left/right biproduct consequences are derived API;
- source/core/bridge triage:
  `source-facing`: the two textbook direct-summand consequences;
  `core/canonical`: `CategoryTheory.HasTorAmplitudeIn` together with
    `ObjectProperty.IsStableUnderRetracts`;
  `bridge/view`: `stalkDerived`, `hasTorAmplitudeIn_iff_forall_stalk`,
    `of_biprod_left`, and `of_biprod_right`.

Accordingly, this file exposes the owner-level retract-stability instance and derives the two
source-facing biproduct lemmas from the canonical object-property API, transporting the proof to
the Chapter 15 module-category owner stalkwise instead of keeping a parallel local retract
argument. -/

/-- Objects of `D(\mathcal O_X)` with tor-amplitude in `[a, b]` are stable under retracts/direct
summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hE := by
    rw [hasTorAmplitudeIn_iff_forall_stalk] at hE ⊢
    intro x
    exact prop_of_retract
      (fun E : DerivedCategory (ModuleCat (stalkCommRing x)) ↦
        CategoryTheory.HasTorAmplitudeIn E a b)
      (h.map (stalkDerived x)) (hE x)

/-- Lemma 20.48.8 (1): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  of_biprod_left TorAmp hKL

/-- Lemma 20.48.8 (2): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `L` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  of_biprod_right TorAmp hKL

end

end AlgebraicGeometry.RingedSpace
