import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_2
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1_Core

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

open RingedSite.Hom

section

variable {X : RingedSite.{u, v}}

local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)
variable [MonoidalCategory (ModuleDerived X)]
variable {a b : ℤ}
local notation "TorAmp" => fun K : DMod ↦ HasTorAmplitudeIn K a b

/- Domain-style sampling for Lemma 21.46.8:
- primary domain: tor-amplitude on `D(𝒪_X)` and its direct-summand stability;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction:
  `source-facing`: the Chapter 21 direct-summand statements for tor-amplitude on a ringed site;
  `core/canonical`: the object property `TorAmp := fun K : DMod ↦ HasTorAmplitudeIn K a b`
    together with its retract-stability instance;
  `bridge/view`: tensor a retract by `ℱ[0]`, apply homology, and use the generic retract-stable
    owner `IsZero`.
- primitive data: the source-facing tor-amplitude predicate `HasTorAmplitudeIn K a b`;
- derived API: retract stability, the source-facing biproduct/summand theorem, and its left/right
  projection companions.

This keeps the Stacks statement source-facing, but removes the ad hoc retract packaging in favor of
the canonical owner-level direct-summand API already used elsewhere in the repository. -/

/-- Objects of `D(𝒪_X)` with tor-amplitude in `[a, b]` are stable under retracts/direct
summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hK ℱ i hi := by
    let F : DMod ⥤ DMod := (tensoringRight DMod).obj ((single0).obj ℱ)
    simpa [F] using
      prop_of_retract IsZero (h.map (F ⋙ H i)) (by simpa [F] using hK ℱ i hi)

/-- Lemma 21.46.8: if `K ⊞ L` has tor-amplitude in `[a, b]`, then both summands have
tor-amplitude in `[a, b]`. -/
@[stacks 08G3]
theorem hasTorAmplitudeIn_summands_of_biprod
    (K L : DMod) [HasBinaryBiproduct K L] (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b ∧ HasTorAmplitudeIn L a b :=
  ⟨of_biprod_left TorAmp hKL, of_biprod_right TorAmp hKL⟩

/-- The left-projection companion to `hasTorAmplitudeIn_summands_of_biprod`. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod) [HasBinaryBiproduct K L] (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  of_biprod_left TorAmp hKL

/-- The right-projection companion to `hasTorAmplitudeIn_summands_of_biprod`. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod) [HasBinaryBiproduct K L] (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  of_biprod_right TorAmp hKL

end

end SheafOfModules.RingedSite
