import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap15.«15_60_1_1»
import stacks_proof.stacks_project.Chap15.Lemma_15_88_1_Base
import stacks_proof.stacks_project.Chap15.Lemma_15_60_3
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.Definition_15_92_4
import stacks_proof.stacks_project.Chap15.Lemma_15_98_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open DerivedModuleTower
open Opposite
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.98.4:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, with stagewise
  derived base change along the quotient transition maps;
- sampled owner declarations:
  `sequentialRingSystem`,
  `DerivedModuleTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChange`,
  `stageDerivedBaseChangeComparison`;
- best owner abstraction: the source-facing ideal-power quotient tower should be a specialization
  of the chapter bridge owner `DerivedModuleTower`, with the fixed-base restriction now owned by
  the generic bridge `stageRestrictionToBaseTower` specialized to the quotient maps
  `A → A / I^(n+1)`;
- primitive data: the quotient stages `A / I^(n+1)`, their transition maps, the quotient
  algebra maps `A → A / I^(n+1)`, realized through `Ideal.Quotient.factorPow`, and the
  specialized derived tower itself;
- derived API: the specialized tower owner `IdealPowerQuotientDerivedTower`, the canonical
  fixed-base tower `stageRestrictionToBaseTower F A`, and the theorem surface specialized from the
  upstream base-change owners `stageDerivedBaseChange` and
  `stageDerivedBaseChangeComparison`.

Source/core/bridge triage:
- `source-facing`: the specialized ideal-power quotient tower and the two theorem statements;
- `core/canonical`: `DerivedModuleTower` and the upstream stagewise base-change owners;
- `bridge/view`: the fixed-base restriction tower over `A`, owned by
  `stageRestrictionToBaseTower` and specialized to the quotient algebra maps
  `A → A / I^(n+1)`. -/

/-- The sequential inverse system of quotient rings `A / I^(n+1)`. -/
abbrev idealPowerQuotientRingSystem : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  sequentialRingSystem (fun n ↦ A ⧸ I ^ (n + 1))
    (fun n ↦ Ideal.Quotient.factorPowSucc I (n + 1))

local notation "F" => idealPowerQuotientRingSystem I

/-- Each stage ring in the quotient system is naturally an `A`-algebra. -/
instance idealPowerQuotientStageRingAlgebra (n : ℕ) :
    Algebra A (stageRing F n) := by
  change Algebra A (A ⧸ I ^ (n + 1))
  exact RingHom.toAlgebra (Ideal.Quotient.mk (I ^ (n + 1)))

private theorem idealPowerQuotient_algebraMap_comp (n : ℕ) :
    algebraMap A (stageRing F n) =
      (stageTransitionRingHom F n).comp (algebraMap A (stageRing F (n + 1))) := by
  ext x
  change (algebraMap A (A ⧸ I ^ (n + 1))) x =
      ((stageTransitionRingHom F n).comp (algebraMap A (A ⧸ I ^ (n + 2)))) x
  have htransition : stageTransitionRingHom F n = Ideal.Quotient.factorPowSucc I (n + 1) := by
    simp [idealPowerQuotientRingSystem, sequentialRingSystem, stageTransitionRingHom]
  rw [htransition]
  rfl

/-- The stage transition in the quotient system is compatible with the ambient `A`-algebra
structure. -/
instance idealPowerQuotientStageRingIsScalarTower (n : ℕ) :
    IsScalarTower A (stageRing F (n + 1)) (stageRing F n) := by
  exact IsScalarTower.of_algebraMap_eq' (idealPowerQuotient_algebraMap_comp I n)

/-- A compatible tower of derived quotient stages `K_n ∈ D(A / I^(n+1))`, expressed through the
chapter owner `DerivedModuleTower` specialized to the ideal-power quotient system. -/
abbrev IdealPowerQuotientDerivedTower :=
  DerivedModuleTower (stageRing F) (stageTransitionRingHom F)

-- Proof sketch: specialize Lemma `15.98.3` to the tower `A / I^(n+1)`, whose transition maps are
-- the canonical quotient morphisms with nilpotent kernels. The perfectness of stage `0`
-- corresponds to the textbook hypothesis that `K_1` is perfect, and the stagewise derived
-- base-change hypothesis identifies the tower with its reductions. Once perfection is known,
-- Lemma `15.92.8` applied to the `I`-adically complete ring `A` yields derived completeness.
/-- Lemma 15.98.4: if `A` is `I`-adically complete, `K_1` is perfect, and a compatible tower of
objects `K_n ∈ D(A / I^(n+1))` has derived reductions
`K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1) ≅ K_n`, then any derived-limit object
`K ∈ D(A)` of the tower viewed over `A` is perfect and derived complete with respect to `I`.
Here stage `0` corresponds to the textbook object `K_1`. -/
@[stacks 09AW]
theorem derivedLimit_of_idealPowerQuotientTower_isPerfect_and_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I)
    (K : DMod)
    (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPerfect)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n)) :
    K.IsPerfect ∧ K.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: this is the base-change part of Lemma `15.98.3` specialized to the tower of
-- quotients `A / I^(n+1)`, using the canonical quotient transition maps between the stages.
/-- For the quotient tower of Lemma `15.98.4`, the derived base change of the chosen limit object
`K` to each stage `A / I^(n+1)` recovers the stage object `K_n`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_derivedLimit
    (T : IdealPowerQuotientDerivedTower I)
    (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPerfect)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))
    (n : ℕ) : IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := sorry

end
