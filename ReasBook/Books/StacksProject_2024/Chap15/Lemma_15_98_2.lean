import Mathlib
import StacksProject_2024.Chap15.Lemma_15_92_14
import StacksProject_2024.Chap15.Lemma_15_98_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "F" => idealPowerQuotientRingSystem I

/- Domain-style sampling for Lemma 15.98.2:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, together with
  pseudo-coherence, derived base change, and derived completeness;
- sampled owner declarations:
  `IdealPowerQuotientDerivedTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChangeComparison`,
  `CategoryTheory.IsDerivedLimit`,
  `IsAdicComplete`,
  `derivedLimit_of_idealPowerQuotientTower_isDerivedComplete`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing specialized tower owner
  `IdealPowerQuotientDerivedTower I` from `Lemma_15_98_4`, together with its canonical fixed-base
  tower `stageRestrictionToBaseTower F A T` and stagewise base-change comparison
  `stageDerivedBaseChangeComparison T n`;
- primitive vs. derived:
  primitive data are the specialized tower `T : IdealPowerQuotientDerivedTower I`, the chosen
  derived-limit object `K : D(A)`, the source-essential adic-completeness hypothesis
  `IsAdicComplete I A`, and the textbook pseudo-coherence/base-change hypotheses on the stages;
  derived API is the pseudo-coherence and derived-completeness conclusion for `K`, together with
  the induced quotient-stage base-change identification.

Source/core/bridge triage:
- `source-facing`: the two theorem statements in this file;
- `core/canonical`: `K.IsPseudoCoherent`, `K.IsDerivedCompleteWithRespectTo I`, and
  `CategoryTheory.IsDerivedLimit`;
- `bridge/view`: `stageRestrictionToBaseTower F A`,
  `stageDerivedBaseChangeComparison`, and the quotient-stage base-change object
  `K ⊗[A]^L[A ⧸ I ^ (n + 1)]`, all reused directly from `Lemma_15_98_4` and
  `Lemma_15_98_5`. -/

-- Proof sketch: specialize Lemma `15.98.1` to the ideal-power quotient tower to obtain
-- pseudo-coherence of the chosen derived limit `K`, then combine it with the specialized
-- derived-completeness result from Lemma `15.98.5` for the same tower.
/-- Lemma 15.98.2: let `A` be a ring, let `I ⊆ A` be an ideal, and let `K` be a chosen derived
limit of the canonical fixed-base tower attached to a compatible tower
`T : IdealPowerQuotientDerivedTower I` of objects `K_n ∈ D(A / I^(n+1))` viewed over `A`.
Assume `A` is `I`-adically complete, the first stage `K_1` is pseudo-coherent, and the stagewise
derived reductions
`K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1) → K_n` induced by `T.stepMap` are
isomorphisms. Then `K` is pseudo-coherent and derived complete with respect to `I`. Here stage
`0` corresponds to the textbook object `K_1`. -/
theorem derivedLimit_of_idealPowerQuotientTower_isPseudoCoherent_and_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n)) :
    K.IsPseudoCoherent ∧ K.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: this is the base-change part of Lemma `15.98.1` specialized to the ideal-power
-- quotient tower `A / I^(n+1)`, whose transition maps are the canonical quotient morphisms.
/-- For the quotient tower of Lemma 15.98.2, if `A` is `I`-adically complete, then the derived
base change of the chosen limit object `K` to each quotient stage `A / I^(n+1)` recovers the
corresponding stage object `K_n`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_pseudoCoherent_derivedLimit
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))
    (n : ℕ) : IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := sorry

end
