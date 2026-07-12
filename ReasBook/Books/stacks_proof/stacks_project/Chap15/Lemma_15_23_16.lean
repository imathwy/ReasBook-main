import StacksProject_2024.Chap15.Lemma_15_23_4
import StacksProject_2024.Chap15.Lemma_15_23_11
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Module
open LocalizedModule (AtPrime)

/-
Domain-style sampling:
- primary domain: reflexive finite modules over commutative Noetherian rings and their Serre condition
  `(S₂)`, with prime-local depth bounds and double-dual linear maps as the local bridge;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.SerreConditionS`,
  `Module.IsReflexive.instSerreConditionSTwo`,
  `moduleDepth`,
  `isReflexive_localization_tfae`,
  `linearMap_serreConditionS_two_of_codomain`;
- best owner abstraction:
  `Module.IsReflexive` is the canonical owner of the source hypothesis and
  `Module.SerreConditionS` is the canonical owner of the conclusion. Clause `(1)` uses the
  localized owner theorem `isReflexive_localization_tfae` together with `moduleDepth` on
  `Localization.AtPrime p.asIdeal`, while clause `(2)` should be implemented as the canonical
  `Module.SerreConditionS` instance `Module.IsReflexive.instSerreConditionSTwo` and recalled
  directly rather than duplicated by a parallel theorem;
- source/core/bridge triage:
  clause `(1)` is `source-facing` local depth input at a single prime localization in the
  Noetherian-ring setting of the canonical owner proof,
  clause `(2)` is the `source-facing` global `(S₂)` theorem expressed in the canonical owner
  predicate `Module.SerreConditionS`.

Primitive data are only the reflexive module and the localized depth comparison. The global `(S₂)`
conclusion is owner-level API, so this file should expose the canonical instance directly, reusing
the chapter owners
`isReflexive_localization_tfae` and `linearMap_serreConditionS_two_of_codomain` rather than
duplicating a local wrapper around double-dual linear maps.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]
variable (p : PrimeSpectrum R)

open scoped ENat
local notation "Rₚ" => Localization.AtPrime p.asIdeal
local notation "Mₚ" => AtPrime p.asIdeal M

/-- Helper for Lemma 15.23.16: reflexivity of a finite module survives localization at a prime. -/
private lemma localized_isReflexive_of_global_reflexive :
    IsReflexive Rₚ Mₚ := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  -- Use the prime-local branch of the localization TFAE for reflexive modules.
  have hReflexive : IsReflexive R M := inferInstance
  have hLocalized :
      ∀ (P : Ideal R) [P.IsPrime], IsReflexive (Localization.AtPrime P) (AtPrime P M) :=
    (isReflexive_localization_tfae.out 0 1).mp hReflexive
  exact hLocalized p.asIdeal

-- Proof sketch: use Lemma `15.23.4` to see that the localized module `Mₚ` is reflexive over the
-- local ring `Localization.AtPrime p.asIdeal`, identify it with its double dual via
-- `Module.evalEquiv`, and apply Lemma `15.23.10 (2)` twice to the local ring
-- `Localization.AtPrime p.asIdeal`.
/-- Lemma 15.23.16 (1): if `R` is a Noetherian ring, `M` is a finite reflexive `R`-module, and
`p` is a prime ideal of `R` such that `depth(Rₚ) ≥ 2`, then `depth(Mₚ) ≥ 2`. -/
@[stacks 0EBA]
theorem moduleDepth_localizationAtPrime_ge_two_of_ringDepth_localizationAtPrime_ge_two
    (hp : (2 : ℕ∞) ≤ moduleDepth Rₚ Rₚ) :
    (2 : ℕ∞) ≤ moduleDepth Rₚ Mₚ := by
  letI : IsReflexive Rₚ Mₚ := localized_isReflexive_of_global_reflexive (R := R) (M := M) p
  let e : Mₚ ≃ₗ[Rₚ] ((Mₚ →ₗ[Rₚ] Rₚ) →ₗ[Rₚ] Rₚ) := Module.evalEquiv Rₚ Mₚ
  letI : Module.Finite Rₚ ((Mₚ →ₗ[Rₚ] Rₚ) →ₗ[Rₚ] Rₚ) := Module.Finite.equiv e
  -- First prove the depth bound for the localized double dual.
  have hDoubleDual :
      (2 : ℕ∞) ≤ moduleDepth Rₚ ((Mₚ →ₗ[Rₚ] Rₚ) →ₗ[Rₚ] Rₚ) :=
    moduleDepth_linearMap_ge_two (R := Rₚ) (M := Mₚ →ₗ[Rₚ] Rₚ) (N := Rₚ) hp
  -- Then transport the bound back along the localized evaluation equivalence.
  have hDepthEq :
      moduleDepth Rₚ Mₚ = moduleDepth Rₚ ((Mₚ →ₗ[Rₚ] Rₚ) →ₗ[Rₚ] Rₚ) :=
    moduleDepth_eq_of_equiv e
  simpa [hDepthEq] using hDoubleDual

end

section

variable {R : Type u} [CommRing R] [R ⊧ (S₂)]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]

namespace Module.IsReflexive

omit [IsReflexive R M] in
/-- Helper for Lemma 15.23.16: if `R` satisfies `(S₂)`, then the double dual of a finite module
also satisfies `(S₂)`. -/
private lemma doubleDual_serreConditionS_two_of_ring_serreConditionS_two :
    SerreConditionS R ((M →ₗ[R] R) →ₗ[R] R) 2 := by
  -- Apply the canonical `Hom`-preservation theorem with codomain `R`.
  exact linearMap_serreConditionS_two_of_codomain (R := R) (M := M →ₗ[R] R) (N := R)

instance instSerreConditionSTwo : SerreConditionS R M 2 := by
  let e : M ≃ₗ[R] ((M →ₗ[R] R) →ₗ[R] R) := Module.evalEquiv R M
  letI : SerreConditionS R ((M →ₗ[R] R) →ₗ[R] R) 2 :=
    doubleDual_serreConditionS_two_of_ring_serreConditionS_two (R := R) (M := M)
  -- Transport the double-dual `(S₂)` structure back to `M` along the evaluation equivalence.
  exact Module.SerreConditionS.of_linearEquiv e.symm

end Module.IsReflexive

end

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Lemma 15.23.16 (2): if `R` satisfies `(S_2)`, then every finite reflexive `R`-module `M`
also satisfies Serre's condition `(S_2)`. This is the canonical owner instance
`Module.IsReflexive.instSerreConditionSTwo`, obtained by applying
`linearMap_serreConditionS_two_of_codomain` to the double dual and transporting along the reflexive
evaluation equivalence. -/
recall Module.IsReflexive.instSerreConditionSTwo

end
