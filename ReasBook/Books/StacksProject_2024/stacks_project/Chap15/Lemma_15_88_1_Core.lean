import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import StacksProject_2024.Chap13.Lemma_13_16_9
import StacksProject_2024.Chap15.Lemma_15_88_1_Base

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars along `A_{n + 1} → A_n`, lifted to derived categories. -/
abbrev sequentialRingedModuleTransitionFunctor
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A n)) ⥤ DerivedCategory (ModuleCat.{u} (A (n + 1))) := by
  sorry

/-- Stagewise derived evaluation for the sequential varying-ring module category. -/
abbrev sequentialRingedModuleDerivedEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) [Abelian (SeqRingMod A ρ)]
    [CategoryWithHomology (SeqRingMod A ρ)] (n : ℕ) :
    DerivedCategory (SeqRingMod A ρ) ⥤ DerivedCategory (ModuleCat.{u} (A n)) := by
  sorry

/-- The induced transition morphism between stagewise derived evaluation functors. -/
abbrev sequentialRingedModuleDerivedEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) [Abelian (SeqRingMod A ρ)]
    [CategoryWithHomology (SeqRingMod A ρ)] (n : ℕ) :
    sequentialRingedModuleDerivedEvaluation A ρ (n + 1) ⟶
      sequentialRingedModuleDerivedEvaluation A ρ n ⋙
        sequentialRingedModuleTransitionFunctor A ρ n := by
  sorry
