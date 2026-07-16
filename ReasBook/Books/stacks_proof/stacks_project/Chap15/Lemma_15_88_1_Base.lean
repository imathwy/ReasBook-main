import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Whiskering
import stacks_proof.stacks_project.Chap12.Definition_12_31_2

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open Opposite
open SheafOfModules

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)

/-- The functor `ℕᵒᵖ ⥤ CommRingCat` attached to a sequential inverse system
`A₀ ← A₁ ← A₂ ← ⋯`. -/
abbrev sequentialRingSystem
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    ℕᵒᵖ ⥤ CommRingCat.{u} :=
  @Functor.ofOpSequence CommRingCat.{u} _
    (fun n ↦ CommRingCat.of (A n))
    (fun n ↦ CommRingCat.ofHom (ρ n))

private abbrev sequentialRingSystemAsRingCat
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    ℕᵒᵖ ⥤ RingCat.{u} :=
  sequentialRingSystem A ρ ⋙ forget₂ CommRingCat RingCat

/-- The `RingCat`-valued sheaf on the chaotic site of `ℕ` attached to a sequential inverse
system of commutative rings. -/
abbrev sequentialRingSystemRingSheaf
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    Sheaf NatSite RingCat.{u} :=
  (sheafBotEquivalence RingCat.{u}).inverse.obj (sequentialRingSystemAsRingCat A ρ)

/-- The varying-ring module category `Mod(ℕ, (A_n))`. -/
abbrev SeqRingMod
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :=
  SheafOfModules (sequentialRingSystemRingSheaf A ρ)

instance seqRingMod_abelian
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    Abelian (SeqRingMod A ρ) :=
  SheafOfModules.instAbelian (sequentialRingSystemRingSheaf A ρ)

instance seqRingMod_categoryWithHomology
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    CategoryWithHomology (SeqRingMod A ρ) := by
  sorry

/-- Evaluation at stage `n` on `Mod(ℕ, (A_n))`. -/
abbrev sequentialRingedModuleEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    SeqRingMod A ρ ⥤ ModuleCat.{u} (A n) :=
  SheafOfModules.evaluation (sequentialRingSystemRingSheaf A ρ) (op n)

instance sequentialRingedModuleEvaluation_additive
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    (sequentialRingedModuleEvaluation A ρ n).Additive := by
  sorry

instance sequentialRingedModuleEvaluation_preservesZeroMorphisms
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    (sequentialRingedModuleEvaluation A ρ n).PreservesZeroMorphisms := by
  sorry

/-- The stage-transition natural transformation on `Mod(ℕ, (A_n))`. -/
abbrev sequentialRingedModuleEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    sequentialRingedModuleEvaluation A ρ (n + 1) ⟶
      sequentialRingedModuleEvaluation A ρ n ⋙ ModuleCat.restrictScalars (ρ n) := by
  simpa [sequentialRingedModuleEvaluation, sequentialRingSystemRingSheaf,
      sequentialRingSystem]
    using Functor.whiskerLeft
      (SheafOfModules.forget (sequentialRingSystemRingSheaf A ρ))
      (PresheafOfModules.restriction
        (sequentialRingSystemAsRingCat A ρ)
        ((homOfLE (Nat.le_succ n)).op))

/-- Evaluation at stage `n` on cochain complexes in `Mod(ℕ, (A_n))`. -/
abbrev sequentialRingedModuleCochainEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    CochainComplex (SeqRingMod A ρ) ℤ ⥤ CochainComplex (ModuleCat.{u} (A n)) ℤ :=
  letI : (sequentialRingedModuleEvaluation A ρ n).PreservesZeroMorphisms := by
    sorry
  (sequentialRingedModuleEvaluation A ρ n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The stage-`n` cochain complex obtained by evaluating a complex of systems of modules. -/
abbrev sequentialRingedModuleCochainEval
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ)
    (M : CochainComplex (SeqRingMod A ρ) ℤ) :
    CochainComplex (ModuleCat.{u} (A n)) ℤ :=
  (sequentialRingedModuleCochainEvaluation A ρ n).obj M

/-- The induced transition natural transformation on stagewise cochain-complex evaluations. -/
abbrev sequentialRingedModuleCochainEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    sequentialRingedModuleCochainEvaluation A ρ (n + 1) ⟶
      sequentialRingedModuleCochainEvaluation A ρ n ⋙
        (ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  letI : (sequentialRingedModuleEvaluation A ρ (n + 1)).PreservesZeroMorphisms := by
    sorry
  letI : (sequentialRingedModuleEvaluation A ρ n).PreservesZeroMorphisms := by
    sorry
  NatTrans.mapHomologicalComplex (sequentialRingedModuleEvaluationStep A ρ n) (ComplexShape.up ℤ)

end
