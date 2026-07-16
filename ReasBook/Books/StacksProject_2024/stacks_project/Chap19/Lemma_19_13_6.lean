import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_4

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

noncomputable section

universe w u₁ v₁ u₂ v₂

namespace CategoryTheory

section

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Abelian A]
variable [Category.{v₂} B] [Abelian B]

local instance additiveFunctor_preservesDerivedLimit_source_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

local instance additiveFunctor_preservesDerivedLimit_target_hasDerivedCategory :
    HasDerivedCategory.{max u₂ v₂} B :=
  HasDerivedCategory.standard B

/-- Lemma 19.13.6: the canonical total right derived functor of an additive functor preserves
chosen derived limits of sequential inverse systems. -/
theorem additiveFunctor_totalRightDerived_preservesDerivedLimit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {Ksys : ℕᵒᵖ ⥤ DerivedCategory A} {K : DerivedCategory A}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ additiveFunctorTotalRightDerived F)
      ((additiveFunctorTotalRightDerived F).obj K) := by
  sorry

end

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable [IsGrothendieckAbelian.{w} A]
variable [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)]

local instance derivedInverseLimit_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

local instance derivedInverseLimitTower_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} (SequentialInverseSystem A) :=
  HasDerivedCategory.standard (SequentialInverseSystem A)

local notation "SeqA" => SequentialInverseSystem A
local notation "DA" => DerivedCategory A
local notation "DSeqA" => DerivedCategory SeqA
local notation "QisSeqA" =>
  (HomologicalComplex.quasiIso SeqA (ComplexShape.up ℤ) :
    MorphismProperty (CochainComplex SeqA ℤ))

private abbrev stageEvaluation (n : ℕ) : SeqA ⥤ A :=
  ((evaluation ℕᵒᵖ A).obj (op n) : SeqA ⥤ A)

local instance stageEvaluation_additive (n : ℕ) :
    (((evaluation ℕᵒᵖ A).obj (op n)) : SeqA ⥤ A).Additive := by
  infer_instance

local instance stageEvaluation_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (((evaluation ℕᵒᵖ A).obj (op n)) : SeqA ⥤ A) := by
  infer_instance

local instance stageEvaluation_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (((evaluation ℕᵒᵖ A).obj (op n)) : SeqA ⥤ A) := by
  infer_instance

private abbrev stageDerivedEvaluation (n : ℕ) : DSeqA ⥤ DA :=
  (stageEvaluation n).mapDerivedCategory

local instance stageDerivedEvaluation_isRightDerivedFunctor (n : ℕ) :
    (stageDerivedEvaluation n).IsRightDerivedFunctor
      (((stageEvaluation n).mapDerivedCategoryFactors.inv) :
        (stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ stageDerivedEvaluation n)
      QisSeqA := by
  simpa [stageDerivedEvaluation] using
    (Functor.isRightDerivedFunctor_of_inverts
      QisSeqA
      ((stageEvaluation n).mapDerivedCategory : DSeqA ⥤ DA)
      ((stageEvaluation n).mapDerivedCategoryFactors))

private abbrev stageEvaluationStep (n : ℕ) :
    (((evaluation ℕᵒᵖ A).obj (op (n + 1))) : SeqA ⥤ A) ⟶
      (((evaluation ℕᵒᵖ A).obj (op n)) : SeqA ⥤ A) :=
  (((evaluation ℕᵒᵖ A).map ((homOfLE (Nat.le_succ n)).op)) :
    ((evaluation ℕᵒᵖ A).obj (op (n + 1)) : SeqA ⥤ A) ⟶
      ((evaluation ℕᵒᵖ A).obj (op n) : SeqA ⥤ A))

private abbrev stageDerivedEvaluationStep (n : ℕ) :
    ((stageEvaluation (n + 1)).mapDerivedCategory : DSeqA ⥤ DA) ⟶
      ((stageEvaluation n).mapDerivedCategory : DSeqA ⥤ DA) :=
  Functor.rightDerivedNatTrans
    ((stageDerivedEvaluation (n + 1)) : DSeqA ⥤ DA)
    ((stageDerivedEvaluation n) : DSeqA ⥤ DA)
    ((stageEvaluation (n + 1)).mapDerivedCategoryFactors.inv
      :
      (stageEvaluation (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ stageDerivedEvaluation (n + 1))
    ((stageEvaluation n).mapDerivedCategoryFactors.inv :
      (stageEvaluation n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ stageDerivedEvaluation n)
    QisSeqA
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (stageEvaluationStep n) (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The tower obtained by evaluating `K : D(SequentialInverseSystem A)` stagewise on `ℕᵒᵖ`. -/
abbrev stagewiseDerivedInverseLimitTower (K : DSeqA) :
    SequentialInverseSystem DA :=
  let X : ℕ → DA := fun n ↦ (stageDerivedEvaluation n).obj K
  let step : (n : ℕ) → X (n + 1) ⟶ X n := fun n ↦
    (stageDerivedEvaluationStep n).app K
  Functor.ofOpSequence step

/-- Lemma 19.13.6: for `K : D(SequentialInverseSystem A)`, the canonical value
`R lim(K)` is a derived limit of the stagewise evaluation tower `(K_n)_n`. -/
theorem derivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    [HasLimitsOfShape ℕᵒᵖ A]
    [(lim : SeqA ⥤ A).Additive]
    [HasCountableProducts A] [CountableAB4Star A]
    [PreservesLimitsOfShape (Discrete ℕ) (lim : SeqA ⥤ A)]
    (K : DSeqA) :
    IsDerivedLimit
      (stagewiseDerivedInverseLimitTower K)
      ((additiveFunctorTotalRightDerived (lim : SeqA ⥤ A)).obj K) := by
  sorry

end

end CategoryTheory
