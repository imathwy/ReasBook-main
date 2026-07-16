import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "DAb" => DerivedCategory Ab
local notation "DAbSeq" => DerivedCategory AbSeq
local notation "Qis" => HomologicalComplex.quasiIso AbSeq (up ℤ)

instance inverseLimitFunctor_additive :
    (lim : AbSeq ⥤ Ab).Additive := by
  sorry

instance sequentialInverseSystemAbelianGroups_isGrothendieckAbelian :
    IsGrothendieckAbelian AbSeq := by
  sorry

/- Domain-style sampling for 15.87.1.1:
- primary domain: right derived functors of inverse limits on sequential inverse systems of
  abelian groups;
- sampled owner declarations:
  `SequentialInverseSystem`,
  `CategoryTheory.Limits.lim`,
  `additiveFunctorTotalRightDerived`,
  `Functor.mapDerivedCategory`,
  `Functor.rightDerivedNatTrans`;
- best owner abstraction: the public source-facing object is the derived inverse-limit functor on
  the chapter owner `SequentialInverseSystem AddCommGrpCat`, while the cochain-level localization
  of `lim` is only bridge data for the chapter owner `additiveFunctorTotalRightDerived`;
- primitive data: the underived inverse-limit functor
  `lim : SequentialInverseSystem AddCommGrpCat ⥤ AddCommGrpCat`;
- derived API: `additiveFunctorTotalRightDerived`,
  `Functor.mapDerivedCategory`, `Functor.rightDerivedNatTrans`, and the induced stagewise tower
  functor on derived categories.

Source/core/bridge triage:
- `source-facing`: the textbook `R lim` functor, its object/cohomology notation, and the
  stagewise tower it assigns to an object of `D(\operatorname{Ab}(\mathbf N))`;
- `core/canonical`: `lim` and `additiveFunctorTotalRightDerived`;
- `bridge/view`: the cochain-level functor computing `R lim` before localization. -/

/- 15.87.1.1: the chosen right derived inverse-limit functor
`R lim : D(\operatorname{Ab}(\mathbf N)) ⟶ D(\operatorname{Ab})` is the canonical specialization
of `additiveFunctorTotalRightDerived` to
`lim : SequentialInverseSystem AddCommGrpCat ⥤ AddCommGrpCat`. -/
recall additiveFunctorTotalRightDerived

/- In this situation, the source-facing `R lim` functor is the chosen total right derived functor
of the ordinary inverse-limit functor on `SequentialInverseSystem AddCommGrpCat`. -/
#check
  (additiveFunctorTotalRightDerived
      (lim : SequentialInverseSystem AddCommGrpCat ⥤ AddCommGrpCat) :
    DAbSeq ⥤ DAb)

/- Internal bridge: the derived evaluation functor extracting the `n`-th stage of an object of
`D(\operatorname{Ab}(\mathbf N))`. The public source-facing API is the resulting tower
`stagewiseAbelianGroupDerivedTower` and its functoriality. -/
private abbrev stagewiseAbelianGroupEvaluation (n : ℕ) :
    AbSeq ⥤ Ab :=
  (evaluation ℕᵒᵖ Ab).obj (op n)

/- Internal bridge: stagewise evaluation on derived categories. -/
private abbrev stagewiseAbelianGroupDerivedEvaluation (n : ℕ) :
    DAbSeq ⥤ DAb :=
  (stagewiseAbelianGroupEvaluation n).mapDerivedCategory

local instance stagewiseAbelianGroupDerivedEvaluation_isRightDerivedFunctor (n : ℕ) :
    (stagewiseAbelianGroupDerivedEvaluation n).IsRightDerivedFunctor
      ((stagewiseAbelianGroupEvaluation n).mapDerivedCategoryFactors.inv)
      Qis := by
  simpa [stagewiseAbelianGroupDerivedEvaluation] using
    (Functor.isRightDerivedFunctor_of_inverts Qis
      ((stagewiseAbelianGroupEvaluation n).mapDerivedCategory)
      ((stagewiseAbelianGroupEvaluation n).mapDerivedCategoryFactors))

private abbrev stagewiseAbelianGroupEvaluationStep (n : ℕ) :
    stagewiseAbelianGroupEvaluation (n + 1) ⟶ stagewiseAbelianGroupEvaluation n :=
  (evaluation ℕᵒᵖ Ab).map ((homOfLE (Nat.le_succ n)).op)

/-- The induced transition natural transformation between stagewise evaluation functors on
derived categories. -/
private abbrev stagewiseAbelianGroupDerivedEvaluationStep (n : ℕ) :
    stagewiseAbelianGroupDerivedEvaluation (n + 1) ⟶
      stagewiseAbelianGroupDerivedEvaluation n :=
  Functor.rightDerivedNatTrans
    (stagewiseAbelianGroupDerivedEvaluation (n + 1))
    (stagewiseAbelianGroupDerivedEvaluation n)
    ((stagewiseAbelianGroupEvaluation (n + 1)).mapDerivedCategoryFactors.inv)
    ((stagewiseAbelianGroupEvaluation n).mapDerivedCategoryFactors.inv)
    Qis
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (stagewiseAbelianGroupEvaluationStep n) (up ℤ))
      DerivedCategory.Q)

/-- The tower `(K_n^\bullet)_n` in `D(\operatorname{Ab})` attached to
`K ∈ D(\operatorname{Ab}(\mathbf N))` by stagewise evaluation. -/
abbrev stagewiseAbelianGroupDerivedTower
    (K : DAbSeq) : SequentialInverseSystem DAb :=
  @Functor.ofOpSequence DAb _
    (fun n ↦ (stagewiseAbelianGroupDerivedEvaluation n).obj K)
    (fun n ↦ (stagewiseAbelianGroupDerivedEvaluationStep n).app K)

private theorem stagewiseAbelianGroupDerivedTowerFunctor_step_naturality
    {E D : DAbSeq} (φ : E ⟶ D) (n : ℕ) :
    (stagewiseAbelianGroupDerivedEvaluationStep n).app E ≫
        (stagewiseAbelianGroupDerivedEvaluation n).map φ =
      (stagewiseAbelianGroupDerivedEvaluation (n + 1)).map φ ≫
        (stagewiseAbelianGroupDerivedEvaluationStep n).app D := by
  simpa using ((stagewiseAbelianGroupDerivedEvaluationStep n).naturality φ).symm

private theorem stagewiseAbelianGroupDerivedTower_naturality
    {E D : DAbSeq} (φ : E ⟶ D) (n : ℕ) :
    (stagewiseAbelianGroupDerivedTower E).map (homOfLE (Nat.le_succ n)).op ≫
        (stagewiseAbelianGroupDerivedEvaluation n).map φ =
      (stagewiseAbelianGroupDerivedEvaluation (n + 1)).map φ ≫
        (stagewiseAbelianGroupDerivedTower D).map (homOfLE (Nat.le_succ n)).op := by
  simpa [stagewiseAbelianGroupDerivedTower] using
    stagewiseAbelianGroupDerivedTowerFunctor_step_naturality φ n

/-- The stagewise evaluation functor
`D(\operatorname{Ab}(\mathbf N)) ⥤ \mathbf N^{op} ⥤ D(\operatorname{Ab})`. -/
abbrev stagewiseAbelianGroupDerivedTowerFunctor :
    DAbSeq ⥤ SequentialInverseSystem DAb where
  obj := stagewiseAbelianGroupDerivedTower
  map φ :=
    show stagewiseAbelianGroupDerivedTower _ ⟶ stagewiseAbelianGroupDerivedTower _ from
      NatTrans.ofOpSequence
        (fun n ↦ (stagewiseAbelianGroupDerivedEvaluation n).map φ)
        (stagewiseAbelianGroupDerivedTower_naturality φ)
  map_id := by
    intro E
    ext n
    simp
  map_comp := by
    intro E D F φ ψ
    ext n
    simp

namespace CategoryTheory

/- Textbook notation for the derived inverse-limit object `R lim(K)` in `D(\operatorname{Ab})`. -/
scoped notation:max "R" " lim(" K ")" =>
  Functor.obj
    (CategoryTheory.additiveFunctorTotalRightDerived
      (CategoryTheory.Limits.lim :
        SequentialInverseSystem AddCommGrpCat ⥤ AddCommGrpCat))
    K

/- Textbook notation for the cohomology object `R^p lim(K) = H^p(R lim(K))`. -/
scoped notation:max "R^" p:max " lim(" K ")" =>
  Functor.obj
    (DerivedCategory.homologyFunctor AddCommGrpCat p)
    (Functor.obj
      (CategoryTheory.additiveFunctorTotalRightDerived
        (CategoryTheory.Limits.lim :
          SequentialInverseSystem AddCommGrpCat ⥤ AddCommGrpCat))
      K)

end CategoryTheory
