import Mathlib
import StacksProject_2024.Chap15.Lemma_15_88_1_FixedBase

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "Qis" => HomologicalComplex.quasiIso SeqMod (up ℤ)

/- Domain-style sampling for Lemma 15.88.3 in the fixed-base derived inverse-limit domain:
- sampled owner declarations:
  * `CategoryTheory.Limits.lim`
  * `CategoryTheory.additiveFunctorTotalRightDerived`
  * `Functor.rightDerivedNatTrans`
  * `CategoryTheory.IsDerivedLimit`
- best owner abstraction: the core/canonical owner remains the chosen total right derived functor
  `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)` together with its
  source-facing textbook object notation `R lim(K)` and the Chapter `13` predicate
  `IsDerivedLimit`;
- primitive data: only the fixed-base inverse-limit functor
  `lim : SeqMod ⥤ ModuleCat A`;
- derived API: the stagewise tower in `D(A)` obtained by evaluating an object of
  `D(ℕᵒᵖ ⥤ Mod A)` stagewise, and the Milnor-triangle comparison theorem below.

Source/core/bridge triage:
- `source-facing`: the theorem asserting that the chosen `R lim(K)` is a derived limit of the
  stagewise tower `(K_n^•)_n`;
- `core/canonical`: `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)` and
  `IsDerivedLimit`;
- `bridge/view`: the stagewise evaluation functors and the induced tower
  `stagewiseModuleDerivedLimitTower K`, whose ambient base ring is inferred from `K`.

This file therefore keeps the source-facing theorem and its minimal stagewise bridge data, while
reusing the canonical fixed-base owner from `Lemma_15_88_1_FixedBase`. -/

/-- Evaluation at stage `n` on sequential inverse systems of `A`-modules. -/
private abbrev stageEvaluation (n : ℕ) :
    SeqMod ⥤ ModuleCat A :=
  (evaluation ℕᵒᵖ (ModuleCat A)).obj (op n)

local instance stageEvaluation_additive (n : ℕ) :
    (stageEvaluation A n).Additive := by
  infer_instance

local instance stageEvaluation_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (stageEvaluation A n) := by
  infer_instance

local instance stageEvaluation_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (stageEvaluation A n) := by
  infer_instance

/-- The stage-`n` functor on the derived category of sequential inverse systems of `A`-modules.
-/
private abbrev stageDerivedEvaluation (n : ℕ) :
    DSeq ⥤ DMod :=
  (stageEvaluation A n).mapDerivedCategory

local instance stageDerivedEvaluation_isRightDerivedFunctor (n : ℕ) :
    (stageDerivedEvaluation A n).IsRightDerivedFunctor
      ((stageEvaluation A n).mapDerivedCategoryFactors.inv)
      Qis := by
  simpa [stageDerivedEvaluation] using
    (Functor.isRightDerivedFunctor_of_inverts Qis
      ((stageEvaluation A n).mapDerivedCategory)
      ((stageEvaluation A n).mapDerivedCategoryFactors))

/-- The transition natural transformation from stage `n + 1` to stage `n`. -/
private abbrev stageEvaluationStep (n : ℕ) :
    stageEvaluation A (n + 1) ⟶ stageEvaluation A n :=
  (evaluation ℕᵒᵖ (ModuleCat A)).map ((homOfLE (Nat.le_succ n)).op)

/-- The induced transition natural transformation on the derived category. -/
private abbrev stageDerivedEvaluationStep (n : ℕ) :
    stageDerivedEvaluation A (n + 1) ⟶ stageDerivedEvaluation A n :=
  Functor.rightDerivedNatTrans
    (stageDerivedEvaluation A (n + 1))
    (stageDerivedEvaluation A n)
    ((stageEvaluation A (n + 1)).mapDerivedCategoryFactors.inv)
    ((stageEvaluation A n).mapDerivedCategoryFactors.inv)
    Qis
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (stageEvaluationStep A n) (up ℤ))
      DerivedCategory.Q)

/-- The stagewise tower in `D(A)` attached to an object of
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`. -/
abbrev stagewiseModuleDerivedLimitTower
    {A : Type u} [CommRing A]
    (K : DerivedCategory (SequentialInverseSystem (ModuleCat A))) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  let X : ℕ → DerivedCategory (ModuleCat A) := fun n ↦ (stageDerivedEvaluation A n).obj K
  Functor.ofOpSequence (fun n ↦
    show X (n + 1) ⟶ X n from (stageDerivedEvaluationStep A n).app K)

private theorem stagewiseModuleDerivedLimitTowerFunctor_step_naturality
    {E D : DSeq} (φ : E ⟶ D) (n : ℕ) :
    (stageDerivedEvaluationStep A n).app E ≫
        (stageDerivedEvaluation A n).map φ =
      (stageDerivedEvaluation A (n + 1)).map φ ≫
        (stageDerivedEvaluationStep A n).app D := by
  simpa using ((stageDerivedEvaluationStep A n).naturality φ).symm

private theorem stagewiseModuleDerivedLimitTower_naturality
    {E D : DSeq} (φ : E ⟶ D) (n : ℕ) :
    (stagewiseModuleDerivedLimitTower E).map (homOfLE (Nat.le_succ n)).op ≫
        (stageDerivedEvaluation A n).map φ =
      (stageDerivedEvaluation A (n + 1)).map φ ≫
        (stagewiseModuleDerivedLimitTower D).map (homOfLE (Nat.le_succ n)).op := by
  simpa [stagewiseModuleDerivedLimitTower] using
    stagewiseModuleDerivedLimitTowerFunctor_step_naturality (A := A) φ n

/-- The stagewise evaluation functor
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A) ⥤ \mathbf N^\mathrm{op} ⥤ D(A)`. -/
abbrev stagewiseModuleDerivedLimitTowerFunctor :
    DSeq ⥤ SequentialInverseSystem DMod where
  obj := stagewiseModuleDerivedLimitTower
  map φ :=
    show stagewiseModuleDerivedLimitTower _ ⟶ stagewiseModuleDerivedLimitTower _ from
      NatTrans.ofOpSequence
        (fun n ↦ (stageDerivedEvaluation A n).map φ)
        (stagewiseModuleDerivedLimitTower_naturality (A := A) φ)
  map_id := by
    intro E
    ext n
    simp
  map_comp := by
    intro E D F φ ψ
    ext n
    simp

/-- Lemma 15.88.3: for `K ∈ D(\mathrm{Mod}(\mathbf N, (A_n)))`, modeled here by the fixed-base
bridge object `DerivedCategory (SequentialInverseSystem (ModuleCat A))`, the canonical total
right derived functor `R \!\varprojlim(K)` of `\varprojlim : \mathbf N^\mathrm{op} \to
\mathrm{Mod}_A \to \mathrm{Mod}_A` is a derived limit of the stagewise tower `(K_n^\bullet)_n`
in `D(A)`.
Equivalently, it fits into the canonical Milnor distinguished triangle
`R \!\varprojlim(K) ⟶ \prod_n K_n^\bullet ⟶ \prod_n K_n^\bullet ⟶
R \!\varprojlim(K)[1]`. -/
theorem moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    (K : DSeq) :
    IsDerivedLimit (stagewiseModuleDerivedLimitTower K) (R lim(K)) := by
  -- The source proof is the fixed-base Milnor triangle, already packaged abstractly in Chapter 19.
  -- We therefore specialize that theorem to `A := ModuleCat A` and simplify the local tower notation.
  simpa [stagewiseModuleDerivedLimitTower] using
    (CategoryTheory.derivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
      (A := ModuleCat A) K)
