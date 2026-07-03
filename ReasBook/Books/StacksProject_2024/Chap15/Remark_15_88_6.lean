import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_88_4
import StacksProject_2024.Chap15.Lemma_15_88_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
local notation "F" => sequentialRingSystem A ρ

variable [CategoryWithHomology (SeqRingMod A ρ)]

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

/- Domain-style sampling:
- primary domain: derived inverse limits for varying-ring systems `Mod(ℕ, (A_n))`, compared
  across different realizations of the same stagewise derived tower;
- sampled owner declarations:
  `DerivedModuleTower.Realization`,
  `DerivedModuleTower.stageRestrictionToLimit`,
  `ringedModuleDerivedInverseLimitFunctor`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit`;
- best owner abstraction: the ambient owner for `R \!\varprojlim` is the canonical Chapter 15
  functor `ringedModuleDerivedInverseLimitFunctor A ρ`, while the source-facing data of the remark
  are carried by the bridge/view predicate `DerivedModuleTower.Realization` and the induced
  fixed-base stages `DerivedModuleTower.stageRestrictionToLimit`;
- primitive data: a compatible tower `T : DerivedModuleTower A ρ` and realizations
  `T.Realization M`, `T.Realization N` in `D(Mod(ℕ, (A_n)))`;
- derived API: the canonical fixed-base inverse system `stageRestrictionToLimitTower T`,
  realization-independence of the image under the canonical owner
  `ringedModuleDerivedInverseLimitFunctor A ρ`, and the descended Milnor short exact sequence on
  cohomology; the source does not assert uniqueness of the realizing object itself in
  `D(Mod(ℕ, (A_n)))`.

Source/core/bridge triage:
- `source-facing`: independence of the isomorphism class of `R \!\varprojlim(M)` from the chosen
  realization of the fixed stagewise tower `T`, together with the fact that the Milnor exact
  sequence depends only on `T`;
- `core/canonical`: `ringedModuleDerivedInverseLimitFunctor A ρ`;
- `bridge/view`: `DerivedModuleTower A ρ`, `DerivedModuleTower.Realization`, and
  `DerivedModuleTower.stageRestrictionToLimit`.
-/

namespace DerivedModuleTower

local notation "DModLim" => DerivedCategory (ModuleCat (inverseLimitRing F))
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat (inverseLimitRing F))

private abbrev asStageRingTower (T : DerivedModuleTower A ρ) :
    DerivedModuleTower (stageRing F) (stageTransitionRingHom F) where
  obj n := T.obj n
  stepMap n := by
    simpa [sequentialRingedModuleTransitionFunctor, stageTransitionRingHom, sequentialRingSystem]
      using T.stepMap n

omit [CategoryWithHomology (SeqRingMod A ρ)] in
private theorem limitProjectionRingHom_comp (n : ℕ) :
    limitProjectionRingHom F n =
      (ρ n).comp (limitProjectionRingHom F (n + 1)) := by
  ext x
  simpa [stageTransitionRingHom, limitProjectionRingHom, sequentialRingSystem] using congrArg
    (fun f : limit (sequentialRingSystem A ρ) ⟶ (sequentialRingSystem A ρ).obj (op n) ↦ f x)
    ((limit.w (sequentialRingSystem A ρ) ((homOfLE (Nat.le_succ n)).op)).symm)

local instance restrictScalars_transition_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{0} (ρ n)) := by
  sorry

local instance restrictScalars_transition_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{0} (ρ n)) := by
  sorry

local instance stageRestrictionFunctor_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{0} (limitProjectionRingHom F n)) := by
  sorry

local instance stageRestrictionFunctor_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{0} (limitProjectionRingHom F n)) := by
  sorry

variable (A) (ρ) in
private abbrev stageRestrictionFunctor (n : ℕ) :
    ModuleCat.{0} (A n) ⥤ ModuleCat.{0} (inverseLimitRing F) :=
  ModuleCat.restrictScalars.{0} (limitProjectionRingHom F n)

variable (A) (ρ) in
local instance stageRestrictionFunctor_preservesFiniteLimits' (n : ℕ) :
    PreservesFiniteLimits (stageRestrictionFunctor A ρ n) := by
  sorry

variable (A) (ρ) in
local instance stageRestrictionFunctor_preservesFiniteColimits' (n : ℕ) :
    PreservesFiniteColimits (stageRestrictionFunctor A ρ n) := by
  sorry

variable (A) (ρ) in
private abbrev stageRestrictionDerivedFunctor (n : ℕ) :
    DerivedCategory (ModuleCat.{0} (A n)) ⥤ DModLim :=
  (stageRestrictionFunctor A ρ n).mapDerivedCategory

variable (A) (ρ) in
private abbrev stageRestrictionThenTransitionFunctor (n : ℕ) :
    ModuleCat.{0} (A n) ⥤ ModuleCat.{0} (inverseLimitRing F) :=
  ModuleCat.restrictScalars.{0} (ρ n) ⋙ stageRestrictionFunctor A ρ (n + 1)

variable (A) (ρ) in
private abbrev stageRestrictionThenTransitionDerivedFunctor (n : ℕ) :
    DerivedCategory (ModuleCat.{0} (A n)) ⥤ DModLim :=
  sequentialRingedModuleTransitionFunctor A ρ n ⋙
    stageRestrictionDerivedFunctor A ρ (n + 1)

variable (A) (ρ) in
private noncomputable abbrev stageRestrictionThenTransitionFactors (n : ℕ) :
    ((stageRestrictionThenTransitionFunctor A ρ n).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat (inverseLimitRing F)) ℤ ⥤ DModLim)) ≅
      (((DerivedCategory.Q :
          CochainComplex (ModuleCat.{0} (A n)) ℤ ⥤ DerivedCategory (ModuleCat.{0} (A n))) ⋙
        sequentialRingedModuleTransitionFunctor A ρ n) ⋙
          stageRestrictionDerivedFunctor A ρ (n + 1)) := by
  simpa [stageRestrictionFunctor, stageRestrictionDerivedFunctor,
      stageRestrictionThenTransitionFunctor, stageRestrictionThenTransitionDerivedFunctor,
      sequentialRingedModuleTransitionFunctor] using
    calc
      (stageRestrictionThenTransitionFunctor A ρ n).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q :
            CochainComplex (ModuleCat (inverseLimitRing F)) ℤ ⥤ DModLim) ≅
        (ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          ((stageRestrictionFunctor A ρ (n + 1)).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Q :
                CochainComplex (ModuleCat (inverseLimitRing F)) ℤ ⥤ DModLim)) :=
        Functor.associator
          ((ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((stageRestrictionFunctor A ρ (n + 1)).mapHomologicalComplex
            (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat (inverseLimitRing F)) ℤ ⥤ DModLim)
      _ ≅
          (ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            ((DerivedCategory.Q :
                CochainComplex (ModuleCat.{0} (A (n + 1))) ℤ ⥤
                  DerivedCategory (ModuleCat.{0} (A (n + 1)))) ⋙
              stageRestrictionDerivedFunctor A ρ (n + 1)) :=
        Functor.isoWhiskerLeft
          ((ModuleCat.restrictScalars.{0} (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ))
          (stageRestrictionFunctor A ρ (n + 1)).mapDerivedCategoryFactors.symm
      _ ≅
          (((ModuleCat.restrictScalars.{0} (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
              (DerivedCategory.Q :
                CochainComplex (ModuleCat.{0} (A (n + 1))) ℤ ⥤
                  DerivedCategory (ModuleCat.{0} (A (n + 1))))) ⋙
            stageRestrictionDerivedFunctor A ρ (n + 1) :=
        (Functor.associator
          ((ModuleCat.restrictScalars.{0} (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{0} (A (n + 1))) ℤ ⥤
              DerivedCategory (ModuleCat.{0} (A (n + 1))))
          (stageRestrictionDerivedFunctor A ρ (n + 1))).symm
      _ ≅
          (((DerivedCategory.Q :
              CochainComplex (ModuleCat.{0} (A n)) ℤ ⥤
                DerivedCategory (ModuleCat.{0} (A n))) ⋙
            sequentialRingedModuleTransitionFunctor A ρ n) ⋙
              stageRestrictionDerivedFunctor A ρ (n + 1)) :=
        by
          simpa [sequentialRingedModuleTransitionFunctor] using
            Functor.isoWhiskerRight
              (ModuleCat.restrictScalars.{0} (ρ n)).mapDerivedCategoryFactors.symm
              (stageRestrictionDerivedFunctor A ρ (n + 1))

variable (A) (ρ) in
private theorem stageRestrictionThenTransitionDerived_isRightDerivedFunctor (n : ℕ) :
    (stageRestrictionThenTransitionDerivedFunctor A ρ n).IsRightDerivedFunctor
      (stageRestrictionThenTransitionFactors A ρ n).hom
      (HomologicalComplex.quasiIso (ModuleCat (A n)) (ComplexShape.up ℤ)) := by
  sorry

variable (A) (ρ) in
private abbrev stageRestrictionCompIso (n : ℕ) :
    stageRestrictionFunctor A ρ n ≅
      stageRestrictionThenTransitionFunctor A ρ n := by
  simpa [stageRestrictionFunctor, stageRestrictionThenTransitionFunctor] using
    (ModuleCat.restrictScalarsComp'.{0}
      (limitProjectionRingHom F (n + 1))
      (ρ n)
      (limitProjectionRingHom F n)
      (limitProjectionRingHom_comp n))

variable (A) (ρ) in
private noncomputable abbrev stageRestrictionCompIsoOnComplexes (n : ℕ) :
    (stageRestrictionFunctor A ρ n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{0} (inverseLimitRing F)) ℤ ⥤ DModLim) ≅
      (stageRestrictionThenTransitionFunctor A ρ n).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{0} (inverseLimitRing F)) ℤ ⥤ DModLim) :=
  Functor.isoWhiskerRight
    (CategoryTheory.NatIso.mapHomologicalComplex
      (stageRestrictionCompIso A ρ n) (ComplexShape.up ℤ))
    (DerivedCategory.Q :
      CochainComplex (ModuleCat.{0} (inverseLimitRing F)) ℤ ⥤ DModLim)

variable (A) (ρ) in
private noncomputable abbrev stageRestrictionDerivedIso (n : ℕ) :
    stageRestrictionDerivedFunctor A ρ n ≅
      stageRestrictionThenTransitionDerivedFunctor A ρ n := by
  letI := stageRestrictionThenTransitionDerived_isRightDerivedFunctor A ρ n
  exact CategoryTheory.Functor.rightDerivedNatIso
    (stageRestrictionDerivedFunctor A ρ n)
    (stageRestrictionThenTransitionDerivedFunctor A ρ n)
    ((stageRestrictionFunctor A ρ n).mapDerivedCategoryFactors.inv)
    (stageRestrictionThenTransitionFactors A ρ n).hom
    (HomologicalComplex.quasiIso (ModuleCat (A n)) (ComplexShape.up ℤ))
    (stageRestrictionCompIsoOnComplexes A ρ n)

private noncomputable abbrev stageRestrictionToLimitStep
    (T : DerivedModuleTower A ρ) (n : ℕ) :
    stageRestrictionToLimit F (asStageRingTower T) (n + 1) ⟶
      stageRestrictionToLimit F (asStageRingTower T) n := by
  simpa [DerivedModuleTower.stageRestrictionToLimit, stageRestrictionDerivedFunctor,
      asStageRingTower] using
    (stageRestrictionDerivedFunctor A ρ (n + 1)).map (T.stepMap n) ≫
      (stageRestrictionDerivedIso A ρ n).inv.app (T.obj n)

/-- The canonical fixed-base inverse system `(K_n)` in `D(A)` attached to `T`, obtained by
restricting each stage `T.obj n ∈ D(A_n)` along `A = \varprojlim_n A_n → A_n`. -/
abbrev stageRestrictionToLimitTower (T : DerivedModuleTower A ρ) :
    SequentialInverseSystem DModLim :=
  Functor.ofOpSequence (stageRestrictionToLimitStep T)

/-- Remark 15.88.6: if `M` realizes `T`, then the canonical fixed-base inverse system
`stageRestrictionToLimitTower T` in `D(A)` has stage `n` equal to `T.obj n` after restricting
scalars along `A → A_n`, and `R \!\varprojlim(M)` is a derived limit of this actual system. This
is the tower-level form of the observation that `R lim(M)` depends only on `T`. -/
theorem stageRestrictionToLimitTower_isDerivedLimit_of_realization
    (T : DerivedModuleTower A ρ) {M : DModSeq} (hM : T.Realization M) :
    IsDerivedLimit (stageRestrictionToLimitTower T) (R lim(M)) := sorry

/- Remark 15.88.6, cohomological owner form: once
`stageRestrictionToLimitTower_isDerivedLimit_of_realization` identifies `R lim(M)` as a derived
limit of the canonical fixed-base tower `stageRestrictionToLimitTower T`, the Milnor short exact
sequence for `H^p(R lim(M))` is exactly the canonical Chapter 15 owner
`CategoryTheory.derivedLimit_cohomology_shortExact`. This file therefore reuses that owner
directly rather than keeping a parallel tower-level wrapper for the same short exact sequence. -/
recall CategoryTheory.derivedLimit_cohomology_shortExact

-- Proof sketch: use `hM` and `hN` to identify the two stagewise `D(A)`-towers obtained by
-- restricting scalars from the evaluations of `M` and `N` along `A = \varprojlim A_n → A_n`.
-- Each image under `ringedModuleDerivedInverseLimitFunctor A ρ` is then a derived limit of the
-- same canonical fixed-base tower `stageRestrictionToLimitTower T`, so the Chapter 15
-- derived-limit uniqueness theorem yields an
-- isomorphism between the two images. The remark does not assert that `M` and `N` themselves are
-- isomorphic in `D(Mod(ℕ, (A_n)))`.
/-- Remark 15.88.6: if `M` and `N` are two realizations of the same compatible tower
`T : DerivedModuleTower A ρ` from Lemma `15.88.5`, then the isomorphism class of the canonical
Chapter 15 object `R \!\varprojlim(M)` depends only on `T`. Equivalently, `R lim(M)` and
`R lim(N)` are isomorphic in the target derived category over `A = \varprojlim_n A_n`. -/
theorem derivedInverseLimit_isIsomorphic_of_realization
    (T : DerivedModuleTower A ρ) {M N : DModSeq}
    (hM : T.Realization M) (hN : T.Realization N) :
    IsIsomorphic (R lim(M)) (R lim(N)) := sorry

end DerivedModuleTower

end
