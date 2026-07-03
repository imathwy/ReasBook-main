import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_15_88_6 (from Chap15) -/
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

/-! ### Lemma_15_88_7 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

/- Domain-style sampling for Lemma 15.88.7:
- primary domain: cochain-complex representatives of derived objects in
  `D(\mathrm{Mod}(\mathbf N, (A_n)))`, together with their stagewise restriction maps;
- sampled declarations:
  `SeqRingMod`,
  `DerivedCategory.Q.obj`,
  `DerivedCategory.Q.objObjPreimageIso`,
  `sequentialRingedModuleCochainEvaluationStep`,
  `cochainComplex_epi_iff_degreewise_epi`;
- best owner abstraction: a representative complex `M` together with its canonical identification
  `DerivedCategory.Q.obj M ≅ K`; the chosen preimage `DerivedCategory.Q.objPreimage K` is only an
  internal bridge to that owner surface;
- target layer here: the `source-facing` existence of a representative whose stagewise transition
  maps are termwise epimorphic, together with the bridge/view expressing the same condition as a
  complex-level `Epi`;
- primitive data: the representative complex `M` and its isomorphism `DerivedCategory.Q.obj M ≅
  K`;
- derived API: the stagewise evaluation complexes and their restriction maps; the complex-level
  `Epi` formulation is derived from the source-facing degreewise condition via
  `cochainComplex_epi_iff_degreewise_epi`.

Source/core/bridge triage:
- `source-facing`: the existence of a representative complex whose stagewise transition maps are
  termwise surjective;
- `core/canonical`: the derived-category realization owner `DerivedCategory.Q.obj`;
- `bridge/view`: the internal preimage comparison `DerivedCategory.Q.objObjPreimageIso K` and the
  cochain-level evaluation-step morphisms `sequentialRingedModuleCochainEvaluationStep A ρ n`. -/

-- Proof sketch: start from the canonical preimage complex `DerivedCategory.Q.objPreimage K`.
-- Evaluating it at each stage `n` gives the system of complexes `M_n^•`, and the structural
-- restriction maps in `\mathrm{Mod}(\mathbf N, (A_n))` induce the transition morphisms
-- `M_{n + 1}^• → M_n^•` after restriction of scalars. Apply Lemma `13.9.8` inductively to replace
-- this canonical preimage by a quasi-isomorphic complex with termwise surjective transition maps.
private theorem exists_complex_representation_with_surjective_transition_maps_to_preimage
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (α : M ⟶ DerivedCategory.Q.objPreimage K),
      QuasiIso α ∧
      ∀ n i,
        Epi (((sequentialRingedModuleCochainEvaluationStep A ρ n).app M).f i) := sorry

/-- Lemma 15.88.7: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, every object
`K ∈ D(\mathrm{Mod}(\mathbf N, (A_n)))` admits a cochain-complex representative `M^•` in
`\mathrm{Mod}(\mathbf N, (A_n))` whose evaluated transition maps
`M_{n + 1}^• → M_n^•` are termwise epimorphic, equivalently termwise surjective after
restriction of scalars along `A_{n + 1} → A_n`. -/
theorem exists_complex_representation_with_surjective_transition_maps
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n i,
        Epi (((sequentialRingedModuleCochainEvaluationStep A ρ n).app M).f i) := by
  obtain ⟨M, α, hα, hM⟩ :=
    exists_complex_representation_with_surjective_transition_maps_to_preimage K
  letI : QuasiIso α := hα
  refine ⟨M, asIso (DerivedCategory.Q.map α) ≪≫ DerivedCategory.Q.objObjPreimageIso K, hM⟩

/-- Companion bridge for Lemma 15.88.7: the same representative may be chosen so that every
evaluated transition map `M_{n + 1}^• → M_n^•` is an epimorphism of cochain complexes. -/
theorem exists_complex_representation_with_epi_transition_maps
    (K : DerivedCategory (SeqRingMod A ρ)) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n,
        Epi ((sequentialRingedModuleCochainEvaluationStep A ρ n).app M) := by
  obtain ⟨M, e, hM⟩ :=
    exists_complex_representation_with_surjective_transition_maps K
  refine ⟨M, e, ?_⟩
  intro n
  exact (cochainComplex_epi_iff_degreewise_epi
    ((sequentialRingedModuleCochainEvaluationStep A ρ n).app M)).2 (hM n)

end

/-! ### Lemma_15_88_8 (from Chap15) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
variable [∀ n : ℕ, MonoidalCategory (ModuleCat (A n))]
variable [∀ n : ℕ, (curriedTensor (ModuleCat (A n))).Additive]
variable [∀ n : ℕ,
  ∀ X : ModuleCat (A n), ((curriedTensor (ModuleCat (A n))).obj X).Additive]

attribute [local instance] seqRingMod_abelian

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

/- Domain-style sampling for Lemma 15.88.8:
- primary domain: K-flat stagewise representatives of derived objects in
  `D(\mathrm{Mod}(\mathbf N, (A_n)))`;
- sampled owner declarations:
  `SeqRingMod`,
  `DerivedCategory.Q.obj`,
  `sequentialRingedModuleCochainEval`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.exists_epi_kFlatResolution`;
- best owner abstraction: a representative complex `M` together with an isomorphism
  `DerivedCategory.Q.obj M ≅ K`, with each stagewise evaluation complex carrying the canonical
  owner predicate `IsKFlat`;
- target layer here: a source-facing existence statement asserting that the stagewise evaluations
  of one representing complex satisfy the canonical K-flatness owner;
- primitive data: the representative complex `M` and its realization isomorphism
  `DerivedCategory.Q.obj M ≅ K`;
- derived API: the stagewise K-flatness assertions obtained by applying
  `sequentialRingedModuleCochainEval` and then the owner predicate `IsKFlat`.

Source/core/bridge triage:
- `source-facing`: the existence of a representative complex whose stagewise evaluations are
  K-flat;
- `core/canonical`: `DerivedCategory.Q.obj` for the realization surface and
  `CochainComplex.IsKFlat` for the stagewise property;
- `bridge/view`: `sequentialRingedModuleCochainEvaluation`; the canonical owner-level resolution
  theorem `CochainComplex.exists_epi_kFlatResolution` from Lemma `15.59.10` belongs to the proof
  route, not to the public owner surface. -/

-- Proof sketch: first use the owner-level companion
-- `exists_complex_representation_with_epi_transition_maps` from Lemma `15.88.7` to choose a
-- representative complex `M^•` of `K` whose evaluated transition maps are epimorphisms of
-- cochain complexes; internally this is obtained by replacing the canonical preimage complex
-- `DerivedCategory.Q.objPreimage K` by a quasi-isomorphic one. Then apply the owner-level
-- stagewise resolution theorem `CochainComplex.exists_epi_kFlatResolution` from Lemma `15.59.10`
-- to the evaluated complexes, replacing each stage by a quasi-isomorphic K-flat complex while
-- preserving compatibility with the transition maps, and reassemble the resulting stagewise data
-- into a representing complex of module systems.
/-- Lemma 15.88.8: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, every object of
`D(\mathrm{Mod}(\mathbf N, (A_n)))` admits a representative by a system of cochain complexes
`(K_n^•)` in which every stage `K_n^•` is K-flat. -/
theorem exists_kFlat_complex_representation
    (K : DModSeq) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ,
        (sequentialRingedModuleCochainEval A ρ n M).IsKFlat := by
  sorry

end

/-! ### Lemma_15_88_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open BraidedCategory
open HomologicalComplex
open HomotopyCategory

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)
local notation "KModSeq" => HomotopyCategory (SeqRingMod A ρ) (up ℤ)
local notation "Qh" => (DerivedCategory.Qh : KModSeq ⥤ DModSeq)
local notation "Qis" => HomotopyCategory.quasiIso (SeqRingMod A ρ) (up ℤ)
local notation "CpxSeq" => CochainComplex (SeqRingMod A ρ) ℤ

attribute [local instance] seqRingMod_abelian seqRingMod_categoryWithHomology

variable [HasBinaryBiproducts (SeqRingMod A ρ)]
variable [HasZeroObject (SeqRingMod A ρ)]
variable [MonoidalCategory (SeqRingMod A ρ)] [SymmetricCategory (SeqRingMod A ρ)]
variable [(curriedTensor (SeqRingMod A ρ)).Additive]
variable [∀ X : SeqRingMod A ρ, ((curriedTensor (SeqRingMod A ρ)).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (SeqRingMod A ρ), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (SeqRingMod A ρ),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (SeqRingMod A ρ),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (SeqRingMod A ρ),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : SeqRingMod A ρ,
  PreservesColimit (Functor.empty.{0} (SeqRingMod A ρ)) ((curriedTensor (SeqRingMod A ρ)).obj X)]
variable [∀ X : SeqRingMod A ρ,
  PreservesColimit (Functor.empty.{0} (SeqRingMod A ρ)) ((curriedTensor (SeqRingMod A ρ)).flip.obj X)]

/-
Domain-style sampling for Lemma 15.88.9:
- primary domain: the canonical derived tensor product on
  `D(SeqRingMod A ρ) = D(\mathrm{Mod}(\mathbf N, (A_n)))`;
- sampled owner declarations:
  `cochainComplexSymmetricCategory`,
  `LocalizedMonoidal`,
  `CategoryTheory.LocalizedMonoidal`,
  `BraidedCategory.braiding`,
  `MonoidalCategory.tensorLeft`,
  `MonoidalCategory.tensorRight`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the source-facing owner is the tensor object `K ⊗ L` on
  `D(Mod(\mathbf N, (A_n)))`, coming from the localized symmetric monoidal structure on the
  derived category itself, and its owner is the symmetric monoidal tensor on `SeqRingMod A ρ`
  together with the canonical Chapter 15 symmetric monoidal structure on cochain complexes and
  the localization to homotopy and derived categories; the exactness statements belong to the
  canonical owners `tensorLeft L` and `tensorRight L`;
- primitive data: the symmetric monoidal tensor on `SeqRingMod A ρ` and the standard Chapter 15
  tensor closure on `CochainComplex (SeqRingMod A ρ) ℤ`;
- derived API: the induced symmetric monoidal structures on `K(Mod(\mathbf N, (A_n)))` and
  `D(Mod(\mathbf N, (A_n)))`, symmetry via the braiding `β_ K L`, and the owner-level
  `CommShift` / `IsTriangulated` structures on left and right tensoring.

Source/core/bridge triage:
- `source-facing`: the canonical derived tensor product on `D(Mod(\mathbf N, (A_n)))`, its
  symmetry, and its exactness in each variable;
- `core/canonical`: the symmetric monoidal tensor on `SeqRingMod A ρ`, the Chapter 15 symmetric
  monoidal structure on `CochainComplex (SeqRingMod A ρ) ℤ`, and the localized symmetric
  monoidal structures on `HomotopyCategory (SeqRingMod A ρ) (up ℤ)` and
  `DerivedCategory (SeqRingMod A ρ)`;
- `bridge/view`: none in this file.
-/

namespace SequentialRingedModules

local instance : Abelian (SeqRingMod A ρ) := seqRingMod_abelian A ρ

local instance : Preadditive (SeqRingMod A ρ) := inferInstance

local instance : CategoryWithHomology (SeqRingMod A ρ) := inferInstance

private abbrev homotopyQuotient :
    CpxSeq ⥤ KModSeq :=
  HomotopyCategory.quotient (SeqRingMod A ρ) (up ℤ)

private abbrev homotopyEquivalences :
    MorphismProperty CpxSeq :=
  HomologicalComplex.homotopyEquivalences (SeqRingMod A ρ) (up ℤ)

private abbrev homotopyQuasiIso :
    MorphismProperty KModSeq :=
  Qis

private noncomputable abbrev homotopyQuotientUnitIso :
    (homotopyQuotient : CpxSeq ⥤ KModSeq).obj (MonoidalCategoryStruct.tensorUnit CpxSeq) ≅
      (homotopyQuotient : CpxSeq ⥤ KModSeq).obj (MonoidalCategoryStruct.tensorUnit CpxSeq) :=
  Iso.refl _

local instance :
    Functor.IsLocalization
      (homotopyQuotient : CpxSeq ⥤ KModSeq)
      (homotopyEquivalences : MorphismProperty CpxSeq) :=
  (ComplexShape.up ℤ).quotient_isLocalization (fun n ↦ ⟨n - 1, by simp⟩) (SeqRingMod A ρ)

/-- Homotopy equivalences of cochain complexes of sequential ringed modules are stable under the
totalized tensor product. -/
private theorem homotopyEquivalences_isMonoidal :
    (homotopyEquivalences : MorphismProperty CpxSeq).IsMonoidal := by
  sorry

/-- The homotopy category `K(\mathrm{Mod}(\mathbf N, (A_n)))` inherits its monoidal structure by
localizing the totalized tensor product on cochain complexes of sequential ringed modules along
homotopy equivalences. -/
noncomputable instance : MonoidalCategory KModSeq := by
  let _ : SymmetricCategory CpxSeq := inferInstance
  let _ : (homotopyEquivalences : MorphismProperty CpxSeq).IsMonoidal :=
    homotopyEquivalences_isMonoidal
  change MonoidalCategory
    (LocalizedMonoidal
      (homotopyQuotient : CpxSeq ⥤ KModSeq)
      (homotopyEquivalences : MorphismProperty CpxSeq)
      homotopyQuotientUnitIso)
  infer_instance

/-- The homotopy category `K(\mathrm{Mod}(\mathbf N, (A_n)))` inherits the symmetric monoidal
structure induced from cochain complexes of sequential ringed modules. -/
noncomputable instance : SymmetricCategory KModSeq := by
  let _ : SymmetricCategory CpxSeq := inferInstance
  let _ : (homotopyEquivalences : MorphismProperty CpxSeq).IsMonoidal :=
    homotopyEquivalences_isMonoidal
  change SymmetricCategory
    (LocalizedMonoidal
      (homotopyQuotient : CpxSeq ⥤ KModSeq)
      (homotopyEquivalences : MorphismProperty CpxSeq)
      homotopyQuotientUnitIso)
  infer_instance

/-- Quasi-isomorphisms in the homotopy category of sequential ringed modules are stable under the
tensor product coming from the sequential-module tensor on `SeqRingMod A ρ`. -/
private theorem homotopyCategory_quasiIso_isMonoidal :
    (homotopyQuasiIso : MorphismProperty KModSeq).IsMonoidal := by
  sorry

/-- The monoidal structure on `D(\mathrm{Mod}(\mathbf N, (A_n)))` obtained by localizing the
tensor product on the homotopy category of complexes of sequential ringed modules. -/
noncomputable instance : MonoidalCategory DModSeq := by
  let _ : (homotopyQuasiIso : MorphismProperty KModSeq).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : MonoidalCategory
      (LocalizedMonoidal
      Qh
      (homotopyQuasiIso : MorphismProperty KModSeq)
      (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KModSeq)))))

/-- The derived category `D(\mathrm{Mod}(\mathbf N, (A_n)))` inherits the symmetric monoidal
structure obtained by localizing the symmetric tensor product on the homotopy category. -/
noncomputable instance : SymmetricCategory DModSeq := by
  let _ : (homotopyQuasiIso : MorphismProperty KModSeq).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : SymmetricCategory
      (LocalizedMonoidal
      Qh
      (homotopyQuasiIso : MorphismProperty KModSeq)
      (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KModSeq)))))

/- Lemma 15.88.9: the canonical derived tensor product on
`D(\mathrm{Mod}(\mathbf N, (A_n)))` is symmetric, via the owner braiding `β_`. -/
#check (β_ : ∀ K L : DModSeq, K ⊗ L ≅ L ⊗ K)

/- Lemma 15.88.9: tensoring on the left by a fixed object of
`D(\mathrm{Mod}(\mathbf N, (A_n)))` is exact in the triangulated sense, through the owner
structures on `tensorLeft L`. -/
noncomputable instance (L : DModSeq) :
    (tensorLeft L : DModSeq ⥤ DModSeq).CommShift ℤ := by
  sorry

instance (L : DModSeq) :
    (tensorLeft L : DModSeq ⥤ DModSeq).IsTriangulated := by
  sorry

/- Lemma 15.88.9: tensoring on the right by a fixed object of
`D(\mathrm{Mod}(\mathbf N, (A_n)))` is exact in the triangulated sense, through the owner
structures on `tensorRight L`. -/
noncomputable instance (L : DModSeq) :
    (tensorRight L : DModSeq ⥤ DModSeq).CommShift ℤ := by
  sorry

instance (L : DModSeq) :
    (tensorRight L : DModSeq ⥤ DModSeq).IsTriangulated := by
  sorry

end SequentialRingedModules

end

/-! ### Remark_15_88_10 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "KSeq" => HomotopyCategory SeqMod (up ℤ)
local notation "CpxSeq" => CochainComplex SeqMod ℤ
local notation "Δ" => (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod)

/- Domain-style sampling for Remark 15.88.10:
- primary domain: the fixed-base derived inverse-limit functor `R lim` on sequential inverse
  systems of `A`-modules, together with the fixed-right-factor derived tensor endofunctor on
  `D(ℕᵒᵖ ⥤ Mod A)`;
- sampled owner declarations:
  `CategoryTheory.additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`,
  `Functor.mapDerivedCategory`,
  `Functor.totalLeftDerived`,
  `CategoryTheory.Quotient.lift`,
  `HomologicalComplex.mapBifunctorMapHomotopy₁`,
  `Functor.totalLeftDerived`;
- best owner abstraction: the source-facing remark is the composite
  `D(A) ⥤ D(ℕᵒᵖ ⥤ Mod A) ⥤ D(ℕᵒᵖ ⥤ Mod A) ⥤ D(A)`, whose middle factor is not a new local
  public owner but a private bridge functor built by left deriving totalized tensoring with a
  chosen representative of the right factor;
- primitive vs. derived:
  primitive data are the fixed derived inverse system `E : DSeq`, the diagonal functor `Δ`, and
  the fixed-base derived inverse-limit owner
  `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`;
  derived API is the source-facing composite functor of the remark.
- source/core/bridge triage:
  `source-facing`: `derivedInverseLimitTensorFunctor`;
  `core/canonical`: `Functor.mapDerivedCategory`, `Functor.totalLeftDerived`,
    `CategoryTheory.Quotient.lift`, and
    `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`;
  `bridge/view`: the private fixed-base derived tensor helper used to express the remark as a
    composite functor without introducing a second public tensor owner. -/

/-- The pointwise tensor product on sequential inverse systems of `A`-modules is additive in each
variable. -/
local instance sequentialAModuleInverseSystem_monoidalPreadditive :
    MonoidalPreadditive SeqMod where
  whiskerLeft_zero := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (0 : Y.obj n ⟶ Z.obj n) = 0
    simp
  zero_whiskerRight := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change (0 : Y.obj n ⟶ Z.obj n) ▷ X.obj n = 0
    simp
  whiskerLeft_add := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (f.app n + g.app n) = X.obj n ◁ f.app n + X.obj n ◁ g.app n
    simp
  add_whiskerRight := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change (f.app n + g.app n) ▷ X.obj n = f.app n ▷ X.obj n + g.app n ▷ X.obj n
    simp

/-- The homotopy-category tensor-totalization functor on sequential inverse systems with fixed
right tensor factor. -/
private abbrev totalizedTensorWithFixedComplexHomotopyFunctor
    (P : CpxSeq) :
    KSeq ⥤ KSeq :=
  CategoryTheory.Quotient.lift _
    ((((curriedTensor SeqMod).map₂CochainComplex).flip.obj P) ⋙
      HomotopyCategory.quotient SeqMod (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 P)
          (curriedTensor SeqMod) (up ℤ)))

/-- The homotopy-category source functor whose total left derived functor computes tensoring by a
chosen derived inverse system `E`. -/
private abbrev tensorRightDerivedSourceFunctor
    (E : DSeq) : KSeq ⥤ DSeq :=
  totalizedTensorWithFixedComplexHomotopyFunctor
      (((DerivedCategory.Qh : KSeq ⥤ DSeq).objPreimage E).as) ⋙
    (DerivedCategory.Qh : KSeq ⥤ DSeq)

/-- Tensoring with a fixed derived inverse system admits a total left derived endofunctor on
`D(ℕᵒᵖ ⥤ Mod A)`. -/
private theorem tensorRightDerivedSourceFunctor_hasLeftDerivedFunctor
    (E : DSeq) :
    (tensorRightDerivedSourceFunctor E).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso SeqMod (up ℤ)) := sorry

/-- The fixed-right-factor derived tensor endofunctor on `D(ℕᵒᵖ ⥤ Mod A)`. This helper stays
private so the remark exposes only the source-facing composite functor below. -/
private noncomputable abbrev tensorRightDerivedFunctor
    (E : DSeq) : DSeq ⥤ DSeq :=
  letI := tensorRightDerivedSourceFunctor_hasLeftDerivedFunctor E
  (tensorRightDerivedSourceFunctor E).totalLeftDerived
    (DerivedCategory.Qh : KSeq ⥤ DSeq)
    (HomotopyCategory.quasiIso SeqMod (up ℤ))

/-- The private fixed-right-factor derived tensor helper commutes with the triangulated shift. -/
private noncomputable instance tensorRightDerivedFunctor_commShift
    (E : DSeq) :
    (tensorRightDerivedFunctor E).CommShift ℤ := sorry

/-- The private fixed-right-factor derived tensor helper is exact in the triangulated sense. -/
private theorem tensorRightDerivedFunctor_isTriangulated
    (E : DSeq) :
    (tensorRightDerivedFunctor E).IsTriangulated := sorry

/-- The constant inverse-system functor on `A`-modules is additive. -/
local instance constantInverseSystemFunctor_additive :
    ((Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod)).Additive where
  map_add := by
    intro X Y f g
    ext n x
    rfl

/-- The constant inverse-system functor on `A`-modules preserves finite limits. -/
local instance constantInverseSystemFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod) := by
  infer_instance

/-- The constant inverse-system functor on `A`-modules preserves finite colimits. -/
local instance constantInverseSystemFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod) := by
  infer_instance

/-- Remark 15.88.10: for a chosen lift `E ∈ D(ℕᵒᵖ ⥤ Mod A)` of the inverse system `(E_n)` in
`D(A)`, the functor
`K ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` is the composite of the diagonal functor
`D(A) ⥤ D(ℕᵒᵖ ⥤ Mod A)`, the fixed-right-factor derived tensor endofunctor, and the derived
inverse-limit functor from Lemma `15.88.1`. -/
abbrev derivedInverseLimitTensorFunctor
    (E : DSeq) : DMod ⥤ DMod :=
  (((Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod).mapDerivedCategory) : DMod ⥤ DSeq) ⋙
    tensorRightDerivedFunctor E ⋙
    additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
      (lim : SeqMod ⥤ ModuleCat A)

/-- The fixed-base tensor-derived-inverse-limit functor commutes with the triangulated shift. -/
noncomputable instance derivedInverseLimitTensorFunctor_commShift
    (E : DSeq) :
    (derivedInverseLimitTensorFunctor E).CommShift ℤ := by
  dsimp [derivedInverseLimitTensorFunctor]
  infer_instance

-- Proof sketch: the diagonal functor is exact because it is induced from an exact functor between
-- abelian categories, the middle tensor functor is exact by
-- `tensorRightDerivedFunctor_isTriangulated`, and the derived inverse-limit functor is exact as
-- the triangulated right derived functor used in Lemma `15.88.1`; the composite of exact
-- functors is exact.
/-- The functor `K ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` is exact in the triangulated sense. -/
theorem derivedInverseLimitTensorFunctor_isTriangulated
    (E : DSeq) :
    (derivedInverseLimitTensorFunctor E).IsTriangulated := by
  letI : (derivedInverseLimitTensorFunctor E).CommShift ℤ := by
    simpa using derivedInverseLimitTensorFunctor_commShift E
  sorry

end

/-! ### Lemma_15_88_11 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "KSeq" => HomotopyCategory SeqMod (ComplexShape.up ℤ)
local notation "CpxSeq" => CochainComplex SeqMod ℤ
local notation "Δ" => (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod)

/- Domain-style sampling for Lemma 15.88.11:
- primary domain: exactness of the fixed-left-factor functor
  `E ↦ R lim (E ⊗_A^{\mathbf L} Δ(K))` on `D(ℕᵒᵖ ⥤ Mod A)`;
- sampled owner declarations:
  `Functor.mapDerivedCategory`,
  `additiveFunctorTotalRightDerived`,
  `Functor.IsTriangulated`,
  `Functor.map_distinguished`;
- best owner abstraction: the source-facing owner remains the composite functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K`, while exactness is controlled canonically
  by `Functor.IsTriangulated`; the fixed-base derived inverse-limit factor should therefore be
  reused directly from `Lemma_15_88_1_FixedBase` rather than wrapped in a second local owner;
- primitive vs. derived:
  primitive data are the fixed object `K : D(A)` and the private derived left-tensor bridge on
  `D(ℕᵒᵖ ⥤ Mod A)`;
  derived API is the source-facing composite functor, its canonical `Functor.IsTriangulated`
  exactness theorem, and the mapped distinguished-triangle corollary;
- source/core/bridge triage:
  `source-facing`: `derivedInverseLimitTensorOnInverseSystemFunctor`, its owner-level exactness
    theorem, and the mapped-triangle corollary below;
  `core/canonical`: `Δ.mapDerivedCategory`,
    `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`,
    `Functor.IsTriangulated`, and `Functor.map_distinguished`;
  `bridge/view`: the private fixed-left-factor derived tensor helper used to express the source
    functor without introducing a second public tensor owner. -/

/-- The pointwise tensor product on sequential inverse systems of `A`-modules is additive in each
variable. -/
local instance sequentialAModuleInverseSystem_monoidalPreadditive_left :
    MonoidalPreadditive SeqMod where
  whiskerLeft_zero := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (0 : Y.obj n ⟶ Z.obj n) = 0
    simp
  zero_whiskerRight := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change (0 : Y.obj n ⟶ Z.obj n) ▷ X.obj n = 0
    simp
  whiskerLeft_add := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (f.app n + g.app n) = X.obj n ◁ f.app n + X.obj n ◁ g.app n
    simp
  add_whiskerRight := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change (f.app n + g.app n) ▷ X.obj n = f.app n ▷ X.obj n + g.app n ▷ X.obj n
    simp

/-- The constant inverse-system functor on `A`-modules is additive. -/
local instance constantSequentialAModuleFunctor_additive :
    (Δ : ModuleCat A ⥤ SeqMod).Additive := sorry

/-- The homotopy-category tensor-totalization functor on sequential inverse systems with fixed
left tensor factor. -/
private abbrev totalizedTensorWithFixedComplexHomotopyFunctor
    (P : CpxSeq) :
    KSeq ⥤ KSeq :=
  CategoryTheory.Quotient.lift _
    ((((curriedTensor SeqMod).map₂CochainComplex).obj P) ⋙
      HomotopyCategory.quotient SeqMod (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 P) h
          (curriedTensor SeqMod) (up ℤ)))

/-- The homotopy-category source functor whose total left derived functor computes tensoring on
the left by a chosen derived inverse system. -/
private abbrev tensorLeftDerivedSourceFunctor
    (K : DMod) : KSeq ⥤ DSeq :=
  totalizedTensorWithFixedComplexHomotopyFunctor
      (((DerivedCategory.Qh : KSeq ⥤ DSeq).objPreimage
        ((((Δ : ModuleCat A ⥤ SeqMod).mapDerivedCategory) : DMod ⥤ DSeq).obj K)).as) ⋙
    (DerivedCategory.Qh : KSeq ⥤ DSeq)

/-- Tensoring on the left with a fixed derived inverse system admits a total left derived
endofunctor on `D(ℕᵒᵖ ⥤ Mod A)`. -/
private theorem tensorLeftDerivedSourceFunctor_hasLeftDerivedFunctor
    (K : DMod) :
    (tensorLeftDerivedSourceFunctor K).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso SeqMod (up ℤ)) := sorry

/-- The fixed-left-factor derived tensor endofunctor on `D(ℕᵒᵖ ⥤ Mod A)`. This helper stays
private so the lemma exposes only the source-facing composite functor below. -/
private noncomputable abbrev tensorLeftDerivedFunctor
    (K : DMod) : DSeq ⥤ DSeq :=
  letI := tensorLeftDerivedSourceFunctor_hasLeftDerivedFunctor K
  (tensorLeftDerivedSourceFunctor K).totalLeftDerived
    (DerivedCategory.Qh : KSeq ⥤ DSeq)
    (HomotopyCategory.quasiIso SeqMod (up ℤ))

/-- The private fixed-left-factor derived tensor helper admits a shift-commuting structure. -/
private theorem tensorLeftDerivedFunctor_commShift_exists
    (K : DMod) :
    Nonempty ((tensorLeftDerivedFunctor K).CommShift ℤ) := by
  sorry

/-- A private shift-commuting witness for the fixed-left-factor derived tensor helper, used only
to form the mapped distinguished triangle below. -/
private noncomputable instance tensorLeftDerivedFunctor_commShift
    (K : DMod) :
    (tensorLeftDerivedFunctor K).CommShift ℤ :=
  Classical.choice (tensorLeftDerivedFunctor_commShift_exists K)

/-- For a fixed `K ∈ D(A)`, this is the exact functor
`E ↦ R lim (E ⊗_A^{\mathbf L} Δ(K))` on `D(ℕᵒᵖ ⥤ Mod A)`, canonically identifying with the
textbook construction `E ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` from Remark `15.88.10` by symmetry of
the derived tensor product. -/
abbrev derivedInverseLimitTensorOnInverseSystemFunctor
    (K : DMod) : DSeq ⥤ DMod :=
  tensorLeftDerivedFunctor K ⋙
    additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
      (lim : SeqMod ⥤ ModuleCat A)

/-- A private shift-commuting witness for the source-facing tensor-derived-inverse-limit functor,
used only to state its mapped-triangle output canonically. -/
private noncomputable instance derivedInverseLimitTensorOnInverseSystemFunctor_commShift
    (K : DMod) :
    (derivedInverseLimitTensorOnInverseSystemFunctor K).CommShift ℤ := by
  letI : (tensorLeftDerivedFunctor K).CommShift ℤ :=
    tensorLeftDerivedFunctor_commShift K
  dsimp [derivedInverseLimitTensorOnInverseSystemFunctor]
  infer_instance

-- Proof sketch: the constant-system functor sends `K` to the diagonal inverse system `Δ(K)`,
-- and the derived tensor product is exact in each variable; composing with the fixed-base
-- derived inverse-limit functor therefore sends distinguished triangles in
-- `D(ℕᵒᵖ ⥤ Mod A)` to distinguished triangles in `D(A)`.
/-- The functor `E ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` is exact in the triangulated sense. -/
theorem derivedInverseLimitTensorOnInverseSystemFunctor_isTriangulated
    (K : DMod) :
    (derivedInverseLimitTensorOnInverseSystemFunctor K).IsTriangulated := by
  sorry

/-- Lemma 15.88.11: if `T` is a distinguished triangle in `D(\mathbf N, A)`, then for every
`K ∈ D(A)` the canonical triangle obtained by applying
`E ↦ R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E)` is distinguished in `D(A)`. In the
notation of the text, for `T = (E ⟶ D ⟶ F ⟶ E[1])` this is the canonical distinguished triangle
`R \!\varprojlim (K \otimes_A^{\mathbf L} E_n) ⟶
R \!\varprojlim (K \otimes_A^{\mathbf L} D_n) ⟶
R \!\varprojlim (K \otimes_A^{\mathbf L} F_n) ⟶
R \!\varprojlim (K \otimes_A^{\mathbf L} E_n)[1]` from Remark `15.88.10`. -/
theorem derivedInverseLimitTensorOnInverseSystemFunctor_map_distinguished
    (K : DMod) (T : Triangle DSeq) (hT : T ∈ distTriang DSeq) :
    ((derivedInverseLimitTensorOnInverseSystemFunctor K).mapTriangle.obj T) ∈ distTriang DMod :=
  by
    letI : (derivedInverseLimitTensorOnInverseSystemFunctor K).IsTriangulated :=
      derivedInverseLimitTensorOnInverseSystemFunctor_isTriangulated K
    simpa using (derivedInverseLimitTensorOnInverseSystemFunctor K).map_distinguished T hT

end

/-! ### Lemma_15_88_12 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open SequentialProObjectMorphismRep

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod

/- Domain-style sampling for Lemma 15.88.12:
- primary domain: fixed-base derived inverse limits of sequential inverse systems of `A`-modules,
  together with the exact tensor-induced functors on `D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`;
- sampled owner declarations:
  `stagewiseModuleDerivedLimitTower`,
  `stagewiseModuleDerivedLimitTowerFunctor`,
  `derivedInverseLimitTensorOnInverseSystemFunctor`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the source-facing theorem should use the Chapter 15 exact functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K : D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)
    ⥤ D(A)`, while the stagewise comparison should be expressed as the canonical stagewise tower
  in `D(A)` obtained from the upstream bridge owner `stagewiseModuleDerivedLimitTowerFunctor`;
- primitive data: a morphism `φ : E ⟶ D` in `D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)` and
  its image under the canonical stagewise tower functor in `D(A)`;
- derived API: the induced map of the stagewise tower functor and the induced map of the exact owner functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K`.

Source/core/bridge triage:
- `source-facing`: the isomorphism statement for
  `R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E) ⟶
    R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} D)`;
- `core/canonical`: `derivedInverseLimitTensorOnInverseSystemFunctor`,
  `stagewiseModuleDerivedLimitTowerFunctor`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the canonical stagewise tower functor
  `stagewiseModuleDerivedLimitTowerFunctor`. -/

-- Proof sketch: the exact owner functor
-- `derivedInverseLimitTensorOnInverseSystemFunctor K` first tensors the inverse system by the
-- fixed factor `K` and then applies `R lim`. Tensoring stagewise preserves the assumed
-- pro-isomorphism of the towers, so Lemma `15.87.13` applied to the tensorized stagewise map
-- yields an isomorphism on the resulting derived inverse limits.
/-- Lemma 15.88.12: let `A` be a ring and let `φ : E ⟶ D` be a morphism in
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`. If the induced stagewise morphism
`(E_n^\bullet) \to (D_n^\bullet)` is an isomorphism of pro-objects in `D(A)`, then for every
`K ∈ D(A)` the corresponding map
`R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E) ⟶
  R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} D)`
is an isomorphism. This is the fixed-base owner-level form of the textbook map
`R \!\varprojlim_n (K \otimes_A^{\mathbf L} E_n) ⟶
  R \!\varprojlim_n (K \otimes_A^{\mathbf L} D_n)`. -/
theorem isIso_map_derivedInverseLimitTensorOnInverseSystemFunctor_of_stagewise_proIsomorphism
    {E D : DSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans ((stagewiseModuleDerivedLimitTowerFunctor A).map φ)).toProObjectHom)
    (K : DMod) :
    IsIso ((derivedInverseLimitTensorOnInverseSystemFunctor K).map φ) := by
  sorry

end
