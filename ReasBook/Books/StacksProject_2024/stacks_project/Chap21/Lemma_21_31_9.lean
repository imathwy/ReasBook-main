import StacksProject_2024.Chap21.Situation_21_30_1
import StacksProject_2024.Chap21.«21_31_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open TopologicalSpace
noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

/- Domain-style sampling for Lemma 21.31.9:
- primary domain: the qc/Zariski comparison situation on `LC`, with source subcategories
  `A'_X = essImage(π_X⁻¹)` on the localized Zariski slice sites;
- inspected owner declarations:
  `CohomologyComparisonSituation`,
  `Functor.essImage`,
  `Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous`,
  `lcZar_pi_pullback_pushforward_unit_isIso`,
  `proper_smallPushforward_piInverse_isomorphic_lcZarPushforward_piInverse`;
- best owner abstraction: the source-facing owner is still the essential-image object property
  `Functor.essImage (piInverseAb (τzar.over X) (πFunctor X))`; the full
  `CohomologyComparisonSituation` is only a later bridge obtained once the separate
  qc-covering-refinement clause is supplied;
- primitive vs derived: the primitive data here are only the localized Zariski inverse-image owner
  `piInverseAb`, the proper-map morphism property on `LCCat`, and the qc/Zariski comparison
  `τzar ≤ τqc`; weak-Serre closure and clauses `(1)`–`(5)` of Situation `21.30.1` are derived
  API and should not remain primitive hypotheses.

Source/core/bridge triage:
- `source-facing`: the weak-Serre statement and clauses `(1)`–`(5)` for
  `A'_X = essImage(π_X⁻¹)`;
- `core/canonical`: `Functor.essImage`, `piInverseAb`, and the proper-map owner `lcProper` on
  `LCCat`;
- `bridge/view`: the final theorem
  `lc_qc_lc_zar_cohomology_comparison_situation_of_tau_covering_refinement`, which packages those
  source-facing clauses into the Chapter `21.30` owner once the extra refinement clause is given
  separately.
-/

/-- The morphism property on `LC` consisting of proper maps. -/
abbrev lcProper : MorphismProperty LCCat.{u} :=
  fun _ _ f ↦ IsProperMap f.hom

/-- The source-facing comparison subcategory `A'_X = essImage (π_X⁻¹)` on the localized Zariski
slice site over `X`. -/
abbrev piInverseAbEssImage
    (τzar : GrothendieckTopology LCCat.{u})
    (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
    [∀ X : LCCat.{u},
      Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [∀ X : LCCat.{u},
      ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
    (X : LCCat.{u}) :
    ObjectProperty (Sheaf (τzar.over X) AddCommGrpCat.{u + 1}) :=
  Functor.essImage (piInverseAb (τzar.over X) (πFunctor X))

/- Source-facing notation for the comparison subcategory `A'_X = essImage (π_X⁻¹)`. -/
scoped notation "A'[" τzar ", " πFunctor "]_(" X ")" =>
  piInverseAbEssImage τzar πFunctor X

open scoped CategoryTheory.GrothendieckTopology

section ProperMaps

/-- Lemma 21.31.9 (1): proper maps in `LC` admit pullbacks. -/
@[stacks 0EZI]
theorem lc_proper_hasPullbacks :
    lcProper.HasPullbacks := by
  sorry

/-- Lemma 21.31.9 (2): proper maps in `LC` are stable under base change. -/
@[stacks 0EZI]
theorem lc_proper_isStableUnderBaseChange :
    lcProper.IsStableUnderBaseChange := by
  sorry

/-- Companion instance for Lemma 21.31.9 (1): proper maps in `LC` admit pullbacks. -/
instance instLcProperHasPullbacks : lcProper.HasPullbacks :=
  lc_proper_hasPullbacks

/-- Companion instance for Lemma 21.31.9 (2): proper maps in `LC` are stable under base change. -/
instance instLcProperIsStableUnderBaseChange : lcProper.IsStableUnderBaseChange :=
  lc_proper_isStableUnderBaseChange

end ProperMaps

section PiInverseEssImage

variable (τzar : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]

/-- Lemma 21.31.9 (3): the essential image `A'_X = essImage (π_X⁻¹)` is a weak Serre
subcategory of `Ab(LC_{Zar}/X)`. -/
@[stacks 0EZI]
theorem piInverseAb_essImage_isWeakSerre
    (X : LCCat.{u}) :
    IsWeakSerreClass (A'[τzar, πFunctor]_(X)) := by
  sorry

/-- Lemma 21.31.9 (4): inverse image along `f : X ⟶ Y` preserves objects of the form
`π_Y⁻¹ ℱ`. -/
@[stacks 0EZI]
theorem piInverseAb_essImage_inverseImage_mem
    {X Y : LCCat.{u}} (f : X ⟶ Y)
    {ℱ : Sheaf (τzar.over Y) AddCommGrpCat.{u + 1}}
    (hℱ : A'[τzar, πFunctor]_(Y) ℱ) :
    A'[τzar, πFunctor]_(X)
      ((τzar.overMapPullback AddCommGrpCat.{u + 1} f).obj ℱ) := by
  sorry

end PiInverseEssImage

section CoarserSheaf

variable (τzar τqc : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]

/-- Lemma 21.31.9 (5): every object of `A'_X` is already a sheaf for the qc topology. -/
@[stacks 0EZI]
theorem piInverseAb_essImage_isSheaf_for_qc
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}} {ℱ : Sheaf (τzar.over X) AddCommGrpCat.{u + 1}}
    (hℱ : A'[τzar, πFunctor]_(X) ℱ) :
    Presheaf.IsSheaf (τqc.over X) ℱ.1 := by
  sorry

end CoarserSheaf

section HigherDirectImage

variable (τzar : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u}, HasInjectiveResolutions (Sheaf (τzar.over X) AddCommGrpCat.{u + 1})]
variable [∀ {X Y : LCCat.{u}} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (τzar.over X) (τzar.over Y))]

/-- Lemma 21.31.9 (6): proper higher direct images preserve the essential image of `π_X⁻¹`. -/
@[stacks 0EZI]
theorem piInverseAb_essImage_higherDirectImage_mem
    {X Y : LCCat.{u}} (f : X ⟶ Y) (hf : lcProper f) (i : ℕ)
    {ℱ : Sheaf (τzar.over X) AddCommGrpCat.{u + 1}}
    (hℱ : A'[τzar, πFunctor]_(X) ℱ) :
    A'[τzar, πFunctor]_(Y)
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (τzar.over X) (τzar.over Y)).rightDerived i).obj ℱ) := by
  sorry

end HigherDirectImage

section SituationBridge

variable (τzar τqc : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [hInjectiveResolutions :
  ∀ X : LCCat.{u}, HasInjectiveResolutions (Sheaf (τzar.over X) AddCommGrpCat.{u + 1})]
variable [hAdditive :
  ∀ {X Y : LCCat.{u}} (f : X ⟶ Y),
    Functor.Additive
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (τzar.over X) (τzar.over Y))]

/-- Bridge to Situation `21.30.1`: once the separate qc-covering-refinement clause is available,
Lemma `21.31.9` packages the weak-Serre statement and clauses `(1)`–`(5)` into the canonical
comparison-situation owner. -/
theorem lc_qc_lc_zar_cohomology_comparison_situation_of_tau_covering_refinement
    (hle : τzar ≤ τqc)
    (tau_covering_refinement :
      ∀ {U : LCCat.{u}} {ι : Type (u + 1)} (cover : ι → Over U),
        (τqc.over U).CoversTop cover →
          ∃ (J : Type (u + 1)) (V : J → Over U),
                (τzar.over U).CoversTop V ∧
                  ∃ (W : J → LCCat.{u}) (f : ∀ j, W j ⟶ (V j).left),
                    ∀ j,
                              lcProper (f j) ∧
                    Sieve.generate (Presieve.singleton (f j)) ∈ τqc (V j).left ∧
                      ∃ (Kj : Type (u + 1)) (Wcoverj : Kj → Over (W j)),
                        (τzar.over (W j)).CoversTop Wcoverj ∧
                          ∀ k : Kj,
                            ∃ i : ι,
                              Nonempty
                                ((Over.mk ((Wcoverj k).hom ≫ f j ≫ (V j).hom)) ⟶ cover i)) :
    CohomologyComparisonSituation τqc τzar lcProper
      (fun X : LCCat.{u} ↦ A'[τzar, πFunctor]_(X)) := by
  refine
    { isWeakSerre := by
        intro X _
        exact piInverseAb_essImage_isWeakSerre τzar πFunctor X
      hasPullbacks := inferInstance
      isStableUnderBaseChange := inferInstance
      inverseImage_mem := by
        intro X Y f ℱ hℱ
        simpa using piInverseAb_essImage_inverseImage_mem τzar πFunctor f hℱ
      isSheaf_for_coarser_topology := by
        intro X ℱ hℱ
        simpa using piInverseAb_essImage_isSheaf_for_qc τzar τqc πFunctor hle hℱ
      higherDirectImage_mem := by
        intro _ _ _ X Y f hf i ℱ hℱ
        let _ := hInjectiveResolutions
        let _ := @hAdditive
        exact piInverseAb_essImage_higherDirectImage_mem τzar πFunctor f hf i hℱ
      tau_covering_refinement := fun cover hcover ↦ tau_covering_refinement cover hcover }

/-- Companion instance for the bridge theorem
`lc_qc_lc_zar_cohomology_comparison_situation_of_tau_covering_refinement`. -/
instance instLcQcLcZarCohomologyComparisonSituationOfTauCoveringRefinement
    (hle : τzar ≤ τqc)
    (tau_covering_refinement :
      ∀ {U : LCCat.{u}} {ι : Type (u + 1)} (cover : ι → Over U),
        (τqc.over U).CoversTop cover →
          ∃ (J : Type (u + 1)) (V : J → Over U),
                (τzar.over U).CoversTop V ∧
                  ∃ (W : J → LCCat.{u}) (f : ∀ j, W j ⟶ (V j).left),
                    ∀ j,
                              lcProper (f j) ∧
                    Sieve.generate (Presieve.singleton (f j)) ∈ τqc (V j).left ∧
                      ∃ (Kj : Type (u + 1)) (Wcoverj : Kj → Over (W j)),
                        (τzar.over (W j)).CoversTop Wcoverj ∧
                          ∀ k : Kj,
                            ∃ i : ι,
                              Nonempty
                                ((Over.mk ((Wcoverj k).hom ≫ f j ≫ (V j).hom)) ⟶ cover i)) :
    CohomologyComparisonSituation τqc τzar lcProper
      (fun X : LCCat.{u} ↦ A'[τzar, πFunctor]_(X)) :=
  lc_qc_lc_zar_cohomology_comparison_situation_of_tau_covering_refinement
    τzar τqc πFunctor hle tau_covering_refinement

end SituationBridge

end CategoryTheory.GrothendieckTopology
