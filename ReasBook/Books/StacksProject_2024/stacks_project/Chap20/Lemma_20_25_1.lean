import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap20.Lemma_20_10_2
import StacksProject_2024.Chap20.Bounded_below_derived_sections_at_open
import StacksProject_2024.Chap20.Sections_on_open
import StacksProject_2024.Chap20.«20_11_0_2»
import StacksProject_2024.Chap20.«20_9_0_1»
import StacksProject_2024.Chap20.«20_14_1_1»
import StacksProject_2024.Chap20.«20_25_3_2»

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open DerivedCategory.TStructure
open ComplexShape HomologicalComplex₂

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "TopOpen" => (⊤ : Opens X.carrier)

/- Domain-style sampling for Lemma 20.25.1:
- primary domain: Čech-to-derived-global-sections comparison for bounded-below complexes of
  `𝒪_X`-modules on a ringed space, with the natural target owner level
  `ModuleCat (globalSectionsRing X)`;
- sampled owner declarations:
  `RingedSpace.hasFiniteProducts_over`,
  `moduleGlobalSectionsFunctor`,
  `ringedSpaceModuleCechComplexFunctor`,
  `ringedSiteModuleCechCohomology`,
  `sectionsRingOnOpen`,
  `moduleSectionsEvaluation_additive`,
  `ObjectProperty.lift`,
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `Functor.HasRightDerivedFunctor`,
  `Functor.totalRightDerived`;
- best owner abstraction: the bounded-below comparison should be centered on the
  `Γ(X, 𝒪_X)`-module-valued owners `moduleGlobalSectionsFunctor`,
  `ringedSpaceModuleCechComplexFunctor (⊤ : Opens X.carrier)`, and the chapter-level bounded-below
  derived-sections owner `boundedBelowDerivedSectionsAtOpen ⊤`; the source-facing comparison
  should target the canonical composite from bounded-below complexes into that owner, with
  forgetting to `AddCommGrpCat` treated only as a bridge/view;
- primitive data: the ringed space `X`, the indexed family of opens `𝒰`, and a bounded-below
  complex `K : CochainComplex.Plus (RingedSpace.Modules X)`;
- derived API: the bounded-below total Čech functor, the bounded-below derived global-sections
  functor, the comparison natural transformation, and the resulting spectral-sequence existence
  theorem.

Source/core/bridge triage:
- `source-facing`: existence of a Čech-to-derived-global-sections comparison with the injective-
  case isomorphism property, and the spectral-sequence existence theorem
  `exists_moduleCechToDerivedGlobalSectionsSpectralSequence`;
- `core/canonical`: `moduleGlobalSectionsFunctor`, `ringedSpaceModuleCechComplexFunctor`,
  `ringedSiteModuleCechCohomology`, `sectionsRingOnOpen`, `ObjectProperty.lift`,
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`, `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `Functor.totalRightDerived`, and `FilteredComplex.convergesToCohomology`;
- `bridge/view`: forgetting the resulting `Γ(X, 𝒪_X)`-module-valued constructions to
  `AddCommGrpCat`.

This file keeps only the local bounded-below comparison layer; the public owners now stay at the
canonical `Γ(X, 𝒪_X)`-module level, with additive forgetting left to existing bridge
functors. -/

/-- The bounded-below Čech complex functor on `𝒪_X`-modules for the cover `𝒰`. -/
private abbrev moduleCechComplexFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    RingedSpace.Modules X ⥤ CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℕ :=
  let F : RingedSpace.PresheafModules X ⥤
      CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℕ :=
    ringedSpaceModuleCechComplexFunctor (⊤ : Opens X.carrier)
      (fun i ↦ Over.mk (Opens.leTop (𝒰 i)))
  SheafOfModules.forget (RingedSpace.ringCatSheaf X) ⋙ F

private instance moduleCechComplexFunctor_preservesZeroMorphisms
    (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    (moduleCechComplexFunctor X 𝒰).PreservesZeroMorphisms := by
  change
    ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)) ⋙
      ringedSpaceModuleCechComplexFunctor (⊤ : Opens X.carrier)
        (fun i ↦ Over.mk (Opens.leTop (𝒰 i)))).PreservesZeroMorphisms
  infer_instance

/-- The extended Čech row functor on `𝒪_X`-modules for the cover `𝒰`. -/
private abbrev moduleCechRowFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    RingedSpace.Modules X ⥤ CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ :=
  moduleCechComplexFunctor X 𝒰 ⋙
    embeddingUpNat.extendFunctor (ModuleCat.{u} (globalSectionsRing X))

private instance moduleCechRowFunctor_preservesZeroMorphisms
    (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    (moduleCechRowFunctor X 𝒰).PreservesZeroMorphisms := by
  let _ := moduleCechComplexFunctor_preservesZeroMorphisms X 𝒰
  infer_instance

/-- The total Čech complex functor on cochain complexes of `𝒪_X`-modules, valued in
cochain complexes of `Γ(X, 𝒪_X)`-modules, built from the Chapter 20 Čech owner
`ringedSpaceModuleCechComplexFunctor`. -/
private abbrev moduleCechDoubleFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) (up ℤ) :=
  (moduleCechRowFunctor X 𝒰).mapHomologicalComplex (up ℤ)

/-- The total Čech complex functor on cochain complexes of `𝒪_X`-modules, valued in
cochain complexes of `Γ(X, 𝒪_X)`-modules, built from the Chapter 20 Čech owner
`ringedSpaceModuleCechComplexFunctor`. -/
private abbrev moduleTotalCechComplexFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      HomologicalComplex (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) :=
  moduleCechDoubleFunctor X 𝒰 ⋙
    (totalFunctor (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) (up ℤ) (up ℤ) :
      HomologicalComplex₂ (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) (up ℤ) ⥤
        HomologicalComplex (ModuleCat.{u} (globalSectionsRing X)) (up ℤ))

-- Proof sketch: the Čech direction is supported in nonnegative degrees, and the input complex is
-- bounded below, so only finitely many summands contribute to sufficiently negative total degrees.
-- Hence the total complex remains bounded below.
/-- The total Čech complex of a bounded-below complex of `𝒪_X`-modules is again bounded
below. -/
private theorem moduleTotalCechComplex_obj_mem (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    CochainComplex.plus (ModuleCat.{u} (globalSectionsRing X))
      ((moduleTotalCechComplexFunctor X 𝒰).obj K.obj) := by
  rcases (CochainComplex.plus_iff (RingedSpace.Modules X) K.obj).1 K.property with ⟨a, ha⟩
  refine (CochainComplex.plus_iff (ModuleCat.{u} (globalSectionsRing X)) _).2 ⟨a, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  let B : HomologicalComplex₂ (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) (up ℤ) :=
    (moduleCechDoubleFunctor X 𝒰).obj K.obj
  let A : CochainComplex (CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ) ℤ :=
    B
  have hzeroFunctor :
      IsZero
        (Discrete.functor
          (B.toGradedObject.mapObjFun (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) n)) := by
    rw [Functor.isZero_iff]
    rintro ⟨⟨p, q⟩, hpq⟩
    dsimp
    by_cases hp : p < a
    · have hzeroColumn : IsZero (A.X p) := by
        let _ : CochainComplex.IsStrictlyGE A a := by
          change
            CochainComplex.IsStrictlyGE
              (((moduleCechRowFunctor X 𝒰).mapHomologicalComplex (up ℤ)).obj K.obj) a
          let _ : K.obj.IsStrictlyGE a := ha
          infer_instance
        exact A.isZero_of_isStrictlyGE a p hp
      simpa [A, moduleCechDoubleFunctor, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
        (HomologicalComplex.eval (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) q).map_isZero
          hzeroColumn
    · have hq : q < 0 := by
        have hpq' : p + q = n := by
          simpa using hpq
        have hpa : a ≤ p := le_of_not_gt hp
        omega
      have hzeroEntry :
          IsZero (((moduleCechRowFunctor X 𝒰).obj (K.obj.X p)).X q) := by
        let _ : CochainComplex.IsStrictlyGE ((moduleCechRowFunctor X 𝒰).obj (K.obj.X p)) 0 := by
          simpa [moduleCechRowFunctor] using
            (inferInstance :
              CochainComplex.IsStrictlyGE
                (((moduleCechComplexFunctor X 𝒰).obj (K.obj.X p)).extend embeddingUpNat) 0)
        exact ((moduleCechRowFunctor X 𝒰).obj (K.obj.X p)).isZero_of_isStrictlyGE 0 q hq
      simpa [A, moduleCechDoubleFunctor, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
        hzeroEntry
  have hzeroDegree :
      IsZero (B.toGradedObject.mapObj (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) n) :=
    (B.toGradedObject.isColimitCofanMapObj (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) n).isZero_pt
      hzeroFunctor
  simpa [A, B, moduleTotalCechComplexFunctor, moduleCechDoubleFunctor,
    HomologicalComplex₂.totalFunctor, HomologicalComplex₂.total] using hzeroDegree

/-- The canonical bounded-below lift of the total Čech complex functor on
`𝒪_X`-modules, built from the Chapter 20 Čech owner
`ringedSpaceModuleCechComplexFunctor`. -/
private abbrev moduleTotalCechComplexToPlus (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤
      CochainComplex.Plus (ModuleCat.{u} (globalSectionsRing X)) :=
  (CochainComplex.plus (ModuleCat.{u} (globalSectionsRing X))).lift
    (CochainComplex.Plus.ι (RingedSpace.Modules X) ⋙ moduleTotalCechComplexFunctor X 𝒰)
    (moduleTotalCechComplex_obj_mem X 𝒰)

section DerivedComparison

variable (X)
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow (moduleGlobalSectionsFunctor X))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]

attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

local notation "ΓModX" => ModuleCat (globalSectionsRing X)
local notation "KplusMod" => CochainComplex.Plus (RingedSpace.Modules X)
local notation "DplusΓX" => boundedBelowDerivedCategory ΓModX
local notation "HΓX" => DerivedCategory.homologyFunctor ΓModX
local notation "QplusModX" =>
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 (RingedSpace.Modules X))
local notation "KplusToDplusModX" =>
  HomotopyCategory.Plus.quotient (RingedSpace.Modules X) ⋙ QplusModX
local notation "QplusΓX" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 ΓModX)
local notation "KplusToDplusΓX" =>
  HomotopyCategory.Plus.quotient ΓModX ⋙ QplusΓX
local notation "RΓplus" => boundedBelowDerivedGlobalSections X

/-- The bounded-below derived functor represented by total Čech complexes for the family `𝒰`. -/
abbrev moduleCechDerivedFunctor (𝒰 : ι → Opens X.carrier) :
    KplusMod ⥤ DplusΓX :=
  moduleTotalCechComplexToPlus X 𝒰 ⋙ KplusToDplusΓX

/-- A comparison from bounded-below total Čech complexes to bounded-below derived global sections
has the expected computation property if it becomes an isomorphism on every bounded-below complex
whose terms are injective `𝒪_X`-modules. -/
def IsModuleCechToDerivedGlobalSectionsComparison
    (𝒰 : ι → Opens X.carrier)
    (τ : moduleCechDerivedFunctor X 𝒰 ⟶ KplusToDplusModX ⋙ RΓplus) : Prop :=
  ∀ K : KplusMod,
    (∀ q : ℤ, Injective (K.obj.X q)) → IsIso (τ.app K)

omit [EnoughInjectives (RingedSpace.Modules X)] in
/-- A comparison with the injective-case computation property is an isomorphism on any bounded-
below complex whose terms are injective `𝒪_X`-modules. -/
instance IsModuleCechToDerivedGlobalSectionsComparison.isIso_app
    {𝒰 : ι → Opens X.carrier}
    {τ : moduleCechDerivedFunctor X 𝒰 ⟶ KplusToDplusModX ⋙ RΓplus}
    (hτ : IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ)
    (K : KplusMod) (hK : ∀ q : ℤ, Injective (K.obj.X q)) :
    IsIso (τ.app K) :=
  hτ K hK

-- Proof sketch: choose a bounded-below injective resolution of the input complex, form the
-- rowwise Čech double complex on that injective resolution, and compare both the total Čech
-- complex and the derived global-sections complex with the total complex of the double complex.
-- Injective sheaf modules are Čech-acyclic on an open cover, so the resulting comparison is a
-- quasi-isomorphism and is natural in the input complex.
/-- Lemma 20.25.1: for an open covering `𝒰 : X = ⋃ i, U_i` of a ringed space `X`, there is a
comparison natural transformation from the total Čech complex functor on bounded-below complexes
of `𝒪_X`-modules to the bounded-below derived global-sections functor `RΓ(X, -)` which is an
isomorphism on bounded-below complexes of injective `𝒪_X`-modules. -/
@[stacks 08BN]
theorem exists_moduleCechToDerivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ : moduleCechDerivedFunctor X 𝒰 ⟶ KplusToDplusModX ⋙ RΓplus,
      IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ := sorry

-- Proof sketch: choose a Cartan-Eilenberg resolution of the bounded-below complex `K`, apply the
-- Čech construction rowwise to obtain a triple complex, reinterpret it as a double complex, and
-- then take the second spectral sequence. The `E₂`-page identifies with Čech cohomology of the
-- cohomology sheaves, and convergence follows from the boundedness of the Cartan-Eilenberg model.
/-- A bounded-below Čech-to-hypercohomology spectral sequence for an open cover of a ringed space.
-/
theorem exists_moduleCechToDerivedGlobalSectionsSpectralSequence
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (K : KplusMod) :
    ∃ (filteredComplex : FilteredComplex ΓModX)
      (spectralSequence : CohomologicalSpectralSequence ΓModX 0)
      (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso : ∀ p : ℕ, ∀ q : ℤ,
        (spectralSequence.page 2).X (Int.ofNat p, q) ≅
          ringedSpaceModuleCechCohomology TopOpen
            (fun i ↦ Over.mk (Opens.leTop (𝒰 i)))
            ((SheafOfModules.forget X.ringCatSheaf).obj (K.obj.homology q)) p)
      (targetIso : ∀ n : ℤ,
        filteredComplex.underlying.homology n ≅
          (HΓX n).obj
            ((moduleDerivedGlobalSections X).obj
              (DerivedCategory.Q.obj K.obj))),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

end DerivedComparison

end AlgebraicGeometry.RingedSpace
