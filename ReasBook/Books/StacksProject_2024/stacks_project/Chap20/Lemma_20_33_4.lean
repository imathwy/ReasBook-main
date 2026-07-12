import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap20.«20_11_0_1»
import StacksProject_2024.Chap20.Sections_on_open
import StacksProject_2024.Chap20.Sections_on_open_global
import StacksProject_2024.Chap21.DerivedCategoryExact

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceDerivedSectionsAtOpenToAb RingedSpaceOpenHypercohomology

section

variable {X : RingedSpace.{u}}
variable [IsGrothendieckAbelian X.Modules]

local notation "DModX" => DerivedCategory X.Modules
local notation "DAb" => DerivedCategory AddCommGrpCat
local notation "DΓX" =>
  DerivedCategory (ModuleCat (sectionsRingOnOpen X (⊤ : Opens X.carrier)))
local notation "QModX" => (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules)
local notation "QisModX" => HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)

private abbrev moduleSectionsToDerived
    (U : Opens X.carrier) :
    CochainComplex X.Modules ℤ ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

private abbrev moduleSectionsRestrictionFunctorOfLE
    {W U : Opens X.carrier} (h : W ≤ U) :
    ModuleCat (sectionsRingOnOpen X W) ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom

private instance moduleSectionsRestrictionFunctorOfLE_additive
    {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleSectionsRestrictionFunctorOfLE h).Additive := by
  infer_instance

private abbrev moduleSectionsRestrictionCompFunctorOfLE
    {W U : Opens X.carrier} (h : W ≤ U) :
    X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op W)) ⋙
    moduleSectionsRestrictionFunctorOfLE h

/-- The derived restriction-of-scalars functor on section modules induced by an inclusion
`W ⊆ U` of opens in a fixed ringed space. -/
abbrev moduleSectionsRestrictionDerivedOfLE
    {W U : Opens X.carrier} (h : W ≤ U) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X W)) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  let _ : PreservesFiniteLimits (moduleSectionsRestrictionFunctorOfLE h) :=
    ((exactFunctor_iff (moduleSectionsRestrictionFunctorOfLE h)).mp
      (restrictScalars_exact (X.presheaf.map (homOfLE h).op).hom)).1
  let _ : PreservesFiniteColimits (moduleSectionsRestrictionFunctorOfLE h) :=
    ((exactFunctor_iff (moduleSectionsRestrictionFunctorOfLE h)).mp
      (restrictScalars_exact (X.presheaf.map (homOfLE h).op).hom)).2
  (moduleSectionsRestrictionFunctorOfLE h).mapDerivedCategory

private instance moduleSectionsRestrictionComp_additive
    {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleSectionsRestrictionCompFunctorOfLE h).Additive where
  map_add := by
    intro ℱ 𝒢 φ ψ
    rfl

private instance moduleSectionsRestrictionComp_preservesZeroMorphisms
    {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleSectionsRestrictionCompFunctorOfLE h).PreservesZeroMorphisms where
  map_zero := by
    intro ℱ 𝒢
    rfl

private abbrev moduleSectionsRestrictionNatTransOfLE
    {W U : Opens X.carrier} (h : W ≤ U) :
    SheafOfModules.evaluation X.ringCatSheaf (op U) ⟶
      moduleSectionsRestrictionCompFunctorOfLE h where
  app ℱ := ℱ.val.map (homOfLE h).op
  naturality {ℱ 𝒢} φ := by
    ext x
    simp [moduleSectionsRestrictionFunctorOfLE]
    simpa using
      DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom ((φ.val.naturality (homOfLE h).op).symm))
        x

private noncomputable def moduleSectionsToDerivedRestrictionIso
    {W U : Opens X.carrier} (h : W ≤ U) :
    ((moduleSectionsRestrictionCompFunctorOfLE h).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q) ≅
      moduleSectionsToDerived W ⋙ moduleSectionsRestrictionDerivedOfLE h := by
  let evalH := (SheafOfModules.evaluation X.ringCatSheaf (op W)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let _ : PreservesFiniteLimits (moduleSectionsRestrictionFunctorOfLE h) :=
    ((exactFunctor_iff (moduleSectionsRestrictionFunctorOfLE h)).mp
      (restrictScalars_exact (X.presheaf.map (homOfLE h).op).hom)).1
  let _ : PreservesFiniteColimits (moduleSectionsRestrictionFunctorOfLE h) :=
    ((exactFunctor_iff (moduleSectionsRestrictionFunctorOfLE h)).mp
      (restrictScalars_exact (X.presheaf.map (homOfLE h).op).hom)).2
  let restrict := moduleSectionsRestrictionFunctorOfLE h
  simpa [moduleSectionsToDerived, moduleSectionsRestrictionDerivedOfLE, evalH, restrict] using
    Functor.isoWhiskerLeft evalH restrict.mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator evalH DerivedCategory.Q restrict.mapDerivedCategory).symm

private abbrev moduleSectionsRestrictionNatTransOnComplexesOfLE
    {W U : Opens X.carrier} (h : W ≤ U) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (moduleSectionsRestrictionCompFunctorOfLE h).mapHomologicalComplex
        (ComplexShape.up ℤ) where
  app K :=
    { f := fun i ↦ (moduleSectionsRestrictionNatTransOfLE h).app (K.X i)
      comm' := by
        intro i j hij
        cases hij
        simpa using
          ((moduleSectionsRestrictionNatTransOfLE h).naturality (K.d i (i + 1))).symm }
  naturality {K L} φ := by
    ext i x
    simpa using
      congrArg (fun f ↦ (ModuleCat.Hom.hom f) x)
        ((moduleSectionsRestrictionNatTransOfLE h).naturality (φ.f i))

private abbrev moduleDerivedSectionsAtOpenUnit
    (T : Opens X.carrier) :
    moduleSectionsToDerived T ⟶ QModX ⋙ moduleDerivedSectionsAtOpen X T :=
  let F : X.Modules ⥤ ModuleCat (sectionsRingOnOpen X T) :=
    SheafOfModules.evaluation X.ringCatSheaf (op T)
  let _ : F.Additive := moduleSectionsEvaluation_additive X T
  let _ :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        QisModX :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerivedUnit
    QModX
    QisModX

private instance moduleDerivedSectionsAtOpen_isRightDerivedFunctor
    (T : Opens X.carrier) :
    (moduleDerivedSectionsAtOpen X T).IsRightDerivedFunctor
      (moduleDerivedSectionsAtOpenUnit T)
      QisModX := by
  let _ : (moduleSectionsToDerived T).HasRightDerivedFunctor QisModX := by
    simpa [moduleSectionsToDerived] using
      (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
        (SheafOfModules.evaluation X.ringCatSheaf (op T)))
  simpa [moduleSectionsToDerived, moduleDerivedSectionsAtOpen,
    moduleDerivedSectionsAtOpenUnit] using
    (inferInstance :
      ((moduleSectionsToDerived T).totalRightDerived QModX QisModX).IsRightDerivedFunctor
        ((moduleSectionsToDerived T).totalRightDerivedUnit QModX QisModX)
        QisModX)

private abbrev moduleDerivedSectionsAtOpenRestrictionUnitOfLE
    {W U : Opens X.carrier} (h : W ≤ U) :
    moduleSectionsToDerived W ⋙ moduleSectionsRestrictionDerivedOfLE h ⟶
      QModX ⋙ (moduleDerivedSectionsAtOpen X W ⋙ moduleSectionsRestrictionDerivedOfLE h) :=
  Functor.whiskerRight
      (moduleDerivedSectionsAtOpenUnit W)
      (moduleSectionsRestrictionDerivedOfLE h) ≫
    (Functor.associator
      QModX
      (moduleDerivedSectionsAtOpen X W)
      (moduleSectionsRestrictionDerivedOfLE h)).hom

private instance moduleDerivedSectionsAtOpenRestriction_isRightDerivedFunctor
    {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleDerivedSectionsAtOpen X W ⋙ moduleSectionsRestrictionDerivedOfLE h).IsRightDerivedFunctor
      (moduleDerivedSectionsAtOpenRestrictionUnitOfLE h)
      QisModX := by
  sorry

/-- The canonical restriction natural transformation on derived sections for nested opens
`W ⊆ U`, with `RΓ(W,-)` viewed over `Γ(U, 𝒪_X)` by restriction of scalars. -/
noncomputable def moduleDerivedSectionsAtOpenRestrictionNatTransOfLE
    {W U : Opens X.carrier} (h : W ≤ U) :
    moduleDerivedSectionsAtOpen X U ⟶
      moduleDerivedSectionsAtOpen X W ⋙ moduleSectionsRestrictionDerivedOfLE h :=
  Functor.rightDerivedNatTrans
    (moduleDerivedSectionsAtOpen X U)
    (moduleDerivedSectionsAtOpen X W ⋙ moduleSectionsRestrictionDerivedOfLE h)
    (moduleDerivedSectionsAtOpenUnit U)
    (moduleDerivedSectionsAtOpenRestrictionUnitOfLE h)
    QisModX
    ((Functor.whiskerRight
        (moduleSectionsRestrictionNatTransOnComplexesOfLE h)
        DerivedCategory.Q) ≫
      (moduleSectionsToDerivedRestrictionIso h).hom)

/-- The canonical restriction morphism on derived sections for nested opens `W ⊆ U`, with the
target viewed over `Γ(U, 𝒪_X)` by restriction of scalars. -/
abbrev moduleDerivedSectionsAtOpenRestrictionOfLE
    {W U : Opens X.carrier} (h : W ≤ U) (K : DModX) :
    (moduleDerivedSectionsAtOpen X U).obj K ⟶
      (moduleSectionsRestrictionDerivedOfLE h).obj
        ((moduleDerivedSectionsAtOpen X W).obj K) :=
  (moduleDerivedSectionsAtOpenRestrictionNatTransOfLE h).app K

/-- The canonical restriction morphism `H^m(U, E) ⟶ H^m(W, E)` on open hypercohomology for
nested opens `W ⊆ U`. -/
noncomputable def moduleOpenHypercohomologyRestrictionOfLE
    {W U : Opens X.carrier} (h : W ≤ U) (E : DModX) (m : ℤ) :
    H^m(U, E) ⟶ H^m(W, E) :=
  let targetIso :
      (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (ModuleCat (sectionsRingOnOpen X U)) m).obj
          ((moduleSectionsRestrictionDerivedOfLE h).obj
            ((moduleDerivedSectionsAtOpen X W).obj E))) ≅
        H^m(W, E) := by
    let F := moduleSectionsRestrictionFunctorOfLE h
    simpa [moduleOpenHypercohomology, moduleSectionsRestrictionFunctorOfLE,
        moduleSectionsRestrictionDerivedOfLE, F] using
      ((forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapIso
        (CategoryTheory.exactFunctor_homology_iso_mapDerivedCategory F
          ((moduleDerivedSectionsAtOpen X W).obj E) m)).symm
  (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).map
      ((DerivedCategory.homologyFunctor (ModuleCat (sectionsRingOnOpen X U)) m).map
        (moduleDerivedSectionsAtOpenRestrictionOfLE h E)) ≫
    targetIso.hom

/-- The canonical Mayer-Vietoris restriction map
`H^m(X, E) ⟶ H^m(U, E) ⊞ H^m(V, E)` on open hypercohomology. -/
abbrev moduleOpenHypercohomologyMayerVietorisToBiprod
    (U V : Opens X.carrier) (E : DModX) (m : ℤ) :
    H^m((⊤ : Opens X.carrier), E) ⟶ H^m(U, E) ⊞ H^m(V, E) :=
  biprod.lift
    (moduleOpenHypercohomologyRestrictionOfLE le_top E m)
    (moduleOpenHypercohomologyRestrictionOfLE le_top E m)

/-- The canonical Mayer-Vietoris overlap-difference map
`H^m(U, E) ⊞ H^m(V, E) ⟶ H^m(U ∩ V, E)` on open hypercohomology. -/
abbrev moduleOpenHypercohomologyMayerVietorisDifference
    (U V : Opens X.carrier) (E : DModX) (m : ℤ) :
    H^m(U, E) ⊞ H^m(V, E) ⟶ H^m(U ⊓ V, E) :=
  biprod.desc
    (moduleOpenHypercohomologyRestrictionOfLE inf_le_left E m)
    (-moduleOpenHypercohomologyRestrictionOfLE inf_le_right E m)

/- Domain-style sampling for Lemma 20.33.4:
- primary domain: Mayer-Vietoris exact segments on open hypercohomology, obtained from the
  Mayer-Vietoris distinguished triangle on derived sections;
- sampled owner declarations:
  `ringedSpaceModule_derivedMayerVietoris_triangle`,
  `moduleDerivedSectionsAtOpen`,
  `moduleSectionsRestrictionDerived`,
  `Functor.mapDerivedCategory`,
  `Functor.homologySequenceComposableArrows₅_exact`;
- best owner abstraction: the source-facing exact sequence of cohomology groups is obtained by
  applying `DerivedCategory.homologyFunctor` to the canonical open-sections owner
  `moduleDerivedSectionsAtOpen X U`, then forgetting the resulting section-module cohomology to
  `AddCommGrpCat`; the file uses the theorem-local restriction-of-scalars bridge for nested opens
  to publicize the canonical restriction maps on open hypercohomology;
- primitive data: the cover opens `U, V`, the cover equation `hUV`, the derived object `E`, and
  the degree `n`;
- derived API: the canonical restriction and overlap-difference maps on open hypercohomology,
  used below to express the resulting exact five-term segment directly on the theorem surface.

Source/core/bridge triage:
- `source-facing`: the Mayer-Vietoris exact segment on open hypercohomology;
- `core/canonical`: `ringedSpaceModule_derivedMayerVietoris_triangle`,
  `moduleDerivedSectionsAtOpen`,
  `moduleSectionsRestrictionDerived`,
  `DerivedCategory.homologyFunctor`, `Triangle`, and
  `Functor.homologySequenceComposableArrows₅_exact`;
- `bridge/view`: the restriction-of-scalars bridge from `Γ(U, 𝒪_X)` to `Γ(W, 𝒪_X)` for nested
  opens `W ⊆ U`, together with the auxiliary distinguished-triangle statement on derived global
  sections over `Γ(X, 𝒪_X)` used only to produce the source exact sequence on hypercohomology.

This file therefore reuses the chapter owner `ringedSpaceModule_derivedMayerVietoris_triangle`
directly, keeps the open-hypercohomology exact segment as the main public outcome for the numbered
item, and treats the distinguished triangle on derived sections over global scalars only as an
auxiliary bridge. -/

-- Proof sketch: the first and second maps are the canonical restriction and overlap-difference
-- maps on open hypercohomology induced by the module-valued derived-sections restriction owner
-- and exact restriction of scalars along `Γ(U, 𝒪_X) → Γ(W, 𝒪_X)`. For a cover `X = U ∪ V`, the
-- connecting morphism is obtained from the canonical homological-functor five-term owner applied
-- to a Mayer-Vietoris triangle, and exactness is read off from that owner theorem.
/-- Lemma 20.33.4: if a ringed space `X` is covered by two opens `U` and `V`, then every derived
`𝒪_X`-module `E` admits a connecting morphism `δ` such that the canonical Mayer-Vietoris
open-hypercohomology five-term sequence with the canonical restriction and overlap-difference maps
is exact. Here `H^n(W, E)` is the chapter-owned open hypercohomology object
`moduleOpenHypercohomology X W E n`, written on the theorem surface as `H^n(W, E)`. -/
@[stacks 08BX]
theorem openHypercohomology_mayerVietoris_sequence_exact
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (E : DModX) (n : ℤ) :
    ∃ δ : H^n(U ⊓ V, E) ⟶ H^(n + 1)((⊤ : Opens X.carrier), E),
      (ComposableArrows.mk₅
        (moduleOpenHypercohomologyMayerVietorisToBiprod U V E n)
        (moduleOpenHypercohomologyMayerVietorisDifference U V E n)
        δ
        (moduleOpenHypercohomologyMayerVietorisToBiprod U V E (n + 1))
        (moduleOpenHypercohomologyMayerVietorisDifference U V E (n + 1))).Exact := by
  -- Apply the canonical homological-functor five-term exact sequence to the functorial
  -- distinguished triangle above, then transport the two middle terms and the displayed first,
  -- second, fourth, and fifth maps to the source-facing restriction/difference maps above.
  sorry

/-- Companion bridge: for a cover `X = U ∪ V`, the canonical restriction and overlap-difference
maps on derived sections over `Γ(X, 𝒪_X)` fit into a distinguished triangle. -/
theorem derivedGlobalSections_mayerVietoris_distinguishedTriangle
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) :
    ∃ δ : moduleDerivedSectionsOverGlobal X (U ⊓ V) ⟶
        moduleDerivedGlobalSections X ⋙ shiftFunctor DΓX (1 : ℤ),
      ∀ E : DModX,
        Triangle.mk
            ((moduleDerivedSectionsOverGlobalMayerVietorisToBiprod X U V).app E)
            ((moduleDerivedSectionsOverGlobalMayerVietorisDifference X U V).app E)
            (δ.app E) ∈ distTriang DΓX := by
  sorry

end

end AlgebraicGeometry.RingedSpace
