import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_33_3
import StacksProject_2024.stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core
import StacksProject_2024.stacks_project.Chap20.RingedSpaceModuleHasDerivedCategory

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom
open scoped TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Primitive data for this owner layer is only the ambient ringed space `X` together with an open
subset `U ⊆ X`. The open-subspace pushforward, its derived functor, and the restriction
comparison maps are derived API and belong in this small owner file rather than in the heavier
Čech-complex development of `Lemma_20_24_1`. -/

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

/-- The direct-image functor from the open subspace `U` back to `X` on sheaves of
`𝒪_U`-modules, expressed through the canonical open-immersion pushforward owner. -/
abbrev modulePushforwardFromOpen (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ ModX :=
  RingedSpace.Hom.pushforward (X.ofRestrict U.isOpenEmbedding)

instance modulePushforwardFromOpen_additive (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Additive := by
  simpa [modulePushforwardFromOpen] using
    (RingedSpace.Hom.pushforward_additive (f := X.ofRestrict U.isOpenEmbedding))

/-- Open pushforward from an open subspace is exact on module sheaves. -/
theorem modulePushforwardFromOpen_exact (U : Opens X.carrier) :
    exactFunctor (openSubspaceModuleCategory X U) ModX (modulePushforwardFromOpen U) := by
  sorry

instance modulePushforwardFromOpen_preservesFiniteLimits
    (U : Opens X.carrier) :
    PreservesFiniteLimits (modulePushforwardFromOpen U) := by
  exact ((exactFunctor_iff (modulePushforwardFromOpen U)).mp
    (modulePushforwardFromOpen_exact U)).1

instance modulePushforwardFromOpen_preservesFiniteColimits
    (U : Opens X.carrier) :
    PreservesFiniteColimits (modulePushforwardFromOpen U) := by
  exact ((exactFunctor_iff (modulePushforwardFromOpen U)).mp
    (modulePushforwardFromOpen_exact U)).2

/-- The derived open pushforward `Rj_* : D(𝒪_U) ⟶ D(𝒪_X)` for the inclusion
`j : U ⟶ X`. -/
abbrev modulePushforwardFromOpenDerived (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  letI : CategoryWithHomology (RingedSpace.Modules X) :=
    ringedSpaceModules_categoryWithHomology X
  letI : HasDerivedCategory (RingedSpace.Modules X) := HasDerivedCategory.standard _
  letI :
      Functor.IsLocalization
        (DerivedCategory.Q :
          CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
            DerivedCategory (openSubspaceModuleCategory X U))
        (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ)) :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  letI :
      Functor.IsLocalization
        (DerivedCategory.Q :
          CochainComplex (RingedSpace.Modules X) ℤ ⥤
            DerivedCategory (RingedSpace.Modules X))
        (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  let F : openSubspaceModuleCategory X U ⥤ RingedSpace.Modules X := modulePushforwardFromOpen U
  let hFadd : F.Additive := by
    simpa [F] using modulePushforwardFromOpen_additive U
  let hFlim : PreservesFiniteLimits F := by
    let _ : F.Additive := hFadd
    simpa [F] using modulePushforwardFromOpen_preservesFiniteLimits U
  let hFcolim : PreservesFiniteColimits F := by
    let _ : F.Additive := hFadd
    simpa [F] using modulePushforwardFromOpen_preservesFiniteColimits U
  @CategoryTheory.Functor.mapDerivedCategory
    (openSubspaceModuleCategory X U) _ _ _ (RingedSpace.Modules X) _ _ _ F hFadd hFlim hFcolim

/-- The unit map from an `𝒪_X`-module to the pushforward of its restriction to the open
subspace `U`. -/
abbrev moduleRestrictionToOpenUnit (U : Opens X.carrier) (ℱ : ModX) :
    ℱ ⟶ (modulePushforwardFromOpen U).obj ((moduleRestrictionToOpen X U).obj ℱ) := by
  simpa [modulePushforwardFromOpen, moduleRestrictionToOpen] using
    (SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding))).unit.app ℱ

/-- The pushforward functor between module categories on nested open subspaces `W ⊆ U`. -/
noncomputable abbrev modulePushforwardBetweenOpens {W U : Opens X.carrier} (h : W ≤ U) :
    openSubspaceModuleCategory X W ⥤ openSubspaceModuleCategory X U :=
  RingedSpace.Hom.pushforward (restrictedMorphismBetweenOpens X h)

/-- Iterated pushforward through an intermediate open agrees with direct pushforward from the
smaller open. -/
noncomputable def modulePushforwardFromOpenCompIso
    {W U : Opens X.carrier} (h : W ≤ U) :
    modulePushforwardBetweenOpens h ⋙
      modulePushforwardFromOpen U ≅
        modulePushforwardFromOpen W := by
  let g : X.restrict W.isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
    restrictedMorphismBetweenOpens X h
  let iU : X.restrict U.isOpenEmbedding ⟶ X := X.ofRestrict U.isOpenEmbedding
  let iW : X.restrict W.isOpenEmbedding ⟶ X := X.ofRestrict W.isOpenEmbedding
  have hfac : g ≫ iU = iW := by
    simpa [g, iU, iW] using restrictedMorphismBetweenOpens_fac (X := X) (h := h)
  have compIso : RingedSpace.Hom.pushforward (g ≫ iU) ≅ RingedSpace.Hom.pushforward iW :=
    eqToIso (congrArg RingedSpace.Hom.pushforward hfac)
  simpa [g, iU, iW, modulePushforwardBetweenOpens, modulePushforwardFromOpen] using
    (SheafOfModules.pushforwardComp
        (RingedSpace.Hom.toRingCatSheafHom iU)
        (RingedSpace.Hom.toRingCatSheafHom g)) ≪≫
      compIso

/-- The restriction map on open-subspace pushforwards induced by an inclusion `W ⊆ U`. -/
noncomputable def modulePushforwardFromOpenRestrictionMap
    {W U : Opens X.carrier} (h : W ≤ U) (ℱ : ModX) :
    (modulePushforwardFromOpen U).obj
        ((moduleRestrictionToOpen X U).obj ℱ) ⟶
      (modulePushforwardFromOpen W).obj
        ((moduleRestrictionToOpen X W).obj ℱ) :=
  let η :
      ((moduleRestrictionToOpen X U).obj ℱ) ⟶
        (modulePushforwardBetweenOpens h).obj
          ((moduleRestrictionBetweenOpens X h).obj
            ((moduleRestrictionToOpen X U).obj ℱ)) := by
    simpa [modulePushforwardBetweenOpens, moduleRestrictionBetweenOpens] using
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom (restrictedMorphismBetweenOpens X h))).unit.app
        ((moduleRestrictionToOpen X U).obj ℱ)
  let α := ((modulePushforwardFromOpenCompIso h).app
    ((moduleRestrictionBetweenOpens X h).obj
      ((moduleRestrictionToOpen X U).obj ℱ))).hom
  let β := (modulePushforwardFromOpen W).map
    ((moduleRestrictionToOpenCompIso X h).app ℱ).hom
  (modulePushforwardFromOpen U).map η ≫ α ≫ β

/-- The direct image to `Y` of an `𝒪_X`-module after restricting it to the open
subspace `U ⊆ X`. This is the canonical composite
`moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U ⋙ (f _*)`. -/
abbrev modulePushforwardFromOpenAlong
    {Y : RingedSpace.{u}} (f : X ⟶ Y) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ RingedSpace.Modules Y :=
  moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U ⋙ (f _*)

section

variable {Y : RingedSpace.{u}} (f : X ⟶ Y)

theorem moduleRestrictionToOpenUnit_naturality
    (U : Opens X.carrier) {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢) :
    (f _*).map φ ≫ (f _*).map (moduleRestrictionToOpenUnit U 𝒢) =
      (f _*).map (moduleRestrictionToOpenUnit U ℱ) ≫
        (f _*).map ((moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U).map φ) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((f _*).map) <|
    by
      simpa [moduleRestrictionToOpenUnit, modulePushforwardFromOpen, moduleRestrictionToOpen] using
        (SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding))).unit.naturality φ

/-- The canonical underived restriction natural transformation
`f_* ⟶ modulePushforwardFromOpenAlong f U`. -/
abbrev modulePushforwardFromOpenAlongUnitNatTrans
    (U : Opens X.carrier) :
    (f _*) ⟶ modulePushforwardFromOpenAlong f U where
  app ℱ := (f _*).map (moduleRestrictionToOpenUnit U ℱ)
  naturality {_ _} φ :=
    moduleRestrictionToOpenUnit_naturality (f := f) U φ

theorem modulePushforwardFromOpenRestrictionMap_naturality
    {W U : Opens X.carrier} (h : W ≤ U) {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢) :
    ((moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U).map φ) ≫
        modulePushforwardFromOpenRestrictionMap (X := X) h 𝒢 =
      modulePushforwardFromOpenRestrictionMap (X := X) h ℱ ≫
        ((moduleRestrictionToOpen X W ⋙ modulePushforwardFromOpen W).map φ) := by
  let RU := moduleRestrictionToOpen X U
  let RW := moduleRestrictionToOpen X W
  let RB := moduleRestrictionBetweenOpens X h
  let PU := modulePushforwardFromOpen U
  let PW := modulePushforwardFromOpen W
  let PB := modulePushforwardBetweenOpens h
  let ηℱ :
      RU.obj ℱ ⟶ (PB.obj (RB.obj (RU.obj ℱ))) := by
    simpa [PB, RB] using
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom (restrictedMorphismBetweenOpens X h))).unit.app
        (RU.obj ℱ)
  let η𝒢 :
      RU.obj 𝒢 ⟶ (PB.obj (RB.obj (RU.obj 𝒢))) := by
    simpa [PB, RB] using
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom (restrictedMorphismBetweenOpens X h))).unit.app
        (RU.obj 𝒢)
  let αℱ := ((modulePushforwardFromOpenCompIso h).app (RB.obj (RU.obj ℱ))).hom
  let α𝒢 := ((modulePushforwardFromOpenCompIso h).app (RB.obj (RU.obj 𝒢))).hom
  let βℱ := (PW.map ((moduleRestrictionToOpenCompIso X h).app ℱ).hom)
  let β𝒢 := (PW.map ((moduleRestrictionToOpenCompIso X h).app 𝒢).hom)
  have hη :
      PU.map (RU.map φ) ≫ PU.map η𝒢 =
        PU.map ηℱ ≫ PU.map ((RB ⋙ PB).map (RU.map φ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg PU.map <|
      by
        simpa [ηℱ, η𝒢, PB, RB] using
          (SheafOfModules.pullbackPushforwardAdjunction
            (RingedSpace.Hom.toRingCatSheafHom
              (restrictedMorphismBetweenOpens X h))).unit.naturality (RU.map φ)
  have hα :
      PU.map ((RB ⋙ PB).map (RU.map φ)) ≫ α𝒢 =
        αℱ ≫ PW.map (RB.map (RU.map φ)) := by
    simpa [Functor.comp_map, αℱ, α𝒢] using
      (Functor.whiskerLeft RB (modulePushforwardFromOpenCompIso h).hom).naturality (RU.map φ)
  have hβ :
      PW.map (RB.map (RU.map φ)) ≫ β𝒢 =
        βℱ ≫ PW.map (RW.map φ) := by
    simpa [Functor.comp_map, βℱ, β𝒢] using
      (Functor.whiskerRight (moduleRestrictionToOpenCompIso X h).hom PW).naturality φ
  change
    PU.map (RU.map φ) ≫ (PU.map η𝒢 ≫ α𝒢 ≫ β𝒢) =
      (PU.map ηℱ ≫ αℱ ≫ βℱ) ≫ PW.map (RW.map φ)
  calc
    PU.map (RU.map φ) ≫ (PU.map η𝒢 ≫ α𝒢 ≫ β𝒢)
        = PU.map ηℱ ≫ PU.map ((RB ⋙ PB).map (RU.map φ)) ≫ α𝒢 ≫ β𝒢 := by
            simpa [Category.assoc] using congrArg (fun t ↦ t ≫ α𝒢 ≫ β𝒢) hη
    _ = PU.map ηℱ ≫ αℱ ≫ PW.map (RB.map (RU.map φ)) ≫ β𝒢 := by
          simpa [Category.assoc] using congrArg (fun t ↦ PU.map ηℱ ≫ t ≫ β𝒢) hα
    _ = (PU.map ηℱ ≫ αℱ ≫ βℱ) ≫ PW.map (RW.map φ) := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ PU.map ηℱ ≫ αℱ ≫ t) hβ

/-- The canonical underived restriction map induced by an inclusion `W ⊆ U`. -/
abbrev modulePushforwardFromOpenAlongRestrictionNatTrans
    {W U : Opens X.carrier} (h : W ≤ U) :
    modulePushforwardFromOpenAlong f U ⟶ modulePushforwardFromOpenAlong f W where
  app ℱ := (f _*).map (modulePushforwardFromOpenRestrictionMap (X := X) h ℱ)
  naturality {_ _} φ := by
    simpa [Functor.map_comp] using
      congrArg ((f _*).map)
        (modulePushforwardFromOpenRestrictionMap_naturality (X := X) h φ)

end

end AlgebraicGeometry.RingedSpace
