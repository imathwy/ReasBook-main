import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import StacksProject_2024.Chap06.Definition_6_25_1
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap06.Lemma_6_31_12
import StacksProject_2024.Chap06.Lemma_6_33_3
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap17.Lemma_17_20_2
import StacksProject_2024.Chap20.RingedSpaceModuleHasDerivedCategory

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSpace.Hom
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Minimal Chapter 20 owner layer for modules on open subspaces. The public owner is the
intrinsic module category on the restricted ringed space. -/

/-- The category of `\mathcal O_U`-modules on the open subspace `U`. -/
abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  RingedSpace.Modules (X.restrict U.isOpenEmbedding)

instance ringedSpaceModules_preadditive (X : RingedSpace.{u}) :
    Preadditive (RingedSpace.Modules X) := by
  change Preadditive (SheafOfModules X.ringCatSheaf)
  infer_instance

instance openSubspaceModuleCategory_preadditive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Preadditive (openSubspaceModuleCategory X U) := by
  change Preadditive (RingedSpace.Modules (X.restrict U.isOpenEmbedding))
  infer_instance

instance openSubspaceModuleCategory_abelian
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Abelian (openSubspaceModuleCategory X U) := by
  change Abelian (RingedSpace.Modules (X.restrict U.isOpenEmbedding))
  infer_instance

instance ringedSpaceModules_hasBinaryBiproducts (X : RingedSpace.{u}) :
    HasBinaryBiproducts (RingedSpace.Modules X) :=
  Abelian.hasBinaryBiproducts

instance openSubspaceModuleCategory_hasBinaryBiproducts
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasBinaryBiproducts (openSubspaceModuleCategory X U) :=
  Abelian.hasBinaryBiproducts

instance openSubspaceModuleCategory_categoryWithHomology
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CategoryWithHomology (openSubspaceModuleCategory X U) :=
  CategoryTheory.categoryWithHomology_of_abelian

instance openSubspaceModuleCategory_hasDerivedCategory
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (openSubspaceModuleCategory X U) :=
  HasDerivedCategory.standard (openSubspaceModuleCategory X U)

/-- Restriction of `\mathcal O_X`-modules from `X` to the open subspace `U`. -/
abbrev moduleRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ openSubspaceModuleCategory X U :=
  RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)

/-- Restriction of cochain complexes of `\mathcal O_X`-modules to the open subspace `U`. -/
abbrev moduleRestrictionComplexToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      CochainComplex (openSubspaceModuleCategory X U) ℤ :=
  (moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)

/-- The restricted cochain complex on the open subspace `U`. -/
abbrev restrictedComplexOnOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ :=
  (moduleRestrictionComplexToOpen X U).obj K

/-- Restriction to an open subspace is exact. -/
theorem moduleRestrictionToOpen_exact
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    exactFunctor (RingedSpace.Modules X) (openSubspaceModuleCategory X U)
      (moduleRestrictionToOpen X U) := by
  letI : RingedSpace.Hom.IsFlat (X.ofRestrict U.isOpenEmbedding) := by
    constructor
    intro x
    change (((X.ofRestrict U.isOpenEmbedding).hom.stalkMap x).hom).Flat
    letI : IsIso ((X.ofRestrict U.isOpenEmbedding).hom.stalkMap x) := by
      infer_instance
    let e :=
      (asIso ((X.ofRestrict U.isOpenEmbedding).hom.stalkMap x)).commRingCatIsoToRingEquiv
    simpa using RingHom.Flat.of_bijective e.bijective
  simpa [moduleRestrictionToOpen] using
    (IsFlat.pullback_exact (X.ofRestrict U.isOpenEmbedding))

/-- Restriction to an open subspace is additive on sheaves of modules. -/
instance moduleRestrictionToOpen_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).Additive :=
  RingedSpace.Hom.pullback_additive (X.ofRestrict U.isOpenEmbedding)

instance moduleRestrictionToOpen_preservesFiniteLimits
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleRestrictionToOpen X U) := by
  letI : RingedSpace.Hom.IsFlat (X.ofRestrict U.isOpenEmbedding) := by
    constructor
    intro x
    change (((X.ofRestrict U.isOpenEmbedding).hom.stalkMap x).hom).Flat
    letI : IsIso ((X.ofRestrict U.isOpenEmbedding).hom.stalkMap x) := by
      infer_instance
    let e :=
      (asIso ((X.ofRestrict U.isOpenEmbedding).hom.stalkMap x)).commRingCatIsoToRingEquiv
    simpa using RingHom.Flat.of_bijective e.bijective
  simpa [moduleRestrictionToOpen] using
    (pullback_preservesFiniteLimits_of_isFlat (X.ofRestrict U.isOpenEmbedding))

instance moduleRestrictionToOpen_preservesFiniteColimits
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleRestrictionToOpen X U) := by
  simpa [moduleRestrictionToOpen] using
    (RingedSpace.Hom.pullback_preservesFiniteColimits (X.ofRestrict U.isOpenEmbedding))

private theorem restrictedMorphismBetweenOpens_range_subset
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    Set.range ((X.ofRestrict W.isOpenEmbedding).hom.base) ⊆
      Set.range ((X.ofRestrict U.isOpenEmbedding).hom.base) := by
  rintro x ⟨w, rfl⟩
  exact ⟨⟨w.1, h w.2⟩, rfl⟩

/-- The morphism of restricted ringed spaces induced by `f : X ⟶ Y` and an open subset
`V ⊆ Y`. -/
noncomputable def restrictedMorphismToOpen
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    X.restrict (preimageOpen f V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  ⟨PresheafedSpace.IsOpenImmersion.lift
    (Y.ofRestrict V.isOpenEmbedding).hom
    ((X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f.hom)
    (by
      rintro x ⟨u, rfl⟩
      exact ⟨⟨f.hom.base u.1, u.2⟩, rfl⟩)⟩

/-- The morphism of restricted ringed spaces induced by an inclusion of opens `W ⊆ U`. -/
noncomputable def restrictedMorphismBetweenOpens
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    X.restrict W.isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
  ⟨PresheafedSpace.IsOpenImmersion.lift
    (X.ofRestrict U.isOpenEmbedding).hom
    (X.ofRestrict W.isOpenEmbedding).hom
    (restrictedMorphismBetweenOpens_range_subset X h)⟩

/-- The morphism `X|_W ⟶ X|_U` induced by `W ⊆ U` factors the open immersion `X|_W ⟶ X`
through `X|_U ⟶ X`. -/
theorem restrictedMorphismBetweenOpens_fac
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    restrictedMorphismBetweenOpens X h ≫ X.ofRestrict U.isOpenEmbedding =
      X.ofRestrict W.isOpenEmbedding := by
  refine InducedCategory.hom_ext ?_
  change
    PresheafedSpace.IsOpenImmersion.lift
        (X.ofRestrict U.isOpenEmbedding).hom
        (X.ofRestrict W.isOpenEmbedding).hom
        (restrictedMorphismBetweenOpens_range_subset X h) ≫
      (X.ofRestrict U.isOpenEmbedding).hom =
        (X.ofRestrict W.isOpenEmbedding).hom
  exact PresheafedSpace.IsOpenImmersion.lift_fac
    (X.ofRestrict U.isOpenEmbedding).hom
    (X.ofRestrict W.isOpenEmbedding).hom
    (restrictedMorphismBetweenOpens_range_subset X h)

instance restrictedMorphismBetweenOpens_isFlat
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    RingedSpace.Hom.IsFlat (restrictedMorphismBetweenOpens X h) := by
  sorry

/-- Restriction of `\mathcal O_U`-modules from `U` to the smaller open subspace `W ⊆ U`. -/
abbrev moduleRestrictionBetweenOpens
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    openSubspaceModuleCategory X U ⥤ openSubspaceModuleCategory X W :=
  RingedSpace.Hom.pullback (restrictedMorphismBetweenOpens X h)

/-- Restriction between nested open subspaces is exact on module sheaves. -/
theorem moduleRestrictionBetweenOpens_exact
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    exactFunctor (openSubspaceModuleCategory X U) (openSubspaceModuleCategory X W)
      (moduleRestrictionBetweenOpens X h) := by
  simpa [moduleRestrictionBetweenOpens] using
    (IsFlat.pullback_exact (restrictedMorphismBetweenOpens X h))

instance moduleRestrictionBetweenOpens_additive
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleRestrictionBetweenOpens X h).Additive :=
  RingedSpace.Hom.pullback_additive (restrictedMorphismBetweenOpens X h)

instance moduleRestrictionBetweenOpens_preservesFiniteLimits
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    PreservesFiniteLimits (moduleRestrictionBetweenOpens X h) := by
  simpa [moduleRestrictionBetweenOpens] using
    (pullback_preservesFiniteLimits_of_isFlat (restrictedMorphismBetweenOpens X h))

instance moduleRestrictionBetweenOpens_preservesFiniteColimits
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    PreservesFiniteColimits (moduleRestrictionBetweenOpens X h) := by
  simpa [moduleRestrictionBetweenOpens] using
    (RingedSpace.Hom.pullback_preservesFiniteColimits (restrictedMorphismBetweenOpens X h))

/-- The Chapter 20 owner derived category `D(\mathcal O_U)` attached to the open subspace `U`. -/
abbrev moduleDerivedOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  DerivedCategory (openSubspaceModuleCategory X U)

instance moduleDerivedOnOpen_category
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Category (moduleDerivedOnOpen X U) := by
  change Category (DerivedCategory (openSubspaceModuleCategory X U))
  infer_instance

instance moduleDerivedOnOpen_hasShift
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasShift (moduleDerivedOnOpen X U) ℤ := by
  let _ : Abelian (openSubspaceModuleCategory X U) :=
    openSubspaceModuleCategory_abelian X U
  let _ : CategoryWithHomology (openSubspaceModuleCategory X U) :=
    openSubspaceModuleCategory_categoryWithHomology X U
  let _ : HasDerivedCategory (openSubspaceModuleCategory X U) :=
    HasDerivedCategory.standard _
  change HasShift (DerivedCategory (openSubspaceModuleCategory X U)) ℤ
  exact DerivedCategory.instHasShiftInt (C := openSubspaceModuleCategory X U)

instance moduleDerivedOnOpen_preadditive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Preadditive (moduleDerivedOnOpen X U) := by
  let _ : HasDerivedCategory (openSubspaceModuleCategory X U) :=
    openSubspaceModuleCategory_hasDerivedCategory X U
  let _ : ∀ n : ℤ,
      (shiftFunctor (HomotopyCategory (openSubspaceModuleCategory X U) (up ℤ)) n).Additive :=
    inferInstance
  change Preadditive (DerivedCategory (openSubspaceModuleCategory X U))
  exact DerivedCategory.instPreadditive (openSubspaceModuleCategory X U)

instance moduleDerivedOnOpen_monoidalCategory
    (X : RingedSpace.{u})
    [∀ U : Opens X.carrier, MonoidalCategory (moduleDerivedOnOpen X U)]
    (U : Opens X.carrier) :
    MonoidalCategory (DerivedCategory (Modules (X.restrict U.isOpenEmbedding))) := by
  change MonoidalCategory (moduleDerivedOnOpen X U)
  exact (inferInstance : ∀ U : Opens X.carrier, MonoidalCategory (moduleDerivedOnOpen X U)) U

/-- The canonical isomorphism identifying direct restriction from `X` with iterated restriction
through an intermediate open. -/
noncomputable def moduleRestrictionToOpenCompIso
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    moduleRestrictionToOpen X U ⋙ moduleRestrictionBetweenOpens X h ≅
      moduleRestrictionToOpen X W := by
  let g : X.restrict W.isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
    restrictedMorphismBetweenOpens X h
  let iU : X.restrict U.isOpenEmbedding ⟶ X := X.ofRestrict U.isOpenEmbedding
  let iW : X.restrict W.isOpenEmbedding ⟶ X := X.ofRestrict W.isOpenEmbedding
  have hfac : g ≫ iU = iW := by
    simpa [g, iU, iW] using restrictedMorphismBetweenOpens_fac (X := X) (h := h)
  have compIso : RingedSpace.Hom.pullback (g ≫ iU) ≅ RingedSpace.Hom.pullback iW :=
    eqToIso (congrArg RingedSpace.Hom.pullback hfac)
  simpa [g, iU, iW, moduleRestrictionToOpen, moduleRestrictionBetweenOpens] using
    (SheafOfModules.pullbackComp
        (RingedSpace.Hom.toRingCatSheafHom iU)
        (RingedSpace.Hom.toRingCatSheafHom g)) ≪≫
      compIso

/-- Restriction of a derived `\mathcal O_X`-module to the open subspace `U`. -/
abbrev moduleRestrictionToOpenDerived
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ moduleDerivedOnOpen X U := by
  letI : CategoryWithHomology (RingedSpace.Modules X) :=
    ringedSpaceModules_categoryWithHomology X
  letI : HasDerivedCategory (RingedSpace.Modules X) := HasDerivedCategory.standard _
  letI :
      Functor.IsLocalization
        (DerivedCategory.Q :
          CochainComplex (RingedSpace.Modules X) ℤ ⥤
            DerivedCategory (RingedSpace.Modules X))
        (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ)) :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  letI :
      Functor.IsLocalization
        (DerivedCategory.Q :
          CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
            DerivedCategory (openSubspaceModuleCategory X U))
        (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (up ℤ)) :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  let F : RingedSpace.Modules X ⥤ openSubspaceModuleCategory X U := moduleRestrictionToOpen X U
  let hFadd : F.Additive := moduleRestrictionToOpen_additive X U
  let hFlim : PreservesFiniteLimits F := moduleRestrictionToOpen_preservesFiniteLimits X U
  let hFcolim : PreservesFiniteColimits F := moduleRestrictionToOpen_preservesFiniteColimits X U
  exact
    @Functor.mapDerivedCategory
      (RingedSpace.Modules X) _ _ _ (openSubspaceModuleCategory X U) _ _ _ F
      hFadd hFlim hFcolim

instance moduleRestrictionToOpenDerived_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpenDerived X U).Additive := by
  sorry

/-- The canonical comparison identifying the restriction of `DerivedCategory.Q.obj K` to `U`
with the derived object of the restricted complex `(moduleRestrictionComplexToOpen X U).obj K`. -/
abbrev moduleRestrictionToOpenDerivedFactors
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    (moduleRestrictionToOpenDerived X U).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((moduleRestrictionComplexToOpen X U).obj K) := by
  let F : RingedSpace.Modules X ⥤ openSubspaceModuleCategory X U := moduleRestrictionToOpen X U
  let hFadd : F.Additive := moduleRestrictionToOpen_additive X U
  let hFlim : PreservesFiniteLimits F := moduleRestrictionToOpen_preservesFiniteLimits X U
  let hFcolim : PreservesFiniteColimits F := moduleRestrictionToOpen_preservesFiniteColimits X U
  simpa [F, moduleRestrictionToOpenDerived] using
    (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ F hFadd hFlim hFcolim).app K

/-- Restriction between the derived categories of modules on nested open subspaces. -/
abbrev derivedRestrictionBetweenOpens
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    moduleDerivedOnOpen X U ⥤ moduleDerivedOnOpen X W := by
  let F : openSubspaceModuleCategory X U ⥤ openSubspaceModuleCategory X W :=
    moduleRestrictionBetweenOpens X h
  let hFadd : F.Additive := moduleRestrictionBetweenOpens_additive X h
  let hFlim : PreservesFiniteLimits F := moduleRestrictionBetweenOpens_preservesFiniteLimits X h
  let hFcolim : PreservesFiniteColimits F :=
    moduleRestrictionBetweenOpens_preservesFiniteColimits X h
  exact
    @Functor.mapDerivedCategory
      (openSubspaceModuleCategory X U) _ _ _ (openSubspaceModuleCategory X W) _ _ _ F
      hFadd hFlim hFcolim

instance derivedRestrictionBetweenOpens_additive
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    (derivedRestrictionBetweenOpens X h).Additive := by
  sorry

/-- Two successive derived restrictions between opens agree with the direct restriction. -/
theorem derivedRestrictionBetweenOpens_comp_eq
    (X : RingedSpace.{u}) {T W U : Opens X.carrier} (hTW : T ≤ W) (hWU : W ≤ U) :
    derivedRestrictionBetweenOpens X hWU ⋙ derivedRestrictionBetweenOpens X hTW =
      derivedRestrictionBetweenOpens X (hTW.trans hWU) := by
  sorry

/-- The canonical isomorphism identifying iterated and direct restriction between nested opens. -/
abbrev derivedRestrictionBetweenOpensCompIso
    (X : RingedSpace.{u}) {T W U : Opens X.carrier} (hTW : T ≤ W) (hWU : W ≤ U) :
    derivedRestrictionBetweenOpens X hWU ⋙ derivedRestrictionBetweenOpens X hTW ≅
      derivedRestrictionBetweenOpens X (hTW.trans hWU) :=
  eqToIso (derivedRestrictionBetweenOpens_comp_eq X hTW hWU)

/-- Restricting from `X` to `U` and then from `U` to `W` agrees with direct restriction from `X`
to `W` on derived categories. -/
theorem moduleRestrictionToOpenDerived_comp_eq
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    moduleRestrictionToOpenDerived X U ⋙ derivedRestrictionBetweenOpens X h =
      moduleRestrictionToOpenDerived X W := by
  sorry

/-- The canonical isomorphism identifying direct restriction from `X` with iterated restriction
through an intermediate open on derived categories. -/
abbrev moduleRestrictionToOpenDerivedCompIso
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    moduleRestrictionToOpenDerived X U ⋙ derivedRestrictionBetweenOpens X h ≅
      moduleRestrictionToOpenDerived X W :=
  eqToIso (moduleRestrictionToOpenDerived_comp_eq X h)

/-- Restriction of a derived `\mathcal O_X`-module to the intrinsic derived category
`D(\mathcal O_U)` of the open subspace. -/
abbrev restrictedModuleDerivedOnOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    moduleDerivedOnOpen X U :=
  DerivedCategory.Q.obj
    ((moduleRestrictionComplexToOpen X U).obj (DerivedCategory.Q.objPreimage K))

scoped[RingedSpace.Hom] notation:max K "↾[" U "]" =>
  AlgebraicGeometry.RingedSpace.restrictedModuleDerivedOnOpen _ U K

end AlgebraicGeometry.RingedSpace
