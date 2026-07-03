import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_32_1 (from Chap20) -/
open CategoryTheory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.32.1:
- primary domain: restriction and extension by zero for sheaves of modules on a ringed space,
  together with preservation of `CochainComplex.IsKInjective` under an exact-adjunction pair;
- sampled owner declarations:
  `moduleSheafExtensionByZeroFromOpen`,
  `moduleRestrictionToOpen`,
  `openSubspaceModuleCategory`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstractions:
  `moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)` for `j_{U!}`,
  `moduleRestrictionToOpen X U` for `j^{-1}`,
  `openSubspaceModuleCategory X U` for the localized module category;
- primitive data: only the ringed space `X`, the open subset `U`, and the K-injective complex
  `I`;
- derived API: exactness of `j_{U!}` and K-injectivity of the restricted complex.

Source/core/bridge triage:
- `source-facing`: exactness of extension by zero on `\mathcal O_U`-modules and preservation of
  K-injectivity under restriction to `U`;
- `core/canonical`: the Chapter 6 functors `moduleSheafExtensionByZeroFromOpen` and
  `moduleRestrictionToOpen`, the Chapter 20 owner `openSubspaceModuleCategory`, and the Chapter 13
  K-injective preservation theorem;
- `bridge/view`: this file is the ringed-space specialization of that generic exact-adjunction
  owner theorem, so it should reuse those owners directly instead of introducing parallel ambient
  and localized module-category aliases. -/

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

-- Proof sketch: extension by zero on `\mathcal O_U`-modules is left adjoint to restriction by
-- Lemma `6.31.8`. On underlying abelian sheaves, this is the usual exact extension-by-zero
-- functor from Lemma `17.3.4`; exactness lifts to module sheaves because the module forgetful
-- functor is exact and reflects finite limits and colimits.
/-- Extension by zero from an open subspace of a ringed space is exact on module sheaves. -/
theorem moduleSheafExtensionByZeroFromOpen_exact :
    exactFunctor (openSubspaceModuleCategory X U) (RingedSpace.Modules X)
      (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

-- Proof sketch: restriction to the open subspace `U` is right adjoint to extension by zero by
-- Lemma `6.31.8`, and the left adjoint is exact by
-- `moduleSheafExtensionByZeroFromOpen_exact`. Apply Lemma `13.31.9` to the induced functors on
-- cochain complexes.
/-- Lemma 20.32.1: if `X` is a ringed space, `U ⊆ X` is open, and `I` is a K-injective complex
of `\mathcal O_X`-modules, then the restricted complex `I|_U` is K-injective as a complex of
`\mathcal O_U`-modules. -/
theorem moduleRestrictionToOpen_isKInjective
    (I : CochainComplex (RingedSpace.Modules X) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective (((moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)).obj I) := by
  let adj := moduleSheafExtensionByZeroAdjunction U (RingedSpace.ringCatSheaf X)
  letI : (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).Additive :=
    adj.left_adjoint_additive
  simpa using
    CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (moduleRestrictionToOpen X U)
      (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X))
      adj
      (moduleSheafExtensionByZeroFromOpen_exact (X := X) U)
      I

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_32_2 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open CategoryTheory.DerivedCategory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The ring `Γ(U, \mathcal O_X)` of sections of the structure sheaf over an open subset `U`. -/
abbrev sectionsRingOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op U)

/-- Modules over `Γ(U, \mathcal O_X)` have their standard derived category. -/
instance sectionsRingOnOpen_hasDerivedCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  HasDerivedCategory.standard (ModuleCat (sectionsRingOnOpen X U))

/-- The sections functor `\Gamma(U, -)` on `\mathcal O_X`-modules. -/
abbrev moduleSectionsFunctorAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)

/-- The sections functor on an open subset is additive. -/
instance moduleSectionsFunctorAtOpen_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsFunctorAtOpen X U).Additive := sorry

/-- The category of `\mathcal O_U`-modules obtained by pulling the structure sheaf of `X` back to
the open subspace `U`. -/
abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))

/-- The category of modules over the pulled-back structure sheaf on the open subspace has its
standard derived category. -/
instance openSubspaceModuleCategory_hasDerivedCategory
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (openSubspaceModuleCategory X U) :=
  HasDerivedCategory.standard (openSubspaceModuleCategory X U)

/-- The ring of global sections of the pulled-back structure sheaf on the open subspace `U`. -/
abbrev openSubspaceGlobalSectionsRing (X : RingedSpace.{u}) (U : Opens X.carrier) : RingCat :=
  ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X)).1.obj
    (op (⊤ : Opens U))

/-- Modules over the global-sections ring of the open subspace carry the standard derived
category. -/
instance openSubspaceGlobalSectionsRing_hasDerivedCategory
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
  HasDerivedCategory.standard (ModuleCat (openSubspaceGlobalSectionsRing X U))

/-- The global-sections functor on `\mathcal O_U`-modules over the open subspace `U`. -/
abbrev openSubspaceGlobalSectionsFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ ModuleCat (openSubspaceGlobalSectionsRing X U) :=
  SheafOfModules.evaluation
    ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))
    (op (⊤ : Opens U))

/-- The global-sections functor on the open subspace is additive. -/
instance openSubspaceGlobalSectionsFunctor_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (openSubspaceGlobalSectionsFunctor X U).Additive := sorry

/-- Restriction of `\mathcal O_X`-modules from `X` to the open subspace `U`. -/
abbrev moduleRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ openSubspaceModuleCategory X U :=
  moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)

/-- Restriction to an open subspace is additive on sheaves of modules. -/
instance moduleRestrictionToOpen_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).Additive := sorry

-- Proof sketch: restriction to the open subspace is exact on the underlying abelian sheaves, and
-- the forgetful functor from module sheaves to abelian sheaves reflects finite limits and finite
-- colimits. Hence restriction is exact on sheaves of `\mathcal O_X`-modules.
/-- Restriction to an open subspace is exact on sheaves of modules. -/
theorem moduleRestrictionToOpen_exact (X : RingedSpace.{u}) (U : Opens X.carrier) :
    exactFunctor (RingedSpace.Modules X) (openSubspaceModuleCategory X U)
      (moduleRestrictionToOpen X U) := sorry

/-- The exact-functor package attached to restricting module sheaves to the open subspace `U`. -/
abbrev moduleRestrictionToOpenExactFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ₑ openSubspaceModuleCategory X U :=
  let _ : PreservesFiniteLimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact X U)).1
  let _ : PreservesFiniteColimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact X U)).2
  ExactFunctor.of (moduleRestrictionToOpen X U)

/-- The complex-level sections functor on an open subset, followed by localization to the derived
category of modules over `Γ(U, \mathcal O_X)`. -/
abbrev moduleSectionsToDerivedAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  let _ : (moduleSectionsFunctorAtOpen X U).Additive := moduleSectionsFunctorAtOpen_additive X U
  let _ : (moduleSectionsFunctorAtOpen X U).PreservesZeroMorphisms := inferInstance
  (moduleSectionsFunctorAtOpen X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Q :
      CochainComplex (ModuleCat (sectionsRingOnOpen X U)) ℤ ⥤
        DerivedCategory (ModuleCat (sectionsRingOnOpen X U)))

-- Proof sketch: compute the derived functor of `Γ(U, -)` by resolving a complex of
-- `\mathcal O_X`-modules by a K-injective complex and applying the sections functor degreewise.
/-- The complex-level sections functor on an open subset admits a total right derived functor. -/
theorem moduleSectionsToDerivedAtOpen_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsToDerivedAtOpen X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) := sorry

/-- The canonical right-derived-functor instance for sections on an open subset. -/
instance moduleSectionsToDerivedAtOpen_instHasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsToDerivedAtOpen X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
  moduleSectionsToDerivedAtOpen_hasRightDerivedFunctor X U

/-- The total right derived functor `RΓ(U, -)` on the ambient derived category
`D(\mathcal O_X)`. -/
abbrev moduleDerivedSectionsAtOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  (moduleSectionsToDerivedAtOpen X U).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ))

/-- The restriction functor on derived categories induced by exact restriction to the open
subspace `U`. -/
abbrev moduleRestrictionToOpenDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (openSubspaceModuleCategory X U) :=
  let _ : (moduleRestrictionToOpenExactFunctor X U).obj.Additive :=
    moduleRestrictionToOpen_additive X U
  (moduleRestrictionToOpenExactFunctor X U).obj.mapDerivedCategory

/-- The complex-level global-sections functor on the open subspace, followed by localization to
its derived category. -/
abbrev openSubspaceGlobalSectionsToDerived
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
      DerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
  let _ : (openSubspaceGlobalSectionsFunctor X U).Additive :=
    openSubspaceGlobalSectionsFunctor_additive X U
  let _ : (openSubspaceGlobalSectionsFunctor X U).PreservesZeroMorphisms := inferInstance
  (openSubspaceGlobalSectionsFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Q :
      CochainComplex (ModuleCat (openSubspaceGlobalSectionsRing X U)) ℤ ⥤
        DerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)))

-- Proof sketch: compute the derived functor of global sections on the open subspace by a
-- K-injective resolution in the category of `\mathcal O_U`-modules and apply the sections
-- functor degreewise.
/-- The complex-level global-sections functor on the open subspace admits a total right derived
functor. -/
theorem openSubspaceGlobalSectionsToDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (openSubspaceGlobalSectionsToDerived X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ)) := sorry

/-- The canonical right-derived-functor instance for global sections on the open subspace. -/
instance openSubspaceGlobalSectionsToDerived_instHasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (openSubspaceGlobalSectionsToDerived X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ)) :=
  openSubspaceGlobalSectionsToDerived_hasRightDerivedFunctor X U

/-- The total right derived functor of global sections on the open subspace `U`. -/
abbrev openSubspaceDerivedGlobalSections
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤
      DerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
  (openSubspaceGlobalSectionsToDerived X U).totalRightDerived
    (DerivedCategory.Q :
      CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
        DerivedCategory (openSubspaceModuleCategory X U))
    (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ))

/-- The ambient hypercohomology group `H^p(U, K)` of a derived `\mathcal O_X`-module, viewed as
an object of `AddCommGrpCat`. -/
abbrev moduleOpenHypercohomology
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) : AddCommGrpCat.{u} :=
  let _ : HasDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
    sectionsRingOnOpen_hasDerivedCategory X U
  (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
    ((DerivedCategory.homologyFunctor (ModuleCat (sectionsRingOnOpen X U)) p).obj
      ((moduleDerivedSectionsAtOpen X U).obj K))

/-- The hypercohomology group of the restricted derived object on the open subspace `X|_U`,
viewed as an object of `AddCommGrpCat`. -/
abbrev restrictedModuleOpenHypercohomology
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) : AddCommGrpCat.{u} :=
  let _ : HasDerivedCategory (ModuleCat (openSubspaceGlobalSectionsRing X U)) :=
    openSubspaceGlobalSectionsRing_hasDerivedCategory X U
  (forget₂ (ModuleCat (openSubspaceGlobalSectionsRing X U)) AddCommGrpCat.{u}).obj
    ((DerivedCategory.homologyFunctor (ModuleCat (openSubspaceGlobalSectionsRing X U)) p).obj
      ((openSubspaceDerivedGlobalSections X U).obj
        ((moduleRestrictionToOpenDerived X U).obj K)))

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

-- Proof sketch: represent `K` by a K-injective complex `I`. The ambient functor `RΓ(U, -)` is
-- computed by the sections complex `Γ(U, I)`. By Lemma `20.32.1`, the restricted complex `I|_U`
-- is K-injective on the open subspace `X|_U`, so `RΓ(X|_U, K|_U)` is computed by the same
-- sections complex `Γ(U, I|_U) = Γ(U, I)`. Taking degree-`p` cohomology yields the comparison.
/-- Lemma 20.32.2: for a ringed space `X`, an open subset `U ⊆ X`, an object `K` of
`D(\mathcal O_X)`, and an integer `p`, the hypercohomology group `H^p(U, K)` is canonically
isomorphic to the hypercohomology group of the restricted object `K|_U` on the open subspace
`X|_U`. -/
theorem openHypercohomology_isomorphic_restricted
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) :
    IsIsomorphic
      (moduleOpenHypercohomology X U K p)
      (restrictedModuleOpenHypercohomology X U K p) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_32_3 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of modules on a ringed space `X`. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The additive functor from `\mathcal O_X`-modules to abelian presheaves on `X`, obtained by
forgetting module structure to the underlying abelian sheaf and then forgetting the sheaf
condition. -/
abbrev ringedSpaceUnderlyingAbelianPresheafFunctor (X : RingedSpace.{u}) :
    ringedSpaceModuleCat X ⥤ (Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The total right derived functor of the underlying-abelian-presheaf functor on a ringed space.
-/
abbrev ringedSpaceUnderlyingAbelianPresheafDerived (X : RingedSpace.{u})
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)] :
    DerivedCategory (ringedSpaceModuleCat X) ⥤
      DerivedCategory ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (ringedSpaceUnderlyingAbelianPresheafFunctor X)

/-- The presheaf on `X` sending an open subset `U` to the objectwise cohomology group
`H^q(U, K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev ringedSpaceObjectwiseCohomologyPresheaf (X : RingedSpace.{u})
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    (Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) q).obj
    ((ringedSpaceUnderlyingAbelianPresheafDerived X).obj K)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(K)` on a ringed space
`X`. -/
abbrev ringedSpaceCohomologySheaf (X : RingedSpace.{u})
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj K)

-- Proof sketch: regard `K` as an object of the derived category of the underlying abelian
-- presheaf functor `Mod(\mathcal O_X) ⥤ PSh(X, Ab)`. Its degree-`q` homology presheaf is exactly
-- `U ↦ H^q(U, K)`, and Lemma `20.32.2` identifies this objectwise with `U ↦ H^q(U, K|_U)`.
-- Sheafifying the resulting presheaf recovers the underlying abelian sheaf of the homology object
-- `(DerivedCategory.homologyFunctor (RingedSpace.Modules X) q).obj K`, i.e. the cohomology sheaf
-- `H^q(K)`.
/-- Lemma 20.32.3: for a ringed space `(X, \mathcal O_X)`, an object `K` of `D(\mathcal O_X)`,
and an integer `q`, the sheaf associated to the presheaf `U ↦ H^q(U, K)` is canonically
isomorphic to the degree-`q` cohomology sheaf `H^q(K)`. Equivalently, by Lemma `20.32.2`, it is
the sheaf associated to `U ↦ H^q(U, K|_U)`. -/
theorem objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    IsIsomorphic
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (ringedSpaceObjectwiseCohomologyPresheaf X K q))
      (ringedSpaceCohomologySheaf X K q) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_32_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The quasi-isomorphisms in the homotopy category of unbounded complexes of
`\mathcal O_X`-modules on a ringed space. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (Modules X)

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(RingedSpace.Hom.pushforward f).Additive] :
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  (RingedSpace.Hom.pushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The unbounded derived direct image functor `Rf_*` on module sheaves over ringed spaces. -/
abbrev modulePushforwardDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(RingedSpace.Hom.pushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The `RingCat`-valued structure sheaf on an open subspace agrees with restricting the ambient
`RingCat`-valued structure sheaf to that open. -/
-- Proof sketch: unfold the open-subspace structure sheaf as pullback of the ambient
-- `CommRingCat`-valued structure sheaf, then commute the forgetful functor
-- `CommRingCat ⥤ RingCat` with this pullback.
private theorem restrict_ringCatSheaf_eq
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding) =
      (TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj ((RingedSpace.ringCatSheaf X)) := sorry

/-- The derived module category on an open subspace agrees with the derived category over the
restricted ambient structure sheaf. -/
-- Proof sketch: apply `DerivedCategory` to the equality of module-sheaf categories induced by
-- `restrict_ringCatSheaf_eq`.
private theorem restrict_moduleDerived_eq
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    ModuleDerived (X.restrict U.isOpenEmbedding) =
      DerivedCategory
        (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj
          ((RingedSpace.ringCatSheaf X)))) := sorry

variable {X Y : RingedSpace.{u}}

/-- Restriction of `\mathcal O_X`-modules to an open subset is additive. -/
instance moduleSheafRestrictionToOpen_additive
    (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U ((RingedSpace.ringCatSheaf X))).Additive := sorry

/-- Restriction of `\mathcal O_X`-modules to an open subset preserves finite limits. -/
instance moduleSheafRestrictionToOpen_preservesFiniteLimits
    (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen U ((RingedSpace.ringCatSheaf X))) := sorry

/-- Restriction of `\mathcal O_X`-modules to an open subset preserves finite colimits. -/
instance moduleSheafRestrictionToOpen_preservesFiniteColimits
    (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafRestrictionToOpen U ((RingedSpace.ringCatSheaf X))) := sorry

/-- The image of the restriction of `f` to `f ⁻¹(V)` lands in the open subspace `V`. -/
-- Proof sketch: a point of `f^{-1}(V)` is, by definition, a point of `X` whose image under `f`
-- lies in `V`, so the composite `f^{-1}(V) ⟶ X ⟶ Y` factors through the inclusion `V ↪ Y`.
private theorem restrictedMorphism_range_subset (f : X ⟶ Y) (V : Opens Y.carrier) :
    Set.range
        (((X.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding) ≫ f).hom.base) ⊆
      Set.range (Y.ofRestrict V.isOpenEmbedding).hom.base := sorry

/-- The restriction `g : f^{-1}(V) ⟶ V` of a morphism of ringed spaces `f : X ⟶ Y` to an open
subspace `V ⊆ Y`. -/
noncomputable def restrictedMorphismToOpen (f : X ⟶ Y) (V : Opens Y.carrier) :
    X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  InducedCategory.homMk
    (PresheafedSpace.IsOpenImmersion.lift
      (Y.ofRestrict V.isOpenEmbedding).hom
      (((X.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding) ≫ f).hom)
      (restrictedMorphism_range_subset f V))

/-- The restriction of a derived `\mathcal O_X`-module to an open subspace, transported to the
standard derived category of modules over the restricted ringed space. -/
noncomputable abbrev restrictedModuleDerivedOnOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) (E : ModuleDerived X) :
    ModuleDerived (X.restrict U.isOpenEmbedding) :=
  Eq.mp (restrict_moduleDerived_eq U).symm
    ((moduleSheafRestrictionToOpen U ((RingedSpace.ringCatSheaf X))).mapDerivedCategory.obj E)

/-- The derived direct image for the restricted morphism `g : f^{-1}(V) ⟶ V`, transported back to
modules over the restricted ambient structure sheaf on `V`. -/
noncomputable abbrev restrictedDerivedPushforwardOnOpen
    (f : X ⟶ Y) (V : Opens Y.carrier)
    [(RingedSpace.Hom.pushforward f).Additive]
    [(RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived (restrictedMorphismToOpen f V))
      (ModuleQis (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding))]
    (E : ModuleDerived X) :
    DerivedCategory
      (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} V.inclusion').obj
        ((RingedSpace.ringCatSheaf Y)))) :=
  Eq.mp (restrict_moduleDerived_eq V)
    ((modulePushforwardDerived (restrictedMorphismToOpen f V)).obj
      (restrictedModuleDerivedOnOpen ((Opens.map f.hom.base).obj V) E))

-- Proof sketch: represent `E` by a K-injective complex `I`. By Lemma `20.32.1`, the restriction
-- `I|_{f^{-1}(V)}` is again K-injective, so `Rf_* E` and `Rg_* (E|_{f^{-1}(V)})` are computed by
-- the underived pushforwards of these representatives. The ordinary sheaf identity
-- `(f_* \mathcal F)|_V = g_*(\mathcal F|_{f^{-1}(V)})` then gives the comparison.
/-- Lemma 20.32.4: for a morphism of ringed spaces `f : (X, \mathcal O_X) \to
(Y, \mathcal O_Y)`, an open subspace `V \subset Y`, the inverse-image open `U = f^{-1}(V)`, and
`g : U \to V` the induced morphism, the restriction of `Rf_* E` to `V` is canonically
isomorphic to `Rg_* (E|_U)` for every `E` in `D(\mathcal O_X)`. -/
theorem modulePushforwardDerived_restrict_isomorphic
    (f : X ⟶ Y) (V : Opens Y.carrier)
    [(RingedSpace.Hom.pushforward f).Additive]
    [(RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived (restrictedMorphismToOpen f V))
      (ModuleQis (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding))]
    (E : ModuleDerived X) :
    IsIsomorphic
      ((moduleSheafRestrictionToOpen V ((RingedSpace.ringCatSheaf Y))).mapDerivedCategory.obj
        ((modulePushforwardDerived f).obj E))
      (restrictedDerivedPushforwardOnOpen f V E) := sorry

end AlgebraicGeometry

/-! ### Lemma_20_32_5 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The underlying continuous map of a morphism of ringed spaces. -/
abbrev baseMap (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  f.hom.base

/-- The morphism of structure sheaves attached to a morphism of ringed spaces. -/
abbrev structureSheafHom (f : X ⟶ Y) :=
  f.hom.c

/-- The inverse-image open subset `f^{-1}(V)` attached to `V ⊆ Y`. -/
abbrev preimageOpen (f : X ⟶ Y) (V : Opens Y.carrier) : Opens X.carrier :=
  Opens.comap (baseMap f).hom V

/-- The map on section rings over an open subset induced by a morphism of ringed spaces. -/
abbrev sectionsMapOnOpen (f : X ⟶ Y) (V : Opens Y.carrier) :
    sectionsRingOnOpen Y V ⟶ sectionsRingOnOpen X (preimageOpen f V) :=
  (structureSheafHom f).app (Opposite.op V)

/-- Restriction of scalars along the map `Γ(V, \mathcal O_Y) → Γ(f^{-1}(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤
      ModuleCat (sectionsRingOnOpen Y V) :=
  ModuleCat.restrictScalars (sectionsMapOnOpen f V).hom

/-- Restriction of scalars on section modules is additive. -/
instance moduleSectionsRestrictionFunctor_additive (f : X ⟶ Y) (V : Opens Y.carrier) :
    (moduleSectionsRestrictionFunctor f V).Additive := by
  infer_instance

/-- Restriction of scalars on derived categories along the map
`Γ(V, \mathcal O_Y) → Γ(f^{-1}(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionExactFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤ₑ
      ModuleCat (sectionsRingOnOpen Y V) :=
  ExactFunctor.of (moduleSectionsRestrictionFunctor f V)

/-- Restriction of scalars on derived categories along the map
`Γ(V, \mathcal O_Y) → Γ(f^{-1}(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionDerivedFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X (preimageOpen f V))) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  let _ : (moduleSectionsRestrictionExactFunctor f V).obj.Additive :=
    moduleSectionsRestrictionFunctor_additive f V
  (moduleSectionsRestrictionExactFunctor f V).obj.mapDerivedCategory

/-- The functor `RΓ(f^{-1}(V), -)` viewed in `D(Γ(V, \mathcal O_Y))` via restriction of
scalars. -/
abbrev moduleDerivedSectionsAtPreimageViaRestriction (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  moduleDerivedSectionsAtOpen X (preimageOpen f V) ⋙
    moduleSectionsRestrictionDerivedFunctor f V

-- Proof sketch: first use Lemma `20.32.4` to identify the restriction of `Rf_*` to `V` with the
-- derived pushforward for the restricted morphism `f^{-1}(V) → V`. Then apply Lemma `20.28.2` to
-- compose this restricted derived pushforward with derived global sections on `V`, obtaining the
-- same functor as derived sections on `f^{-1}(V)`, viewed over `Γ(V, \mathcal O_Y)` by
-- restriction of scalars.
/-- Lemma 20.32.5: for a morphism of ringed spaces `f : X ⟶ Y` and an open subset `V ⊆ Y`, with
`U = f^{-1}(V)`, the functor `RΓ(U, -)` viewed in `D(Γ(V, \mathcal O_Y))` via restriction of
scalars is isomorphic to `RΓ(V, -) ∘ Rf_*`. -/
theorem moduleDerivedSectionsAtPreimageViaRestriction_iso_pushforward_comp
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIsomorphic
      (moduleDerivedSectionsAtPreimageViaRestriction f V)
      (moduleDerivedPushforward f ⋙ moduleDerivedSectionsAtOpen Y V) := sorry

-- Proof sketch: specialize
-- `moduleDerivedSectionsAtPreimageViaRestriction_iso_pushforward_comp` to `V = ⊤`, where
-- `Γ(⊤, \mathcal O_Y) = Γ(Y, \mathcal O_Y)` and `f^{-1}(⊤) = X`.
/-- The global-sections case of the preimage comparison, viewed over `Γ(Y, \mathcal O_Y)`. -/
theorem moduleDerivedGlobalSectionsViaRestriction_iso_pushforward_comp
    (f : X ⟶ Y) :
    IsIsomorphic
      (moduleDerivedSectionsAtPreimageViaRestriction f ⊤)
      (moduleDerivedPushforward f ⋙ moduleDerivedGlobalSections Y) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_32_6 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

-- Proof sketch: evaluate the presheaf
-- `ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) i` on `V`.
-- By Lemma `20.32.5`, the derived sections of `Rf_* K` on `V` identify with the derived
-- sections of `K` on `f^{-1}(V)`. Taking degree-`i` homology and forgetting to abelian groups
-- gives the stated objectwise comparison.
/-- The canonical cohomology presheaf of `Rf_* K` has value `H^i(f^{-1}(V), K)` on each open
subset `V ⊆ Y`. -/
lemma pushforward_objectwiseCohomologyPresheaf_obj_isomorphic_preimageHypercohomology
    (f : X ⟶ Y)
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) (V : Opens Y.carrier) :
    IsIsomorphic
      ((ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) i).obj
        (op V))
      (moduleOpenHypercohomology X (preimageOpen f V) K i) := sorry

-- Proof sketch: apply Lemma `20.32.3` on the target ringed space `Y` to the derived object
-- `Rf_* K`. By the previous lemma and Lemma `20.32.5`, this objectwise cohomology presheaf is
-- exactly the presheaf `V ↦ H^i(f^{-1}(V), K)` from the textbook statement.
/-- Lemma 20.32.6: for a morphism of ringed spaces `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`
and an object `K` of `D(\mathcal O_X)`, the degree-`i` cohomology sheaf `H^i(Rf_* K)` is the
sheaf associated to the presheaf on `Y` whose value on an open subset `V ⊆ Y` is
`H^i(f^{-1}(V), K) = H^i(V, Rf_* K)`. In the formalization, this is the sheafification of the
canonical objectwise cohomology presheaf of `Rf_* K`. -/
lemma pushforward_objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) :
    IsIsomorphic
      ((presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).obj
        (ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) i))
      (ringedSpaceCohomologySheaf Y ((moduleDerivedPushforward f).obj K) i) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_32_7 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The abelian category of sheaves of abelian groups on the underlying topological space of a
ringed space. -/
abbrev AbelianSheafCat (X : RingedSpace.{u}) :=
  Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The forgetful functor from `\mathcal O_X`-modules to their underlying abelian sheaves. -/
abbrev underlyingAbelianSheafFunctor (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ AbelianSheafCat X :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)

/-- The derived functor sending a derived `\mathcal O_X`-module to its underlying derived abelian
sheaf. -/
abbrev underlyingAbelianSheafDerived (X : RingedSpace.{u})
    [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (AbelianSheafCat X) :=
  CategoryTheory.additiveFunctorTotalRightDerived (underlyingAbelianSheafFunctor X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor X U)

/-- The underived sections functor `\Gamma(U,-)` on abelian sheaves over the underlying space of
`X`. -/
abbrev abelianSectionsFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    AbelianSheafCat X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on derived abelian sheaves over the underlying
space of `X`. -/
abbrev abelianSectionsDerived (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(abelianSectionsFunctor X U).Additive]
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (abelianSectionsFunctor X U)

/-- The direct-image functor on abelian sheaves induced by a morphism of ringed spaces. -/
abbrev abelianPushforwardFunctor {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    AbelianSheafCat X ⥤ AbelianSheafCat Y :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base

/-- The derived direct-image functor on underlying abelian sheaves. -/
abbrev abelianPushforwardDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(abelianPushforwardFunctor f).Additive]
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory (AbelianSheafCat Y) :=
  CategoryTheory.additiveFunctorTotalRightDerived (abelianPushforwardFunctor f)

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [IsGrothendieckAbelian.{u} (AbelianSheafCat X)]
variable [(moduleSectionsAsAbelianFunctor X U).Additive]
variable [(abelianSectionsFunctor X U).Additive]

-- Proof sketch: both underived section functors on `U` are evaluation of the same underlying
-- abelian presheaf, once starting from `\mathcal O_X`-modules and once starting from abelian
-- sheaves. Compare their total right derived functors to obtain the canonical map
-- `R\Gamma(U, K) \to R\Gamma(U, K_{ab})`; the textbook K-injective construction shows that this
-- comparison is an isomorphism.
/-- Lemma 20.32.7 (1): for an open subset `U ⊆ X` and an object `K` of `D(\mathcal O_X)`, the
canonical comparison map `R\Gamma(U, K) \to R\Gamma(U, K_{ab})` is an isomorphism in
`D(\operatorname{Ab})`. Here `K_{ab}` denotes the image of `K` in the derived category of
abelian sheaves on `X`. -/
lemma moduleSectionsAsAbelianDerived_underlyingAbelian_isomorphic
    (K : DerivedCategory (RingedSpace.Modules X)) :
    IsIsomorphic
      ((moduleSectionsAsAbelianDerived X U).obj K)
      ((abelianSectionsDerived X U).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules Y)]
variable [IsGrothendieckAbelian.{u} (AbelianSheafCat X)]
variable [(abelianPushforwardFunctor f).Additive]

-- Proof sketch: underived pushforward of `\mathcal O_X`-modules followed by forgetting module
-- structure agrees with pushforward of the underlying abelian sheaf along the underlying
-- continuous map. Comparing the two total right derived functors yields the canonical morphism
-- `Rf_* K \to Rf_*(K_{ab})` in the derived category of abelian sheaves on `Y`, and the same
-- K-injective representative computes both sides.
/-- Lemma 20.32.7 (2): for a morphism of ringed spaces `f : X ⟶ Y` and an object `K` of
`D(\mathcal O_X)`, the canonical comparison map `Rf_* K \to Rf_*(K_{ab})`, viewed in the derived
category of abelian sheaves on `Y`, is an isomorphism. Here `K_{ab}` denotes the image of `K` in
the derived category of abelian sheaves on `X`. -/
lemma modulePushforwardDerived_underlyingAbelian_isomorphic
    (K : DerivedCategory (RingedSpace.Modules X)) :
    IsIsomorphic
      ((underlyingAbelianSheafDerived Y).obj ((moduleDerivedPushforward f).obj K))
      ((abelianPushforwardDerived f).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_32_8 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) :
    TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The restricted `RingCat`-valued structure sheaf on the open subset `U`. -/
private abbrev restrictedRingCatSheaf (U : Opens X.carrier) :=
  (TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X)

local notation "ModX" => SheafOfModules (ringedSpaceRingCatSheaf X)
local notation "ModU" => SheafOfModules (restrictedRingCatSheaf U)
local notation "DModX" => DerivedCategory ModX
local notation "DModU" => DerivedCategory ModU
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DModX)
local notation "QU" => (DerivedCategory.Q : CochainComplex ModU ℤ ⥤ DModU)
local notation "QisX" => HomologicalComplex.quasiIso ModX (up ℤ)
local notation "QisU" => HomologicalComplex.quasiIso ModU (up ℤ)

/-- Restriction of `\mathcal O_X`-modules from `X` to the open subspace `U`. -/
private abbrev moduleRestrictionToOpen :
    ModX ⥤ ModU :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

-- Proof sketch: for an open immersion, module restriction is the inverse-image functor on module
-- sheaves. Its left adjoint is extension by zero, so this restriction functor is a right
-- adjoint.
/-- Restriction of module sheaves to an open subspace is a right adjoint. -/
private instance moduleRestrictionToOpen_isRightAdjoint :
    (moduleRestrictionToOpen U).IsRightAdjoint := sorry

/-- Extension by zero of `\mathcal O_U`-modules from the open subspace `U` back to `X`. -/
private noncomputable abbrev moduleExtensionByZeroFromOpen :
    ModU ⥤ ModX :=
  (moduleRestrictionToOpen U).leftAdjoint

-- Proof sketch: extension by zero is the chosen left adjoint to restriction to the open
-- subspace. The corresponding adjunction is obtained formally from
-- `Adjunction.ofIsRightAdjoint`.
/-- The chosen extension-by-zero functor is left adjoint to restriction to the open subspace. -/
private noncomputable abbrev moduleExtensionByZeroFromOpenAdjunction :
    moduleExtensionByZeroFromOpen U ⊣ moduleRestrictionToOpen U :=
  Adjunction.ofIsRightAdjoint (moduleRestrictionToOpen U)

-- Proof sketch: restriction to an open subspace is exact on the underlying abelian sheaves, and
-- the forgetful functor from module sheaves to abelian sheaves reflects finite limits and finite
-- colimits. Hence the module-valued restriction functor preserves both finite limits and finite
-- colimits.
/-- Restriction to an open subspace is exact on sheaves of modules. -/
private theorem moduleRestrictionToOpen_exact :
    exactFunctor ModX ModU (moduleRestrictionToOpen U) := sorry

-- Proof sketch: extension by zero is exact on underlying abelian sheaves for an open immersion,
-- and the module structure is transported functorially, so finite limits and finite colimits are
-- preserved on module sheaves as well.
/-- Extension by zero from an open subspace is exact on sheaves of modules. -/
private theorem moduleExtensionByZeroFromOpen_exact :
    exactFunctor ModU ModX (moduleExtensionByZeroFromOpen U) := sorry

/-- Restriction to an open subspace preserves finite limits. -/
private noncomputable instance moduleRestrictionToOpen_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestrictionToOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen U)).mp
    (moduleRestrictionToOpen_exact U)).1

/-- Restriction to an open subspace preserves finite colimits. -/
private noncomputable instance moduleRestrictionToOpen_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestrictionToOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen U)).mp
    (moduleRestrictionToOpen_exact U)).2

/-- Extension by zero from an open subspace preserves finite limits. -/
private noncomputable instance moduleExtensionByZeroFromOpen_preservesFiniteLimits :
    PreservesFiniteLimits (moduleExtensionByZeroFromOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleExtensionByZeroFromOpen U)).mp
    (moduleExtensionByZeroFromOpen_exact U)).1

/-- Extension by zero from an open subspace preserves finite colimits. -/
private noncomputable instance moduleExtensionByZeroFromOpen_preservesFiniteColimits :
    PreservesFiniteColimits (moduleExtensionByZeroFromOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleExtensionByZeroFromOpen U)).mp
    (moduleExtensionByZeroFromOpen_exact U)).2

-- Proof sketch: any left exact or right exact functor between abelian categories is additive. The
-- exactness statement for restriction provides both hypotheses.
/-- Restriction to an open subspace is additive. -/
private instance moduleRestrictionToOpen_additive :
    (moduleRestrictionToOpen U).Additive := sorry

-- Proof sketch: any left exact or right exact functor between abelian categories is additive. The
-- exactness statement for extension by zero provides both hypotheses.
/-- Extension by zero from an open subspace is additive. -/
private instance moduleExtensionByZeroFromOpen_additive :
    (moduleExtensionByZeroFromOpen U).Additive := sorry

-- Proof sketch: exact extension by zero preserves quasi-isomorphisms, so the induced functor on
-- derived categories is the left derived functor of the cochain-level extension-by-zero functor.
/-- The derived functor induced by exact extension by zero is its left derived functor. -/
private theorem moduleExtensionByZeroFromOpen_mapDerivedCategory_isLeftDerivedFunctor :
    (moduleExtensionByZeroFromOpen U).mapDerivedCategory.IsLeftDerivedFunctor
      ((moduleExtensionByZeroFromOpen U).mapDerivedCategoryFactors.hom)
      QisU := sorry

attribute [local instance] moduleExtensionByZeroFromOpen_mapDerivedCategory_isLeftDerivedFunctor

/-- Exact open-subspace extension by zero has an everywhere-defined total left derived functor. -/
private noncomputable instance moduleExtensionByZeroFromOpen_hasLeftDerivedFunctor :
    ((moduleExtensionByZeroFromOpen U).mapHomologicalComplex (up ℤ) ⋙ QX).HasLeftDerivedFunctor
      QisU :=
  Functor.HasLeftDerivedFunctor.mk'
    ((moduleExtensionByZeroFromOpen U).mapDerivedCategory)
    ((moduleExtensionByZeroFromOpen U).mapDerivedCategoryFactors.hom)

-- Proof sketch: exact restriction to an open subspace preserves quasi-isomorphisms, so the
-- induced functor on derived categories is the right derived functor of the cochain-level
-- restriction functor.
/-- The derived functor induced by exact restriction to an open subspace is its right derived
functor. -/
private theorem moduleRestrictionToOpen_mapDerivedCategory_isRightDerivedFunctor :
    (moduleRestrictionToOpen U).mapDerivedCategory.IsRightDerivedFunctor
      ((moduleRestrictionToOpen U).mapDerivedCategoryFactors.inv)
      QisX := sorry

attribute [local instance] moduleRestrictionToOpen_mapDerivedCategory_isRightDerivedFunctor

/-- Exact open-subspace restriction has an everywhere-defined total right derived functor. -/
private noncomputable instance moduleRestrictionToOpen_hasRightDerivedFunctor :
    ((moduleRestrictionToOpen U).mapHomologicalComplex (up ℤ) ⋙ QU).HasRightDerivedFunctor
      QisX :=
  Functor.HasRightDerivedFunctor.mk'
    ((moduleRestrictionToOpen U).mapDerivedCategory)
    ((moduleRestrictionToOpen U).mapDerivedCategoryFactors.inv)

/-- The left derived extension-by-zero functor attached to the open immersion `j : U ↪ X`. -/
noncomputable abbrev moduleExtensionByZeroFromOpenDerived :
    DModU ⥤ DModX :=
  (((moduleExtensionByZeroFromOpen U).mapHomologicalComplex (up ℤ)) ⋙ QX).totalLeftDerived
    QU
    QisU

/-- The right derived restriction functor attached to the open immersion `j : U ↪ X`. -/
noncomputable abbrev moduleRestrictionToOpenDerived :
    DModX ⥤ DModU :=
  (((moduleRestrictionToOpen U).mapHomologicalComplex (up ℤ)) ⋙ QU).totalRightDerived
    QX
    QisX

-- Proof sketch: start from the underived adjunction
-- `openSubsetModuleSheafExtensionByZero U (ringedSpaceRingCatSheaf X) ⊣
-- moduleSheafRestrictionToOpen U (ringedSpaceRingCatSheaf X)`. Exactness of both functors
-- identifies extension by zero with its total left derived functor and restriction with its total
-- right derived functor; then apply the generic derived-adjunction theorem of Lemma `13.30.3`.
/-- Lemma 20.32.8: for a ringed space `(X, \mathcal O_X)` and an open subset `U \subset X`, the
restriction functor on derived categories is right adjoint to extension by zero along the open
immersion `j : (U, \mathcal O_U) \to (X, \mathcal O_X)`. In the present formalization this is the
adjunction between the derived extension-by-zero functor and the derived restriction functor on
sheaves of modules. -/
theorem moduleRestrictionToOpenDerived_rightAdjoint_to_extensionByZeroFromOpenDerived :
    Nonempty
      (moduleExtensionByZeroFromOpenDerived U ⊣
        moduleRestrictionToOpenDerived U) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_32_9 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.32.9:
- primary domain: K-injective cochain complexes of module sheaves on ringed spaces under the
  pullback-pushforward adjunction attached to a flat morphism;
- sampled owner declarations:
  `RingedSpace.Hom.IsFlat`,
  `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstraction: the Chapter 13 owner theorem for a right adjoint to an exact additive
  left adjoint, specialized to `f^* ⊣ f_*` for a flat morphism of ringed spaces.

Primitive-vs-derived split:
- primitive data: a morphism `f : X ⟶ Y`, the canonical owner hypothesis `[RingedSpace.Hom.IsFlat f]`,
  and a K-injective complex `I : CochainComplex (RingedSpace.Modules X) ℤ`;
- derived API: K-injectivity of the pushforward complex `((f _*).mapHomologicalComplex (up ℤ)).obj I`.

Source/core/bridge triage:
- `source-facing`: a flat direct image on ringed spaces sends K-injective complexes to
  K-injective complexes;
- `core/canonical`: `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: this file is the ringed-space specialization using the canonical owners
  `RingedSpace.Hom.IsFlat`, `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`, and
  `f _*`.
-/

section

variable {X Y : RingedSpace.{u}}

local notation "ModX" => (RingedSpace.Modules X)
local notation "ModY" => (RingedSpace.Modules Y)

-- Proof sketch: the adjunction `f^* ⊣ f_*` is the canonical module-sheaf adjunction from Chapter
-- 6, and flatness upgrades `f^*` to an exact functor by Lemma `17.20.2`. Apply the Chapter 13
-- owner theorem saying that a right adjoint to an exact additive left adjoint preserves
-- K-injective cochain complexes.
/-- Lemma 20.32.9: for a flat morphism of ringed spaces `f : X ⟶ Y`, the direct image of a
K-injective complex of `\mathcal O_X`-modules is K-injective as a complex of
`\mathcal O_Y`-modules. -/
theorem ringedSpaceModulePushforward_isKInjective_of_flat
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f]
    (I : CochainComplex ModX ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((f _*).mapHomologicalComplex (up ℤ)).obj I) := by
  let adj :=
    SheafOfModules.pullbackPushforwardAdjunction (RingedSpace.Hom.toRingCatSheafHom f)
  let hExact := AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact f
  letI : CategoryTheory.Limits.PreservesFiniteLimits (f^*) :=
    (CategoryTheory.exactFunctor_iff (f^*)).mp hExact |>.1
  letI : CategoryTheory.Limits.PreservesBinaryBiproducts (f^*) :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts (f^*)
  letI : (f^*).Additive := Functor.additive_of_preservesBinaryBiproducts _
  letI : (f _*).Additive := adj.right_adjoint_additive
  simpa using
    right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (f _*) (f^*) adj hExact I

end

end AlgebraicGeometry.RingedSpace
