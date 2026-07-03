import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_33_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/- Domain-style sampling for Lemma 20.33.1:
- primary domain: Mayer-Vietoris distinguished triangles in `D(\mathcal O_X)` built from
  restriction to opens and derived extension by zero;
- sampled owner declarations:
  `moduleSheafRestrictionToOpen`,
  `moduleSheafExtensionByZeroFromOpen`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `Triangle.mk`,
  `distTriang`;
- best owner abstraction: the Chapter 6 open-immersion restriction/extension-by-zero functors,
  passed to derived categories through the canonical owner `CategoryTheory.Functor.mapDerivedCategory`,
  together with the canonical triangle owner `Triangle`;
- primitive data: the cover opens `U, V`, the object `E`, and the three triangle morphisms
  `α, β, δ`;
- derived API: the two named Mayer-Vietoris vertices below, kept only to avoid repeating the same
  composite terms throughout the theorem statement.

Source/core/bridge triage:
- `source-facing`: the existence of the Mayer-Vietoris distinguished triangle for `E`;
- `core/canonical`: `moduleSheafRestrictionToOpen`, `moduleSheafExtensionByZeroFromOpen`,
  `CategoryTheory.Functor.mapDerivedCategory`, and `Triangle.mk`;
- `bridge/view`: the private derived-open functors and the two vertex abbreviations below.

This file therefore keeps only the two vertex names and uses `Triangle.mk` directly, rather than
introducing a parallel local triangle wrapper. -/

private abbrev openSubspaceModuleCategory (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))

private instance moduleSheafRestrictionToOpen_additive (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

private instance moduleSheafRestrictionToOpen_preservesFiniteLimits (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)) := sorry

private instance moduleSheafRestrictionToOpen_preservesFiniteColimits (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)) := sorry

private noncomputable abbrev moduleRestrictionToOpenDerived (U : Opens X.carrier) :
    DModX ⥤ DerivedCategory (openSubspaceModuleCategory U) :=
  (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory

private instance moduleSheafExtensionByZeroFromOpen_additive (U : Opens X.carrier) :
    (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

private instance moduleSheafExtensionByZeroFromOpen_preservesFiniteLimits
    (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

private instance moduleSheafExtensionByZeroFromOpen_preservesFiniteColimits
    (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

private noncomputable abbrev moduleExtensionByZeroFromOpenDerived (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory U) ⥤ DModX :=
  (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory

/-- The intersection term `j_{U ∩ V,!}(E|_{U ∩ V})` in the Mayer-Vietoris triangle. -/
abbrev moduleDerivedMayerVietorisIntersection
    (U V : Opens X.carrier) (E : DModX) : DModX :=
  (moduleExtensionByZeroFromOpenDerived (U ⊓ V)).obj
    ((moduleRestrictionToOpenDerived (U ⊓ V)).obj E)

/-- The middle term `j_{U,!}(E|_U) \oplus j_{V,!}(E|_V)` in the Mayer-Vietoris triangle. -/
abbrev moduleDerivedMayerVietorisMiddle
    (U V : Opens X.carrier) (E : DModX) : DModX :=
  (moduleExtensionByZeroFromOpenDerived U).obj
      ((moduleRestrictionToOpenDerived U).obj E) ⊞
    (moduleExtensionByZeroFromOpenDerived V).obj
      ((moduleRestrictionToOpenDerived V).obj E)

-- Proof sketch: choose a complex `\mathcal E^\bullet` representing `E`, apply restriction and
-- extension by zero termwise to obtain the short exact sequence of complexes
-- `0 \to j_{U \cap V,!}(\mathcal E^\bullet|_{U \cap V}) \to
-- j_{U,!}(\mathcal E^\bullet|_U) \oplus j_{V,!}(\mathcal E^\bullet|_V) \to \mathcal E^\bullet
-- \to 0`, and then pass to the associated distinguished triangle in the derived category.
/-- Lemma 20.33.1: if a ringed space `X` is covered by two opens `U` and `V`, then every object
`E` of `D(\mathcal O_X)` fits into a Mayer-Vietoris distinguished triangle
`j_{U \cap V,!}(E|_{U \cap V}) \to j_{U,!}(E|_U) \oplus j_{V,!}(E|_V) \to E \to
j_{U \cap V,!}(E|_{U \cap V})[1]`. -/
theorem moduleDerived_mayerVietoris_distinguishedTriangle
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (E : DModX) :
    ∃ (α : moduleDerivedMayerVietorisIntersection U V E ⟶
          moduleDerivedMayerVietorisMiddle U V E)
      (β : moduleDerivedMayerVietorisMiddle U V E ⟶ E)
      (δ : E ⟶ (moduleDerivedMayerVietorisIntersection U V E)⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang DModX := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_33_2 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- Restriction of `\mathcal O_X`-modules to an open subspace. -/
noncomputable abbrev moduleSheafRestrictionToOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤
      SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj
        (ringedSpaceRingCatSheaf X)) :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

/-- Pushforward of modules from an open subspace back to the ambient ringed space. -/
noncomputable abbrev ringedSpaceModulePushforwardFromOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj
        (ringedSpaceRingCatSheaf X)) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf X) :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

/-- Restriction to an open subspace is additive on module sheaves. -/
instance moduleSheafRestrictionToOpen_additive {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U).Additive := sorry

/-- Pushforward from an open subspace is additive on module sheaves. -/
instance ringedSpaceModulePushforwardFromOpen_additive {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    (ringedSpaceModulePushforwardFromOpen U).Additive := sorry

/-- The endofunctor on `\mathcal O_X`-modules given by restriction to `U` followed by pushforward
back to `X`. -/
abbrev modulePushforwardAlongOpen {X : RingedSpace.{u}} (U : Opens X.carrier) :=
  moduleSheafRestrictionToOpen U ⋙ ringedSpaceModulePushforwardFromOpen U

/-- The cochain-level functor used to define `Rj_{U, *}(-|_U)`. -/
abbrev modulePushforwardAlongOpenToDerived {X : RingedSpace.{u}} (U : Opens X.carrier) :
    CochainComplex (SheafOfModules (ringedSpaceRingCatSheaf X)) ℤ ⥤
      DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (modulePushforwardAlongOpen U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- The open-pushforward endofunctor on cochain complexes admits a total right derived functor. -/
instance modulePushforwardAlongOpenToDerived_hasRightDerivedFunctor {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    Functor.HasRightDerivedFunctor
      (modulePushforwardAlongOpenToDerived U)
      (HomologicalComplex.quasiIso (SheafOfModules (ringedSpaceRingCatSheaf X))
        (ComplexShape.up ℤ)) := sorry

/-- The derived endofunctor representing `Rj_{U, *}(-|_U)` on `D(\mathcal O_X)`. -/
abbrev moduleDerivedPushforwardAlongOpen {X : RingedSpace.{u}} (U : Opens X.carrier) :
    DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X)) ⥤
      DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (modulePushforwardAlongOpenToDerived U).totalRightDerived
    (DerivedCategory.Q : CochainComplex (SheafOfModules (ringedSpaceRingCatSheaf X)) ℤ ⥤
      DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X)))
    (HomologicalComplex.quasiIso (SheafOfModules (ringedSpaceRingCatSheaf X))
      (ComplexShape.up ℤ))

/-- The middle derived object in the Mayer-Vietoris triangle for a two-open cover. -/
abbrev derivedMayerVietorisMiddleTerm {X : RingedSpace.{u}}
    (U V : Opens X.carrier) (E : DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X))) :=
  (moduleDerivedPushforwardAlongOpen U).obj E ⊞ (moduleDerivedPushforwardAlongOpen V).obj E

/-- The intersection derived object in the Mayer-Vietoris triangle for a two-open cover. -/
abbrev derivedMayerVietorisIntersectionTerm {X : RingedSpace.{u}}
    (U V : Opens X.carrier) (E : DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X))) :=
  (moduleDerivedPushforwardAlongOpen (U ⊓ V)).obj E

variable {X : RingedSpace.{u}}

-- Proof sketch: choose a K-injective complex representing `E`, identify the three displayed
-- terms with the pushforwards of its restrictions to `U`, `V`, and `U ∩ V`, use the classical
-- Mayer-Vietoris short exact sequence of complexes for the cover `U ∪ V = X`, and then apply
-- the distinguished triangle attached to a short exact sequence of complexes in the derived
-- category.
/-- Lemma 20.33.2: if a ringed space `X` is covered by two opens `U` and `V`, then every
derived `\mathcal O_X`-module `E` fits into a Mayer-Vietoris distinguished triangle with terms
`E`, `Rj_{U, *}(E|_U) ⊞ Rj_{V, *}(E|_V)`, and `Rj_{U \cap V, *}(E|_{U \cap V})`. -/
theorem ringedSpaceModule_derivedMayerVietoris_triangle
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (E : DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X))) :
    ∃ α : E ⟶ derivedMayerVietorisMiddleTerm U V E,
      ∃ β : derivedMayerVietorisMiddleTerm U V E ⟶
          derivedMayerVietorisIntersectionTerm U V E,
        ∃ δ : derivedMayerVietorisIntersectionTerm U V E ⟶ E⟦(1 : ℤ)⟧,
          Triangle.mk α β δ ∈
            distTriang (DerivedCategory (SheafOfModules (ringedSpaceRingCatSheaf X))) := sorry

end AlgebraicGeometry

/-! ### Lemma_20_33_3 (from Chap20) -/
open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The Hom group `Hom_{D(\mathcal O_X)}(E, F)` viewed as an object of `AddCommGrpCat`. -/
abbrev derived_hom_group (X : RingedSpace.{u}) (E F : DerivedCategory (RingedSpace.Modules X)) :
    AddCommGrpCat :=
  AddCommGrpCat.of (E ⟶ F)

/-- The Hom group on an open subspace `U`, i.e. `Hom_{D(\mathcal O_U)}(E|_U, F|_U)`. -/
abbrev derived_open_hom_group (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E F : DerivedCategory (RingedSpace.Modules X)) : AddCommGrpCat :=
  AddCommGrpCat.of
    (((moduleRestrictionToOpenDerived X U).obj E) ⟶
      ((moduleRestrictionToOpenDerived X U).obj F))

/-- The degree `-1` Ext group on an open subspace `U`, written as `Hom(E|_U, F|_U[-1])`. -/
abbrev derived_open_ext_neg_one_group (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E F : DerivedCategory (RingedSpace.Modules X)) : AddCommGrpCat :=
  AddCommGrpCat.of
    (((moduleRestrictionToOpenDerived X U).obj E) ⟶
      (((moduleRestrictionToOpenDerived X U).obj F)⟦(-1 : ℤ)⟧))

/-- The middle term `Hom(E|_U, F|_U) \oplus Hom(E|_V, F|_V)` in the Mayer-Vietoris segment. -/
abbrev derived_open_pair_hom_group (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E F : DerivedCategory (RingedSpace.Modules X)) : AddCommGrpCat :=
  derived_open_hom_group X U E F ⊞ derived_open_hom_group X V E F

section

variable {X : RingedSpace.{u}}

-- Proof sketch: apply the contravariant Hom functor `Hom_{D(\mathcal O_X)}(-, F)` to the
-- Mayer-Vietoris distinguished triangle for `E` from Lemma `20.33.1`, then rewrite the resulting
-- terms using the derived adjunction between extension by zero and restriction to opens from
-- Lemma `20.32.8`.
/-- Lemma 20.33.3: if a ringed space `X` is covered by two opens `U` and `V`, then the groups
`Ext^{-1}_{D(\mathcal O_{U \cap V})}(E|_{U \cap V}, F|_{U \cap V})`,
`Hom_{D(\mathcal O_X)}(E, F)`,
`Hom_{D(\mathcal O_U)}(E|_U, F|_U) \oplus Hom_{D(\mathcal O_V)}(E|_V, F|_V)`, and
`Hom_{D(\mathcal O_{U \cap V})}(E|_{U \cap V}, F|_{U \cap V})`
fit into the displayed Mayer-Vietoris exact segment. -/
theorem module_derived_mayer_vietoris_hom_exact_segment
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (E F : DerivedCategory (RingedSpace.Modules X)) :
    ∃ δ :
        derived_open_ext_neg_one_group X (U ⊓ V) E F ⟶
          derived_hom_group X E F,
      ∃ α :
          derived_hom_group X E F ⟶
            derived_open_pair_hom_group X U V E F,
        ∃ β :
            derived_open_pair_hom_group X U V E F ⟶
              derived_open_hom_group X (U ⊓ V) E F,
          (mk₃ δ α β).Exact := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_33_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.DerivedCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The ambient unbounded derived category `D(\mathcal O_X)`. -/
abbrev ringedSpaceModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The unbounded derived category of abelian groups used for derived global sections. -/
abbrev abelianDerived :=
  DerivedCategory AddCommGrpCat.{u}

/-- The derived global-sections functor `RΓ(X, -)` after forgetting the module structure on
`Γ(X, \mathcal O_X)`. -/
abbrev derivedGlobalSectionsToAbelian (X : RingedSpace.{u}) :
    ringedSpaceModuleDerived X ⥤ abelianDerived :=
  moduleDerivedGlobalSections X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The derived sections functor `RΓ(U, -)` on an open subset `U`, viewed in `D(\mathrm{Ab})`. -/
abbrev derivedSectionsAtOpenToAbelian (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ringedSpaceModuleDerived X ⥤ abelianDerived :=
  moduleDerivedSectionsAtOpen X U ⋙
    (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The derived global-sections object `RΓ(X, E)` in `D(\mathrm{Ab})`. -/
abbrev derivedGlobalSectionsObject (X : RingedSpace.{u}) (E : ringedSpaceModuleDerived X) :
    abelianDerived :=
  (derivedGlobalSectionsToAbelian X).obj E

/-- The derived sections object `RΓ(U, E)` in `D(\mathrm{Ab})`. -/
abbrev derivedSectionsAtOpenObject (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) : abelianDerived :=
  (derivedSectionsAtOpenToAbelian X U).obj E

/-- The middle biproduct `RΓ(U, E) \oplus RΓ(V, E)` in the Mayer-Vietoris triangle. -/
abbrev derivedSectionsBiprodObject (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) : abelianDerived :=
  derivedSectionsAtOpenObject X U E ⊞ derivedSectionsAtOpenObject X V E

/-- The intersection term `RΓ(U \cap V, E)` in the Mayer-Vietoris triangle. -/
abbrev derivedSectionsIntersectionObject (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) : abelianDerived :=
  derivedSectionsAtOpenObject X (U ⊓ V) E

/-- The functorial map on the middle biproduct term induced by a morphism in `D(\mathcal O_X)`.
-/
abbrev derivedSectionsBiprodMap {X : RingedSpace.{u}} (U V : Opens X.carrier)
    {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E') :
    derivedSectionsBiprodObject X U V E ⟶ derivedSectionsBiprodObject X U V E' :=
  biprod.map ((derivedSectionsAtOpenToAbelian X U).map φ)
    ((derivedSectionsAtOpenToAbelian X V).map φ)

/-- The hypercohomology object `H^n(X, E)` computed from derived global sections in
`D(\mathrm{Ab})`. -/
abbrev derivedGlobalSectionsCohomology (X : RingedSpace.{u}) (E : ringedSpaceModuleDerived X)
    (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    (derivedGlobalSectionsObject X E)

/-- The hypercohomology object `H^n(U, E)` for an open subset `U`. -/
abbrev derivedSectionsAtOpenCohomology (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    (derivedSectionsAtOpenObject X U E)

/-- The biproduct cohomology object `H^n(U, E) \oplus H^n(V, E)`. -/
abbrev derivedSectionsBiprodCohomology (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) (n : ℤ) : AddCommGrpCat.{u} :=
  derivedSectionsAtOpenCohomology X U E n ⊞ derivedSectionsAtOpenCohomology X V E n

/-- The cohomology object `H^n(U \cap V, E)` of the intersection term. -/
abbrev derivedSectionsIntersectionCohomology (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : ringedSpaceModuleDerived X) (n : ℤ) : AddCommGrpCat.{u} :=
  derivedSectionsAtOpenCohomology X (U ⊓ V) E n

section

variable {X : RingedSpace.{u}}

-- Proof sketch: start from the Mayer-Vietoris distinguished triangle of
-- `Lemma_20_33_1` in `D(\mathcal O_X)`, then apply the additive derived global-sections functor
-- of `20_14_1_1` together with the open-section comparison of `Lemma_20_32_2` to rewrite the
-- three vertices as `RΓ(X, E)`, `RΓ(U, E) \oplus RΓ(V, E)`, and `RΓ(U ∩ V, E)` in
-- `D(\mathrm{Ab})`.
/-- Lemma 20.33.4: for a ringed space `(X, \mathcal O_X)` covered by two opens `U` and `V`, every
object `E` of `D(\mathcal O_X)` fits into a distinguished triangle
`RΓ(X, E) ⟶ RΓ(U, E) \oplus RΓ(V, E) ⟶ RΓ(U \cap V, E) ⟶ RΓ(X, E)[1]`
in the derived category of abelian groups. -/
theorem derivedGlobalSections_mayerVietoris_triangle
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (E : ringedSpaceModuleDerived X) :
    ∃ α : derivedGlobalSectionsObject X E ⟶ derivedSectionsBiprodObject X U V E,
        ∃ β : derivedSectionsBiprodObject X U V E ⟶
          derivedSectionsIntersectionObject X U V E,
        ∃ δ : derivedSectionsIntersectionObject X U V E ⟶
            (derivedGlobalSectionsObject X E)⟦(1 : ℤ)⟧,
          Triangle.mk α β δ ∈ distTriang abelianDerived := sorry

-- Proof sketch: apply the homology functors `H^n` and `H^(n + 1)` on `D(\mathrm{Ab})` to the
-- distinguished triangle of `derivedGlobalSections_mayerVietoris_triangle`; the standard long
-- exact homology sequence yields the displayed five-arrow exact segment.
/-- The Mayer-Vietoris distinguished triangle on derived global sections yields the standard
cohomology exact segment
`H^n(X, E) ⟶ H^n(U, E) \oplus H^n(V, E) ⟶ H^n(U \cap V, E) ⟶ H^{n+1}(X, E) ⟶
H^{n+1}(U, E) \oplus H^{n+1}(V, E) ⟶ H^{n+1}(U \cap V, E)`. -/
theorem derivedGlobalSections_mayerVietoris_cohomology_sequence
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (E : ringedSpaceModuleDerived X) (n : ℤ) :
    ∃ f : derivedGlobalSectionsCohomology X E n ⟶
        derivedSectionsBiprodCohomology X U V E n,
      ∃ g : derivedSectionsBiprodCohomology X U V E n ⟶
          derivedSectionsIntersectionCohomology X U V E n,
        ∃ δ : derivedSectionsIntersectionCohomology X U V E n ⟶
            derivedGlobalSectionsCohomology X E (n + 1),
          ∃ f' : derivedGlobalSectionsCohomology X E (n + 1) ⟶
              derivedSectionsBiprodCohomology X U V E (n + 1),
            ∃ g' : derivedSectionsBiprodCohomology X U V E (n + 1) ⟶
                derivedSectionsIntersectionCohomology X U V E (n + 1),
              (ComposableArrows.mk₅ f g δ f' g').Exact := sorry

-- Proof sketch: choose the triangle maps functorially by applying derived global sections to a
-- functorial K-injective resolution model for `E`. Naturality of the resolution, of restriction
-- to opens, and of the triangle attached to the short exact sequence of complexes gives the three
-- naturality identities.
/-- The Mayer-Vietoris triangle on derived global sections can be chosen functorially in the
derived object `E`. -/
theorem derivedGlobalSections_mayerVietoris_functorial
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) :
    ∃ α : ∀ E : ringedSpaceModuleDerived X,
        derivedGlobalSectionsObject X E ⟶ derivedSectionsBiprodObject X U V E,
      ∃ β : ∀ E : ringedSpaceModuleDerived X,
          derivedSectionsBiprodObject X U V E ⟶
            derivedSectionsIntersectionObject X U V E,
        ∃ δ : ∀ E : ringedSpaceModuleDerived X,
            derivedSectionsIntersectionObject X U V E ⟶
              (derivedGlobalSectionsObject X E)⟦(1 : ℤ)⟧,
          (∀ E : ringedSpaceModuleDerived X,
            Triangle.mk (α E) (β E) (δ E) ∈ distTriang abelianDerived) ∧
          (∀ {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E'),
            (derivedGlobalSectionsToAbelian X).map φ ≫ α E' =
              α E ≫ derivedSectionsBiprodMap U V φ) ∧
          (∀ {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E'),
            derivedSectionsBiprodMap U V φ ≫ β E' =
              β E ≫ (derivedSectionsAtOpenToAbelian X (U ⊓ V)).map φ) ∧
          (∀ {E E' : ringedSpaceModuleDerived X} (φ : E ⟶ E'),
            (derivedSectionsAtOpenToAbelian X (U ⊓ V)).map φ ≫ δ E' =
              δ E ≫
                (shiftFunctor abelianDerived (1 : ℤ)).map
                  ((derivedGlobalSectionsToAbelian X).map φ)) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_33_5 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The derived category `D(\mathcal O_X)` of sheaves of modules on a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  letI : HasDerivedCategory (RingedSpace.Modules X) := HasDerivedCategory.standard (RingedSpace.Modules X)
  DerivedCategory (RingedSpace.Modules X)

/-- The quasi-isomorphisms in unbounded cochain complexes of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The category of `\mathcal O_U`-modules on the open subspace `U \subset X`. -/
abbrev OpenSubsetSheafModules {X : RingedSpace.{u}} (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X))

/-- The derived category of `\mathcal O_U`-modules on the open subspace `U`. -/
abbrev OpenSubsetModuleDerived {X : RingedSpace.{u}} (U : Opens X.carrier) :=
  letI : HasDerivedCategory (OpenSubsetSheafModules U) :=
    HasDerivedCategory.standard (OpenSubsetSheafModules U)
  DerivedCategory (OpenSubsetSheafModules U)

/-- The structure-sheaf morphism `\mathcal O_Y ⟶ f_* \mathcal O_X` associated to a morphism of
ringed spaces. -/
noncomputable abbrev ringedSpaceCommRingSheafPushforwardMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The corresponding morphism after forgetting commutativity of the structure sheaves. -/
noncomputable abbrev ringedSpacePushforwardStructureSheafHom
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ringedSpaceRingCatSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (ringedSpaceRingCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (ringedSpaceCommRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules associated to a morphism of ringed
spaces. -/
noncomputable abbrev ringedSpaceModulePushforward
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (ringedSpacePushforwardStructureSheafHom f)

/-- The cochain-level pushforward followed by localization to the derived category. -/
noncomputable abbrev modulePushforwardToDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive] :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ ModuleDerived Y :=
  letI : HasDerivedCategory (RingedSpace.Modules Y) := HasDerivedCategory.standard (RingedSpace.Modules Y)
  (ringedSpaceModulePushforward f).mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y))

/-- The derived direct-image functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
noncomputable abbrev modulePushforwardDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  letI : HasDerivedCategory (RingedSpace.Modules X) := HasDerivedCategory.standard (RingedSpace.Modules X)
  letI : HasDerivedCategory (RingedSpace.Modules Y) := HasDerivedCategory.standard (RingedSpace.Modules Y)
  (modulePushforwardToDerived f).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (ModuleQis X)

/-- Restriction of `\mathcal O_X`-modules to an open subspace. -/
noncomputable abbrev moduleSheafRestrictionToOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ OpenSubsetSheafModules U :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

/-- Restriction to an open subspace is additive on sheaves of modules. -/
instance moduleSheafRestrictionToOpen_additive {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U).Additive := sorry

/-- Restriction to an open subspace preserves finite limits on sheaves of modules. -/
instance moduleSheafRestrictionToOpen_preservesFiniteLimits {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen U) := sorry

/-- Pushforward of `\mathcal O_U`-modules from an open subspace back to the ambient ringed
space. -/
noncomputable abbrev ringedSpaceModulePushforwardFromOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    OpenSubsetSheafModules U ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

/-- Pushforward from an open subspace to the ambient ringed space is additive on sheaves of
modules. -/
instance ringedSpaceModulePushforwardFromOpen_additive {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    (ringedSpaceModulePushforwardFromOpen U).Additive := sorry

/-- Pushforward from an open subspace to the ambient ringed space preserves finite colimits on
sheaves of modules. -/
instance ringedSpaceModulePushforwardFromOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (ringedSpaceModulePushforwardFromOpen U) := sorry

/-- The derived restriction functor from `D(\mathcal O_X)` to the derived category on `U`. -/
noncomputable abbrev moduleDerivedRestrictionToOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    ModuleDerived X ⥤ OpenSubsetModuleDerived U :=
  letI : HasDerivedCategory (RingedSpace.Modules X) := HasDerivedCategory.standard (RingedSpace.Modules X)
  letI : HasDerivedCategory (OpenSubsetSheafModules U) :=
    HasDerivedCategory.standard (OpenSubsetSheafModules U)
  (moduleSheafRestrictionToOpen U).mapDerivedCategory

/-- The derived pushforward functor from an open subspace back to the ambient derived category. -/
noncomputable abbrev moduleDerivedPushforwardFromOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    OpenSubsetModuleDerived U ⥤ ModuleDerived X :=
  letI : HasDerivedCategory (RingedSpace.Modules X) := HasDerivedCategory.standard (RingedSpace.Modules X)
  letI : HasDerivedCategory (OpenSubsetSheafModules U) :=
    HasDerivedCategory.standard (OpenSubsetSheafModules U)
  (ringedSpaceModulePushforwardFromOpen U).mapDerivedCategory

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(ringedSpaceModulePushforward f).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The derived direct image along the restricted morphism `a = f|_U : U ⟶ Y`, written as the
composite of restriction to `U`, pushforward from `U` back to `X`, and `Rf_*`. -/
noncomputable abbrev derivedPushforwardAlongOpen
    (U : Opens X.carrier) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  moduleDerivedRestrictionToOpen U ⋙
    moduleDerivedPushforwardFromOpen U ⋙
      modulePushforwardDerived f

/-- The middle functor `Ra_*(E|_U) \oplus Rb_*(E|_V)` in the relative Mayer-Vietoris triangle. -/
noncomputable abbrev relativeDerivedMayerVietorisMiddleFunctor
    (U V : Opens X.carrier) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  derivedPushforwardAlongOpen f U ⊞ derivedPushforwardAlongOpen f V

/-- The intersection functor `Rc_*(E|_{U \cap V})` in the relative Mayer-Vietoris triangle. -/
noncomputable abbrev relativeDerivedMayerVietorisIntersectionFunctor
    (U V : Opens X.carrier) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  derivedPushforwardAlongOpen f (U ⊓ V)

-- Proof sketch: expand the pointwise binary biproduct in the functor category and then unfold the
-- definition of `relativeDerivedMayerVietorisMiddleFunctor`.
/-- Evaluating the middle relative Mayer-Vietoris functor gives the expected biproduct of the two
derived direct images from `U` and `V`. -/
theorem relativeDerivedMayerVietorisMiddleFunctor_obj
    (U V : Opens X.carrier) (E : ModuleDerived X) :
    (relativeDerivedMayerVietorisMiddleFunctor f U V).obj E =
      ((derivedPushforwardAlongOpen f U).obj E ⊞
        (derivedPushforwardAlongOpen f V).obj E) := sorry

-- Proof sketch: choose a functorial K-injective resolution of representatives of objects of
-- `D(\mathcal O_X)`, apply `f_*` to the short exact Mayer-Vietoris sequence of the restricted
-- complexes from Lemmas `20.32.1` and `20.8.3`, and pass to the canonical distinguished triangle
-- of Lemma `13.12.1`. Functoriality in `E` is encoded by taking the three displayed morphisms to
-- be natural transformations.
/-- Lemma 20.33.5: if `f : X ⟶ Y` is a morphism of ringed spaces and `X = U \cup V`, then there
exist natural morphisms
`Rf_* E ⟶ Ra_*(E|_U) \oplus Rb_*(E|_V) ⟶ Rc_*(E|_{U \cap V}) ⟶ Rf_* E[1]`
whose evaluation at every `E ∈ D(\mathcal O_X)` is a distinguished triangle; hence the relative
Mayer-Vietoris triangle is functorial in `E`. -/
theorem ringedSpaceModulePushforward_derivedMayerVietoris_triangle
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) :
    ∃ α :
        modulePushforwardDerived f ⟶ relativeDerivedMayerVietorisMiddleFunctor f U V,
      ∃ β :
          relativeDerivedMayerVietorisMiddleFunctor f U V ⟶
            relativeDerivedMayerVietorisIntersectionFunctor f U V,
        ∃ δ :
            relativeDerivedMayerVietorisIntersectionFunctor f U V ⟶
              modulePushforwardDerived f ⋙ shiftFunctor (ModuleDerived Y) (1 : ℤ),
          ∀ E : ModuleDerived X,
            Triangle.mk (α.app E) (β.app E) (δ.app E) ∈ distTriang (ModuleDerived Y) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_33_6 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The support of an abelian sheaf on a topological space, defined by nonzero stalks. -/
def abelianSheafSupport {X : TopCat.{u}} (ℱ : X.Sheaf AddCommGrpCat.{u}) : Set X :=
  { x | ¬ IsZero (ℱ.presheaf.stalk x) }

/-- The cohomology sheaf of a derived module over a sheaf of rings on a topological space. -/
abbrev moduleDerivedCohomologySheaf
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf 𝒪).obj
    ((DerivedCategory.homologyFunctor (SheafOfModules 𝒪) q).obj K)

/-- A derived module has cohomology supported on `T` when every cohomology sheaf is supported on
`T`. -/
def moduleDerivedCohomologySupportedOn
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (T : Set X) : Prop :=
  ∀ q : ℤ, abelianSheafSupport (moduleDerivedCohomologySheaf 𝒪 K q) ⊆ T

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  (RingedSpace.Modules X)

/-- The structural ring-sheaf morphism attached to the inclusion of the open subspace `U`. -/
noncomputable abbrev ringedSpaceOpenSubsetStructureSheafHom
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (RingedSpace.ringCatSheaf X) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} U.inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
    (RingedSpace.ringCatSheaf X)

/-- Pushforward of modules from the open subspace `U` back to the ambient ringed space. -/
noncomputable abbrev modulePushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pushforward (ringedSpaceOpenSubsetStructureSheafHom U)

/-- Pushforward from an open subspace is additive on module sheaves. -/
instance modulePushforwardFromOpen_additive
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Additive := sorry

/-- Pushforward from an open subspace preserves finite limits on module sheaves. -/
instance modulePushforwardFromOpen_preservesFiniteLimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteLimits (modulePushforwardFromOpen U) := sorry

/-- Pushforward from an open subspace preserves finite colimits on module sheaves. -/
instance modulePushforwardFromOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (modulePushforwardFromOpen U) := sorry

/-- The derived pushforward functor from the open subspace `U` back to `X`. -/
noncomputable abbrev moduleDerivedPushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤
      DerivedCategory (RingedSpace.Modules X) :=
  (modulePushforwardFromOpen U).mapDerivedCategory

/-- Extension by zero from the open subspace `U` is additive on module sheaves. -/
instance moduleExtensionByZeroFromOpen_additive
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

/-- Extension by zero from the open subspace `U` preserves finite limits on module sheaves. -/
instance moduleExtensionByZeroFromOpen_preservesFiniteLimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

/-- Extension by zero from the open subspace `U` preserves finite colimits on module sheaves. -/
instance moduleExtensionByZeroFromOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

/-- The derived extension-by-zero functor attached to the open immersion `j : U ↪ X`. -/
noncomputable abbrev moduleExtensionByZeroFromOpenDerived
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤
      DerivedCategory (RingedSpace.Modules X) :=
  (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory

section

variable {X : RingedSpace.{u}}

-- Proof sketch: let `V = X \ T`. The support hypothesis implies that every cohomology sheaf of
-- `E` restricts to zero on `V`, hence `E|_V = 0`. By Lemma `20.32.4`, the restriction of
-- `Rj_* (E|_U)` to `V` is also zero, while its restriction to `U` identifies with `E|_U`.
-- Comparing on the open cover `X = U ∪ V` gives the claimed isomorphism.
/-- Lemma 20.33.6 (1): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`E ∈ D(\mathcal O_X)` is supported on a closed subset `T ⊆ U`, then `E` is canonically
isomorphic to `Rj_*(E|_U)`. In this formalization `Rj_*` is represented by the exact pushforward
functor from the open subspace to `X`. -/
theorem isIsomorphic_pushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier) {T : Set X.carrier} (hT_closed : IsClosed T)
    (hTU : T ⊆ (U : Set X.carrier))
    (E : DerivedCategory (ambientModuleCategory X))
    (hE : moduleDerivedCohomologySupportedOn (RingedSpace.ringCatSheaf X) E T) :
    IsIsomorphic E
      ((moduleDerivedPushforwardFromOpen U).obj
        ((moduleRestrictionToOpenDerived X U).obj E)) := sorry

-- Proof sketch: let `V = X \ T` and `W = U ∩ V`. The support hypothesis implies that the
-- restriction of `F` to `W` has zero cohomology sheaves, hence vanishes in the derived category.
-- Lemma `20.32.4` then gives `(Rj_* F)|_V = 0`, while ordinary extension by zero also restricts
-- to zero on `V`. Both `j_! F` and `Rj_* F` restrict to `F` on `U`, so comparison on the cover
-- `X = U ∪ V` yields the isomorphism.
/-- Lemma 20.33.6 (2): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`F ∈ D(\mathcal O_U)` is supported on a closed subset `T ⊆ U`, then `j_! F` is canonically
isomorphic to `Rj_* F`. Here `j_!` is the derived extension-by-zero functor on module sheaves. -/
theorem extensionByZeroDerived_isIsomorphic_pushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier) {T : Set X.carrier} (hT_closed : IsClosed T)
    (hTU : T ⊆ (U : Set X.carrier))
    (F : DerivedCategory (openSubspaceModuleCategory X U))
    (hF : moduleDerivedCohomologySupportedOn
      ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))
      F
      (Subtype.val ⁻¹' T)) :
    IsIsomorphic
      ((moduleExtensionByZeroFromOpenDerived U).obj F)
      ((moduleDerivedPushforwardFromOpen U).obj F) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_33_7 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The derived category `D(A)` for the global-sections ring `A = Γ(X, \mathcal O_X)`. -/
abbrev globalSectionsDerived (X : RingedSpace.{u}) :=
  DerivedCategory (ModuleCat (globalSectionsRing X))

/-- The restriction map `Γ(X, \mathcal O_X) → Γ(W, \mathcal O_X)` for an open subset `W ⊆ X`. -/
abbrev globalToOpenSectionsMap (X : RingedSpace.{u}) (W : Opens X.carrier) :
    globalSectionsRing X ⟶ sectionsRingOnOpen X W :=
  X.presheaf.map (TopologicalSpace.Opens.leTop W).op

/-- Restriction of scalars from `Γ(W, \mathcal O_X)` to `Γ(X, \mathcal O_X)`. -/
abbrev openSectionsRestrictionFunctor (X : RingedSpace.{u}) (W : Opens X.carrier) :
    ModuleCat (sectionsRingOnOpen X W) ⥤ ModuleCat (globalSectionsRing X) :=
  ModuleCat.restrictScalars (globalToOpenSectionsMap X W).hom

/-- Restriction of scalars along `Γ(X, \mathcal O_X) → Γ(W, \mathcal O_X)` is additive. -/
instance openSectionsRestrictionFunctor_additive (X : RingedSpace.{u}) (W : Opens X.carrier) :
    (openSectionsRestrictionFunctor X W).Additive := by
  infer_instance

/-- The derived restriction-of-scalars functor from `D(Γ(W, \mathcal O_X))` to `D(Γ(X, \mathcal
O_X))`. -/
abbrev openSectionsRestrictionDerived (X : RingedSpace.{u}) (W : Opens X.carrier) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X W)) ⥤ globalSectionsDerived X :=
  let F := ExactFunctor.of (openSectionsRestrictionFunctor X W)
  let _ : F.obj.Additive := openSectionsRestrictionFunctor_additive X W
  F.obj.mapDerivedCategory

/-- The open-sections functor `RΓ(W, -)` viewed in `D(Γ(X, \mathcal O_X))` via restriction of
scalars. -/
abbrev moduleDerivedSectionsOverGlobal (X : RingedSpace.{u}) (W : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ globalSectionsDerived X :=
  moduleDerivedSectionsAtOpen X W ⋙ openSectionsRestrictionDerived X W

/-- The object `RΓ(X, K)` in `D(Γ(X, \mathcal O_X))`. -/
abbrev derivedGlobalSectionsObject (X : RingedSpace.{u}) (K : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  (moduleDerivedGlobalSections X).obj K

/-- The object `RΓ(W, K)` viewed in `D(Γ(X, \mathcal O_X))`. -/
abbrev derivedOpenSectionsOverGlobalObject (X : RingedSpace.{u}) (W : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) : globalSectionsDerived X :=
  (moduleDerivedSectionsOverGlobal X W).obj K

/-- The middle Mayer-Vietoris term
`RΓ(U, K) \oplus RΓ(V, K)` viewed over `Γ(X, \mathcal O_X)`. -/
abbrev derivedOpenSectionsBiprodOverGlobalObject (X : RingedSpace.{u})
    (U V : Opens X.carrier) (K : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  derivedOpenSectionsOverGlobalObject X U K ⊞
    derivedOpenSectionsOverGlobalObject X V K

/-- The intersection Mayer-Vietoris term `RΓ(U ∩ V, K)` viewed over `Γ(X, \mathcal O_X)`. -/
abbrev derivedOpenSectionsIntersectionOverGlobalObject (X : RingedSpace.{u})
    (U V : Opens X.carrier) (K : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  derivedOpenSectionsOverGlobalObject X (U ⊓ V) K

/-- The Mayer-Vietoris triangle for `RΓ(-, E)` over the global-sections ring. -/
abbrev derivedSectionsMayerVietorisTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : DerivedCategory (RingedSpace.Modules X))
    (α : derivedGlobalSectionsObject X E ⟶
      derivedOpenSectionsBiprodOverGlobalObject X U V E)
    (β : derivedOpenSectionsBiprodOverGlobalObject X U V E ⟶
      derivedOpenSectionsIntersectionOverGlobalObject X U V E)
    (δ : derivedOpenSectionsIntersectionOverGlobalObject X U V E ⟶
      (derivedGlobalSectionsObject X E)⟦(1 : ℤ)⟧) :
    Triangle (globalSectionsDerived X) :=
  Triangle.mk α β δ

/-- The tensor-product object
`RΓ(X, K) \otimes_A^{\mathbf L} RΓ(X, M)` in `D(A)`. -/
abbrev derivedGlobalSectionsTensorObject (X : RingedSpace.{u})
    (K M : DerivedCategory (RingedSpace.Modules X)) : globalSectionsDerived X :=
  (CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).obj
    (derivedGlobalSectionsObject X M)

/-- The tensor-product object
`RΓ(X, K) \otimes_A^{\mathbf L} RΓ(W, M)` in `D(A)`. -/
abbrev derivedTensorOpenSectionsOverGlobalObject (X : RingedSpace.{u})
    (W : Opens X.carrier) (K M : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  (CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).obj
    (derivedOpenSectionsOverGlobalObject X W M)

/-- The tensor-product object
`RΓ(X, K) \otimes_A^{\mathbf L} (RΓ(U, M) \oplus RΓ(V, M))` in `D(A)`. -/
abbrev derivedTensorOpenSectionsBiprodOverGlobalObject (X : RingedSpace.{u})
    (U V : Opens X.carrier) (K M : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  (CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).obj
    (derivedOpenSectionsBiprodOverGlobalObject X U V M)

/-- A chosen derived tensor product `K \otimes_{\mathcal O_X}^{\mathbf L} M` in
`D(\mathcal O_X)`. -/
abbrev ringedSpaceDerivedTensorObject (X : RingedSpace.{u})
    (derivedTensorX :
      DerivedCategory (RingedSpace.Modules X) ⥤
        DerivedCategory (RingedSpace.Modules X) ⥤
          DerivedCategory (RingedSpace.Modules X))
    (K M : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules X) :=
  (derivedTensorX.obj M).obj K

/-- Applying the exact functor `RΓ(X, K) \otimes_A^{\mathbf L} -` to the Mayer-Vietoris triangle
for `M`. -/
abbrev tensorMayerVietorisSourceTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (K M : DerivedCategory (RingedSpace.Modules X))
    (α : derivedGlobalSectionsObject X M ⟶
      derivedOpenSectionsBiprodOverGlobalObject X U V M)
    (β : derivedOpenSectionsBiprodOverGlobalObject X U V M ⟶
      derivedOpenSectionsIntersectionOverGlobalObject X U V M)
    (δ : derivedOpenSectionsIntersectionOverGlobalObject X U V M ⟶
      (derivedGlobalSectionsObject X M)⟦(1 : ℤ)⟧) :
    Triangle (globalSectionsDerived X) :=
  ((CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).mapTriangle).obj
    (derivedSectionsMayerVietorisTriangle X U V M α β δ)

/-- The Mayer-Vietoris triangle for `K \otimes_{\mathcal O_X}^{\mathbf L} M`, viewed over
`Γ(X, \mathcal O_X)`. -/
abbrev tensorMayerVietorisTargetTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (derivedTensorX :
      DerivedCategory (RingedSpace.Modules X) ⥤
        DerivedCategory (RingedSpace.Modules X) ⥤
          DerivedCategory (RingedSpace.Modules X))
    (K M : DerivedCategory (RingedSpace.Modules X))
    (α : derivedGlobalSectionsObject X (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
      derivedOpenSectionsBiprodOverGlobalObject X U V
        (ringedSpaceDerivedTensorObject X derivedTensorX K M))
    (β : derivedOpenSectionsBiprodOverGlobalObject X U V
          (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
      derivedOpenSectionsIntersectionOverGlobalObject X U V
        (ringedSpaceDerivedTensorObject X derivedTensorX K M))
    (δ : derivedOpenSectionsIntersectionOverGlobalObject X U V
        (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
      (derivedGlobalSectionsObject X
        (ringedSpaceDerivedTensorObject X derivedTensorX K M))⟦(1 : ℤ)⟧) :
    Triangle (globalSectionsDerived X) :=
  derivedSectionsMayerVietorisTriangle X U V
    (ringedSpaceDerivedTensorObject X derivedTensorX K M) α β δ

section

variable {X : RingedSpace.{u}}

-- Proof sketch: choose the Mayer-Vietoris triangle for `M` over `Γ(X, \mathcal O_X)` and the
-- Mayer-Vietoris triangle for `K \otimes_{\mathcal O_X}^{\mathbf L} M`. The exact functor
-- `RΓ(X, K) \otimes_A^{\mathbf L} -` carries the first to a distinguished triangle, and the cup
-- product maps on `X`, `U`, `V`, and `U ∩ V` are compatible with restriction, so the two squares
-- on the first two rows and the square on the third row commute. These compatibilities assemble
-- into a morphism of triangles.
/-- Lemma 20.33.7: for a ringed space `(X, \mathcal O_X)` with `X = U ∪ V` and objects `K, M` of
`D(\mathcal O_X)`, there is a morphism from the distinguished triangle obtained by applying the
exact functor `RΓ(X, K) \otimes_{\Gamma(X,\mathcal O_X)}^{\mathbf L} -` to the Mayer-Vietoris
triangle for `M` to the Mayer-Vietoris distinguished triangle for
`K \otimes_{\mathcal O_X}^{\mathbf L} M`, for a chosen derived tensor-product bifunctor
`derivedTensorX`, whose components are the cup-product maps on `X`, `U ⊔ V`, and `U ∩ V`. -/
theorem derivedGlobalSections_tensor_mayerVietoris_triangle_morphism
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (derivedTensorX :
      DerivedCategory (RingedSpace.Modules X) ⥤
        DerivedCategory (RingedSpace.Modules X) ⥤
          DerivedCategory (RingedSpace.Modules X))
    (K M : DerivedCategory (RingedSpace.Modules X)) :
    ∃ (αM : derivedGlobalSectionsObject X M ⟶
          derivedOpenSectionsBiprodOverGlobalObject X U V M)
      (βM : derivedOpenSectionsBiprodOverGlobalObject X U V M ⟶
          derivedOpenSectionsIntersectionOverGlobalObject X U V M)
      (δM : derivedOpenSectionsIntersectionOverGlobalObject X U V M ⟶
          (derivedGlobalSectionsObject X M)⟦(1 : ℤ)⟧)
      (hM : derivedSectionsMayerVietorisTriangle X U V M αM βM δM ∈
          distTriang (globalSectionsDerived X))
      (αKM : derivedGlobalSectionsObject X
            (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
          derivedOpenSectionsBiprodOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (βKM : derivedOpenSectionsBiprodOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
          derivedOpenSectionsIntersectionOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (δKM : derivedOpenSectionsIntersectionOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
          (derivedGlobalSectionsObject X
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))⟦(1 : ℤ)⟧)
      (hKM : tensorMayerVietorisTargetTriangle X U V derivedTensorX K M αKM βKM δKM ∈
          distTriang (globalSectionsDerived X))
      (cupX : derivedGlobalSectionsTensorObject X K M ⟶
          derivedGlobalSectionsObject X
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (cupUV : derivedTensorOpenSectionsBiprodOverGlobalObject X U V K M ⟶
          derivedOpenSectionsBiprodOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (cupI : derivedTensorOpenSectionsOverGlobalObject X (U ⊓ V) K M ⟶
          derivedOpenSectionsIntersectionOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (hLeft : tensorMayerVietorisSourceTriangle X U V K M αM βM δM ∈
          distTriang (globalSectionsDerived X)),
      ∃ φ : tensorMayerVietorisSourceTriangle X U V K M αM βM δM ⟶
          tensorMayerVietorisTargetTriangle X U V derivedTensorX K M αKM βKM δKM,
        ∃ hφ₁ : φ.hom₁ = cupX,
          ∃ hφ₂ : φ.hom₂ = cupUV, φ.hom₃ = cupI := sorry

end

end AlgebraicGeometry.RingedSpace
