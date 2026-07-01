import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
