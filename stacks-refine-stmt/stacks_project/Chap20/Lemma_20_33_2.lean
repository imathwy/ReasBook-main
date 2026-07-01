import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
