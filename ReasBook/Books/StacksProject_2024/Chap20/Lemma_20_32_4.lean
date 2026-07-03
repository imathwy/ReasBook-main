import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.Chap06.Definition_6_31_2
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap20.«20_3_0_4»

-- Declarations for this item will be appended below by the statement pipeline.

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
