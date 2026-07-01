import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable {A : Type w} [Category A] [Abelian A] [HasDerivedCategory A]
variable [HasDerivedCategory (Cᵒᵖ ⥤ A)]
variable [HasColimitsOfShape Cᵒᵖ A]

/-- Two simplicial objects are homotopy equivalent if there are maps in both directions whose
composites are simplicially homotopic to the corresponding identity morphisms. -/
def SimplicialObjectHomotopyEquivalent (X Y : SimplicialObject C) : Prop :=
  ∃ (f : X ⟶ Y) (g : Y ⟶ X),
    Nonempty (SimplicialObject.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))

/-- The simplicial set `n ↦ \operatorname{Mor}_{\mathcal C}(U_n, U)` attached to a cosimplicial
object `U_•` and an object `U` of `C`. -/
private abbrev cosimplicialHomSSet (Ubullet : CosimplicialObject C) (U : C) :
    SSet.{v} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj
      ((CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))).obj
    (yoneda.obj U)

/-- Applying a functor to a cosimplicial object degreewise. -/
private abbrev whiskeredCosimplicialObject (u : C' ⥤ C) (Ubullet : CosimplicialObject C') :
    CosimplicialObject C :=
  ((CosimplicialObject.whiskering C' C).obj u).obj Ubullet

/-- Every simplicial set of maps from `U_•` to an object of `C` is homotopy equivalent to the
singleton simplicial set `Δ[0]`. This is the hypothesis appearing in Lemma `21.39.7`. -/
def CosimplicialObjectHasPointlikeHomSpaces (Ubullet : CosimplicialObject C) : Prop :=
  ∀ U : C,
    SimplicialObjectHomotopyEquivalent
      (cosimplicialHomSSet Ubullet U)
      (Δ[0] : SSet)

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for the projection from a category over a point. -/
abbrev categoryOverPointColimitToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  ((colim : (Cᵒᵖ ⥤ A) ⥤ A)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for the projection from a category over a point. -/
abbrev categoryOverPointDerivedColimit
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived :
        HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  Functor.totalLeftDerived
    (categoryOverPointColimitToDerived :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ A))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))

end Generic

section AddCommGrp

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable (u : C' ⥤ C)

local notation "AbPresheaf" => Cᵒᵖ ⥤ AddCommGrpCat
local notation "AbPresheaf'" => C'ᵒᵖ ⥤ AddCommGrpCat
local notation "QisAbPresheaf" => HomotopyCategory.quasiIso AbPresheaf (up ℤ)
local notation "QisAbPresheaf'" => HomotopyCategory.quasiIso AbPresheaf' (up ℤ)
local notation "AbelianColimitToDerived" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory AbPresheaf (up ℤ) ⥤ DerivedCategory AddCommGrpCat)
local notation "AbelianColimitToDerived'" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory AbPresheaf' (up ℤ) ⥤ DerivedCategory AddCommGrpCat)

/-- The exact inverse-image functor on derived categories induced by precomposition with
`u.op` on abelian presheaves. -/
private abbrev abelianPrecompositionDerivedInverseImage :
    DerivedCategory AbPresheaf ⥤ DerivedCategory AbPresheaf' :=
  ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ AddCommGrpCat).obj u.op).mapDerivedCategory

-- Proof sketch: choose `U'_•` from the hypothesis. Lemma `21.39.7` applied in `C'` identifies
-- `Lπ'_!` with evaluation on `U'_•`, and applied in `C` to the whiskered cosimplicial object
-- `u(U'_•)` identifies `Lπ_!` with evaluation on `u(U'_•)`. Since `g⁻¹` is precomposition with
-- `u`, these two evaluation functors agree, yielding the desired functor isomorphism.
/-- Lemma 21.39.8 (1): if there is a cosimplicial object `U'_•` of `\mathcal C'` to which Lemma
21.39.7 applies both in `\mathcal C'` and, after applying `u`, in `\mathcal C`, then the derived
lower shriek from `\mathcal C'` to a point composed with inverse image along `u` is functorially
isomorphic to the derived lower shriek from `\mathcal C` to a point on
`D(\mathcal C, \mathrm{Ab}) \to D(\mathrm{Ab})`. -/
theorem abelianPrecompositionDerivedInverseImage_comp_categoryOverPointDerivedLowerShriek_isomorphic
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]
    [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat]
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf]
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived' QisAbPresheaf']
    (hUbullet :
      ∃ Ubullet' : CosimplicialObject C',
        CosimplicialObjectHasPointlikeHomSpaces Ubullet' ∧
          CosimplicialObjectHasPointlikeHomSpaces
            (whiskeredCosimplicialObject u Ubullet')) :
    IsIsomorphic
      ((abelianPrecompositionDerivedInverseImage u) ⋙
        (categoryOverPointDerivedColimit :
          DerivedCategory AbPresheaf' ⥤ DerivedCategory AddCommGrpCat))
      (categoryOverPointDerivedColimit :
        DerivedCategory AbPresheaf ⥤ DerivedCategory AddCommGrpCat) := sorry

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable (B : Type w) [Ring B]
variable (u : C' ⥤ C)

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "BPresheaf'" => C'ᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "QisBPresheaf'" => HomotopyCategory.quasiIso BPresheaf' (up ℤ)
local notation "ModuleColimitToDerived" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
local notation "ModuleColimitToDerived'" =>
  (categoryOverPointColimitToDerived :
    HomotopyCategory BPresheaf' (up ℤ) ⥤ DerivedCategory (ModuleCat B))

/-- The exact inverse-image functor on derived categories induced by precomposition with
`u.op` on presheaves of `B`-modules. -/
private abbrev modulePrecompositionDerivedInverseImage :
    DerivedCategory BPresheaf ⥤ DerivedCategory BPresheaf' :=
  ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (ModuleCat B)).obj u.op).mapDerivedCategory

-- Proof sketch: choose `U'_•` from the hypothesis. Lemma `21.39.7` applied in `C'` identifies
-- `Lπ'_!` with evaluation on `U'_•`, and applied in `C` to the whiskered cosimplicial object
-- `u(U'_•)` identifies `Lπ_!` with evaluation on `u(U'_•)`. Since `g⁻¹` is precomposition with
-- `u`, the two evaluation functors coincide, giving the module-valued comparison isomorphism.
/-- Lemma 21.39.8 (2): under the same cosimplicial-object hypothesis, the derived lower shriek
from `\mathcal C'` to a point composed with inverse image along `u` is functorially isomorphic
to the derived lower shriek from `\mathcal C` to a point on
`D(\mathcal C, \underline{B}) \to D(B)`. -/
theorem modulePrecompositionDerivedInverseImage_comp_categoryOverPointDerivedLowerShriek_isomorphic
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [HasColimitsOfShape C'ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived' QisBPresheaf']
    (hUbullet :
      ∃ Ubullet' : CosimplicialObject C',
        CosimplicialObjectHasPointlikeHomSpaces Ubullet' ∧
          CosimplicialObjectHasPointlikeHomSpaces
            (whiskeredCosimplicialObject u Ubullet')) :
    IsIsomorphic
      ((modulePrecompositionDerivedInverseImage B u) ⋙
        (categoryOverPointDerivedColimit :
          DerivedCategory BPresheaf' ⥤ DerivedCategory (ModuleCat B)))
      (categoryOverPointDerivedColimit :
        DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) := sorry

end Module

end CategoryTheory
