import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [CommRing B]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)

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
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  ((colim : BPresheaf ⥤ ModuleCat B)).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for presheaves of `B`-modules on a category over a
point. -/
abbrev categoryOverPointDerivedColimit
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived :
        HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
      QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived
    (categoryOverPointColimitToDerived :
      HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
    (DerivedCategory.Qh :
      HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory BPresheaf)
    QisBPresheaf

-- Proof sketch: choose a cosimplicial object `U_•` with pointlike hom-spaces. Apply Lemma
-- `21.39.8` to the diagonal functor `\mathcal C → \mathcal C × \mathcal C` and use the product
-- description of the simplicial mapping sets together with Simplicial, Lemma `14.26.10` to see
-- that the hypothesis needed there is satisfied. Then identify the tensor product on
-- `D(\underline B)` with the inverse image along the diagonal of the tensor of the two projection
-- inverse images by Lemma `21.18.4`, and finish with Lemma `21.39.9`.
/-- Lemma 21.39.10: if there exists a cosimplicial object `U_\bullet` of `\mathcal C` to which
Lemma `21.39.7` applies, then the derived lower shriek for the category-over-a-point situation
commutes with the derived tensor product on `D(\underline B)`. In Lean this is expressed as an
objectwise isomorphism
`L\pi_!(K₁ \otimes_{\underline B}^{\mathbf L} K₂) \cong
  L\pi_!(K₁) \otimes_B^{\mathbf L} L\pi_!(K₂)`. -/
theorem categoryOverPointDerivedLowerShriek_tensor_isomorphic
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived :
        HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))
      QisBPresheaf]
    [MonoidalCategory (DerivedCategory BPresheaf)]
    [MonoidalCategory (DerivedCategory (ModuleCat B))]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObjectHasPointlikeHomSpaces Ubullet)
    (K₁ K₂ : DerivedCategory BPresheaf) :
    IsIsomorphic
      ((categoryOverPointDerivedColimit).obj (K₁ ⊗ K₂))
      (((categoryOverPointDerivedColimit).obj K₁) ⊗
        ((categoryOverPointDerivedColimit).obj K₂)) := sorry

end

end CategoryTheory
