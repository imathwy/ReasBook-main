import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]

/-- Two simplicial objects are homotopy equivalent if there are maps in both directions whose
composites are simplicially homotopic to the corresponding identity morphisms. -/
def SimplicialHomotopyEquivalent (X Y : SimplicialObject C) : Prop :=
  ∃ (f : X ⟶ Y) (g : Y ⟶ X),
    Nonempty (SimplicialObject.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))

/-- The simplicial object of `Cᵒᵖ` corresponding to a cosimplicial object of `C`. -/
private abbrev oppositeSimplicialObject (Ubullet : CosimplicialObject C) :
    SimplicialObject Cᵒᵖ :=
  (CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet)

/-- The simplicial set `n ↦ \operatorname{Mor}_{\mathcal C}(U_n, U)` attached to a cosimplicial
object `U_•` and an object `U` of `C`. -/
private abbrev cosimplicialHomSSet (Ubullet : CosimplicialObject C) (U : C) :
    SSet.{v} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj
      (oppositeSimplicialObject Ubullet)).obj
    (yoneda.obj U)

end Generic

section AddCommGrp

variable {C : Type u} [Category.{v} C]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]

/-- The lower shriek functor for the projection from a category over a point on abelian
presheaves is the colimit functor. -/
private abbrev abelianCategoryOverPointLowerShriek :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat :=
  colim

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek on
abelian presheaves over a point. -/
private abbrev abelianCategoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat :=
  abelianCategoryOverPointLowerShriek.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory AddCommGrpCat (ComplexShape.up ℤ) ⥤ DerivedCategory AddCommGrpCat)

/-- The derived lower shriek functor `L\pi_!` for abelian presheaves on a category over a point.
-/
private abbrev abelianCategoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      (abelianCategoryOverPointLowerShriekToDerived :
        HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
          DerivedCategory AddCommGrpCat)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat :=
  Functor.totalLeftDerived
    (abelianCategoryOverPointLowerShriekToDerived :
      HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
        DerivedCategory AddCommGrpCat)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ))

/-- Evaluating an abelian presheaf on the simplicial object attached to `U_•` produces a
simplicial abelian group. -/
private abbrev abelianPresheafEvaluationSimplicialObject (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ SimplicialObject AddCommGrpCat :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ AddCommGrpCat).obj
    (oppositeSimplicialObject Ubullet)

/-- The chain complex associated to the simplicial abelian group `\mathcal F(U_•)`. -/
private abbrev abelianPresheafEvaluationChainComplex (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ ChainComplex AddCommGrpCat ℕ :=
  abelianPresheafEvaluationSimplicialObject Ubullet ⋙ alternatingFaceMapComplex AddCommGrpCat

/-- The derived-category realization of the simplicial abelian group `\mathcal F(U_•)`. -/
noncomputable abbrev abelianCosimplicialEvaluationToDerived (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat :=
  abelianPresheafEvaluationChainComplex Ubullet ⋙
    (ComplexShape.embeddingDownNat.extendFunctor AddCommGrpCat) ⋙
    DerivedCategory.Q

variable [Functor.HasLeftDerivedFunctor
  (abelianCategoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (ComplexShape.up ℤ))]

-- Proof sketch: resolve each abelian presheaf by sums of representables, evaluate the resolution
-- on `U_•`, and use the assumption that every simplicial set `Mor_C(U_•, U)` is homotopy
-- equivalent to `Δ[0]` to identify the resulting simplicial abelian groups with the corresponding
-- representable resolutions of the colimit. This yields a functorial isomorphism in the derived
-- category.
/-- Lemma 21.39.7 (1): in the category-over-a-point situation of Example 21.39.1, if every
simplicial set `\operatorname{Mor}_{\mathcal C}(U_\bullet, U)` is homotopy equivalent to the
singleton simplicial set `\Delta[0]`, then the derived lower shriek of a degree-zero abelian
presheaf is functorially isomorphic to the derived object represented by the simplicial abelian
group `\mathcal F(U_\bullet)`. -/
theorem categoryOverPointDerivedLowerShriek_singleFunctor_isIsomorphic_abelianCosimplicialEvaluation
    (Ubullet : CosimplicialObject C)
    (hUbullet : ∀ U : C,
      SimplicialHomotopyEquivalent
        (cosimplicialHomSSet Ubullet U)
        (Δ[0] : SSet)) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat) (0 : ℤ)) ⋙
          abelianCategoryOverPointDerivedLowerShriek :
            (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat))
      (abelianCosimplicialEvaluationToDerived Ubullet) := sorry

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable (B : Type w) [Ring B]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]

/-- The lower shriek functor for the projection from a category over a point on presheaves of
`B`-modules is the colimit functor. -/
private abbrev moduleCategoryOverPointLowerShriek :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ ModuleCat B :=
  colim

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek on
presheaves of `B`-modules over a point. -/
private abbrev moduleCategoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat B) :=
  (moduleCategoryOverPointLowerShriek B).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat B) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat B))

/-- The derived lower shriek functor `L\pi_!` for presheaves of `B`-modules on a category over a
point. -/
private abbrev moduleCategoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      (moduleCategoryOverPointLowerShriekToDerived B :
        HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat B))
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived
    (moduleCategoryOverPointLowerShriekToDerived B :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat B))
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ ModuleCat B))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ))

/-- Evaluating a presheaf of `B`-modules on the simplicial object attached to `U_•` produces a
simplicial object of `B`-modules. -/
private abbrev modulePresheafEvaluationSimplicialObject (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ SimplicialObject (ModuleCat B) :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (ModuleCat B)).obj
    (oppositeSimplicialObject Ubullet)

/-- The chain complex associated to the simplicial `B`-module object `\mathcal F(U_•)`. -/
private abbrev modulePresheafEvaluationChainComplex (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ ChainComplex (ModuleCat B) ℕ :=
  modulePresheafEvaluationSimplicialObject B Ubullet ⋙
    alternatingFaceMapComplex (ModuleCat B)

/-- The derived-category realization of the simplicial `B`-module object `\mathcal F(U_•)`. -/
noncomputable abbrev moduleCosimplicialEvaluationToDerived (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B) :=
  modulePresheafEvaluationChainComplex B Ubullet ⋙
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat B)) ⋙
    DerivedCategory.Q

variable [Functor.HasLeftDerivedFunctor
  (moduleCategoryOverPointLowerShriekToDerived B :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat B))
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (ComplexShape.up ℤ))]

-- Proof sketch: apply the abelian-sheaf argument objectwise to the underlying additive presheaf of
-- a `B`-module presheaf, use the compatibility of `L\pi_!` for modules with the abelian version,
-- and transport the resulting functorial comparison back to `D(B)`.
/-- Lemma 21.39.7 (2): under the same hypothesis on `U_\bullet`, the derived lower shriek of a
degree-zero presheaf of `B`-modules is functorially isomorphic to the derived object represented
by the simplicial `B`-module object `\mathcal F(U_\bullet)`. -/
theorem categoryOverPointDerivedLowerShriek_singleFunctor_isIsomorphic_moduleCosimplicialEvaluation
    (Ubullet : CosimplicialObject C)
    (hUbullet : ∀ U : C,
      SimplicialHomotopyEquivalent
        (cosimplicialHomSSet Ubullet U)
        (Δ[0] : SSet)) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ ModuleCat B) (0 : ℤ)) ⋙
          moduleCategoryOverPointDerivedLowerShriek B :
            (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B)))
      (moduleCosimplicialEvaluationToDerived B Ubullet) := sorry

end Module

end CategoryTheory
