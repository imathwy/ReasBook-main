import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the scheme-side finite-presentation owner
-- `LocallyOfFinitePresentation`; local Section 29.21 provides the source-facing strengthening
-- `Scheme.Hom.FinitePresentation`. Local precedent represents restricted categories by
-- `ObjectProperty.FullSubcategory` and categorical equivalences by `Functor.IsEquivalence`.

/-- The full subcategory of schemes over `S` whose structure morphism is of finite presentation. -/
abbrev finitePresentationOverProperty (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ Scheme.Hom.FinitePresentation X.hom

/-- A bottom span `U <- V -> T` of schemes, used to encode the gluing diagram in Lemma 32.20.1. -/
abbrev schemeSpan (V U T : Scheme.{u}) (toU : V ⟶ U) (toT : V ⟶ T) :
    WalkingSpan ⥤ Scheme.{u} :=
  span toU toT

/-- A diagram over a bottom span `U <- V -> T` has finite-presentation vertical maps and
cartesian left and right squares. -/
class FinitePresentationCartesianSpanDiagram
    {V U T : Scheme.{u}} (toU : V ⟶ U) (toT : V ⟶ T)
    (leftLeg : WalkingSpan.zero ⟶ WalkingSpan.left)
    (rightLeg : WalkingSpan.zero ⟶ WalkingSpan.right)
    (D : Over (schemeSpan V U T toU toT)) : Prop where
  /-- The vertical arrow over `U` is of finite presentation. -/
  finitePresentation_left :
    Scheme.Hom.FinitePresentation (D.hom.app WalkingSpan.left)
  /-- The vertical arrow over `V` is of finite presentation. -/
  finitePresentation_zero :
    Scheme.Hom.FinitePresentation (D.hom.app WalkingSpan.zero)
  /-- The vertical arrow over `T` is of finite presentation. -/
  finitePresentation_right :
    Scheme.Hom.FinitePresentation (D.hom.app WalkingSpan.right)
  /-- The square over `V -> U` is cartesian. -/
  isPullback_left :
    IsPullback (D.left.map leftLeg)
      (D.hom.app WalkingSpan.zero) (D.hom.app WalkingSpan.left) toU
  /-- The square over `V -> T` is cartesian. -/
  isPullback_right :
    IsPullback (D.left.map rightLeg)
      (D.hom.app WalkingSpan.zero) (D.hom.app WalkingSpan.right) toT

/-- The full subcategory of diagrams over a bottom span `U <- V -> T` whose vertical morphisms
are of finite presentation and whose two squares are cartesian. -/
abbrev finitePresentationCartesianSpanDiagramProperty
    {V U T : Scheme.{u}} (toU : V ⟶ U) (toT : V ⟶ T)
    (leftLeg : WalkingSpan.zero ⟶ WalkingSpan.left)
    (rightLeg : WalkingSpan.zero ⟶ WalkingSpan.right) :
    ObjectProperty (Over (schemeSpan V U T toU toT)) :=
  fun D ↦ FinitePresentationCartesianSpanDiagram toU toT leftLeg rightLeg D

/-- A functor from finite-presentation `S`-schemes to finite-presentation cartesian span diagrams
has the source-indicated object action when its three vertical arrows are, up to isomorphism over
their bases, the restrictions to `U`, to the punctured local scheme `V`, and to `Spec(O_{S,s})`. -/
class IsPuncturedLocalSpanRestrictionFunctor
    (S : Scheme.{u}) (s : S) (U : S.Opens)
    (T : Scheme.{u}) (eT : T ≅ Spec (CommRingCat.of (S.presheaf.stalk s))) (V : T.Opens)
    (toU : V.toScheme ⟶ U.toScheme)
    (leftLeg : WalkingSpan.zero ⟶ WalkingSpan.left)
    (rightLeg : WalkingSpan.zero ⟶ WalkingSpan.right)
    (F : (finitePresentationOverProperty S).FullSubcategory ⥤
      (finitePresentationCartesianSpanDiagramProperty toU V.ι leftLeg rightLeg).FullSubcategory) :
    Prop where
  /-- The left vertical arrow is the restriction over `U`. -/
  leftIso : ∀ X : (finitePresentationOverProperty S).FullSubcategory,
    Nonempty (Over.mk
      (((finitePresentationCartesianSpanDiagramProperty toU V.ι leftLeg rightLeg).ι.obj
        (F.obj X)).hom.app WalkingSpan.left) ≅ (Over.pullback U.ι).obj X.obj)
  /-- The middle vertical arrow is the restriction over the punctured local scheme `V`. -/
  zeroIso : ∀ X : (finitePresentationOverProperty S).FullSubcategory,
    Nonempty (Over.mk
      (((finitePresentationCartesianSpanDiagramProperty toU V.ι leftLeg rightLeg).ι.obj
        (F.obj X)).hom.app WalkingSpan.zero) ≅
      (Over.pullback (V.ι ≫ eT.hom ≫ S.fromSpecStalk s)).obj X.obj)
  /-- The right vertical arrow is the restriction over `Spec(O_{S,s})`. -/
  rightIso : ∀ X : (finitePresentationOverProperty S).FullSubcategory,
    Nonempty (Over.mk
      (((finitePresentationCartesianSpanDiagramProperty toU V.ι leftLeg rightLeg).ι.obj
        (F.obj X)).hom.app WalkingSpan.right) ≅
      (Over.pullback (eT.hom ≫ S.fromSpecStalk s)).obj X.obj)

/-- Lemma 32.20.1: let `S` be a scheme and let `s` be a closed point such that the open complement
`U = S \ {s}` is quasi-compact over `S`. With `T = Spec(O_{S,s})` and
`V = T \ {s}`, finitely presented schemes over `S` form a category equivalent to the category of
finite-presentation cartesian diagrams over the span `U <- V -> T`.

The hypotheses `hU` and `hV` identify the two displayed open subschemes with the punctured
complements from the source statement. -/
@[stacks 0BPA]
theorem finitePresentationOver_equivalence_puncturedLocalSpan
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens)
    (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (T : Scheme.{u}) (eT : T ≅ Spec (CommRingCat.of (S.presheaf.stalk s)))
    (V : T.Opens)
    (hV : (V : Set T) =
      ({(eT.inv.base) (IsLocalRing.closedPoint (S.presheaf.stalk s))} : Set T)ᶜ)
    (toU : V.toScheme ⟶ U.toScheme)
    (htoU : toU ≫ U.ι = V.ι ≫ eT.hom ≫ S.fromSpecStalk s)
    (leftLeg : WalkingSpan.zero ⟶ WalkingSpan.left)
    (rightLeg : WalkingSpan.zero ⟶ WalkingSpan.right) :
    ∃ F : (finitePresentationOverProperty S).FullSubcategory ⥤
        (finitePresentationCartesianSpanDiagramProperty toU V.ι leftLeg rightLeg).FullSubcategory,
      IsPuncturedLocalSpanRestrictionFunctor S s U T eT V toU leftLeg rightLeg F ∧
        Functor.IsEquivalence F := sorry

end AlgebraicGeometry
