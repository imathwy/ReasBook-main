import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found `Scheme.fromSpecStalk` as the canonical stalk scheme
-- morphism. Current project precedent uses `Scheme.Hom.FinitePresentation` for finite
-- presentation over a base and `ObjectProperty.FullSubcategory` for restricted over-categories.

/-- The object property on `Over S` selecting morphisms of finite presentation whose restriction
to the open `U` is an isomorphism. -/
abbrev puncturedLocalFinitePresentationIsoOverOpenProperty
    {S : Scheme.{u}} (U : S.Opens) : ObjectProperty (Over S) :=
  fun X ↦ Scheme.Hom.FinitePresentation X.hom ∧ IsIso (X.hom ∣_ U)

/-- The full subcategory of `S`-schemes of finite presentation which are isomorphisms over
the open `U`. -/
abbrev PuncturedLocalFinitePresentationIsoOverOpen
    {S : Scheme.{u}} (U : S.Opens) : Type (u + 1) :=
  (puncturedLocalFinitePresentationIsoOverOpenProperty U).FullSubcategory

/-- The inclusion of the restricted category into the over-category. -/
abbrev puncturedLocalFinitePresentationIsoOverOpenInclusion
    {S : Scheme.{u}} (U : S.Opens) :
    PuncturedLocalFinitePresentationIsoOverOpen U ⥤ Over S :=
  (puncturedLocalFinitePresentationIsoOverOpenProperty U).ι

/-- Pulling back along the stalk morphism sends the finite-presentation/isomorphism-over-`U`
subcategory to the analogous subcategory over the punctured local scheme. -/
theorem puncturedLocalBaseChange_mem
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : PuncturedLocalFinitePresentationIsoOverOpen U) :
    puncturedLocalFinitePresentationIsoOverOpenProperty V
      ((Over.pullback (S.fromSpecStalk s)).obj X.obj) := sorry

/-- Lemma 32.21.1: let `S` be a scheme and let `s ∈ S` be a closed point such that the open
complement `U = S \ {s}` is quasi-compact over `S`. With
`V = Spec(𝒪_{S,s}) \ {s}`, the base-change functor from finitely presented `S`-schemes which are
isomorphisms over `U` to finitely presented `Spec(𝒪_{S,s})`-schemes which are isomorphisms over
`V` is an equivalence of categories. -/
@[stacks 0B3X]
theorem puncturedLocalBaseChange_finitePresentationIsoOverOpen_isEquivalence
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ) :
    Functor.IsEquivalence
      (ObjectProperty.lift
        (puncturedLocalFinitePresentationIsoOverOpenProperty V)
        ((puncturedLocalFinitePresentationIsoOverOpenInclusion U) ⋙
          Over.pullback (S.fromSpecStalk s))
        (fun X ↦ puncturedLocalBaseChange_mem S s hs U hU hUqc V hV X)) := sorry

end AlgebraicGeometry
