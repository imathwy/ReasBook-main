import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Pullback.gluing` for scheme gluing
-- infrastructure and `CategoricalPullback` for categories of pairs with an isomorphism after
-- restriction. Local Chapter 32 precedent in `Lemma_32_10_5` models categories of schemes over a
-- base by `ObjectProperty.FullSubcategory` and colimits of such categories in `Cat`.

/-- The object property on `Over T` selecting morphisms of finite presentation. -/
abbrev finitePresentationOverProperty (T : Scheme.{u}) : ObjectProperty (Over T) :=
  fun X ↦ Scheme.Hom.FinitePresentation X.hom

/-- The full subcategory of schemes of finite presentation over a base scheme `T`. -/
abbrev FinitePresentationOver (T : Scheme.{u}) : Type (u + 1) :=
  (finitePresentationOverProperty T).FullSubcategory

namespace FinitePresentationOver

/-- The inclusion of schemes of finite presentation over `T` into all schemes over `T`. -/
abbrev inclusion (T : Scheme.{u}) : FinitePresentationOver T ⥤ Over T :=
  (finitePresentationOverProperty T).ι

/-- Base change preserves the finite-presentation-over property. -/
theorem baseChange_mem {T T' : Scheme.{u}} (f : T' ⟶ T)
    (X : FinitePresentationOver T) :
    finitePresentationOverProperty T' ((Over.pullback f).obj X.obj) := sorry

/-- The base-change functor on finite-presentation over-categories. -/
abbrev baseChange {T T' : Scheme.{u}} (f : T' ⟶ T) :
    FinitePresentationOver T ⥤ FinitePresentationOver T' :=
  ObjectProperty.lift (finitePresentationOverProperty T')
    ((inclusion T) ⋙ Over.pullback f) (fun X ↦ baseChange_mem f X)

end FinitePresentationOver

/-- The opposite ordered index of open neighborhoods `W` of `s` containing a fixed open `U`. -/
abbrev OpenNeighborhoodIndex (S : Scheme.{u}) (U : S.Opens) (s : S) : Type u :=
  ({ W : S.Opens // U ≤ W ∧ s ∈ (W : Set S) })ᵒᵖ

namespace OpenNeighborhoodIndex

/-- The underlying open subset of an open-neighborhood index object. -/
abbrev toOpen {S : Scheme.{u}} {U : S.Opens} {s : S}
    (W : OpenNeighborhoodIndex S U s) : S.Opens :=
  W.unop.1

end OpenNeighborhoodIndex

/-- The open `Spec(𝒪_{S,s}) ×_S U`, i.e. the intersection of the canonical stalk scheme with
`U`. -/
abbrev stalkOpenIntersection (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (Spec (S.presheaf.stalk s)).Opens :=
  (S.fromSpecStalk s) ⁻¹ᵁ U

/-- The category of finite-presentation gluing data over `U`, over the stalk scheme
`Spec(𝒪_{S,s})`, and over their intersection. It is modeled as the categorical pullback of the
restriction functors to the open `Spec(𝒪_{S,s}) ×_S U`, so the two cartesian squares in the source
are encoded by base change. -/
abbrev finitePresentationStalkGluingCategory
    (S : Scheme.{u}) (U : S.Opens) (s : S) : Type (u + 1) :=
  CategoricalPullback
    (FinitePresentationOver.baseChange ((S.fromSpecStalk s) ∣_ U))
    (FinitePresentationOver.baseChange ((stalkOpenIntersection S U s).ι))

/-- Lemma 32.20.3: for a retrocompact open `U ⊆ S` and a point `s` outside `U`, any strict
`Cat`-diagram `D` modeling the categories of finite-presentation schemes over open neighborhoods
`U'` with `s ∈ U'` and `U ⊆ U'` has categorical colimit equivalent to the category of
finite-presentation gluing data over `U`, over `Spec(𝒪_{S,s})`, and over their intersection
`V = Spec(𝒪_{S,s}) ×_S U`. -/
@[stacks 0BQ5]
theorem finitePresentation_openNeighborhood_colimit_equivalence_stalkGluing
    (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S))
    (D : OpenNeighborhoodIndex S U s ⥤ Cat)
    (hD_obj : ∀ W, D.obj W = Cat.of (FinitePresentationOver W.toOpen.toScheme))
    (hD_map : ∀ {W W'} (h : W ⟶ W'),
      D.map h =
        eqToHom (hD_obj W) ≫
          (FinitePresentationOver.baseChange (S.homOfLE
            (leOfHom h.unop : W'.toOpen ≤ W.toOpen)) : _ ⥤ _).toCatHom ≫
        eqToHom (Eq.symm (hD_obj W')))
    [HasColimit D] :
    Nonempty
      (((colimit D : Cat) : Type (u + 1)) ≌
        finitePresentationStalkGluingCategory S U s) := sorry

end AlgebraicGeometry
