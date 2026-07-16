import Mathlib
import StacksProject_2024.stacks_project.Chap08.Lemma_8_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open BasedFunctor

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver C} {S' X : StackOver J}

/- Domain-style sampling for Lemma 8.8.3:
- primary domain: the universal property of stackification in the `2`-category of fibred
  categories over a site, specialized to morphisms into a stack target.
- inspected owner-level declarations:
  `FibredCategoryMor`,
  `FibredCategoryMor.IsStackification`,
  `StackOver.InducedCategory.Hom.toFibredCategoryMor`,
  `SubTwoCategory.Hom.toHom`,
  `FibredCategoryMor.ofBasedFunctor`,
  `FibredCategoryMor.objectProperty`,
  `FibredCategoryMor.ofObjectProperty`,
  `Functor.IsEquivalence`.
- best owner abstraction: the induced precomposition functor
  `stackification_precompose_functor X G : (S' ⟶ X) ⥤ (S ⟶ X)`, together with the owner predicate
  `Functor.IsEquivalence`.
- primitive data: a stackification morphism `G : S ⟶ S'` and a target stack `X`.
- derived API: the induced functor on morphism categories and the canonical equivalence object
  `(stackification_precompose_functor X G).asEquivalence`.

Source/core/bridge triage:
- `source-facing`: the precomposition equivalence expressing the universal property of a
  stackification.
- `core/canonical`: `FibredCategoryMor.IsStackification`,
  `SubTwoCategory.Hom.toHom`, `FibredCategoryMor.ofBasedFunctor`,
  `Functor.IsEquivalence`.
- `bridge/view`: the temporary passage through based functors preserving strongly cartesian
  morphisms. -/

private abbrev forgetToFibredCategoryMor (S' X : StackOver J) :
    (S' ⟶ X) ⥤ FibredCategoryMor S'.toFibredCategoryOver X.toFibredCategoryOver :=
  ((stackOverSubTwoCategory J).hom S' X).inclusion

-- Proof sketch: left whiskering by the based functor underlying `G` leaves identity vertical
-- natural transformations unchanged.
private theorem stackification_precompose_based_map_id
    (G : FibredCategoryMor S S') :
    ∀ F : S'.toBasedCategory ⥤ᵇ X.toBasedCategory,
      BasedCategory.whiskerLeft G.toHom (𝟙 F) =
        𝟙 (BasedFunctor.comp G.toHom F) := sorry

-- Proof sketch: left whiskering by a fixed based functor commutes with vertical composition of
-- based natural transformations.
private theorem stackification_precompose_based_map_comp
    (G : FibredCategoryMor S S') :
    ∀ {F₁ F₂ F₃ : S'.toBasedCategory ⥤ᵇ X.toBasedCategory}
      (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃),
      BasedCategory.whiskerLeft G.toHom (τ ≫ σ) =
        BasedCategory.whiskerLeft G.toHom τ ≫
          BasedCategory.whiskerLeft G.toHom σ := sorry

private abbrev stackification_precompose_based_functor
    (G : FibredCategoryMor S S') :
    (S'.toBasedCategory ⥤ᵇ X.toBasedCategory) ⥤
      (S.toBasedCategory ⥤ᵇ X.toBasedCategory) where
  obj F := BasedFunctor.comp G.toHom F
  map τ := BasedCategory.whiskerLeft G.toHom τ
  map_id := stackification_precompose_based_map_id G
  map_comp := fun τ σ ↦ stackification_precompose_based_map_comp G τ σ

private abbrev stackification_precompose_stackMor_to_based
    (X : StackOver J)
    (G : FibredCategoryMor S S') :
    (S' ⟶ X) ⥤ (S.toBasedCategory ⥤ᵇ X.toBasedCategory) :=
  forgetToFibredCategoryMor S' X ⋙
    (((fibredCategoryOverSubTwoCategory C).hom S'.toFibredCategoryOver X.toFibredCategoryOver).inclusion) ⋙
    stackification_precompose_based_functor G

-- Proof sketch: both `G` and `H` preserve strongly cartesian morphisms, so their composite over
-- `C` does as well. This is exactly the owner object property
-- `FibredCategoryMor.objectProperty S X`.
private theorem stackification_precompose_preservesStronglyCartesian
    (G : FibredCategoryMor S S')
    (H : S' ⟶ X) :
    BasedFunctor.PreservesStronglyCartesian
      ((stackification_precompose_stackMor_to_based X G).obj H) := sorry

/-- Precomposition with `G : S ⟶ S'` sends a stack morphism `S' ⟶ X` to the induced owner
morphism `S ⟶ X`. -/
abbrev stackification_precompose_functor
    (X : StackOver J)
    (G : S ⟶ S') :
    (S' ⟶ X) ⥤ (S ⟶ X) :=
  (FibredCategoryMor.objectProperty S X).lift
      (stackification_precompose_stackMor_to_based X G)
      (fun H ↦ stackification_precompose_preservesStronglyCartesian G H) ⋙
    FibredCategoryMor.ofObjectProperty S X

/-- Lemma 8.8.3: if `G : S ⟶ S'` is a stackification morphism, then precomposition with `G`
induces an equivalence on morphism categories into any stack `X`. The canonical owner statement is
that `stackification_precompose_functor X G` is an equivalence of categories. -/
instance stackification_precompose_functor_isEquivalence
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G) :
    Functor.IsEquivalence
      (stackification_precompose_functor X G :
        (S' ⟶ X) ⥤ (S ⟶ X)) := sorry

end

end CategoryTheory
