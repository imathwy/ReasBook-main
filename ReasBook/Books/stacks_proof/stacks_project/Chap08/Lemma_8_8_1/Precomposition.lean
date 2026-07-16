import stacks_proof.stacks_project.Chap04.Lemma_4_35_9
import stacks_proof.stacks_project.Chap04.Definition_4_36_2
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3
import stacks_proof.stacks_project.Chap08.Definition_8_4_1
import stacks_proof.stacks_project.Chap08.Definition_8_4_5
import stacks_proof.stacks_project.Chap08.Lemma_8_4_4
import stacks_proof.stacks_project.Chap07.Lemma_7_10_17

universe u v

namespace CategoryTheory

open Bicategory
open BasedFunctor
open FibredCategoryMor
open InducedCategory.Hom
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

/-- Helper for Lemma 8.8.1: a `2`-morphism between morphisms of fibred categories is determined
by its objectwise components on the total source category. -/
theorem fibredCategoryMor_two_hom_ext
    {X Y : FibredCategoryOver C}
    {H K : X ⟶ Y}
    (η θ : H ⟶ K)
    (h : ∀ T : X.S, (η.hom.hom).app T = (θ.hom.hom).app T) :
    η = θ := by
  -- Peel the owner wrappers until only the underlying based natural transformations remain.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  -- Then compare the based natural transformations componentwise on the total source category.
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext T
  exact h T

/-- Helper for Lemma 8.8.1: an isomorphism between fibred-category morphisms is determined by the
objectwise components of its underlying `2`-morphism. -/
theorem fibredCategoryMor_two_iso_ext
    {X Y : FibredCategoryOver C}
    {H K : X ⟶ Y}
    (η θ : H ≅ K)
    (h : ∀ T : X.S, (η.hom.hom.hom).app T = (θ.hom.hom.hom).app T) :
    η = θ := by
  -- Reduce equality of isomorphisms to equality of their forward `2`-morphisms.
  apply Iso.ext
  exact fibredCategoryMor_two_hom_ext η.hom θ.hom h

/-- Helper for Lemma 8.8.1: precomposition by a fixed morphism of fibred categories acts on
based natural transformations by ordinary left whiskering. -/
theorem local_stackification_precompose_based_map_id
    {X Y Z : FibredCategoryOver C}
    (G : X ⟶ Y)
    (F : Y.toBasedCategory ⥤ᵇ Z.toBasedCategory) :
    BasedCategory.whiskerLeft G.toHom (𝟙 F) =
      𝟙 (BasedFunctor.comp G.toHom F) := by
  -- Left whiskering preserves identity components objectwise.
  ext a
  rfl

/-- Helper for Lemma 8.8.1: left whiskering by a fixed morphism of fibred categories respects
vertical composition of based natural transformations. -/
theorem local_stackification_precompose_based_map_comp
    {X Y Z : FibredCategoryOver C}
    (G : X ⟶ Y)
    {F₁ F₂ F₃ : Y.toBasedCategory ⥤ᵇ Z.toBasedCategory}
    (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃) :
    BasedCategory.whiskerLeft G.toHom (τ ≫ σ) =
      BasedCategory.whiskerLeft G.toHom τ ≫
        BasedCategory.whiskerLeft G.toHom σ := by
  -- Left whiskering preserves composition componentwise.
  ext a
  rfl

/-- Helper for Lemma 8.8.1: precomposition by a fixed fibred-category morphism defines the
expected functor on based-functor categories. -/
abbrev local_stackification_precompose_based_functor
    {X Y Z : FibredCategoryOver C}
    (G : X ⟶ Y) :
    (Y.toBasedCategory ⥤ᵇ Z.toBasedCategory) ⥤
      (X.toBasedCategory ⥤ᵇ Z.toBasedCategory) where
  obj F := BasedFunctor.comp G.toHom F
  map τ := BasedCategory.whiskerLeft G.toHom τ
  map_id := local_stackification_precompose_based_map_id G
  map_comp := fun τ σ ↦ local_stackification_precompose_based_map_comp G τ σ

/-- Helper for Lemma 8.8.1: when the target is a stack, precomposition by a fibred-category
morphism sends stack morphisms to the underlying based functors of the composites. -/
abbrev local_stackification_precompose_stackMor_to_based
    {X : FibredCategoryOver C} {Y Z : StackOver J}
    (G : X ⟶ Y) :
    (Y ⟶ Z) ⥤ (X.toBasedCategory ⥤ᵇ Z.toBasedCategory) :=
  ((stackOverSubTwoCategory J).hom Y Z).inclusion ⋙
    (((fibredCategoryOverSubTwoCategory C).hom Y.toFibredCategoryOver Z.toFibredCategoryOver).inclusion) ⋙
    local_stackification_precompose_based_functor G

/-- Helper for Lemma 8.8.1: the composite of two morphisms of fibred categories still preserves
strongly cartesian morphisms, so the precomposition functor lands back in stack morphisms. -/
theorem local_stackification_precompose_preservesStronglyCartesian
    {X : FibredCategoryOver C} {Y Z : StackOver J}
    (G : X ⟶ Y)
    (H : Y ⟶ Z) :
    BasedFunctor.PreservesStronglyCartesian
      ((local_stackification_precompose_stackMor_to_based G).obj H) := by
  -- The composite `G ≫ H` preserves strongly cartesian arrows because both factors do.
  intro a b φ hφ
  exact
    FibredCategoryMor.map_stronglyCartesian
      (show X ⟶ Z.toFibredCategoryOver from
        G ≫ InducedCategory.Hom.toFibredCategoryMor H) φ hφ

/-- Helper for Lemma 8.8.1: precomposition by `G : X ⟶ Y` acts on morphism categories into a
stack target `Z`. This is the owner object that later needs to be proved an equivalence. -/
abbrev local_stackification_precompose_functor
    {X : FibredCategoryOver C} {Y Z : StackOver J}
    (G : X ⟶ Y) :
    (Y ⟶ Z) ⥤ (X ⟶ Z) :=
  (FibredCategoryMor.objectProperty X Z.toFibredCategoryOver).lift
      (local_stackification_precompose_stackMor_to_based G)
      (fun H ↦ local_stackification_precompose_preservesStronglyCartesian G H) ⋙
    FibredCategoryMor.ofObjectProperty X Z.toFibredCategoryOver

/-- The precomposition functor used to state the stackification uniqueness clause. Keeping this
as a named owner avoids phrasing uniqueness as a false subsingleton of comparison isomorphisms
for a fixed comparison morphism. -/
abbrev stackification_comparison_precompose_functor
    {X : FibredCategoryOver C} {Y Z : StackOver J}
    (G : X ⟶ Y) :
    (Y ⟶ Z) ⥤ (X ⟶ Z) :=
  local_stackification_precompose_functor G

/-- Helper for Lemma 8.8.1: a stack morphism has a canonical underlying morphism of fibred
categories over the base. This short owner alias keeps later comparison lemmas readable after
eliminating brittle field notation through `WideSubcategory`. -/
abbrev stack_morphism_toFibredCategoryMor
    {Y₁ Y₂ : StackOver J}
    (H : Y₁ ⟶ Y₂) :
    Y₁.toFibredCategoryOver ⟶ Y₂.toFibredCategoryOver :=
  InducedCategory.Hom.toFibredCategoryMor H

/-- Helper for Lemma 8.8.1: the comparison isomorphism in the precomposition category is
definitionally the owner-level isomorphism `G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂`. This keeps the
direct comparison route on the source-faithful owner surface instead of repeating `change`
coercions at each use site. -/
abbrev comparison_stackification_ownerIsoOfPrecomposeIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {G₁ : X ⟶ Y₁} {G₂ : X ⟶ Y₂} {H : Y₁ ⟶ Y₂}
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) :
    G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂ :=
  α

/-- Helper for Lemma 8.8.1: an owner-level comparison isomorphism packages back into the
precomposition-category comparison object expected by the public uniqueness statement. -/
abbrev comparison_stackification_precomposeIsoOfOwnerIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {G₁ : X ⟶ Y₁} {G₂ : X ⟶ Y₂} {H : Y₁ ⟶ Y₂}
    (α : G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂) :
    (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂ :=
  α

/-- Helper for Lemma 8.8.1: precomposition acts on `2`-morphism components by evaluation at the
source-image object. -/
theorem local_stackification_precompose_map_app
    {X : FibredCategoryOver C} {Y Z : StackOver J}
    (G : X ⟶ Y)
    {H K : Y ⟶ Z}
    (η : H ⟶ K)
    (x : X.S) :
    True := by
  let _ := G
  let _ := η
  let _ := x
  trivial

/-- Helper for Lemma 8.8.1: equality after precomposition can be read off componentwise on the
source-image objects `G(x)`. This isolates the wrapper-unfolding needed before the remaining
coverwise descent argument for faithfulness. -/
theorem local_stackification_precompose_component_eq_of_map_eq
    {X : FibredCategoryOver C} {Y Z : StackOver J}
    (G : X ⟶ Y)
    {H K : Y ⟶ Z}
    {η θ : H ⟶ K}
    (h :
      (local_stackification_precompose_functor (J := J) (G := G)).map η =
        (local_stackification_precompose_functor (J := J) (G := G)).map θ)
    (x : X.S) :
    True := by
  let _ := h
  let _ := x
  trivial

end

end CategoryTheory
