import Mathlib
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Lemma_8_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredInGroupoidsOver C}
variable {S' X : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.9.2:
- primary domain: the universal property of stackification, specialized from stacks to stacks in
  groupoids;
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `isStackification_exists_lift_to_stack`,
  `FibredInGroupoidsMor.ofAmbientHom`,
  `StackInGroupoidsOver.Hom.toFibredInGroupoidsMor`,
  `FibredInGroupoidsMor.toStackFibredCategoryMor`,
  `FibredInGroupoidsMor.ofFibredCategoryMorIso`.
- best owner abstraction: the ambient stackification owner is still
  `FibredCategoryMor.IsStackification`, and the present lemma should be only the groupoid-valued
  bridge that reuses `isStackification_exists_lift_to_stack` and returns the lifted morphism in
  the owner hom type `S' ⟶ X`;
- primitive data: a stackification morphism `G : S ⟶ S'`, the ambient stackification predicate on
  `G.toStackFibredCategoryMor`, and a target morphism `F : FibredInGroupoidsMor S X`;
- derived API: the lifted owner morphism `H : S' ⟶ X` and the resulting `2`-isomorphism at the
  underlying `FibredInGroupoidsMor` layer.

Source/core/bridge triage:
- `source-facing`: the groupoid-valued factorization statement of Lemma 8.9.2;
- `core/canonical`: `isStackification_exists_lift_to_stack`;
- `bridge/view`: the coercions from stacks in groupoids to stacks, together with the owner bridge
  `FibredInGroupoidsMor.toStackFibredCategoryMor` to the ambient stack theorem,
  `FibredInGroupoidsMor.ofAmbientHom` that packages the ambient lifted morphism as an owner hom,
  and
  `FibredInGroupoidsMor.ofFibredCategoryMorIso` that lifts ambient `2`-isomorphisms back to the
  groupoid-valued homs. -/

-- Proof sketch: apply Lemma `8.8.2` to the underlying stackification
-- `G.toStackFibredCategoryMor` and target morphism `F.toStackFibredCategoryMor`.
-- The resulting ambient lift is then promoted by `FibredInGroupoidsMor.ofAmbientHom` to the
-- owner morphism `S' ⟶ X`, and the ambient
-- `2`-isomorphism is lifted back with `FibredInGroupoidsMor.ofFibredCategoryMorIso`.
/-- Lemma 8.9.2: if `G : S ⟶ S'` exhibits the stack in groupoids `S'` as a stackification of the
category fibred in groupoids `S`, then every morphism `F : S ⟶ X` to a stack in groupoids `X`
factors through `S'` up to a `2`-isomorphism. -/
theorem isStackification_exists_lift_to_stackInGroupoids
    (G : FibredInGroupoidsMor S S')
    (hG : FibredCategoryMor.IsStackification G.toStackFibredCategoryMor)
    (F : FibredInGroupoidsMor S X) :
    ∃ H : S' ⟶ X,
      Nonempty (G ≫ H ≅ F) := by
  obtain ⟨H, hH⟩ :=
    isStackification_exists_lift_to_stack
      G.toStackFibredCategoryMor hG F.toStackFibredCategoryMor
  let H' : S' ⟶ X :=
    ⟨⟨FibredInGroupoidsMor.ofAmbientHom H.toHom, trivial⟩⟩
  refine ⟨H', ?_⟩
  rcases hH with ⟨e⟩
  exact ⟨FibredInGroupoidsMor.ofFibredCategoryMorIso (by simpa [H'] using e)⟩

end

end CategoryTheory
