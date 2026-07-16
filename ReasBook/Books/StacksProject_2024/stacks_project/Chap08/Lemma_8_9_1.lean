import Mathlib
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_5
import StacksProject_2024.stacks_project.Chap08.Lemma_8_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : FibredInGroupoidsOver C}
variable {Y : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.9.1:
- primary domain: stackification of categories fibred in groupoids, specialized from the Chapter 8
  stackification theory for fibred categories;
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `exists_stackification`,
  `stackification_unique_up_to_unique_twoIso`,
  `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`;
- best owner abstraction: the stackification predicate should stay on the ambient owner
  `FibredCategoryMor.IsStackification` after passing from a morphism of fibred-in-groupoids to the
  canonical bridge `toStackFibredCategoryMor`; comparison morphisms between stackifications should
  reuse the owner hom type `Y₁ ⟶ Y₂`;
- primitive data: a target `Y : StackInGroupoidsOver J`, a morphism `G : FibredInGroupoidsMor X Y`,
  and the ambient stackification predicate on `G.toStackFibredCategoryMor`;
- derived API: the comparison equivalence-over-base predicate on owner homs in
  `StackInGroupoidsOver J` and the
  uniqueness statement for compatible `2`-isomorphisms.

Source/core/bridge triage:
- `source-facing`: the existence and uniqueness statements for stackifications in groupoids;
- `core/canonical`: `FibredCategoryMor.IsStackification`, `exists_stackification`,
  `stackification_unique_up_to_unique_twoIso`, and
  `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`;
- `bridge/view`: the canonical bridge `FibredInGroupoidsMor.toStackFibredCategoryMor` from the
  groupoid-specialized morphism to the ambient owner predicate. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable (X : FibredInGroupoidsOver C)

-- Proof sketch: apply the generic stackification result of Lemma `8.8.1` to the underlying
-- fibred category of `X`, then use Lemma `8.5.2` to see that the resulting stack is again fibred
-- in groupoids. Since both source and target are now bundled in the groupoid-specific APIs, the
-- stackification morphism is canonically a `FibredInGroupoidsMor`.
/-- Lemma 8.9.1 (1): a category fibred in groupoids over a site admits a stackification by a
stack in groupoids, with the induced morphism presheaf maps identifying the target with the
sheafification of the source and with local essential surjectivity on objects in each fiber. -/
theorem exists_stackInGroupoids_stackification :
    ∃ Y : StackInGroupoidsOver J,
      ∃ G : FibredInGroupoidsMor X Y,
        FibredCategoryMor.IsStackification G.toStackFibredCategoryMor := sorry

-- Proof sketch: forget the two stackifications in groupoids to stackifications in the sense of
-- Lemma `8.8.1`, apply `stackification_unique_up_to_unique_twoIso` there, and observe that the
-- comparison equivalence is automatically an owner hom between the underlying stacks of the two
-- stack-in-groupoids structures.
/-- Lemma 8.9.1 (2): a stackification of a category fibred in groupoids by a stack in groupoids is
determined up to equivalence over the base together with a unique compatible `2`-isomorphism. -/
theorem stackInGroupoids_stackification_unique_up_to_unique_twoIso
    {Y₁ Y₂ : StackInGroupoidsOver J}
    (G₁ : FibredInGroupoidsMor X Y₁)
    (G₂ : FibredInGroupoidsMor X Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁.toStackFibredCategoryMor)
    (hG₂ : FibredCategoryMor.IsStackification G₂.toStackFibredCategoryMor) :
    ∃ H : Y₁ ⟶ Y₂,
      StackInGroupoidsOver.Hom.IsEquivalenceOverBase H ∧
        let GH : FibredInGroupoidsMor X Y₂ :=
          G₁ ≫ StackInGroupoidsOver.Hom.toFibredInGroupoidsMor H
        Nonempty (GH ≅ G₂) ∧ Subsingleton (GH ≅ G₂) := sorry

end

end CategoryTheory
