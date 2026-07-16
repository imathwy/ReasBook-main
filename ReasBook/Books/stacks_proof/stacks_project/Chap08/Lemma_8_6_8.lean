import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_35_9
import stacks_proof.stacks_project.Chap08.Definition_8_6_1
import stacks_proof.stacks_project.Chap08.Lemma_8_4_6
import stacks_proof.stacks_project.Chap08.Lemma_8_6_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredCategoryOver
open InducedCategory.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S₁ S₂ S : StackOver J}

section

variable [IsStackInSetoids J S₁.p] [IsStackInSetoids J S₂.p]
variable [IsFibredInGroupoids S.p]
variable (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S)

/- Domain-style sampling for Lemma 8.6.8:
- primary domain: stacks in setoids over a site and the explicit `2`-fibre product of the
  underlying fibred categories;
- inspected owner-level declarations:
  `IsStackInSetoids`,
  `twoFibreProduct`,
  `FibredCategoryMor.faithful_iff_fiberwise`,
  `stackTwoFibreProduct_isStackInSetoids_of_leftFaithful`;
- best owner abstraction: the canonical owner is the projection
  `(twoFibreProduct f₁.toFibredCategoryMor
    f₂.toFibredCategoryMor).p`;
  the present lemma is source-facing only in that it derives the left-faithful hypothesis from the
  stronger source assumption that `S₁` itself is a stack in setoids;
- primitive data: the stack morphisms `f₁ : S₁ ⟶ S` and `f₂ : S₂ ⟶ S`;
- derived API: faithfulness of `f₁.toBasedFunctor`, obtained fiberwise from the thin fibers of
  `S₁`, and then the Chapter 8 owner theorem for a left-faithful explicit `2`-fibre product.

Source/core/bridge triage:
- `source-facing`: `stackTwoFibreProduct_isStackInSetoids_of_factors`;
- `core/canonical`: `IsStackInSetoids J` on the explicit projection
  `(twoFibreProduct f₁.toFibredCategoryMor
    f₂.toFibredCategoryMor).p`;
- `bridge/view`: the derived faithfulness witness for `f₁.toBasedFunctor`. -/

-- Proof sketch: any morphism from a stack in setoids is faithful on fibers, hence faithful on the
-- total category. Apply Lemma `8.6.7` to the left leg `f₁ : S₁ ⟶ S` and the right leg
-- `f₂ : S₂ ⟶ S`.
/-- Lemma 8.6.8: if `S₁` and `S₂` are stacks in setoids over the site `(C, J)` and
`f₁ : S₁ ⟶ S`, `f₂ : S₂ ⟶ S` are `1`-morphisms to a stack in groupoids `S`, then the explicit
`2`-fibre product `S₁ ×[S] S₂` is again a stack in setoids over `(C, J)`. -/
@[stacks 05UJ]
theorem stackTwoFibreProduct_isStackInSetoids_of_factors
    :
    IsStackInSetoids J
      (twoFibreProduct (toFibredCategoryMor f₁)
        (toFibredCategoryMor f₂)).p := by
  let P := twoFibreProduct (toFibredCategoryMor f₁) (toFibredCategoryMor f₂)
  let F₁ := toFibredCategoryMor f₁
  letI : (FibredCategoryMor.toBasedFunctor F₁).Faithful := by
    refine
      (FibredCategoryMor.faithful_iff_fiberwise F₁).2 ?_
    intro U
    letI : Quiver.IsThin ((BasedCategory.ofFunctor S₁.toFibredCategoryOver.1.p).p.Fiber U) := by
      simpa using (inferInstance : Quiver.IsThin (S₁.p.Fiber U))
    refine ⟨?_⟩
    intro x y α β _
    exact Subsingleton.elim α β
  change IsStackInSetoids J P.p
  exact stackTwoFibreProduct_isStackInSetoids_of_leftFaithful f₁ f₂ inferInstance

end

end CategoryTheory
