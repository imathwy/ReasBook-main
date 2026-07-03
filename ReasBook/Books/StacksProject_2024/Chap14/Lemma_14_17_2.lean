import StacksProject_2024.Chap14.Definition_14_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open scoped Simplicial

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.17.2:
- primary domain: representable presheaves obtained by restricting the simplicial mapping-object
  presheaf along constant simplicial objects;
- sampled owner-style declarations:
  `SimplicialObject.const`,
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`,
  `simplicialHomPresheaf`,
  `Functor.IsRepresentable`;
- best owner abstraction: the ambient owner is `simplicialHomPresheaf U V`, while the present file
  is only its `C`-indexed `bridge/view` specialization along `SimplicialObject.const`;
- primitive data: the simplicial set `U`, the target simplicial object `V`, and the owner
  hypothesis that the simplicial copowers `U × W` exist for every simplicial object `W`;
- auxiliary source hypotheses: binary coproducts on `C`, degreewise finiteness of `U`, and a
  `0`-simplex of `U`, which only supply the owner hypothesis through
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`;
- derived API: the representability statement for the constant-object restriction
  `(SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V` under the stronger source-facing
  hypotheses.

This file therefore deletes the parallel compatible-family model and reuses the upstream owner
construction directly. -/

variable {C : Type u} [Category.{v} C]

section Restriction

variable [HasBinaryCoproducts C]
variable (U : SSet.{w}) (V : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]

-- Proof sketch: this is the source-facing `C`-indexed specialization of the owner presheaf
-- `simplicialHomPresheaf U V`; the representability argument is unchanged, but now expressed on
-- the canonical restricted presheaf rather than a parallel compatible-family model.
/-- Lemma 14.17.2: assume `C` has binary coproducts and countable limits, and that `U` is
degreewise finite with a `0`-simplex. Then the presheaf `X ↦ Mor_{Simp(C)}(X × U, V)` is
representable. In Lean this presheaf is the constant-object restriction
`(SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V` of the owner presheaf
`simplicialHomPresheaf U V`. -/
theorem simplicialHomPresheaf_const_isRepresentable
    [HasCountableLimits C] :
    ((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable := sorry

attribute [instance] simplicialHomPresheaf_const_isRepresentable

end Restriction

end CategoryTheory
