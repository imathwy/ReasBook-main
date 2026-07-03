import StacksProject_2024.Chap14.Lemma_14_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped Simplicial

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable [HasBinaryCoproducts C] [HasFiniteLimits C]

section Restriction

variable (U : SSet.{w}) (V : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]

/- Domain-style sampling for Lemma 14.17.3:
- primary domain: representability of the `C`-indexed restriction of the simplicial mapping-object
  presheaf under a finite-dimensionality hypothesis on the source simplicial set;
- sampled owner-style declarations:
  `Functor.IsRepresentable`,
  `simplicialHomPresheaf`,
  `(const C).op ⋙ simplicialHomPresheaf U V`,
  `SSet.HasDimensionLE`;
- best owner abstraction: the ambient owner remains `simplicialHomPresheaf U V`, while this lemma
  is the `source-facing` `bridge/view` statement for its restriction along constant simplicial
  objects, so it should not be collapsed to the later owner-level statement of Lemma `14.17.4`;
- primitive data: the simplicial set `U`, the simplicial object `V`, the direct degreewise-finite
  family on `U`, a `0`-simplex of `U`, and the chapter owner predicate
  `∃ d : ℕ, U.HasDimensionLE d`;
- derived API: representability of the restricted presheaf
  `(const C).op ⋙ simplicialHomPresheaf U V`, expressed with the canonical owner
  `((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable`.
-/

-- Proof sketch: choose `d` with `U.HasDimensionLE d`, replace the indexing category from the proof
-- of `Lemma 14.17.2` by its finite full subcategory on simplices in degrees at most `2d`, and use
-- the initial-functor criterion from `Definition 4.17.3` and `Lemma 4.17.4` to identify the
-- resulting finite limit with the original compatible-family limit.
/-- Lemma 14.17.3: if `C` has binary coproducts and finite limits, if `U` is degreewise finite
with a `0`-simplex, and if all sufficiently high simplices of `U` are degenerate (formalized as
`∃ d : ℕ, U.HasDimensionLE d`), then the presheaf
`X ↦ Mor_{Simp(C)}(X × U, V)` is representable.
Here this presheaf is the constant-object restriction
`(const C).op ⋙ simplicialHomPresheaf U V` from Lemma 14.17.2. -/
theorem simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    ((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable := sorry

instance simplicialHomPresheaf_const_isRepresentable_of_fact_eventually_degenerate
    [Fact (∃ d : ℕ, U.HasDimensionLE d)] :
    ((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable :=
  simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate U V Fact.out

end Restriction

end

end CategoryTheory
