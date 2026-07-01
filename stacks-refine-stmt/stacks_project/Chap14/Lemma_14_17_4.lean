import stacks_project.Chap14.Definition_14_17_1
import stacks_project.Chap14.Lemma_14_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.17.4:
- primary domain: representable simplicial mapping-object presheaves;
- sampled owner-style declarations:
  `Functor.IsRepresentable`,
  `Functor.representableBy`,
  `simplicialHomPresheaf`,
  `simplicialHom`;
- best owner abstraction: the source-facing owner remains `simplicialHomPresheaf U V`, and the
  file’s main content is the owner predicate `(simplicialHomPresheaf U V).IsRepresentable`;
- primitive data: the simplicial set `U`, the target simplicial object `V`, the degreewise
  finiteness family on `U`, a `0`-simplex of `U`, and the eventual degeneracy hypothesis;
- derived API: the source-facing representability theorem and its `Fact`-packaged instance.

Any later comparison between concrete representing objects should be expressed through the
canonical owner API `Functor.RepresentableBy.uniqueUpToIso` or `Functor.RepresentableBy.isoReprX`,
not by introducing a parallel local chosen-object wrapper here. -/

-- Proof sketch: evaluate the presheaf `W ↦ Mor(W × U, V)` degreewise at each simplex `[n]`.
-- Lemma `14.17.3` gives representability of the resulting `C`-valued presheaf
-- `X ↦ Mor(X × (U ⊗ Δ[n]), V)`, and Lemma `14.13.4` identifies maps out of `X × Δ[n]` with maps
-- into the `n`-th component, allowing these representing objects to assemble into a simplicial
-- object. This yields representability of `simplicialHomPresheaf U V`.
section EventuallyDegenerate

variable [HasBinaryCoproducts C] [HasFiniteLimits C]
variable (U : SSet.{w}) [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]
variable (V : SimplicialObject C)

/-- Lemma 14.17.4: if `C` has binary coproducts and finite limits, if `U` is degreewise finite
with a `0`-simplex, and if all sufficiently high simplices of `U` are degenerate, then the presheaf
`W ↦ Mor_{Simp(C)}(W × U, V)` is representable. Equivalently, the simplicial mapping object
`simplicialHom U V` exists. -/
theorem simplicialHomPresheaf_isRepresentable_of_eventually_degenerate
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (simplicialHomPresheaf U V).IsRepresentable := sorry

instance simplicialHomPresheaf_isRepresentable_of_fact_eventually_degenerate
    [Fact (∃ d : ℕ, U.HasDimensionLE d)] :
    (simplicialHomPresheaf U V).IsRepresentable :=
  simplicialHomPresheaf_isRepresentable_of_eventually_degenerate U V Fact.out

end EventuallyDegenerate

end CategoryTheory
