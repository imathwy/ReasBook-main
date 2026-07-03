import Mathlib
import stacks_project.Chap14.Lemma_14_30_5
import stacks_project.Chap14.Definition_14_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped SSet.modelCategoryQuillen

universe u

section

variable {X : ℕ → SSet.{u}}
variable (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
variable [∀ n : ℕ, Fibration (f n)]

/-
Domain-style sampling for Lemma 14.31.4:
- primary domain: simplicial-set fibrations in the Quillen model structure, together with
  categorical inverse limits of countable towers;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`,
  `CategoryTheory.Functor.ofOpSequence`,
  `CategoryTheory.Limits.limit.π`;
- best owner abstraction: the canonical predicate `Fibration`, with the inverse-limit projection
  expressed directly as a theorem on the canonical morphism `limit.π (Functor.ofOpSequence f)
  (op 0)`, using the owner theorem `J.rlp_limitProjection_ofSequence` together with
  the canonical owner identification `SSet.modelCategoryQuillen.fibration_iff`;
- primitive-vs-derived split:
  primitive data: the tower maps `f n : X (n + 1) ⟶ X n` and the owner instances
    `[∀ n, Fibration (f n)]`;
  derived API: the source-facing recall that the canonical projection from the inverse limit of the
    tower to `X 0` is again a Kan fibration.

Source/core/bridge triage:
- `source-facing`: the textbook statement about inverse limits of Kan fibrations;
- `core/canonical`: the owner predicate `Fibration`;
- `bridge/view`: the owner equivalence `SSet.modelCategoryQuillen.fibration_iff`;
- owner theorem reused by the proof:
  `J.rlp_limitProjection_ofSequence`.

This item is `source-facing`, but it is not the owner of new simplicial-set data or a new bridge.
Unlike the pullback, composition, and product cases nearby, the exact inverse-limit statement is
not exposed upstream as an instance, so the correct refinement is a thin theorem stated directly in
the canonical owner predicate `Fibration`, not a fake `#synth` recall and not a second local
horn-lifting wrapper.
-/

/- Lemma 14.31.4: for a countable inverse sequence of Kan fibrations of simplicial sets, the
canonical projection from the inverse limit of the sequence to the initial term is again a Kan
fibration. The public statement stays on the owner predicate `Fibration` for the canonical
projection `limit.π (Functor.ofOpSequence f) (op 0)`. -/
theorem fibration_limitProjection_ofSequence :
    Fibration (limit.π (Functor.ofOpSequence f) (op 0)) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  exact J.rlp_limitProjection_ofSequence f fun m ↦
    (SSet.modelCategoryQuillen.fibration_iff (f m)).1 (inferInstance : Fibration (f m))

end
