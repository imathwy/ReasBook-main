import StacksProject_2024.stacks_project.Chap14.Definition_14_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped SSet.modelCategoryQuillen

universe u v

section

variable {ι : Type v} {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
variable [HasProduct X] [HasProduct Y]
variable [∀ i, Fibration (f i)]

/- Domain-style sampling for Lemma 14.31.5:
- primary domain: simplicial-set fibrations in the Quillen model structure, together with their
  stability under products;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `CategoryTheory.MorphismProperty.limMap`,
  the abstract product instance for `Fibration (Limits.Pi.map f)` in
    `Mathlib.AlgebraicTopology.ModelCategory.Instances`;
- best owner abstraction: `Fibration (Limits.Pi.map f)`;
- primitive data: the family `f`, the product hypotheses `[HasProduct X] [HasProduct Y]`, and the
  componentwise fibrations as owner instances `[∀ i, Fibration (f i)]`;
- derived API: the source-facing theorem that the induced product map again has the owner
  predicate `Fibration`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a product of Kan fibrations of simplicial sets is a
  Kan fibration;
- `core/canonical`: the owner predicate `Fibration`;
- `bridge/view`: the horn-filling reformulation
  `SSet.modelCategoryQuillen.fibration_iff`.

This item is `source-facing`, but it adds no new source-defined data beyond the existing owner
predicate `Fibration`. There is an abstract upstream product instance, but it assumes the ambient
weak-factorization-system package for a model category, and that instance is not inferable here
from the scoped simplicial-set Quillen structure alone. By the semantic-priority rule, the main
lemma should stay at the weaker source-faithful simplicial-set assumptions and use only the thin
bridge from `Fibration` to `J.rlp`, `MorphismProperty.limMap`, and back.
-/

/-- Lemma 14.31.5: if each `f i : X i ⟶ Y i` is a Kan fibration of simplicial sets, then the
induced product map `Limits.Pi.map f : ∏ᶜ X ⟶ ∏ᶜ Y` is also a Kan fibration. This is exactly the
canonical owner-level product statement, expressed through `Fibration`. -/
theorem fibration_piMap : Fibration (Limits.Pi.map f) := by
  -- Rewrite fibrations as the horn-inclusion lifting property and apply product stability.
  rw [SSet.modelCategoryQuillen.fibration_iff]
  exact MorphismProperty.limMap _ fun ⟨i⟩ ↦
    (SSet.modelCategoryQuillen.fibration_iff (f i)).1 inferInstance

end
