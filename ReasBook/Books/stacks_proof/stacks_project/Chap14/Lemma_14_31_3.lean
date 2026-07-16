import Mathlib
import stacks_proof.stacks_project.Chap14.Definition_14_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

section

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/- Domain-style sampling for Lemma 14.31.3:
- primary domain: simplicial-set fibrations in the Quillen model structure;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  the generic composition instance
  `[CategoryWithFibrations C] [(fibrations C).IsStableUnderComposition]
    [Fibration f] [Fibration g] : Fibration (f ≫ g)`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `MorphismProperty.rlp_isMultiplicative`;
- best owner abstraction: the canonical predicate `Fibration`, with composition supplied by the
  ambient owner morphism property `fibrations SSet`;
- primitive data: the instance assumptions `[Fibration f]` and `[Fibration g]`;
- derived API: the source-facing conclusion `Fibration (f ≫ g)`.

Source/core/bridge triage:
- `source-facing`: the statement that a composite of two Kan fibrations is again a Kan fibration;
- `core/canonical`: the generic composition instance for `Fibration`;
- `bridge/view`: the horn-filling characterization `SSet.modelCategoryQuillen.fibration_iff`.

This item adds no new simplicial-set primitive data, so the correct refinement is reuse of the
existing `Fibration` composition instance directly. The needed owner-property stability is already
supplied by mathlib's model-category infrastructure, so no parallel local copy is part of the
public API. -/

variable [Fibration f] [Fibration g]

/-- Lemma 14.31.3: the composition of two Kan fibrations is again a Kan fibration. -/
@[stacks 08NW]
theorem fibration_comp : Fibration (f ≫ g) := by
  -- Rewrite Kan fibrations as the canonical right lifting property against horn inclusions.
  rw [SSet.modelCategoryQuillen.fibration_iff]
  -- The underlying morphism property is stable under composition in any category.
  exact MorphismProperty.comp_mem SSet.modelCategoryQuillen.J.rlp f g
    ((SSet.modelCategoryQuillen.fibration_iff f).1 (inferInstance : Fibration f))
    ((SSet.modelCategoryQuillen.fibration_iff g).1 (inferInstance : Fibration g))

end
