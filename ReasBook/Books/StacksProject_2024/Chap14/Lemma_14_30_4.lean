import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SSet.modelCategoryQuillen

universe u

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/- Domain-style sampling for Lemma 14.30.4:
- primary domain: simplicial-set lifting properties in the Quillen model structure;
- sampled owner declarations:
  `SSet.modelCategoryQuillen.I`,
  `CategoryTheory.MorphismProperty.rlp`,
  `CategoryTheory.MorphismProperty.comp_mem`,
  `MorphismProperty.comp_mem`;
- best owner abstraction: `I.rlp`;
- primitive-vs-derived split:
  primitive data: only the morphisms `f`, `g` together with the owner-property proofs
    `I.rlp f` and `I.rlp g`;
  derived API: closure of that owner property under composition via the canonical owner theorem
    `MorphismProperty.comp_mem I.rlp f g`.

Source/core/bridge triage:
- `source-facing`: the statement that a composite of trivial Kan fibrations is again a trivial Kan
  fibration;
- `core/canonical`: `MorphismProperty.comp_mem I.rlp f g`;
- `bridge/view`: the textbook phrase “trivial Kan fibration” for the owner-level predicate `I.rlp`.

This item introduces no simplicial-specific primitive data beyond `I.rlp`, so the correct
refinement is to reuse the canonical composition theorem directly rather than keep a parallel
chapter-local lemma. -/

/- Lemma 14.30.4: the composition of two trivial Kan fibrations is again a trivial Kan fibration.
Canonically, this is the specialization `MorphismProperty.comp_mem I.rlp f g` of the generic owner
theorem `CategoryTheory.MorphismProperty.comp_mem`. -/
recall MorphismProperty.comp_mem

#check (MorphismProperty.comp_mem I.rlp f g : I.rlp f → I.rlp g → I.rlp (f ≫ g))
