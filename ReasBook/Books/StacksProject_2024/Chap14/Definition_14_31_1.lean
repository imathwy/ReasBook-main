import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomotopicalAlgebra Simplicial

open scoped SSet.modelCategoryQuillen

universe u v

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Definition 14.31.1:
- primary domain: simplicial-set fibrations and fibrant objects in the Quillen model structure;
- inspected owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `HomotopicalAlgebra.isFibrant_iff`,
  `SSet.KanComplex`;
- best owner abstractions:
  `Fibration f` for Kan fibrations, and `KanComplex X` for Kan complexes;
- primitive-vs-derived split:
  primitive data: none beyond the owner predicates themselves;
  derived API: the horn-inclusion lifting characterization of `Fibration`, and the terminal-map
  characterization of `KanComplex` via `IsFibrant`.

Source/core/bridge triage:
- `source-facing`: the textbook notions of Kan fibration and Kan complex for simplicial sets;
- `core/canonical`: `Fibration` on morphisms and `KanComplex`/`IsFibrant` on objects;
- `bridge/view`: the horn-filling reformulation for fibrations and the terminal-map reformulation
  for fibrant objects.

This item introduces no new simplicial-set data, so the correct refinement is to reuse the owner
predicates directly and keep only the genuinely source-facing reformulation as a local theorem. -/

/- Definition 14.31.1 (1): for a morphism `f : X ⟶ Y` of simplicial sets, the Stacks notion of
a Kan fibration is the canonical predicate `HomotopicalAlgebra.Fibration f`; in `SSet`, this is
the right lifting property with respect to all horn inclusions `Λ[n + 1, i].ι`. -/
recall HomotopicalAlgebra.Fibration

/- Bridge/view companion to Definition 14.31.1 (1): in simplicial sets, the canonical owner
`Fibration f` is exactly the horn-inclusion right lifting property. -/
theorem fibration_iff_has_horn_lifting_property :
    Fibration f ↔ ∀ ⦃n : ℕ⦄ (i : Fin (n + 2)), HasLiftingProperty (Λ[n + 1, i].ι) f := by
  rw [fibration_iff]
  constructor
  · intro hf n i
    exact hf _ (horn_ι_mem_J n i)
  · intro hf A B g hg
    rw [J, CategoryTheory.MorphismProperty.iSup_iff] at hg
    rcases hg with ⟨n, hg⟩
    cases hg with
    | mk i => simpa using hf i

/- Definition 14.31.1 (2): a Kan complex is the canonical predicate `SSet.KanComplex X`,
meaning that the terminal morphism `X ⟶ ⊤_ SSet` is a Kan fibration. -/
recall SSet.KanComplex
recall HomotopicalAlgebra.isFibrant_iff

end SSet
