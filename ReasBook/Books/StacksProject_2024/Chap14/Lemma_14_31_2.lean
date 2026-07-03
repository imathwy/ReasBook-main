import Mathlib
import stacks_project.Chap14.Definition_14_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Simplicial
open CategoryTheory.Limits
open HomotopicalAlgebra
open SSet.modelCategoryQuillen

open scoped SSet.modelCategoryQuillen

universe u

section

variable {X Y Y' : SSet.{u}}
variable {f : X ⟶ Y} {g : Y' ⟶ Y}

/- Domain-style sampling for Lemma 14.31.2:
- primary domain: simplicial-set fibrations in the Quillen model structure;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  the generic base-change instance
  `[CategoryWithFibrations C] [(fibrations C).IsStableUnderBaseChange]
    [Fibration f] : Fibration (pullback.snd f g)`,
  `CategoryTheory.MorphismProperty.rlp_isStableUnderBaseChange`.
- best owner abstraction: the canonical predicate `Fibration`, with base-change closure supplied by
  the ambient owner morphism property `fibrations SSet`;
- primitive data: the morphism `f` together with the owner property `Fibration f`;
- derived API: the pulled-back fibration statement on `pullback.snd f g`.

Source/core/bridge triage:
- `source-facing`: the statement that a base change of a Kan fibration is again a Kan fibration;
- `core/canonical`: the generic base-change instance for `Fibration`;
- `bridge/view`: the horn-filling identification `SSet.modelCategoryQuillen.fibration_iff`.

This item introduces no new source-facing data beyond the owner property `Fibration f`, so the
correct refinement is to reuse the generic `Fibration` pullback instance directly. In `SSet`,
the needed owner-property stability is already synthesized from mathlib's model-category
infrastructure, so the public statement needs no parallel local instance and no extra
`[HasPullback f g]` binder. -/

variable [Fibration f]

/- Lemma 14.31.2: the base change of a Kan fibration of simplicial sets is again a Kan
fibration. Canonically, this is the generic pullback instance for `Fibration`. -/
#check (inferInstance : Fibration (pullback.snd f g))

end
