import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MorphismProperty
open SSet.modelCategoryQuillen

universe u

section

variable {X Y Y' : SSet.{u}}
variable {f : X ⟶ Y} {g : Y' ⟶ Y}

/-
Domain-style sampling for Lemma 14.30.3:
- primary domain: lifting properties of simplicial-set morphisms under pullback.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.pullback_snd`,
  `MorphismProperty.rlp_isStableUnderBaseChange`.
- best owner abstraction: the morphism property `SSet.modelCategoryQuillen.I.rlp`;
  the relevant canonical derived theorem is `CategoryTheory.MorphismProperty.pullback_snd`,
  specialized here as `I.rlp.pullback_snd`.
- primitive-vs-derived split:
  primitive data: the morphisms `f`, `g`, and the owner property `I.rlp f`.
  derived API: the textbook statement that a trivial Kan fibration stays trivial after pullback;
  the specialized consequence `I.rlp (pullback.snd f g)` is derived by the canonical owner theorem
  `MorphismProperty.pullback_snd`,
  and the pullback existence needed for `pullback.snd f g` is already supplied canonically in
  `SSet`. -/

/- Source/core/bridge triage for Lemma 14.30.3:
- source-facing: trivial Kan fibrations of simplicial sets.
- core/canonical: the owner property `I.rlp` together with its canonical base-change theorem
  `I.rlp.pullback_snd`.
- bridge/view: the source wording "trivial Kan fibration" for the owner-level property `I.rlp`.

This item adds no simplicial-specific data beyond the owner property `I.rlp`, and mathlib already
provides the exact base-change theorem for that owner. The correct refinement is therefore direct
canonical use of `I.rlp.pullback_snd f g`, rather than a renamed local theorem shell. -/

/- Lemma 14.30.3: for a trivial Kan fibration `f : X ⟶ Y` of simplicial sets and any morphism
`g : Y' ⟶ Y`, the pullback projection `X ×[Y] Y' ⟶ Y'` is again a trivial Kan fibration.
Canonically, this is `I.rlp.pullback_snd f g`, the owner-prefixed specialization of the generic
base-change theorem to the boundary-inclusion right lifting
property `I.rlp`. -/
recall MorphismProperty.pullback_snd

#check (I.rlp.pullback_snd f g : I.rlp f → I.rlp (pullback.snd f g))

end
