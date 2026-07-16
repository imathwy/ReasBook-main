import Mathlib
import stacks_proof.stacks_project.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open SSet.modelCategoryQuillen

universe w u

section

variable {J : Type w} {X Y : J → SSet.{u}}
variable [HasProduct X] [HasProduct Y]

/-
Domain-style sampling for Lemma 14.30.6:
- primary domain: lifting properties of simplicial-set morphisms under products.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.HasLiftingProperty`,
  `CategoryTheory.MorphismProperty.limMap`,
  `CategoryTheory.MorphismProperty.rlp_isStableUnderProductsOfShape`.
- best owner abstraction: `I.rlp`.
- primitive-vs-derived split:
  primitive data: the family `f` and the componentwise owner property `I.rlp (f j)`.
  derived API: the source-facing product conclusion `I.rlp (Limits.Pi.map f)`. -/

/- Source/core/bridge triage for Lemma 14.30.6:
- source-facing: products of trivial Kan fibrations of simplicial sets.
- core/canonical: `MorphismProperty.limMap`, specialized to the owner morphism property `I.rlp`.
- bridge/view: the textbook phrase "trivial Kan fibration" for the owner-level property
  `I.rlp`. -/

/-- Lemma 14.30.6: a family of trivial Kan fibrations of simplicial sets has product map again a
trivial Kan fibration. Since Definition 14.30.1 already identifies “trivial Kan fibration” with
the owner property `I.rlp`, this source-facing statement is a thin bridge from the canonical owner
theorem `MorphismProperty.limMap`, whose native interface is formulated on the corresponding
natural transformation in the discrete functor category. -/
@[stacks 08NR]
theorem boundaryInclusions_rlp_piMap (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, I.rlp (f j)) :
    I.rlp (Limits.Pi.map f) := by
  -- Products are limits of discrete diagrams, so `limMap` upgrades the componentwise `I.rlp`
  -- hypotheses to the induced product map.
  exact MorphismProperty.limMap _ (fun ⟨j⟩ ↦ hf j)

end
