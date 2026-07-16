import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_6
import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the generic scheme-side base-change bridge
  `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`;
- local Chapter 29 precedent `Lemma_29_14_6.lean` records the base-changed morphism on the
  canonical projection `pullback.snd f g`, and Definition 29.30.1 fixes the source-facing owner
  for syntomic morphisms as `Syntomic f := LocallyOfType RingHom.Syntomic f`.
-/

section

variable {X S S' : Scheme.{u}}

/-- Lemma 29.30.4: the base change of a morphism which is syntomic is syntomic. -/
@[stacks 01UI]
theorem syntomic_pullback_snd (f : X ⟶ S) (hf : Syntomic f) (g : S' ⟶ S) :
    Syntomic (pullback.snd f g) := by
  sorry

end

end AlgebraicGeometry
