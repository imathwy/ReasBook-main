import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import StacksProject_2024.stacks_project.Chap29.Definition_29_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

-- The owner file `Chap29/Definition_29_24_1.lean` already defines the source-facing notions
-- `Submersive` and `UniversallySubmersive`; this file records the source-labeled base-change
-- closure theorem as a thin bridge to that owner API.

universe u

section

variable {X Y T : Scheme.{u}}

/-- Any base change of a universally submersive morphism is universally submersive. -/
theorem UniversallySubmersive.pullback_snd
    {f : X ⟶ Y} (hf : UniversallySubmersive f) (g : T ⟶ Y) :
    UniversallySubmersive (pullback.snd f g) := by
  rw [universallySubmersive_iff_universally] at hf ⊢
  exact submersiveProperty.universally.pullback_snd f g hf

/-- Lemma 29.24.2: the base change of a universally submersive morphism of schemes by any
morphism of schemes is universally submersive. -/
@[stacks 0CES]
theorem universallySubmersive_pullback_snd
    (f : X ⟶ Y) (hf : UniversallySubmersive f) (g : T ⟶ Y) :
    UniversallySubmersive (pullback.snd f g) :=
  UniversallySubmersive.pullback_snd hf g

end

end AlgebraicGeometry
