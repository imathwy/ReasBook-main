import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the exact mathlib instance
-- `AlgebraicGeometry.Flat.isStableUnderBaseChange`; local Chapter 29 precedent records the
-- base-changed morphism of `f : X ⟶ S` along `g : S' ⟶ S` as `pullback.snd f g`.

/-- Lemma 29.25.8: the base change of a flat morphism is flat. -/
@[stacks 01U9]
theorem flat_pullback_snd (f : X ⟶ S) [Flat f] (g : S' ⟶ S) :
    Flat (pullback.snd f g) := sorry

end

end AlgebraicGeometry
