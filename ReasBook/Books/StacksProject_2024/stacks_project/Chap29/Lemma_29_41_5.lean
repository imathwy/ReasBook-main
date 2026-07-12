import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

-- Semantic recall: `lean_leansearch` found the canonical scheme-morphism owners
-- `AlgebraicGeometry.IsProper` and `AlgebraicGeometry.UniversallyClosed`, with the base-change
-- stability hooks `AlgebraicGeometry.IsProper.isStableUnderBaseChange` and
-- `AlgebraicGeometry.universallyClosed_isStableUnderBaseChange`.

/-- Lemma 29.41.5 (1): the base change of a proper morphism is proper. -/
@[stacks 01W4]
theorem isProper_baseChange [IsProper f] :
    IsProper (pullback.snd f g) := sorry

/-- Lemma 29.41.5 (2): the base change of a universally closed morphism is universally closed. -/
@[stacks 01W4]
theorem universallyClosed_baseChange [UniversallyClosed f] :
    UniversallyClosed (pullback.snd f g) := sorry

end

end AlgebraicGeometry
