import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical base-change instances
-- `IsImmersion.isStableUnderBaseChange`, `IsClosedImmersion.isStableUnderBaseChange`,
-- and `isOpenImmersion_stableUnderBaseChange`; local Chapter 26 precedent uses
-- `Over.pullback`/`MorphismProperty.overPullbackMap` for base change over a fixed scheme.

variable {S S' : Scheme.{u}} (g : S' ⟶ S)
variable {X Y : Over S} (f : X ⟶ Y)

/-- Lemma 26.18.2 (1): if a morphism of schemes over `S` is an immersion, then its base change
along any morphism `S' ⟶ S` is an immersion. -/
@[stacks 01JY]
theorem isImmersion_overPullbackMap_of_isImmersion [IsImmersion f.left] :
    IsImmersion (((Over.pullback g).map f).left) := sorry

/-- Lemma 26.18.2 (2): if a morphism of schemes over `S` is a closed immersion, then its base
change along any morphism `S' ⟶ S` is a closed immersion. -/
@[stacks 01JY]
theorem isClosedImmersion_overPullbackMap_of_isClosedImmersion [IsClosedImmersion f.left] :
    IsClosedImmersion (((Over.pullback g).map f).left) := sorry

/-- Lemma 26.18.2 (3): if a morphism of schemes over `S` is an open immersion, then its base
change along any morphism `S' ⟶ S` is an open immersion. -/
@[stacks 01JY]
theorem isOpenImmersion_overPullbackMap_of_isOpenImmersion [IsOpenImmersion f.left] :
    IsOpenImmersion (((Over.pullback g).map f).left) := sorry

end AlgebraicGeometry
