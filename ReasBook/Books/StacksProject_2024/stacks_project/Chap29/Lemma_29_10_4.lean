import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}}

-- The source-facing Stacks statement is the pullback projection formulation, while the canonical
-- owner is mathlib's `AlgebraicGeometry.UniversallyInjective`. This file only records the
-- base-change closure statement on `pullback.snd`.

/-- Lemma 29.10.4: a base change of a universally injective morphism is universally injective. -/
@[stacks 0472]
theorem universallyInjective_pullback_snd (f : X ⟶ S) [UniversallyInjective f] (g : S' ⟶ S) :
    UniversallyInjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

end

end AlgebraicGeometry
