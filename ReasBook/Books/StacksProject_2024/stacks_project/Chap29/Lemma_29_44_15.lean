import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Semantic recall: mathlib already exposes the canonical scheme-morphism equivalence
-- `AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`, so this Stacks lemma is kept as a
-- source-facing implication on the same canonical owners.

/-- Lemma 29.44.15: if a morphism of schemes is finite and a monomorphism, then it is a closed
immersion. -/
@[stacks 03BB]
theorem IsFinite.isClosedImmersion [IsFinite f] [Mono f] :
    IsClosedImmersion f :=
  (IsClosedImmersion.iff_isFinite_and_mono f).2 ⟨inferInstance, inferInstance⟩

end

end AlgebraicGeometry
