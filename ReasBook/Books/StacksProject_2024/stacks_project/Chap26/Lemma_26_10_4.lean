import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical criterion
-- `AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion`; this Stacks-facing statement keeps
-- the source assumption as an immersion and uses the Chapter 26 convention `Set.range f.base`
-- for the image subset of the target scheme.

/-- Lemma 26.10.4: let `f : Y ⟶ X` be an immersion of schemes. Then `f` is a closed immersion if
and only if its image is a closed subset of `X`. -/
@[stacks 01IQ]
theorem Scheme.Hom.isClosedImmersion_iff_isClosed_range_of_isImmersion {X Y : Scheme}
    (f : Y ⟶ X) [IsImmersion f] :
    IsClosedImmersion f ↔ IsClosed (Set.range f.base) := sorry

end AlgebraicGeometry
