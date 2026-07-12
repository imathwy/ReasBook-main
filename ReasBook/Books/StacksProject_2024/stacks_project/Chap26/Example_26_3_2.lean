import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u

namespace AlgebraicGeometry

section

variable (X : LocallyRingedSpace.{u}) (U : Opens X)

-- Semantic recall: `Definition_26_3_3` already records the source-facing owner
-- `AlgebraicGeometry.LocallyRingedSpace.restrict` for the restricted locally ringed space.
-- The new content of this example is the canonical open-immersion structure on the inclusion
-- `X.ofRestrict U.isOpenEmbedding`, owned by
-- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.ofRestrict`.

/- Example 26.3.2: the canonical inclusion of the restricted locally ringed space is an open
immersion. In mathlib this is exactly
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.ofRestrict`. -/
recall LocallyRingedSpace.IsOpenImmersion.ofRestrict

#check LocallyRingedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding

end

end AlgebraicGeometry
