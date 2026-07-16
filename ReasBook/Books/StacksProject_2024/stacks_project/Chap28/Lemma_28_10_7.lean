import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the scheme-side owner `IsLocallyNoetherian`, while
-- Chapter 5 fixes the source-facing local dimension owner as `topologicalKrullDimAt` and isolated
-- points as singleton openness `IsOpen ({x} : Set X)`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 28.10.7: for a point `x` of a locally Noetherian scheme `X`, the local dimension
`dim_x(X)`, formalized by `topologicalKrullDimAt x`, vanishes if and only if `x` is an isolated
point of `X`, formalized by `IsOpen ({x} : Set X)`. -/
@[stacks 0H7C]
theorem topologicalKrullDimAt_eq_zero_iff_isOpen_singleton {x : X} :
    topologicalKrullDimAt x = 0 ↔ IsOpen ({x} : Set X) := sorry

end AlgebraicGeometry.Scheme
