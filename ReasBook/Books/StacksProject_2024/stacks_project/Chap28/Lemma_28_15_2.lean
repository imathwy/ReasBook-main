import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap28.Definition_28_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: Chapter 28 already packages both notions stalkwise via `Scheme.isNormalAt`
-- and `Scheme.isGeometricallyUnibranchAt`, so the faithful public API is the pointwise
-- implication as companion API on `Scheme.isNormalAt`, followed by the global scheme theorem.

variable {X : Scheme.{u}}

/-- If a scheme is normal at `x`, then it is geometrically unibranch at `x`. -/
theorem isNormalAt.isGeometricallyUnibranchAt {x : X}
    (hx : X.isNormalAt x) :
    X.isGeometricallyUnibranchAt x := by
  sorry

/-- Lemma 28.15.2: a normal scheme is geometrically unibranch. -/
@[stacks 0BQ3]
theorem isGeometricallyUnibranch_of_isNormal
    (hX : X.isNormal) :
    X.isGeometricallyUnibranch := fun x ↦
  (hX.isNormalAt x).isGeometricallyUnibranchAt

end AlgebraicGeometry.Scheme
