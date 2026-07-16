import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_29_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `LocallyOfFiniteType` and `QuasiCompact`. Local Chapter 29 precedent then packages a uniform
-- pointwise fibre-dimension bound as `RelativeDimensionLE`, but the source statement itself is the
-- raw existence of such a bound.

variable {X Y : Scheme.{u}}

/-- Lemma 29.28.5: if `f : X ⟶ Y` is of finite type and `Y` is quasi-compact, then there exists a
uniform natural-number bound on the local dimensions `dim_x(X_{f(x)})` of the fibres of `f`. -/
@[stacks 0A3V]
theorem exists_fiberDimensionAt_le_of_finiteType
    (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f] [CompactSpace Y] :
    ∃ n : ℕ, ∀ x : X, f.fiberDimensionAt x ≤ (n : WithBot ℕ∞) := sorry

/-- A finite type morphism over a quasi-compact base has some relative-dimension-at-most bound. -/
theorem exists_relativeDimensionLE_of_finiteType
    (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f] [CompactSpace Y] :
    ∃ n : ℕ, RelativeDimensionLE f n := sorry

end Scheme.Hom
end AlgebraicGeometry
