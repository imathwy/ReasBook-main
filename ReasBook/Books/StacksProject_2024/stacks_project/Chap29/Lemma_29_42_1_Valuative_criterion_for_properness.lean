import Mathlib.AlgebraicGeometry.ValuativeCriterion

namespace AlgebraicGeometry

universe u

-- `lean_leansearch` was unavailable in this workspace (HTTP 429), so this entry is matched
-- directly against `IsProper.eq_valuativeCriterion` and the standard finite-type split.

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 29.42.1 (Valuative criterion for properness): if `f` is quasi-separated and of finite
type, then `f` is proper if and only if it satisfies the valuative criterion, i.e. every
valuative commutative square over `f` admits a unique lift. Here "of finite type" is expressed by
`[QuasiCompact f] [LocallyOfFiniteType f]`. -/
@[stacks 0BX5]
theorem isProper_iff_valuativeCriterion [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] :
    IsProper f ↔ ValuativeCriterion f := by
  constructor
  · intro h
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  · exact IsProper.of_valuativeCriterion f

end AlgebraicGeometry
