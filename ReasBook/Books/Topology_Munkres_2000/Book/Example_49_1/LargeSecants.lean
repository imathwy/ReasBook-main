import Topology_Munkres_2000.Book.Definition_49_2.Infimum
import Mathlib.Topology.ContinuousMap.Compact

open Set
open scoped UnitIntervalSecant

/-- The closed unit interval used in the strict secant constructions of §49. -/
abbrev ClosedUnitInterval := unitInterval

namespace UnitIntervalSecant

/-- The source set `Uₙ` of continuous real-valued functions on the closed unit
interval whose infimum secant magnitude exceeds `n` at some scale
`0 < h ≤ 1 / n`. -/
def largeSecantSet (n : ℕ) : Set C(unitInterval, ℝ) :=
  {f | ∃ h : ℝ, 0 < h ∧ h ≤ 1 / (n : ℝ) ∧ (n : ℝ) < Δ_{h} f}

/- The source notation `U_{n}` for the strict large-secant set. -/
scoped notation "U_{" n "}" => largeSecantSet n

/-- Membership in `U_{n}` is the existence of a scale at most
`1 / n` where the infimum secant magnitude is greater than `n`. -/
theorem mem_largeSecantSet {n : ℕ} {f : C(unitInterval, ℝ)} :
    f ∈ U_{n} ↔
      ∃ h : ℝ, 0 < h ∧ h ≤ 1 / (n : ℝ) ∧ (n : ℝ) < Δ_{h} f := Iff.rfl

end UnitIntervalSecant
