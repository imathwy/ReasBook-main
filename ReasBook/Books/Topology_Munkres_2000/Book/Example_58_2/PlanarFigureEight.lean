module

public import Mathlib.Analysis.Complex.Basic

public section

/-- The complex plane with the two points `p` and `q` removed. -/
abbrev TwoPuncturePlane (p q : ℂ) := {z : ℂ // z ≠ p ∧ z ≠ q}

namespace PlanarFigureEight

/-- The two equal-radius circles centered at `p` and `q`, tangent at their midpoint. -/
def carrier (p q : ℂ) : Set ℂ :=
  Metric.sphere p (dist p q / 2) ∪ Metric.sphere q (dist p q / 2)

/-- The planar figure eight regarded as a subset of the plane punctured at `p` and `q`. -/
def inComplement (p q : ℂ) : Set (TwoPuncturePlane p q) :=
  {z | (z : ℂ) ∈ carrier p q}

/-- Membership in the planar figure eight means lying on one of its two circles. -/
theorem mem_carrier_iff (p q z : ℂ) :
    z ∈ carrier p q ↔
      dist z p = dist p q / 2 ∨ dist z q = dist p q / 2 := by
  change (dist z p = dist p q / 2 ∨ dist z q = dist p q / 2) ↔ _
  rfl

/-- Membership in the complement-relative figure eight is membership of its planar image. -/
theorem mem_inComplement_iff (p q : ℂ) (z : TwoPuncturePlane p q) :
    z ∈ inComplement p q ↔ (z : ℂ) ∈ carrier p q := Iff.rfl

end PlanarFigureEight
