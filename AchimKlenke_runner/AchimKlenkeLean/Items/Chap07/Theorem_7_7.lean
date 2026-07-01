import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped Topology

variable {I : Set ℝ} {φ : ℝ → ℝ} {a b t x y : ℝ}

/- Theorem 7.7 (1): The textbook continuity statement for a convex real-valued function on the
interior of an interval is exactly the canonical mathlib theorem
`ConvexOn.continuousOn_interior`. -/
recall ConvexOn.continuousOn_interior

/-- Theorem 7.7 (2): A convex real-valued function on an interval is Borel measurable for the
subspace Borel structure on that interval. -/
-- Proof sketch: Use continuity on `interior I`, then extend measurability across the at-most
-- two boundary points of an interval to obtain measurability on the whole subtype `I`.
theorem convexOn_subtype_measurable
    (hφ : ConvexOn ℝ I φ) :
    Measurable (Set.restrict I φ) := sorry

/- Theorem 7.7 (3): The monotonicity of the secant-slope map for a convex function is the
canonical theorem `ConvexOn.slope_mono`. -/
recall ConvexOn.slope_mono

/- Theorem 7.7 (4): The left-derivative formula for convex functions at interior points is the
canonical theorem `ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior`. -/
recall ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior

/- Theorem 7.7 (5): The right-derivative formula for convex functions at interior points is the
canonical theorem `ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior`. -/
recall ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior

/- Theorem 7.7 (6): The inequality between the left and right derivatives at an interior point of a
convex function is the canonical theorem `ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior`. -/
recall ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior

section InteriorPoint

/-- Theorem 7.7 (7): A real number `t` is a supporting slope of a convex function at an interior
point `x` exactly when it lies between the left and right derivatives at `x`. -/
-- Proof sketch: For `y > x`, compare `t` with secant slopes using the right derivative; for
-- `y < x`, compare with secant slopes using the left derivative, then combine the two directions.
theorem convexOn_supportingSlope_iff (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    (∀ y ∈ I, φ x + t * (y - x) ≤ φ y) ↔
      t ∈ Icc (derivWithin φ (Iio x) x) (derivWithin φ (Ioi x) x) := sorry

/- Theorem 7.7 (8): The monotonicity of the left-derivative map is the canonical theorem
`ConvexOn.monotoneOn_leftDeriv`. -/
recall ConvexOn.monotoneOn_leftDeriv

/- Theorem 7.7 (9): The monotonicity of the right-derivative map is the canonical theorem
`ConvexOn.monotoneOn_rightDeriv`. -/
recall ConvexOn.monotoneOn_rightDeriv

/-- Theorem 7.7 (10): The left-derivative map of a convex function is left continuous on the
interior of the interval. -/
-- Proof sketch: Apply one-sided continuity of monotone functions to the monotone left-derivative
-- map on `interior I`.
theorem convexOn_leftDeriv_continuousWithinAt_Iic
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    ContinuousWithinAt (fun z ↦ derivWithin φ (Iio z) z) (Iic x) x := sorry

/-- Theorem 7.7 (11): The right-derivative map of a convex function is right continuous on the
interior of the interval. -/
-- Proof sketch: Apply one-sided continuity of monotone functions to the monotone right-derivative
-- map on `interior I`.
theorem convexOn_rightDeriv_continuousWithinAt_Ici
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    ContinuousWithinAt (fun z ↦ derivWithin φ (Ioi z) z) (Ici x) x := sorry

/-- Theorem 7.7 (12): At any interior point where the left-derivative map is left continuous, the
left and right derivatives of a convex function coincide. -/
-- Proof sketch: Use left continuity of `D⁻φ`, monotonicity of both one-sided derivative maps, and
-- the inequality `D⁻φ ≤ D⁺φ` to squeeze the right derivative to the same value.
theorem convexOn_leftDeriv_eq_rightDeriv_of_leftDeriv_continuousWithinAt_Iic
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I)
    (hcont : ContinuousWithinAt (fun z ↦ derivWithin φ (Iio z) z) (Iic x) x) :
    derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := sorry

/-- Theorem 7.7 (13): At any interior point where the right-derivative map is right continuous, the
left and right derivatives of a convex function coincide. -/
-- Proof sketch: Use right continuity of `D⁺φ`, monotonicity of both one-sided derivative maps, and
-- the inequality `D⁻φ ≤ D⁺φ` to squeeze the left derivative to the same value.
theorem convexOn_leftDeriv_eq_rightDeriv_of_rightDeriv_continuousWithinAt_Ici
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I)
    (hcont : ContinuousWithinAt (fun z ↦ derivWithin φ (Ioi z) z) (Ici x) x) :
    derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := sorry

/-- Theorem 7.7 (14): A convex function is differentiable at an interior point exactly when its
left and right derivatives at that point agree. -/
-- Proof sketch: If `φ` is differentiable, both one-sided derivatives equal the ordinary
-- derivative; conversely, equality of the one-sided derivatives upgrades the two one-sided limits
-- of the secant slopes to a single derivative.
theorem convexOn_differentiableAt_iff_leftDeriv_eq_rightDeriv
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    DifferentiableAt ℝ φ x ↔
      derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := sorry

end InteriorPoint

/- Theorem 7.7 (15): When a real function is differentiable at `x`, its ordinary derivative and
its right derivative at `x` agree; this is the canonical calculus theorem
`DifferentiableAt.derivWithin`, applied with `uniqueDiffWithinAt_Ioi`. In the convex setting, this
applies at every differentiability point. -/
recall DifferentiableAt.derivWithin {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x

/-- Theorem 7.7 (16): A convex function on an interval is differentiable almost everywhere on that
interval. -/
-- Proof sketch: The one-sided derivative maps are monotone on `interior I`, so their
-- discontinuity sets are countable; outside this null set the left and right derivatives coincide,
-- hence `φ` is differentiable there.
theorem convexOn_ae_differentiableAt
    (hφ : ConvexOn ℝ I φ) :
    ∀ᵐ x ∂(volume.restrict I), DifferentiableAt ℝ φ x := sorry

/-- Theorem 7.7 (17): On interior points of the interval, the increment of a convex function is
the interval integral of its right derivative. -/
-- Proof sketch: The right derivative is monotone, hence measurable and locally integrable; then
-- use almost-everywhere differentiability together with the one-dimensional fundamental theorem of
-- calculus for monotone derivatives.
theorem convexOn_sub_eq_intervalIntegral_rightDeriv
    (hφ : ConvexOn ℝ I φ) (ha : a ∈ interior I) (hb : b ∈ interior I) :
    φ b - φ a = ∫ x in a..b, derivWithin φ (Ioi x) x := sorry
