import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_7_14 (from Items/Chap07) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: this is the source-facing `ConcaveOn` formulation of the textbook claim. The
-- owner abstraction is the chapter's concavity/Jensen interface on the nonnegative quadrant, not
-- the later `lpNorm` inequality API.
/-- Example 7.14: for `p > 1`, the function
`ψ(x, y) = (x^(1/p) + y^(1/p))^p` is concave on the nonnegative quadrant
`[0, ∞) × [0, ∞)`. -/
theorem concaveOn_nonneg_rpow_add_rpow {p : ℝ} (hp : 1 < p) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun z : ℝ × ℝ ↦ (z.1.rpow (1 / p) + z.2.rpow (1 / p)).rpow p) := sorry

-- Proof sketch: apply the concave Jensen inequality to the random vector `ω ↦ (X ω, Y ω)` and
-- the source-facing concavity theorem above. This keeps the expectation estimate as a companion
-- consequence of the canonical `ConcaveOn` owner abstraction.
/-- Example 7.14: if `X` and `Y` are nonnegative integrable real random variables on a probability
space and `p ∈ (1, ∞)`, then Jensen's inequality for the concave map
`(x, y) ↦ (x^(1/p) + y^(1/p))^p` gives
`E[(X^(1/p) + Y^(1/p))^p] ≤ (E[X]^(1/p) + E[Y]^(1/p))^p`. -/
theorem expectation_rpow_add_le_rpow_add_expectations {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} {p : ℝ} (hp : 1 < p) (hX : Integrable X P)
    (hY : Integrable Y P) (hX_nonneg : 0 ≤ᵐ[P] X) (hY_nonneg : 0 ≤ᵐ[P] Y) :
    P[fun ω ↦ ((X ω).rpow (1 / p) + (Y ω).rpow (1 / p)).rpow p] ≤
      ((P[X]).rpow (1 / p) + (P[Y]).rpow (1 / p)).rpow p := sorry
