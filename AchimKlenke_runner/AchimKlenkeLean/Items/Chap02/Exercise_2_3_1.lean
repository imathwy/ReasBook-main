import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The `n`th partial sum of an integer-valued sequence of increments, using the first `n`
coordinates `X 0, …, X (n - 1)`. -/
def random_walk_partial_sum (X : ℕ → Ω → ℤ) (n : ℕ) : Ω → ℤ :=
  fun ω ↦ Finset.sum (Finset.range n) fun i ↦ X i ω

-- Proof sketch: a finite sum of measurable coordinate maps is measurable.
/-- Each finite random-walk partial sum is measurable when the increments are measurable. -/
theorem measurable_random_walk_partial_sum (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (n : ℕ) : Measurable (random_walk_partial_sum X n) := by
  simpa [random_walk_partial_sum] using
    Finset.measurable_sum (Finset.range n) fun i _ ↦ hX_meas i

-- Proof sketch: unfold `random_walk_partial_sum` and evaluate the empty finite sum.
/-- The zeroth partial sum of the random walk is identically zero. -/
theorem random_walk_partial_sum_zero {Ω : Type u} (X : ℕ → Ω → ℤ) :
    random_walk_partial_sum X 0 = fun _ : Ω ↦ 0 := by
  ext ω
  simp [random_walk_partial_sum]

-- Proof sketch: consider the tail event that the walk exceeds each integer level infinitely often;
-- this event is tail-measurable, so Kolmogorov's zero-one law reduces the claim to showing it has
-- positive probability, which follows from the independence and fair-sign hypotheses.
/-- Exercise 2.3.1: if `(X n)` is an independent family of fair-sign integer-valued random
variables, then the random-walk partial sums satisfy `limsup S_n = ∞` almost surely. Here
`random_walk_partial_sum X n = X 0 + ⋯ + X (n - 1)`, so this is the canonical `0`-based version of
the textbook statement. -/
theorem ae_limsup_random_walk_partial_sum_eq_top_of_independent_fair_signs (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (h_indep : iIndepFun X μ)
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, limsup (fun n ↦ (((random_walk_partial_sum X n ω : ℤ) : ℝ) : EReal)) atTop = ⊤ :=
      sorry

/-- Companion form of Exercise 2.3.1: almost surely, every integer level is crossed infinitely
often by the random-walk partial sums. This is the threshold-event reformulation of
`limsup S_n = ∞`. -/
theorem ae_infinite_partial_sum_ge_of_independent_fair_signs (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℤ) (hX_meas : ∀ n, Measurable (X n))
    (h_indep : iIndepFun X μ)
    (hX_neg : ∀ n : ℕ, μ ((X n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hX_pos : ∀ n : ℕ, μ ((X n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, ∀ M : ℤ, Set.Infinite {n : ℕ | M ≤ random_walk_partial_sum X n ω} := sorry
