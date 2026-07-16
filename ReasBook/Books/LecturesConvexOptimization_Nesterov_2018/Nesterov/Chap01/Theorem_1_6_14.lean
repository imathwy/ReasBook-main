import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Primary domain:
* scalar one-step contraction factors and radius recurrences for locally optimal gradient steps

Relevant owner-style declarations sampled before refining:
* `IsMinOn` in mathlib, the canonical owner predicate for an attained minimizer of a real-valued
  function on a set
* `HasGeometricRateOfConvergence` and
  `HasGeometricRateOfConvergence.of_step_bound` in `Definition_1_2_6.lean`
* `gradientMethod_dist_le_optimal_geometric_rate` in `Chap02/Theorem_2_17.lean`, the later
  owner-style optimal constant-step result
* the schedule type `(ℕ → ℝ)` recalled in `Definition_1_6_2.lean`

Source/core/bridge triage:
* source-facing: the step-dependent coefficients `a_k(h)` and `b_k(h)`, the optimal-step
  minimizer condition, the strict radius invariance, and the displayed recurrences and bounds
* core/canonical: `IsMinOn` for `h_k^*` and `HasGeometricRateOfConvergence` for the transformed
  gap sequence
* bridge/view: the radius owner `localGradientRadius μ M = 2 * μ / M`, the scaled radius
  `a_k = (M / (L + μ)) r_k`, and the gap ratio `r_k / ((2 * μ / M) - r_k)`

Best owner abstraction:
* `IsMinOn` for the source minimizer `h_k^*`, paired with `HasGeometricRateOfConvergence` for the
  intrinsic gap-ratio sequence

Primitive data:
* the radius sequence `r`
* the step schedule `h`
* the parameters `μ`, `L`, and the positive radius/Lipschitz datum `M : NNRealˣ`
* the initial source bound `0 < r_0 < localGradientRadius μ M`
* nonnegativity of the radius sequence, from which positivity of later radii is derived under
  the optimal-step hypotheses
* the one-step estimate
  `r_{k+1} ≤ max { a_k(h_k), b_k(h_k) } * r_k`

Derived API:
* `h_k^* = 2 / (L + μ)`
* strict invariance `r_{k+1} < r_k < localGradientRadius μ M`
* positivity of every later radius, obtained from the initial positivity and nonnegativity data
* the explicit radius recurrence
* the scaled recurrence for `a_k = (M / (L + μ)) r_k`
* the owner geometric-rate statement for the gap ratio
* the displayed bounds `(1.2.31)` and `(1.2.32)`

This file keeps those textbook scalar expressions as local notation inside the theorem layer,
uses `IsMinOn` only for the source minimizer layer, and lets the downstream recurrence lemmas
consume the derived textbook identity `h_k = 2 / (L + μ)` rather than repeating the minimizer
witness. The bridge to `HasGeometricRateOfConvergence` remains public instead of a private
helper. The positive denominator datum is carried canonically by `M : NNRealˣ` and the owner
`localGradientRadius`, rather than being recovered only from side inequalities. -/

section

variable {r h : ℕ → ℝ} {μ L : ℝ} {M : NNRealˣ}

/-- The local radius `2 * μ / M` from Theorem 1.6.14, with positivity of `M` encoded in
`M : NNRealˣ`. -/
def localGradientRadius (μ : ℝ) (M : NNRealˣ) : ℝ :=
  2 * μ / (M : ℝ)

/-- Expanding `localGradientRadius μ M` gives the textbook radius `2 * μ / M`. -/
theorem localGradientRadius_def (μ : ℝ) (M : NNRealˣ) :
    localGradientRadius μ M = 2 * μ / (M : ℝ) :=
  rfl

local notation "radius" => localGradientRadius μ M
local notation "step" => (2 / (L + μ) : ℝ)
local notation "q" => (2 * μ / (L + μ) : ℝ)
local notation "positiveSteps" => Set.Ioi (0 : ℝ)
local notation "aCoeff" =>
  fun k hStep ↦ 1 - hStep * (μ - (M : ℝ) * r k / 2)
local notation "bCoeff" =>
  fun k hStep ↦ hStep * (L + (M : ℝ) * r k / 2) - 1
local notation "bound" =>
  fun k hStep ↦ max (aCoeff k hStep) (bCoeff k hStep)
local notation "scaled" => fun k ↦ ((M : ℝ) / (L + μ)) * r k
local notation "gap" => fun k ↦ r k / (radius - r k)

/-- Helper for Theorem 1.6.14: the two affine radius factors cross exactly at the textbook step
`2 / (L + μ)`. -/
lemma localGradient_aCoeff_eq_bCoeff_iff
    (hLμ : 0 < L + μ) {k : ℕ} {hStep : ℝ} :
    aCoeff k hStep = bCoeff k hStep ↔ hStep = step := by
  constructor
  · intro hEq
    -- The shared `M r_k / 2` terms cancel, leaving a scalar linear equation in `hStep`.
    have hmul : hStep * (L + μ) = 2 := by
      linarith
    apply (eq_div_iff hLμ.ne').2
    linarith
  · intro hStep_eq
    subst hStep
    -- Substituting the textbook step makes the two branches coincide.
    field_simp [hLμ.ne']
    ring_nf

/-- Helper for Theorem 1.6.14: evaluating the maximum branch at the textbook step gives the
common affine value `((L - μ) + M r_k) / (L + μ)`. -/
lemma localGradient_bound_at_step
    (hLμ : 0 < L + μ) (k : ℕ) :
    bound k step = ((L - μ) + (M : ℝ) * r k) / (L + μ) := by
  have hcross : aCoeff k step = bCoeff k step :=
    (localGradient_aCoeff_eq_bCoeff_iff (r := r) (μ := μ) (L := L) (M := M) hLμ).2 rfl
  -- At the crossing point the maximum collapses to either branch.
  change max (aCoeff k step) (bCoeff k step) = ((L - μ) + (M : ℝ) * r k) / (L + μ)
  rw [max_eq_left hcross.ge]
  field_simp [hLμ.ne']
  ring_nf

/-- If `0 ≤ r_k < 2 * μ / M` and `h_k^*` minimizes `max {a_k(h), b_k(h)}` over positive
step sizes, then `h_k^* = 2 / (L + μ)`. -/
theorem localGradientRadiusBound_optimalStep_eq
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} {hStar : ℝ}
    (hrk_nonneg : 0 ≤ r k) (hrk_lt : r k < radius)
    (hopt : IsMinOn (bound k) positiveSteps hStar) :
    hStar = step := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hslope_left : 0 < μ - (M : ℝ) * r k / 2 := by
    -- The source radius constraint makes the decreasing branch genuinely decreasing.
    unfold localGradientRadius at hrk_lt
    have hrk_mul : r k * (M : ℝ) < 2 * μ := by
      exact (lt_div_iff₀ hM).mp hrk_lt
    nlinarith [hrk_mul]
  have hstep_pos : 0 < step := by
    positivity
  have hcross : aCoeff k step = bCoeff k step :=
    (localGradient_aCoeff_eq_bCoeff_iff (r := r) (μ := μ) (L := L) (M := M) hLμ).2 rfl
  have hmin := isMinOn_iff.mp hopt
  have hstep_mem : step ∈ positiveSteps := by
    change 0 < step
    exact hstep_pos
  have hstep_le : bound k hStar ≤ bound k step := by
    exact hmin step hstep_mem
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hbranch_lt : bCoeff k hStar < aCoeff k hStar := by
      have : hStar * (L + μ) < 2 := by
        nlinarith [hlt, hLμ]
      linarith
    have hbound_star : bound k hStar = aCoeff k hStar := by
      change max (aCoeff k hStar) (bCoeff k hStar) = aCoeff k hStar
      rw [max_eq_left hbranch_lt.le]
    have hbound_step : bound k step = aCoeff k step := by
      change max (aCoeff k step) (bCoeff k step) = aCoeff k step
      rw [max_eq_left hcross.ge]
    have hbetter : aCoeff k step < aCoeff k hStar := by
      -- Left of the crossing, the maximum is the decreasing branch.
      nlinarith [hlt, hslope_left]
    have : bound k step < bound k hStar := by
      simpa [hbound_star, hbound_step] using hbetter
    exact not_lt_of_ge hstep_le this
  · have hbranch_gt : aCoeff k hStar < bCoeff k hStar := by
      have : 2 < hStar * (L + μ) := by
        nlinarith [hgt, hLμ]
      linarith
    have hbound_star : bound k hStar = bCoeff k hStar := by
      change max (aCoeff k hStar) (bCoeff k hStar) = bCoeff k hStar
      rw [max_eq_right hbranch_gt.le]
    have hbound_step : bound k step = bCoeff k step := by
      change max (aCoeff k step) (bCoeff k step) = bCoeff k step
      rw [max_eq_right hcross.le]
    have hbetter : bCoeff k step < bCoeff k hStar := by
      -- Right of the crossing, the maximum is the increasing branch.
      have hslope_right : 0 < L + (M : ℝ) * r k / 2 := by
        nlinarith [hμ, hμL, hrk_nonneg]
      nlinarith [hgt, hslope_right]
    have : bound k step < bound k hStar := by
      simpa [hbound_star, hbound_step] using hbetter
    exact not_lt_of_ge hstep_le this

section Recurrence

variable (hμ : 0 < μ) (hμL : μ ≤ L)
variable (hstep : ∀ k : ℕ, h k = step)
variable (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)

/-- Under `0 < μ` and `μ ≤ L`, so that `L + μ > 0`, once the step schedule is identified with
the textbook value `h_k = 2 / (L + μ)`, the source radius estimate becomes
`r_{k+1} ≤ ((L - μ) r_k + M r_k^2) / (L + μ)`. -/
theorem localGradientRadius_recurrence_of_optimal_step
    (k : ℕ) :
    r (k + 1) ≤ ((L - μ) * r k + (M : ℝ) * r k ^ (2 : ℕ)) / (L + μ) := sorry

/-- Under `0 < μ` and `μ ≤ L`, so that the scaling by `L + μ` is nondegenerate, for the scaled
radii `a_k = (M / (L + μ)) r_k`, substituting the textbook step `h_k = 2 / (L + μ)` turns the
source recurrence into
`a_{k+1} ≤ (1 - q + a_k) a_k` with `q = 2 * μ / (L + μ)`. -/
theorem localGradientScaledRadius_recurrence_of_optimal_step
    (k : ℕ) :
    scaled (k + 1) ≤ (1 - q + scaled k) * scaled k := sorry

end Recurrence

section OptimalStep

variable (hμ : 0 < μ) (hμL : μ ≤ L)
variable (hr0 : 0 < r 0 ∧ r 0 < radius)
variable (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
variable (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
variable (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)

/-- If the sequence `r` is nonnegative, `0 < r_0 < 2 * μ / M`, and each `h_k` is the source
minimizer `h_k^*`, then the optimal-step identity `h_k = 2 / (L + μ)` propagates along the
radius-invariant region `r_k < 2 * μ / M`. -/
theorem localGradientRadius_strict_decay_of_optimal_step
    (k : ℕ) :
    h k = step ∧ r k < radius := sorry

/-- Helper for Theorem 1.6.14: under the optimal-step schedule, the gap ratio contracts by the
factor `1 / (1 + q)` in one step. -/
lemma localGradientGap_step_bound_of_optimal_step
    (k : ℕ) :
    gap (k + 1) ≤ gap k / (1 + q) := sorry

/-- The owner geometric-rate statement for the gap ratio
`r_k / ((2 * μ / M) - r_k)` under the source optimal-step choice, with positivity of each radius
derived from `0 < r_0 < 2 * μ / M`, nonnegativity, and the strict-decay layer above. -/
theorem localGradientGap_hasGeometricRate_of_optimal_step
    :
    HasGeometricRateOfConvergence gap (q / (1 + q)) (gap 0) := sorry

-- Proof sketch: combine the geometric-rate statement for `gap k = r k / (radius - r k)` with
-- the algebraic identity `radius / r k - 1 = 1 / gap k`, then rewrite the textbook recurrence
-- into the displayed reciprocal-gap inequality.
/-- Theorem 1.6.14 (1): if each `h_k` is the source minimizer `h_k^*` of
`max {a_k(h), b_k(h)}`, the radius sequence is nonnegative, and `0 < r_0 < 2 * μ / M`, then
the reciprocal-gap estimate `(1.2.31)` holds:
`radius / r_k - 1 ≥ (1 + q)^k (radius / r_0 - 1)`. -/
theorem localGradientScaledRadius_reciprocal_gap_lower_bound_of_optimal_step
    (k : ℕ) :
    radius / r k - 1 ≥ (1 + q) ^ k * (radius / r 0 - 1) := by
    -- TODO: The current formal hypotheses allow `r (k + 1) = 0` because `hrec` is only an
    -- upper bound. Then `radius / r (k + 1) - 1 = -1` in Lean, so the displayed reciprocal-gap
    -- inequality is false without an additional positivity or exact-recurrence assumption.
    sorry

-- Proof sketch: start from the reciprocal-gap estimate `(1.2.31)` and solve the resulting
-- inequality for `r k`. Multiplying by `M / (L + μ)` rewrites the bound in terms of
-- `scaled k = (M / (L + μ)) r k`.
/-- Theorem 1.6.14 (2): under the same optimal-step hypotheses, the scaled radii satisfy the
first explicit upper bound from `(1.2.32)`:
`a_k ≤ (q r_0) / (r_0 + (1 + q)^k (radius - r_0))`. -/
theorem localGradientScaledRadius_first_upper_bound_of_optimal_step
    (k : ℕ) :
    scaled k ≤ (q * r 0) / (r 0 + (1 + q) ^ k * (radius - r 0)) := sorry

-- Proof sketch: derive the first bound in `(1.2.32)` from `(1.2.31)`, then bound the
-- denominator below by `(radius - r 0) * (1 + q)^k` to obtain the geometric upper estimate.
/-- Theorem 1.6.14 (3): under the same optimal-step hypotheses, the scaled radii satisfy the
second explicit upper bound from `(1.2.32)`:
`a_k ≤ ((q r_0) / (radius - r_0)) (1 / (1 + q))^k`. -/
theorem localGradientScaledRadius_second_upper_bound_of_optimal_step
    (k : ℕ) :
    scaled k ≤ ((q * r 0) / (radius - r 0)) * (1 / (1 + q)) ^ k := sorry

end OptimalStep

end

end
