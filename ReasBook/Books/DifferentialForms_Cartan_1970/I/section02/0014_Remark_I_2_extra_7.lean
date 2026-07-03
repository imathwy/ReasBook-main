import DifferentialForms_Cartan_1970.I.section02.«0004_Definition_I_2_extra_3»
import DifferentialForms_Cartan_1970.I.section02.«0013_Proposition_7_1»
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.RingTheory.PowerSeries.Derivative

-- Declarations for this item will be appended below by the statement pipeline.

open Filter FormalMultilinearSeries
open scoped ENNReal Topology PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

-- Source/core/bridge triage:
-- * source-facing: the present `PowerSeries` theorem on uniform convergence of scalar difference
--   quotients on a closed disk strictly inside the convergence radius;
-- * core/canonical: Mathlib's `FormalMultilinearSeries` analytic calculus, especially
--   `HasFPowerSeriesOnBall`, its derivative API, and the one-variable slope formulation of
--   `HasDerivAt`;
-- * bridge/view: the local `PowerSeries.radius`/`PowerSeries.sum` owner together with the nearby
--   Proposition 7.1 scalar derivative bridge for `ofScalarsSum`.

namespace PowerSeries

/-- Helper for Remark I.2-extra-7: on the disk of convergence, the ordinary derivative of the
summed scalar series is the sum of the formal derivative series. -/
lemma deriv_sum_eq_derivSeries_sum
    (S : 𝕜⟦X⟧) {z : 𝕜} (hz : ENNReal.ofReal ‖z‖ < S.radius) :
    deriv S.sum z = (d⁄dX 𝕜 S).sum z := by
  let a : ℕ → 𝕜 := fun n ↦ coeff n S
  have hderiv :
      HasDerivAt (ofScalarsSum a) (ofScalarsSum (ofScalarsDerivCoeff a) z) z := by
    -- Proposition 7.1 already identifies the scalar derivative of the summed series.
    simpa [a, PowerSeries.sum] using
      hasDerivAt_ofScalarsSum_eq_ofScalarsSum_derivCoeff (𝕜 := 𝕜) a hz
  have hsum :
      ofScalarsSum (ofScalarsDerivCoeff a) z = (d⁄dX 𝕜 S).sum z := by
    -- The source-facing derived coefficients are exactly the coefficients of `d⁄dX S`.
    simp [a, PowerSeries.sum, ofScalarsSum_eq_tsum, ofScalarsDerivCoeff, coeff_derivative,
      Nat.succ_eq_add_one, mul_comm]
  calc
    deriv S.sum z = ofScalarsSum (ofScalarsDerivCoeff a) z := by
      simpa [a, PowerSeries.sum] using hderiv.deriv
    _ = (d⁄dX 𝕜 S).sum z := hsum

/-- Helper for Remark I.2-extra-7: on the diagonal, `dslope` is the summed derivative series. -/
lemma dslope_sum_self_eq_derivSeries_sum
    (S : 𝕜⟦X⟧) {z : 𝕜} (hz : ENNReal.ofReal ‖z‖ < S.radius) :
    dslope S.sum z z = (d⁄dX 𝕜 S).sum z := by
  rw [dslope_same]
  simpa using deriv_sum_eq_derivSeries_sum S hz

/-- Helper for Remark I.2-extra-7: the summed derivative series is the shifted `tsum` of the
coefficientwise derivatives of the monomials. -/
lemma derivSeries_sum_eq_tsum_coeff_deriv_pow
    (S : 𝕜⟦X⟧) {z : 𝕜} (hz : ENNReal.ofReal ‖z‖ < S.radius) :
    (d⁄dX 𝕜 S).sum z = ∑' n : ℕ, coeff n S * deriv (fun x : 𝕜 => x ^ n) z := by
  -- TODO: identify the diagonal `tsum` with the shifted derivative-coefficient series by an
  -- explicit `tsum_nat_add` reindexing after Proposition 7.1's scalar bridge.
  sorry

/-- Helper for Remark I.2-extra-7: formal differentiation does not shrink the scalar convergence
radius. -/
lemma radius_le_radius_derivative (S : 𝕜⟦X⟧) :
    S.radius ≤ (d⁄dX 𝕜 S).radius := by
  -- TODO: recover the radius bridge from the canonical `derivSeries` radius inequality and the
  -- scalar evaluation-at-`1` comparison, without assuming a separate `CharZero` instance.
  sorry

/-- Helper for Remark I.2-extra-7: the difference quotient of the monomial `z ↦ z^n` is the
standard geometric sum. -/
lemma differenceQuotient_pow_eq_geom_sum
    {z h : 𝕜} (n : ℕ) (hh : h ≠ 0) :
    ((z + h) ^ n - z ^ n) / h =
      ∑ i ∈ Finset.range n, (z + h) ^ i * z ^ (n - 1 - i) := by
  have hgeom :
      h * (∑ i ∈ Finset.range n, (z + h) ^ i * z ^ (n - 1 - i)) =
        (z + h) ^ n - z ^ n := by
    -- Rewrite the standard factorization `x^n - y^n = (x - y) * Σ x^i y^(n-1-i)` with
    -- `x = z + h` and `y = z`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Commute.all (z + h) z).mul_geom_sum₂ n
  -- Divide the geometric-sum identity by the nonzero increment `h`.
  apply (div_eq_iff hh).2
  simpa [mul_comm] using hgeom.symm

/-- Helper for Remark I.2-extra-7: on a smaller disk, the monomial slope is bounded by the
matching derivative majorant. -/
lemma norm_dslope_pow_succ_le_q_majorant
    (n : ℕ) {r q : NNReal} {z h : 𝕜}
    (hz : ‖z‖ ≤ r) (hh : ‖h‖ < q - r) :
    ‖dslope (fun x : 𝕜 => x ^ (n + 1)) z (z + h)‖ ≤ (n + 1 : ℝ) * (q : ℝ) ^ n := by
  have hrq_real : (r : ℝ) < q := by
    have hnonneg : 0 ≤ ‖h‖ := norm_nonneg h
    linarith
  have hzq : ‖z‖ ≤ (q : ℝ) := le_trans hz (le_of_lt hrq_real)
  have hzhq : ‖z + h‖ < (q : ℝ) := by
    calc
      ‖z + h‖ ≤ ‖z‖ + ‖h‖ := norm_add_le _ _
      _ < (r : ℝ) + ((q : ℝ) - r) := add_lt_add_of_le_of_lt hz hh
      _ = q := by ring
  by_cases hh0 : h = 0
  · -- On the diagonal the slope is the derivative, so only the norm bound on `z^n` remains.
    subst hh0
    have hnat : ‖(n + 1 : 𝕜)‖ ≤ (n + 1 : ℝ) := by
      simpa [nsmul_eq_mul, norm_one] using (norm_nsmul_le (a := (1 : 𝕜)) (n := n + 1))
    calc
      ‖dslope (fun x : 𝕜 ↦ x ^ (n + 1)) z (z + 0)‖ = ‖((n + 1 : 𝕜) * z ^ n)‖ := by
        simp [dslope_same, deriv_pow_field]
      _ = ‖(n + 1 : 𝕜)‖ * ‖z‖ ^ n := by
        rw [norm_mul, norm_pow]
      _ ≤ (n + 1 : ℝ) * ‖z‖ ^ n := by
        exact mul_le_mul_of_nonneg_right hnat (pow_nonneg (norm_nonneg _) _)
      _ ≤ (n + 1 : ℝ) * (q : ℝ) ^ n := by
        gcongr
  · have hne : z + h ≠ z := by
      intro hEq
      apply hh0
      exact add_left_cancel (show z + h = z + 0 by simpa using hEq)
    have hgeom :
        dslope (fun x : 𝕜 ↦ x ^ (n + 1)) z (z + h) =
          ∑ i ∈ Finset.range (n + 1), (z + h) ^ i * z ^ (n - i) := by
      rw [dslope_of_ne _ hne, slope_def_field]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        differenceQuotient_pow_eq_geom_sum (z := z) (h := h) (n := n + 1) hh0
    -- Bound the geometric sum termwise by the common majorant `q^n`.
    rw [hgeom]
    calc
      ‖∑ i ∈ Finset.range (n + 1), (z + h) ^ i * z ^ (n - i)‖
          ≤ ∑ i ∈ Finset.range (n + 1), ‖(z + h) ^ i * z ^ (n - i)‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), (q : ℝ) ^ n := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            calc
              ‖(z + h) ^ i * z ^ (n - i)‖ = ‖z + h‖ ^ i * ‖z‖ ^ (n - i) := by
                simp [norm_mul, norm_pow]
              _ ≤ (q : ℝ) ^ i * (q : ℝ) ^ (n - i) := by
                gcongr
              _ = (q : ℝ) ^ n := by
                rw [← pow_add, Nat.add_sub_of_le hi']
      _ = (n + 1 : ℝ) * (q : ℝ) ^ n := by
            simp

/-- Helper for Remark I.2-extra-7: the second `dslope` of the monomial `x ↦ x^(n+2)` reindexes to
the first `dslope`s of the lower monomials. -/
lemma second_dslope_pow_succ_eq_reindexed_sum
    (n : ℕ) {z h : 𝕜} (hh0 : h ≠ 0) :
    dslope (fun y : 𝕜 ↦ dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z y) z (z + h) =
      ∑ j ∈ Finset.range (n + 1), dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j) := by
  -- TODO: recover the second-`dslope` reindexing by dividing the already-expanded remainder
  -- identity by `h`.
  sorry

/-- Helper for Remark I.2-extra-7: the monomial slope remainder is `h` times the reindexed second
`dslope` sum from the source proof. -/
lemma geom_sum_sub_deriv_eq_h_mul_reindexed_sum
    (n : ℕ) {z h : 𝕜} (hh0 : h ≠ 0) :
    dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z (z + h) - ((n + 2 : 𝕜) * z ^ (n + 1)) =
      h * ∑ j ∈ Finset.range (n + 1), dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j) := by
  have hne : z + h ≠ z := by
    intro hEq
    apply hh0
    exact add_left_cancel (show z + h = z + 0 by simpa using hEq)
  have hvalue :
      dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z (z + h) =
        ∑ i ∈ Finset.range (n + 2), (z + h) ^ i * z ^ (n + 1 - i) := by
    -- Rewrite the first slope by the geometric-sum identity.
    rw [dslope_of_ne _ hne, slope_def_field]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      differenceQuotient_pow_eq_geom_sum (z := z) (h := h) (n := n + 2) hh0
  -- Expand the remainder and then reindex the `i = j + 1` terms.
  calc
    dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z (z + h) - ((n + 2 : 𝕜) * z ^ (n + 1))
        = (∑ i ∈ Finset.range (n + 2), (z + h) ^ i * z ^ (n + 1 - i))
            - ∑ i ∈ Finset.range (n + 2), z ^ (n + 1) := by
              rw [hvalue]
              simp
    _ = ∑ i ∈ Finset.range (n + 2), ((z + h) ^ i * z ^ (n + 1 - i) - z ^ (n + 1)) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i ∈ Finset.range (n + 2), (((z + h) ^ i - z ^ i) * z ^ (n + 1 - i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi' : i ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hzpow : z ^ (n + 1) = z ^ i * z ^ (n + 1 - i) := by
            symm
            rw [← pow_add, Nat.add_sub_of_le hi']
          rw [hzpow, ← sub_mul]
    _ = ∑ j ∈ Finset.range (n + 1), (((z + h) ^ (j + 1) - z ^ (j + 1)) * z ^ (n - j)) := by
          rw [Finset.sum_range_succ']
          simp
    _ = ∑ j ∈ Finset.range (n + 1),
          (h * dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h)) * z ^ (n - j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hterm :
                h * dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) =
                  (z + h) ^ (j + 1) - z ^ (j + 1) := by
              simpa [smul_eq_mul] using
                (sub_smul_dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h))
            rw [← hterm]
    _ = h * ∑ j ∈ Finset.range (n + 1),
          dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring

/-- Helper for Remark I.2-extra-7: the linear weights in the reindexed finite sum collapse to the
expected `(∑ i < n + 2, i) * q^n` factor. -/
lemma reindexed_linear_weight_sum_eq
    (n : ℕ) (q : NNReal) :
    ∑ j ∈ Finset.range (n + 1), ((j + 1 : ℝ) * (q : ℝ) ^ j * (q : ℝ) ^ (n - j)) =
      (((Finset.range (n + 2)).sum fun i ↦ (i : ℝ)) * (q : ℝ) ^ n) := by
  calc
    ∑ j ∈ Finset.range (n + 1), ((j + 1 : ℝ) * (q : ℝ) ^ j * (q : ℝ) ^ (n - j))
        = ∑ j ∈ Finset.range (n + 1), ((j + 1 : ℝ) * (q : ℝ) ^ n) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            calc
              ((j + 1 : ℝ) * (q : ℝ) ^ j * (q : ℝ) ^ (n - j))
                  = (j + 1 : ℝ) * ((q : ℝ) ^ j * (q : ℝ) ^ (n - j)) := by
                      rw [mul_assoc]
              _ = (j + 1 : ℝ) * (q : ℝ) ^ n := by
                    rw [← pow_add, Nat.add_sub_of_le hj']
    _ = (∑ j ∈ Finset.range (n + 1), (j + 1 : ℝ)) * (q : ℝ) ^ n := by
          rw [Finset.sum_mul]
    _ = (((Finset.range (n + 2)).sum fun i ↦ (i : ℝ)) * (q : ℝ) ^ n) := by
          congr 1
          symm
          rw [Finset.sum_range_succ']
          simp

lemma norm_dslope_pow_succ_sub_deriv_monomial_le_mul_norm
    (n : ℕ) {r q : NNReal} {z h : 𝕜}
    (hz : ‖z‖ ≤ r) (hh : ‖h‖ < q - r) :
    ‖dslope (fun x : 𝕜 => x ^ (n + 2)) z (z + h) - ((n + 2 : 𝕜) * z ^ (n + 1))‖ ≤
      ‖h‖ * (((Finset.range (n + 2)).sum fun i ↦ (i : ℝ)) * (q : ℝ) ^ n) := by
  have hrq_real : (r : ℝ) < q := by
    have hnonneg : 0 ≤ ‖h‖ := norm_nonneg h
    linarith
  have hzq : ‖z‖ ≤ (q : ℝ) := le_trans hz (le_of_lt hrq_real)
  by_cases hh0 : h = 0
  · -- On the diagonal the slope equals the derivative, so the remainder is exactly zero.
    subst hh0
    simp [dslope_same]
  · -- Replace the remainder by the explicit `h`-multiple from the source proof.
    rw [geom_sum_sub_deriv_eq_h_mul_reindexed_sum (n := n) (z := z) (h := h) hh0]
    calc
      ‖h * ∑ j ∈ Finset.range (n + 1), dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j)‖
          = ‖h‖ *
              ‖∑ j ∈ Finset.range (n + 1),
                  dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j)‖ := by
                    rw [norm_mul]
      _ ≤ ‖h‖ *
            ∑ j ∈ Finset.range (n + 1),
              ‖dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j)‖ := by
                gcongr
                exact norm_sum_le _ _
      _ ≤ ‖h‖ *
            ∑ j ∈ Finset.range (n + 1),
              ((j + 1 : ℝ) * (q : ℝ) ^ j * (q : ℝ) ^ (n - j)) := by
                gcongr with j hj
                calc
                  ‖dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j)‖
                      = ‖dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h)‖ * ‖z‖ ^ (n - j) := by
                          simp [norm_mul, norm_pow]
                  _ ≤ ((j + 1 : ℝ) * (q : ℝ) ^ j) * (q : ℝ) ^ (n - j) := by
                        gcongr
                        exact norm_dslope_pow_succ_le_q_majorant (n := j) (z := z) (h := h) hz hh
      _ = ‖h‖ * (((Finset.range (n + 2)).sum fun i ↦ (i : ℝ)) * (q : ℝ) ^ n) := by
            rw [reindexed_linear_weight_sum_eq]

/-- Helper for Remark I.2-extra-7: each coefficient-weighted monomial slope converges uniformly on
the closed inner disk to its derivative term. -/
lemma tendstoUniformlyOn_weighted_dslope_pow
    (a : 𝕜) (n : ℕ) {r q : NNReal}
    (hrq : r < q) :
    TendstoUniformlyOn
      (fun h z ↦ a * dslope (fun x : 𝕜 => x ^ n) z (z + h))
      (fun z ↦ a * deriv (fun x : 𝕜 => x ^ n) z)
      (𝓝 (0 : 𝕜))
      (Metric.closedBall (0 : 𝕜) r) := by
  -- TODO: combine the explicit `O(‖h‖)` bound with `Metric.tendstoUniformlyOn_iff`, splitting the
  -- low-degree cases `n = 0, 1` from the general `n = m + 2` remainder estimate.
  sorry

/-- Helper for Remark I.2-extra-7: every finite prefix of the coefficientwise slope series
converges uniformly to the corresponding finite derivative prefix. -/
lemma tendstoUniformlyOn_dslope_monomial_prefix
    (S : 𝕜⟦X⟧) {r q : NNReal}
    (hrq : r < q) :
    ∀ N,
      TendstoUniformlyOn
        (fun h z ↦ ∑ n ∈ Finset.range N, coeff n S * dslope (fun x : 𝕜 => x ^ n) z (z + h))
        (fun z ↦ ∑ n ∈ Finset.range N, coeff n S * deriv (fun x : 𝕜 => x ^ n) z)
        (𝓝 (0 : 𝕜))
        (Metric.closedBall (0 : 𝕜) r) := by
  -- TODO: prove the prefix statement by induction once the one-term weighted convergence is
  -- available.
  sorry

/-- Helper for Remark I.2-extra-7: away from the diagonal, the slope of the summed power series
is obtained by subtracting the two convergent scalar expansions termwise and dividing by `h`. -/
lemma hasSum_coeff_dslope_pow_off_diagonal
    (S : 𝕜⟦X⟧) {r q : NNReal}
    (hqS : (q : ℝ≥0∞) < S.radius)
    {z h : 𝕜} (hz : ‖z‖ ≤ r) (hh : ‖h‖ < q - r) (hh0 : h ≠ 0) :
    HasSum
      (fun n : ℕ ↦ coeff n S * dslope (fun x : 𝕜 => x ^ n) z (z + h))
      (dslope S.sum z (z + h)) := by
  -- TODO: subtract the two scalar `HasSum`s at `z + h` and `z`, divide by `h`, and rewrite each
  -- term to `coeff n S * dslope (fun x ↦ x^n) z (z+h)`.
  sorry

/-- Helper for Remark I.2-extra-7: within a smaller disk, the slope of the summed power series is
the sum of the coefficientwise monomial slopes. -/
lemma dslope_sum_eq_tsum_coeff_dslope_pow
    (S : 𝕜⟦X⟧) {r q : NNReal}
    (hqS : (q : ℝ≥0∞) < S.radius)
    {z h : 𝕜} (hz : ‖z‖ ≤ r) (hh : ‖h‖ < q - r) :
    dslope S.sum z (z + h) =
      ∑' n : ℕ, coeff n S * dslope (fun x : 𝕜 => x ^ n) z (z + h) := by
  -- TODO: split into the diagonal branch `h = 0` and the off-diagonal `HasSum` branch.
  sorry

/-- Canonical `dslope` reformulation of Remark I.2-extra-7: on every closed disk
`‖z‖ ≤ r` strictly inside the radius of convergence, the slope function
`h ↦ dslope S.sum z (z + h)` converges uniformly to the summed formal derivative. -/
theorem tendstoUniformlyOn_dslope_sum
    (S : 𝕜⟦X⟧) {r : NNReal}
    (hr : (r : ℝ≥0∞) < S.radius) :
    TendstoUniformlyOn
      (fun h z ↦ dslope S.sum z (z + h))
      (d⁄dX 𝕜 S).sum
      (𝓝 (0 : 𝕜))
      (Metric.closedBall (0 : 𝕜) r) := by
  -- TODO: close the source-faithful `ε/3` argument after the coefficientwise slope series, the
  -- derivative bridge, and the prefix convergence have all been certified.
  sorry

/-- Remark I.2-extra-7, source-facing statement over the scalar `PowerSeries` owner: on every
closed disk `‖z‖ ≤ r` strictly inside the radius of convergence, the difference quotients of the
summed power series converge uniformly to the sum of the formal derivative power series. -/
theorem tendstoUniformlyOn_differenceQuotient_sum
    (S : 𝕜⟦X⟧) {r : NNReal}
    (hr : (r : ℝ≥0∞) < S.radius) :
    TendstoUniformlyOn
      (fun h z ↦ (S.sum (z + h) - S.sum z) / h)
      (d⁄dX 𝕜 S).sum
      (𝓝[≠] (0 : 𝕜))
      (Metric.closedBall (0 : 𝕜) r) := by
  have hds := tendstoUniformlyOn_dslope_sum S hr
  have hds' : TendstoUniformlyOn
      (fun h z ↦ dslope S.sum z (z + h))
      (d⁄dX 𝕜 S).sum
      (𝓝[≠] (0 : 𝕜))
      (Metric.closedBall (0 : 𝕜) r) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at hds ⊢
    exact hds.mono_left inf_le_left
  refine hds'.congr ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  intro z hz
  have hh0 : h ≠ 0 := by
    simpa using hh
  have hne : z + h ≠ z := by
    intro hEq
    apply hh0
    exact add_left_cancel (show z + h = z + 0 by simpa using hEq)
  calc
    dslope S.sum z (z + h) = slope S.sum z (z + h) := dslope_of_ne S.sum hne
    _ = (S.sum (z + h) - S.sum z) / h := by
      rw [slope_def_field]
      congr 1
      abel

end PowerSeries
