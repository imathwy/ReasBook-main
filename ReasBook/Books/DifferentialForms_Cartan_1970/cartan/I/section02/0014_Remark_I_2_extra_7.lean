import DifferentialForms_Cartan_1970.cartan.I.section02.«0004_Definition_I_2_extra_3»
import DifferentialForms_Cartan_1970.cartan.I.section02.«0013_Proposition_7_1»
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

omit [CompleteSpace 𝕜] in
/-- Helper for Remark I.2-extra-7: the scalar owner of the formal derivative has the textbook
derived coefficients. -/
lemma derivativeOwner_eq_ofScalarsDerivCoeff (S : 𝕜⟦X⟧) :
    ofScalars 𝕜 (fun n ↦ coeff n ((d⁄dX 𝕜 S))) =
      ofScalars 𝕜 (ofScalarsDerivCoeff fun n ↦ coeff n S) := by
  ext n
  simp [ofScalarsDerivCoeff, coeff_derivative, mul_comm]

/-- Helper for Remark I.2-extra-7: the summed derivative series is the shifted `tsum` of the
coefficientwise derivatives of the monomials. -/
lemma derivSeries_sum_eq_tsum_coeff_deriv_pow
    (S : 𝕜⟦X⟧) {z : 𝕜} (hz : ENNReal.ofReal ‖z‖ < S.radius) :
    (d⁄dX 𝕜 S).sum z = ∑' n : ℕ, coeff n S * deriv (fun x : 𝕜 => x ^ n) z := by
  let a : ℕ → 𝕜 := fun n ↦ coeff n S
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 (ofScalarsDerivCoeff a)
  have hz' : ENNReal.ofReal ‖z‖ < p.radius := by
    have hradius : S.radius ≤ p.radius := by
      let q : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
      have hcomp :
          ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
            q.derivSeries) = p := by
        simpa [q, p, a] using apply_one_comp_derivSeries_eq_ofScalars_derivCoeff a
      calc
        S.radius = q.radius := by simp [q, a, PowerSeries.radius]
        _ ≤ q.derivSeries.radius := q.radius_le_radius_derivSeries
        _ ≤
            ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
              q.derivSeries).radius :=
          radius_le_radius_continuousLinearMap_comp _ _
        _ = p.radius := by
              simp [hcomp]
    exact lt_of_lt_of_le hz hradius
  have hzp : z ∈ Metric.eball (0 : 𝕜) p.radius := by
    apply mem_eball_zero_iff.2
    simpa using hz'
  have hsumm :
      Summable (fun n : ℕ ↦ z ^ n * ofScalarsDerivCoeff a n) := by
    simpa [p, ofScalars_apply_eq, mul_comm] using p.summable hzp
  have hshifted :
      HasSum (fun n : ℕ ↦ z ^ n * ofScalarsDerivCoeff a n) ((d⁄dX 𝕜 S).sum z) := by
    have htsum :
        ∑' n : ℕ, z ^ n * ofScalarsDerivCoeff a n = (d⁄dX 𝕜 S).sum z := by
      calc
        ∑' n : ℕ, z ^ n * ofScalarsDerivCoeff a n
            = ∑' n : ℕ, ofScalarsDerivCoeff a n * z ^ n := by
              refine tsum_congr ?_
              intro n
              rw [mul_comm]
        _ = (d⁄dX 𝕜 S).sum z := by
          rw [PowerSeries.sum, ofScalarsSum_eq_tsum]
          refine tsum_congr ?_
          intro n
          simp [a, ofScalarsDerivCoeff, coeff_derivative, mul_comm]
    simpa [htsum] using hsumm.hasSum
  have hcoeff :
      ∑' n : ℕ, coeff n S * deriv (fun x : 𝕜 => x ^ n) z = (d⁄dX 𝕜 S).sum z := by
    let f : ℕ → 𝕜 := fun n ↦ coeff n S * deriv (fun x : 𝕜 => x ^ n) z
    have hshifted' :
        HasSum (fun n : ℕ ↦ f (n + 1)) ((d⁄dX 𝕜 S).sum z) := by
      simpa [f, a, ofScalarsDerivCoeff, deriv_pow_field, Nat.succ_eq_add_one, mul_comm,
        mul_left_comm, mul_assoc] using hshifted
    have hsummf : Summable (fun n : ℕ ↦ f (n + 1)) := hshifted'.summable
    have hsplit := hsummf.sum_add_tsum_nat_add' (k := 1)
    have hf0 : f 0 = 0 := by
      simp [f]
    calc
      ∑' n : ℕ, f n = ∑ i ∈ Finset.range 1, f i + ∑' i : ℕ, f (i + 1) := by
            simpa using hsplit.symm
      _ = (d⁄dX 𝕜 S).sum z := by
            simp [hf0, hshifted'.tsum_eq]
  exact hcoeff.symm

omit [CompleteSpace 𝕜] in
/-- Helper for Remark I.2-extra-7: formal differentiation does not shrink the scalar convergence
radius. -/
lemma radius_le_radius_derivative (S : 𝕜⟦X⟧) :
    S.radius ≤ (d⁄dX 𝕜 S).radius := by
  let a : ℕ → 𝕜 := fun n ↦ coeff n S
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  -- Move first to the canonical `derivSeries` radius, then evaluate at `1` to recover the scalar
  -- derivative-series owner.
  calc
    S.radius = p.radius := by simp [p, a, PowerSeries.radius]
    _ ≤ p.derivSeries.radius := p.radius_le_radius_derivSeries
    _ ≤
        ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
          p.derivSeries).radius :=
      radius_le_radius_continuousLinearMap_comp _ _
    _ = (d⁄dX 𝕜 S).radius := by
      have howner :
          ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries p.derivSeries)
            = ofScalars 𝕜 (fun n ↦ coeff n ((d⁄dX 𝕜 S))) := by
        calc
          ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries p.derivSeries)
              = ofScalars 𝕜 (ofScalarsDerivCoeff a) := by
                  simpa [p, a] using apply_one_comp_derivSeries_eq_ofScalars_derivCoeff a
          _ = ofScalars 𝕜 (fun n ↦ coeff n ((d⁄dX 𝕜 S))) := by
                ext n
                simp [a, ofScalarsDerivCoeff, coeff_derivative, mul_comm]
      simpa [PowerSeries.radius] using congrArg FormalMultilinearSeries.radius howner

omit [CompleteSpace 𝕜] in
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

omit [CompleteSpace 𝕜] in
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
        simp [dslope_same]
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

omit [CompleteSpace 𝕜] in
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

omit [CompleteSpace 𝕜] in
/-- Helper for Remark I.2-extra-7: the second `dslope` of the monomial `x ↦ x^(n+2)` reindexes to
the first `dslope`s of the lower monomials. -/
lemma second_dslope_pow_succ_eq_reindexed_sum
    (n : ℕ) {z h : 𝕜} (hh0 : h ≠ 0) :
    dslope (fun y : 𝕜 ↦ dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z y) z (z + h) =
      ∑ j ∈ Finset.range (n + 1), dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j) := by
  -- Divide the already-established remainder identity by the nonzero increment `h`.
  have hne : z + h ≠ z := by
    intro hEq
    apply hh0
    exact add_left_cancel (show z + h = z + 0 by simpa using hEq)
  rw [dslope_of_ne _ hne, slope_def_field]
  have hzsub : z + h - z = h := by ring
  rw [hzsub]
  apply (div_eq_iff hh0).2
  calc
    dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z (z + h) - dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z z
        = dslope (fun x : 𝕜 ↦ x ^ (n + 2)) z (z + h) - ((n + 2 : 𝕜) * z ^ (n + 1)) := by
            simp [dslope_same]
    _ = h * ∑ j ∈ Finset.range (n + 1), dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j) :=
          geom_sum_sub_deriv_eq_h_mul_reindexed_sum (n := n) (z := z) (h := h) hh0
    _ =
        (∑ j ∈ Finset.range (n + 1),
          dslope (fun x : 𝕜 ↦ x ^ (j + 1)) z (z + h) * z ^ (n - j)) * h := by
          rw [mul_comm]

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

omit [CompleteSpace 𝕜] in
/-- Helper for Remark I.2-extra-7: the quadratic-and-higher monomial slope remainder is bounded
linearly by `‖h‖` on the smaller closed disk. -/
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

omit [CompleteSpace 𝕜] in
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
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε εpos
  rcases n with _ | n
  · -- The constant monomial contributes identically zero.
    refine Filter.Eventually.of_forall ?_
    intro h z hz
    by_cases hh0 : h = 0
    · subst hh0
      simpa [dslope_same] using εpos
    · have hne : z + h ≠ z := by
        intro hEq
        apply hh0
        exact add_left_cancel (show z + h = z + 0 by simpa using hEq)
      rw [dist_eq_norm, dslope_of_ne _ hne, slope_def_field]
      simpa [pow_zero] using εpos
  · rcases n with _ | m
    · -- The linear monomial has slope equal to derivative everywhere.
      refine Filter.Eventually.of_forall ?_
      intro h z hz
      by_cases hh0 : h = 0
      · subst hh0
        simpa [dslope_same] using εpos
      · have hne : z + h ≠ z := by
          intro hEq
          apply hh0
          exact add_left_cancel (show z + h = z + 0 by simpa using hEq)
        have hdslope : dslope (fun x : 𝕜 ↦ x ^ 1) z (z + h) = 1 := by
          rw [dslope_of_ne _ hne, slope_def_field]
          field_simp [hh0]
        rw [dist_eq_norm, hdslope]
        simp [εpos]
    · let C : ℝ := (((Finset.range (m + 2)).sum fun i ↦ (i : ℝ)) * (q : ℝ) ^ m)
      let δ : ℝ := min (q - r) (ε / (‖a‖ * C + 1))
      have hδ_pos : 0 < δ := by
        have h1 : 0 < (q : ℝ) - r := by
          have hrq_real : (r : ℝ) < q := by exact_mod_cast hrq
          linarith
        have h2 : 0 < ε / (‖a‖ * C + 1) := by positivity
        exact lt_min h1 h2
      refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : 𝕜) hδ_pos) ?_
      intro h hh z hz
      have hhδ : ‖h‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hh
      have hzr : ‖z‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hhqr : ‖h‖ < q - r := lt_of_lt_of_le hhδ (min_le_left _ _)
      have hbound :=
        norm_dslope_pow_succ_sub_deriv_monomial_le_mul_norm (n := m) (z := z) (h := h) hzr hhqr
      have hlt : ‖a‖ * (‖h‖ * C) < ε := by
        have hhε : ‖h‖ < ε / (‖a‖ * C + 1) := lt_of_lt_of_le hhδ (min_le_right _ _)
        have hden : 0 < ‖a‖ * C + 1 := by positivity
        have hhε' : ‖h‖ * (‖a‖ * C + 1) < ε := by
          exact (lt_div_iff₀ hden).mp hhε
        have hcoef : ‖h‖ * (‖a‖ * C) ≤ ‖h‖ * (‖a‖ * C + 1) := by
          have haux : ‖a‖ * C ≤ ‖a‖ * C + 1 := by linarith
          exact mul_le_mul_of_nonneg_left haux (norm_nonneg h)
        have hrew : ‖a‖ * (‖h‖ * C) = ‖h‖ * (‖a‖ * C) := by ring
        rw [hrew]
        exact lt_of_le_of_lt hcoef hhε'
      -- The quadratic-and-higher remainder estimate is linear in `‖h‖`, so it closes the
      -- uniform convergence bound on the whole closed ball.
      calc
        dist (a * deriv (fun x : 𝕜 => x ^ (m + 2)) z)
            (a * dslope (fun x : 𝕜 => x ^ (m + 2)) z (z + h))
            = ‖a‖ *
                ‖dslope (fun x : 𝕜 => x ^ (m + 2)) z (z + h) - ((m + 2 : 𝕜) * z ^ (m + 1))‖ := by
                  calc
                    dist (a * deriv (fun x : 𝕜 => x ^ (m + 2)) z)
                        (a * dslope (fun x : 𝕜 => x ^ (m + 2)) z (z + h))
                        = ‖a * (deriv (fun x : 𝕜 => x ^ (m + 2)) z -
                            dslope (fun x : 𝕜 => x ^ (m + 2)) z (z + h))‖ := by
                              rw [dist_eq_norm, ← mul_sub]
                    _ = ‖a‖ *
                        ‖deriv (fun x : 𝕜 => x ^ (m + 2)) z -
                          dslope (fun x : 𝕜 => x ^ (m + 2)) z (z + h)‖ := by
                            rw [norm_mul]
                    _ = ‖a‖ *
                        ‖dslope (fun x : 𝕜 => x ^ (m + 2)) z (z + h) -
                          deriv (fun x : 𝕜 => x ^ (m + 2)) z‖ := by
                            rw [norm_sub_rev]
                    _ = ‖a‖ *
                        ‖dslope (fun x : 𝕜 => x ^ (m + 2)) z (z + h) -
                          ((m + 2 : 𝕜) * z ^ (m + 1))‖ := by
                            simp
        _ ≤ ‖a‖ * (‖h‖ * C) := by
              gcongr
        _ < ε := hlt

omit [CompleteSpace 𝕜] in
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
  intro N
  induction N with
  | zero =>
      -- The empty prefix is the constant zero function.
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε εpos
      refine Filter.Eventually.of_forall ?_
      intro h z hz
      simpa using εpos
  | succ N ih =>
      have hterm :=
        tendstoUniformlyOn_weighted_dslope_pow (a := coeff N S) (n := N) (r := r) (q := q) hrq
      -- Add the next monomial term to the already-controlled finite prefix.
      simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using ih.add hterm

/-- Helper for Remark I.2-extra-7: away from the diagonal, the slope of the summed power series
is obtained by subtracting the two convergent scalar expansions termwise and dividing by `h`. -/
lemma hasSum_coeff_dslope_pow_off_diagonal
    (S : 𝕜⟦X⟧) {r q : NNReal}
    (hqS : (q : ℝ≥0∞) < S.radius)
    {z h : 𝕜} (hz : ‖z‖ ≤ r) (hh : ‖h‖ < q - r) (hh0 : h ≠ 0) :
    HasSum
      (fun n : ℕ ↦ coeff n S * dslope (fun x : 𝕜 => x ^ n) z (z + h))
      (dslope S.sum z (z + h)) := by
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 fun n ↦ coeff n S
  have hqpos : 0 < (q : ℝ) := by
    have hnonneg : 0 ≤ ‖h‖ := norm_nonneg h
    linarith [show (0 : ℝ) ≤ r by exact_mod_cast r.2]
  have hrq : (r : ℝ≥0∞) < q := by
    exact_mod_cast (show (r : ℝ) < q by linarith [norm_nonneg h])
  have hp0 : 0 < p.radius := by
    have hq0 : (0 : ℝ≥0∞) < q := by
      exact_mod_cast hqpos
    exact lt_of_lt_of_le hq0 hqS.le
  have hp : HasFPowerSeriesOnBall S.sum p 0 p.radius := by
    simpa [p, PowerSeries.sum, PowerSeries.radius] using p.hasFPowerSeriesOnBall hp0
  have hz_mem : z ∈ Metric.eball (0 : 𝕜) p.radius := by
    apply mem_eball_zero_iff.2
    calc
      (‖z‖₊ : ℝ≥0∞) ≤ r := by exact_mod_cast hz
      _ < q := hrq
      _ < p.radius := by
            simpa [p, PowerSeries.radius] using hqS
  have hzh_mem : z + h ∈ Metric.eball (0 : 𝕜) p.radius := by
    apply mem_eball_zero_iff.2
    have hzhr : ‖z + h‖ < (q : ℝ) := by
      calc
        ‖z + h‖ ≤ ‖z‖ + ‖h‖ := norm_add_le _ _
        _ < (r : ℝ) + (q - r) := add_lt_add_of_le_of_lt hz hh
        _ = q := by ring
    have hzhr' : (‖z + h‖₊ : ℝ≥0∞) < q := by
      exact_mod_cast hzhr
    exact lt_trans hzhr' (by simpa [p, PowerSeries.radius] using hqS)
  have hsum_add : HasSum (fun n : ℕ ↦ coeff n S * (z + h) ^ n) (S.sum (z + h)) := by
    simpa [p, mul_comm] using hp.hasSum_sub hzh_mem
  have hsum_z : HasSum (fun n : ℕ ↦ coeff n S * z ^ n) (S.sum z) := by
    simpa [p, mul_comm] using hp.hasSum_sub hz_mem
  have hsub : HasSum (fun n : ℕ ↦ coeff n S * ((z + h) ^ n - z ^ n)) (S.sum (z + h) - S.sum z) := by
    -- Subtract the two convergent scalar expansions termwise.
    simpa [sub_mul, mul_comm, mul_left_comm, mul_assoc] using hsum_add.sub hsum_z
  have hne : z + h ≠ z := by
    intro hEq
    apply hh0
    exact add_left_cancel (show z + h = z + 0 by simpa using hEq)
  have hslope :
      HasSum (fun n : ℕ ↦ coeff n S * slope (fun x : 𝕜 ↦ x ^ n) z (z + h))
        (slope S.sum z (z + h)) := by
    -- Divide the termwise difference identity by the nonzero increment.
    simpa [slope_def_field, hh0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hsub.mul_left h⁻¹
  simpa [dslope_of_ne _ hne, dslope_of_ne _ hne] using hslope

/-- Helper for Remark I.2-extra-7: within a smaller disk, the slope of the summed power series is
the sum of the coefficientwise monomial slopes. -/
lemma dslope_sum_eq_tsum_coeff_dslope_pow
    (S : 𝕜⟦X⟧) {r q : NNReal}
    (hqS : (q : ℝ≥0∞) < S.radius)
    {z h : 𝕜} (hz : ‖z‖ ≤ r) (hh : ‖h‖ < q - r) :
    dslope S.sum z (z + h) =
      ∑' n : ℕ, coeff n S * dslope (fun x : 𝕜 => x ^ n) z (z + h) := by
  by_cases hh0 : h = 0
  · subst hh0
    have hrq : (r : ℝ) < q := by
      have hnonneg : 0 ≤ ‖(0 : 𝕜)‖ := norm_nonneg (0 : 𝕜)
      linarith
    have hzq' : (‖z‖₊ : ℝ≥0∞) < q := by
      exact_mod_cast lt_of_le_of_lt hz hrq
    have hzq : ENNReal.ofReal ‖z‖ < (q : ℝ≥0∞) := by
      simpa using hzq'
    have hzS : ENNReal.ofReal ‖z‖ < S.radius := lt_trans hzq hqS
    -- On the diagonal, both sides identify with the derivative series.
    calc
      dslope S.sum z (z + 0) = (d⁄dX 𝕜 S).sum z := by
        simpa using dslope_sum_self_eq_derivSeries_sum S hzS
      _ = ∑' n : ℕ, coeff n S * dslope (fun x : 𝕜 => x ^ n) z (z + 0) := by
        rw [derivSeries_sum_eq_tsum_coeff_deriv_pow S hzS]
        refine congrArg tsum ?_
        ext n
        simp [dslope_same]
  · exact
      (hasSum_coeff_dslope_pow_off_diagonal (S := S) (r := r) (q := q) hqS hz hh hh0).tsum_eq.symm

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
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hr with ⟨q, hrq, hqS⟩
  have hrq_real : (r : ℝ) < q := by exact_mod_cast hrq
  have hrq_nn : r < q := by exact_mod_cast hrq
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 fun n ↦ coeff n S
  obtain ⟨a, ha, C, hCpos, hbound⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius hqS
  have hcoeff : ∀ n : ℕ, ‖coeff n S‖ * (q : ℝ) ^ n ≤ C * a ^ n := by
    simpa [p, ofScalars_norm] using hbound
  have hqpos : 0 < (q : ℝ) := by
    linarith [show (0 : ℝ) ≤ r by exact_mod_cast r.2]
  let u : ℕ → ℝ := fun n ↦ ((n : ℝ) * a ^ n) * (C / q)
  have hu : Summable u := by
    have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) * a ^ n) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (k := 1)
          (show ‖a‖ < 1 by
            simpa [Real.norm_eq_abs, abs_of_pos ha.1] using ha.2))
    simpa [u, mul_assoc, mul_left_comm, mul_comm] using hgeom.mul_right (C / q)
  let s : Set (𝕜 × 𝕜) := Metric.ball (0 : 𝕜) (q - r) ×ˢ Metric.closedBall (0 : 𝕜) r
  let F : ℕ → 𝕜 × 𝕜 → 𝕜 := fun n w ↦
    coeff n S * dslope (fun x : 𝕜 => x ^ n) w.2 (w.2 + w.1)
  let G : ℕ → 𝕜 → 𝕜 := fun n z ↦ coeff n S * deriv (fun x : 𝕜 => x ^ n) z
  have hFbound : ∀ n w, w ∈ s → ‖F n w‖ ≤ u n := by
    intro n w hw
    rcases hw with ⟨hh, hz⟩
    rcases n with _ | n
    · have hconst : dslope (fun x : 𝕜 => x ^ 0) w.2 (w.2 + w.1) = 0 := by
        by_cases hw0 : w.1 = 0
        · simp [hw0, dslope_same]
        · have hne : w.2 + w.1 ≠ w.2 := by
            intro hEq
            apply hw0
            exact add_left_cancel (show w.2 + w.1 = w.2 + 0 by simpa using hEq)
          rw [dslope_of_ne _ hne, slope_def_field]
          simp [pow_zero]
      have hconst' : dslope (fun x : 𝕜 ↦ (1 : 𝕜)) w.2 (w.2 + w.1) = 0 := by
        simpa [pow_zero] using hconst
      simp [F, u, pow_zero, hconst']
    · have hhqr : ‖w.1‖ < q - r := by
        simpa [s, Metric.mem_ball, dist_eq_norm] using hh
      have hzr : ‖w.2‖ ≤ r := by
        simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz
      have hcoeff_div :
          ‖coeff n.succ S‖ * (q : ℝ) ^ n ≤ (C * a ^ n.succ) / q := by
        refine (le_div_iff₀ hqpos).2 ?_
        calc
          (‖coeff n.succ S‖ * (q : ℝ) ^ n) * q
              = ‖coeff n.succ S‖ * (q : ℝ) ^ n.succ := by
                  rw [pow_succ]
                  ring
          _ ≤ C * a ^ n.succ := hcoeff n.succ
      -- Bound each slope term by the common geometric majorant coming from the coefficient bound.
      calc
        ‖F n.succ w‖
            = ‖coeff n.succ S‖ * ‖dslope (fun x : 𝕜 ↦ x ^ n.succ) w.2 (w.2 + w.1)‖ := by
                simp [F, norm_mul]
        _ ≤ ‖coeff n.succ S‖ * ((n.succ : ℝ) * (q : ℝ) ^ n) := by
              gcongr
              simpa [Nat.succ_eq_add_one] using
                norm_dslope_pow_succ_le_q_majorant (n := n) (z := w.2) (h := w.1) hzr hhqr
        _ = (n.succ : ℝ) * (‖coeff n.succ S‖ * (q : ℝ) ^ n) := by ring
        _ ≤ (n.succ : ℝ) * ((C * a ^ n.succ) / q) := by
              exact mul_le_mul_of_nonneg_left hcoeff_div (by positivity)
        _ = u n.succ := by
              simp [u, div_eq_mul_inv]
              ring_nf
  have hGbound : ∀ n z, z ∈ Metric.closedBall (0 : 𝕜) r → ‖G n z‖ ≤ u n := by
    intro n z hz
    rcases n with _ | n
    · simp [G, u]
    · have hzr : ‖z‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hzq : ‖z‖ ≤ (q : ℝ) := le_trans hzr (by exact_mod_cast hrq.le)
      have hnat : ‖(n.succ : 𝕜)‖ ≤ (n.succ : ℝ) := by
        simpa [nsmul_eq_mul, norm_one] using (norm_nsmul_le (a := (1 : 𝕜)) (n := n.succ))
      have hcoeff_div :
          ‖coeff n.succ S‖ * (q : ℝ) ^ n ≤ (C * a ^ n.succ) / q := by
        refine (le_div_iff₀ hqpos).2 ?_
        calc
          (‖coeff n.succ S‖ * (q : ℝ) ^ n) * q
              = ‖coeff n.succ S‖ * (q : ℝ) ^ n.succ := by
                  rw [pow_succ]
                  ring
          _ ≤ C * a ^ n.succ := hcoeff n.succ
      -- The derivative terms obey the same summable majorant on the closed inner disk.
      calc
        ‖G n.succ z‖ = ‖coeff n.succ S‖ * ‖deriv (fun x : 𝕜 ↦ x ^ n.succ) z‖ := by
            simp [G, norm_mul]
        _ = ‖coeff n.succ S‖ * ‖(n.succ : 𝕜) * z ^ n‖ := by
              simp
        _ = ‖coeff n.succ S‖ * (‖(n.succ : 𝕜)‖ * ‖z‖ ^ n) := by
              rw [norm_mul, norm_pow]
        _ ≤ ‖coeff n.succ S‖ * ((n.succ : ℝ) * (q : ℝ) ^ n) := by
              gcongr
        _ = (n.succ : ℝ) * (‖coeff n.succ S‖ * (q : ℝ) ^ n) := by ring
        _ ≤ (n.succ : ℝ) * ((C * a ^ n.succ) / q) := by
              exact mul_le_mul_of_nonneg_left hcoeff_div (by positivity)
        _ = u n.succ := by
              simp [u, div_eq_mul_inv]
              ring_nf
  have htailF := tendstoUniformlyOn_tsum_nat hu hFbound
  have htailG := tendstoUniformlyOn_tsum_nat hu hGbound
  rw [Metric.tendstoUniformlyOn_iff] at htailF htailG ⊢
  intro ε εpos
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (htailF (ε / 3) hthird)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (htailG (ε / 3) hthird)
  let N := max N1 N2
  have hprefix := tendstoUniformlyOn_dslope_monomial_prefix (S := S) (r := r) (q := q) hrq_nn N
  rw [Metric.tendstoUniformlyOn_iff] at hprefix
  have hball : Metric.ball (0 : 𝕜) (q - r) ∈ 𝓝 (0 : 𝕜) := by
    apply Metric.ball_mem_nhds
    linarith
  filter_upwards [hprefix (ε / 3) hthird, hball] with h hpref hh z hz
  have hhqr : ‖h‖ < q - r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hpair : (h, z) ∈ s := ⟨hh, hz⟩
  have htail1 := hN1 N (le_max_left _ _) (h, z) hpair
  have htail2 := hN2 N (le_max_right _ _) z hz
  have hzr : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hzq' : (‖z‖₊ : ℝ≥0∞) < q := by
    exact_mod_cast lt_of_le_of_lt hzr hrq_real
  have hzq : ENNReal.ofReal ‖z‖ < (q : ℝ≥0∞) := by
    simpa using hzq'
  have hzS : ENNReal.ofReal ‖z‖ < S.radius := lt_trans hzq hqS
  have hdslope : dslope S.sum z (z + h) = ∑' n : ℕ, F n (h, z) := by
    simpa [F] using dslope_sum_eq_tsum_coeff_dslope_pow (S := S) (r := r) (q := q) hqS hzr hhqr
  have hderiv : (d⁄dX 𝕜 S).sum z = ∑' n : ℕ, G n z := by
    simpa [G] using derivSeries_sum_eq_tsum_coeff_deriv_pow (S := S) hzS
  have htail1' : dist (∑ n ∈ Finset.range N, F n (h, z)) (∑' n : ℕ, F n (h, z)) < ε / 3 := by
    simpa [dist_comm] using htail1
  -- The final `ε / 3` decomposition uses derivative tail, finite-prefix convergence, and slope
  -- tail control on the common small neighborhood.
  calc
    dist ((d⁄dX 𝕜 S).sum z) (dslope S.sum z (z + h))
        ≤ dist ((d⁄dX 𝕜 S).sum z) (∑ n ∈ Finset.range N, G n z) +
            dist (∑ n ∈ Finset.range N, G n z) (dslope S.sum z (z + h)) := by
              exact dist_triangle _ _ _
    _ ≤ dist ((d⁄dX 𝕜 S).sum z) (∑ n ∈ Finset.range N, G n z) +
            (dist (∑ n ∈ Finset.range N, G n z) (∑ n ∈ Finset.range N, F n (h, z)) +
              dist (∑ n ∈ Finset.range N, F n (h, z)) (dslope S.sum z (z + h))) := by
              gcongr
              exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
          gcongr
          · simpa [hderiv] using htail2
          · simpa [F, G] using hpref z hz
          · simpa [hdslope] using htail1'
    _ = ε := by ring

/-- Cartan section02 0014_Remark_I_2_extra_7. Remark I.2-extra-7, source-facing statement over
the scalar `PowerSeries` owner: on every closed disk `‖z‖ ≤ r` strictly inside the radius of
convergence, the difference quotients of the summed power series converge uniformly to the sum of
the formal derivative power series. -/
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
