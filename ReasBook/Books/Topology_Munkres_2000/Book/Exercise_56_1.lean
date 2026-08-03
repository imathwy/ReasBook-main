module

public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open Polynomial
open scoped BigOperators

public section

/-- Helper for Exercise 56.1: a monic polynomial root bounds its top norm power by
the norm-weighted sum of all lower powers. -/
private lemma normPowNatDegree_le_sumNormCoeffMulNormPow {K : Type*} [NormedDivisionRing K]
    (p : Polynomial K) (hp : p.Monic) {z : K} (hz : p.IsRoot z) :
    ‖z‖ ^ p.natDegree ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * ‖z‖ ^ i := by
  -- Separate the leading monomial from the root equation using monicity.
  rw [IsRoot.def, eval_eq_sum_range, Finset.range_add_one] at hz
  simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert,
    hp.coeff_natDegree, one_mul, add_eq_zero_iff_eq_neg] at hz
  -- Take norms and estimate the remaining finite sum term by term.
  calc
    ‖z‖ ^ p.natDegree = ‖z ^ p.natDegree‖ := (norm_pow z p.natDegree).symm
    _ = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖ := by
      rw [hz, norm_neg]
    _ ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * ‖z‖ ^ i := by
      simp only [norm_mul, norm_pow]

/-- Helper for Exercise 56.1: when `1 ≤ r`, a nonnegative weighted sum of powers
below `n` is at most the total weight times `r ^ n`. -/
private lemma sumMulPow_le_sumMulTopPow (a : ℕ → ℝ) (n : ℕ) (r : ℝ) (hr : 1 ≤ r)
    (ha : ∀ i ∈ Finset.range n, 0 ≤ a i) :
    (∑ i ∈ Finset.range n, a i * r ^ i) ≤ (∑ i ∈ Finset.range n, a i) * r ^ n := by
  -- Bound every lower power by the common top power and sum the inequalities.
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hr (Nat.le_of_lt (Finset.mem_range.mp hi))) (ha i hi)

/-- Helper for Exercise 56.1: mapping a real polynomial to `ℂ` preserves the sum
of the norms of its coefficients over any fixed range. -/
private lemma sumNormCoeffRealMap (p : Polynomial ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖(p.map (algebraMap ℝ ℂ)).coeff i‖) =
      ∑ i ∈ Finset.range n, ‖p.coeff i‖ := by
  -- Reduce coefficientwise to the isometric embedding `ℝ → ℂ`.
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coeff_map, Complex.coe_algebraMap, Complex.norm_real]

/-- Exercise 56.1 (1). Every root of a monic complex polynomial whose
non-leading coefficient norms have sum less than `1` lies in the open unit ball. -/
theorem monicComplexPolynomial_root_mem_unitBall (p : Polynomial ℂ) (hp : p.Monic)
    (hcoeff : (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) < 1) (z : ℂ)
    (hz : p.IsRoot z) : z ∈ Metric.ball 0 1 := by
  -- It suffices to exclude the complementary case `1 ≤ ‖z‖`.
  simp only [Metric.mem_ball, dist_zero_right]
  by_contra hzNotSmall
  have hzLarge : 1 ≤ ‖z‖ := le_of_not_gt hzNotSmall
  have hroot := normPowNatDegree_le_sumNormCoeffMulNormPow p hp hz
  have hlower := sumMulPow_le_sumMulTopPow (fun i ↦ ‖p.coeff i‖) p.natDegree ‖z‖ hzLarge
    (fun i hi ↦ norm_nonneg (p.coeff i))
  have htopPos : 0 < ‖z‖ ^ p.natDegree :=
    pow_pos (zero_lt_one.trans_le hzLarge) p.natDegree
  -- The coefficient hypothesis makes the resulting common-factor bound strict.
  have hstrict :
      (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖z‖ ^ p.natDegree <
        ‖z‖ ^ p.natDegree := by
    calc
      (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖z‖ ^ p.natDegree <
          1 * ‖z‖ ^ p.natDegree := mul_lt_mul_of_pos_right hcoeff htopPos
      _ = ‖z‖ ^ p.natDegree := one_mul _
  exact (not_lt_of_ge (hroot.trans hlower)) hstrict

/-- Companion for Exercise 56.1 (2): every complex root of a monic real polynomial whose
non-leading coefficient norms have sum less than `1` lies in the open unit ball. -/
theorem monicRealPolynomial_complexRoot_mem_unitBall (p : Polynomial ℝ) (hp : p.Monic)
    (hcoeff : (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) < 1) (z : ℂ)
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) : z ∈ Metric.ball 0 1 := by
  -- Transport monicity, degree, and the coefficient sum through `Polynomial.map`.
  have hpMap : (p.map (algebraMap ℝ ℂ)).Monic := hp.map _
  have hdegree : (p.map (algebraMap ℝ ℂ)).natDegree = p.natDegree := hp.natDegree_map _
  have hcoeffMap :
      (∑ i ∈ Finset.range (p.map (algebraMap ℝ ℂ)).natDegree,
        ‖(p.map (algebraMap ℝ ℂ)).coeff i‖) < 1 := by
    rw [hdegree, sumNormCoeffRealMap]
    exact hcoeff
  -- Apply the complex result after the coefficientwise normalization.
  exact monicComplexPolynomial_root_mem_unitBall
    (p.map (algebraMap ℝ ℂ)) hpMap hcoeffMap z hz

end
