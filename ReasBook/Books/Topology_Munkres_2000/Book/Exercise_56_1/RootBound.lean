module

public import Mathlib.Analysis.Polynomial.CauchyBound

open scoped BigOperators

public section

namespace Polynomial.IsRoot

/-- A root of a monic polynomial lies in the open unit ball when the sum of the
norms of its non-leading coefficients is less than `1`. -/
theorem norm_lt_one_of_monic_of_sum_norm_lt_one {K : Type*} [NormedDivisionRing K]
    (p : Polynomial K) (hp : p.Monic)
    (hcoeff : (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) < 1) {z : K}
    (hz : p.IsRoot z) : ‖z‖ < 1 := by
  -- Separate the leading monomial from the root equation and take norms.
  rw [IsRoot.def, eval_eq_sum_range, Finset.range_add_one] at hz
  simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert,
    hp.coeff_natDegree, one_mul, add_eq_zero_iff_eq_neg] at hz
  have hroot :
      ‖z‖ ^ p.natDegree ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * ‖z‖ ^ i := by
    calc
      ‖z‖ ^ p.natDegree = ‖z ^ p.natDegree‖ := (norm_pow z p.natDegree).symm
      _ = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖ := by
        rw [hz, norm_neg]
      _ ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * ‖z‖ ^ i := by
        simp only [norm_mul, norm_pow]
  -- If the root norm were at least one, every lower power would be bounded by the top power.
  by_contra hzNotSmall
  have hzLarge : 1 ≤ ‖z‖ := le_of_not_gt hzNotSmall
  have hlower :
      (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * ‖z‖ ^ i) ≤
        (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖z‖ ^ p.natDegree := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hzLarge (Nat.le_of_lt (Finset.mem_range.mp hi)))
      (norm_nonneg (p.coeff i))
  have htopPos : 0 < ‖z‖ ^ p.natDegree :=
    pow_pos (zero_lt_one.trans_le hzLarge) p.natDegree
  have hstrict :
      (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖z‖ ^ p.natDegree <
        ‖z‖ ^ p.natDegree := by
    calc
      (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖z‖ ^ p.natDegree <
          1 * ‖z‖ ^ p.natDegree := mul_lt_mul_of_pos_right hcoeff htopPos
      _ = ‖z‖ ^ p.natDegree := one_mul _
  exact (not_lt_of_ge (hroot.trans hlower)) hstrict

end Polynomial.IsRoot
