import Mathlib
import ProbabilityTheory_Klenke_2020.Chap05.Definition_5_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u}

-- Proof sketch: expand `entropy` as the Shannon sum `-∑ p(e) log p(e)` and use the standard
-- inequality `x * log x ≤ 0` on `[0,1]` for each probability weight; this does not use
-- finiteness.
/-- Exercise 5.3.3 (1): entropy is bounded below by `0`. -/
theorem entropy_nonneg (p : PMF E) :
    0 ≤ entropy p := sorry

-- Proof sketch: evaluate the entropy of `PMF.pure e`; the pmf is `1` at `e` and `0` elsewhere, so
-- every summand vanishes; this does not use finiteness.
/-- Exercise 5.3.3 (2): a Dirac mass has entropy `0`. -/
theorem entropy_pure_eq_zero (e : E) :
    entropy (PMF.pure e) = 0 := by
  rw [entropy_def, tsum_eq_single e]
  · simp
  · intro e' he'
    simp [PMF.pure_apply, he']

section Fintype

variable [Fintype E]

-- Proof sketch: apply the classical finite-alphabet entropy bound, for instance via Jensen's
-- inequality for the concave function `x ↦ -x log x` under the constraint `∑ p(e) = 1`.
/-- Exercise 5.3.3 (3): on a finite set, entropy is bounded above by `log (#E)`. -/
theorem entropy_le_log_card (p : PMF E) :
    entropy p ≤ Real.log (Fintype.card E) := sorry

-- Proof sketch: compute the entropy of `PMF.uniformOfFintype E`; every atom has weight
-- `(Fintype.card E)⁻¹`, so the sum simplifies to `log (Fintype.card E)`.
/-- Exercise 5.3.3 (4): the uniform distribution on a finite nonempty set has entropy
`log (#E)`. -/
theorem entropy_uniformOfFintype_eq_log_card [Nonempty E] :
    entropy (PMF.uniformOfFintype E) = Real.log (Fintype.card E) := by
  rw [entropy_eq_sum]
  simp [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_inv,
    Real.log_inv]

end Fintype
