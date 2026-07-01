import Mathlib

open Polynomial
open scoped BigOperators

universe u

-- Declarations for this item will be appended below by the statement pipeline.

/-- Theorem 1.3.44: over a characteristic-zero field, every polynomial of degree at most `n`
coincides with its Taylor expansion at `a`, written using iterated derivatives and factorial
denominators. -/
-- Proof sketch: start from the canonical polynomial identity `Polynomial.sum_taylor_eq P a`.
-- Rewrite the coefficients of `P.taylor a` using `Polynomial.taylor_coeff`, then convert Hasse
-- derivatives to iterated ordinary derivatives by `Polynomial.factorial_smul_hasseDeriv`. The
-- assumption `P.natDegree ≤ n` kills all terms of degree larger than `n`, so the finite sum over
-- `Finset.range (n + 1)` is the whole Taylor expansion.
theorem polynomial_taylor_formula_of_natDegree_le
    {K : Type u} [Field K] [CharZero K] (P : K[X]) (n : ℕ) (hP : P.natDegree ≤ n) (a : K) :
    P = ∑ i ∈ Finset.range (n + 1),
      C ((((derivative^[i]) P).eval a) / (i.factorial : K)) * (X - C a) ^ i := by
  calc
    P = (P.taylor a).sum (fun i b ↦ C b * (X - C a) ^ i) :=
      (sum_taylor_eq P a).symm
    _ = ∑ i ∈ Finset.range (n + 1), C ((P.taylor a).coeff i) * (X - C a) ^ i := by
      rw [(P.taylor a).sum_over_range' (fun i ↦ by simp) (n + 1)]
      simpa using lt_of_le_of_lt (natDegree_taylor P a ▸ hP) (Nat.lt_succ_self n)
    _ = ∑ i ∈ Finset.range (n + 1),
          C ((((derivative^[i]) P).eval a) / (i.factorial : K)) * (X - C a) ^ i := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [taylor_coeff]
      have h_eval : (i.factorial : K) * (hasseDeriv i P).eval a = ((derivative^[i]) P).eval a := by
        simpa [nsmul_eq_mul] using
          congrArg
            (fun Q : K[X] ↦ Q.eval a)
            (congrFun (factorial_smul_hasseDeriv i) P)
      have hfac : (i.factorial : K) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero i
      have h_coeff : (hasseDeriv i P).eval a = ((derivative^[i]) P).eval a / (i.factorial : K) := by
        apply (eq_div_iff hfac).2
        simpa [mul_comm] using h_eval
      rw [h_coeff]
