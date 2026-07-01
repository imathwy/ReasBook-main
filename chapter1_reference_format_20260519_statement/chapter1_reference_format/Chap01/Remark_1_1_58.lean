import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: rewrite the coprimality hypothesis as `Int.gcd a b = 1` using
-- `Int.isCoprime_iff_gcd_eq_one`, then apply `Int.gcd_eq_gcd_ab`.
/-- Remark 1.1.58: if two integers are coprime, then the extended Euclidean algorithm produces
coefficients `Int.gcdA a b` and `Int.gcdB a b` satisfying Bézout's identity. -/
theorem bezout_eq_one_of_isCoprime {a b : ℤ} (h : IsCoprime a b) :
    a * Int.gcdA a b + b * Int.gcdB a b = 1 := by
  simpa [Int.isCoprime_iff_gcd_eq_one.mp h] using (Int.gcd_eq_gcd_ab a b).symm
