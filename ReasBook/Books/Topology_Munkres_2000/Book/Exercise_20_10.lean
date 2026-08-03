module

public import Mathlib.Analysis.Normed.Lp.lpSpace

public section

open scoped lp

/- Exercise 20.10 (2): square-summable real sequences are closed under addition. -/
#check fun (x y : ℓ²(ℕ, ℝ)) ↦ x + y

/- Exercise 20.10 (3): square-summable real sequences are closed under real scalar
multiplication. -/
#check fun (c : ℝ) (x : ℓ²(ℕ, ℝ)) ↦ c • x

/-- Exercise 20.10: products of square-summable real sequences are absolutely summable. -/
theorem l2Summable_abs_mul (x y : ℓ²(ℕ, ℝ)) :
    Summable (fun i : ℕ ↦ |x i * y i|) := by
  -- Specialize Hölder conjugacy to the exponent representation used by `lp`.
  have conjugateTwo :
      (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  -- Hölder summability becomes absolute summability after normalizing real norms.
  simpa only [Real.norm_eq_abs, abs_mul] using lp.summable_mul conjugateTwo x y

/-- The canonical distance on square-summable real sequences is the square root of the
sum of the squared coordinate differences. -/
theorem l2Dist_eq_sqrt_tsum_sq (x y : ℓ²(ℕ, ℝ)) :
    dist x y = Real.sqrt (∑' i : ℕ, (x i - y i) ^ 2) := by
  -- Express the squared ℓ² norm through the coordinate square sum.
  have normSubSq : ‖x - y‖ ^ 2 = ∑' i : ℕ, (x i - y i) ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      lp.coeFn_sub, Pi.sub_apply, sq_abs] using
      lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (x - y)
  -- Rewrite distance as a norm, recover it from its square, and transport the formula.
  calc
    dist x y = ‖x - y‖ := dist_eq_norm x y
    _ = Real.sqrt (‖x - y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (∑' i : ℕ, (x i - y i) ^ 2) := congrArg Real.sqrt normSubSq

/- Exercise 20.10 (5): square-summable real sequences carry the canonical metric
structure associated to this distance. -/
#check (inferInstance : MetricSpace (ℓ²(ℕ, ℝ)))
