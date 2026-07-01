import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoundedContinuousFunction

variable {d : ℕ}

/-- The phase-one set for the characteristic-function kernel at frequency `t`; equivalently, the
points `x` with `⟪x, t⟫ ∈ 2πℤ`. -/
def charFunPeriodSet (t : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | Complex.exp (inner ℝ x t * Complex.I) = 1}

/-- Membership in `charFunPeriodSet t` means that the owner Fourier kernel `innerProbChar t`
takes the value `1`. -/
@[simp]
theorem mem_charFunPeriodSet_iff_innerProbChar_eq_one {t x : EuclideanSpace ℝ (Fin d)} :
    x ∈ charFunPeriodSet t ↔ innerProbChar t x = 1 := by
  simp [charFunPeriodSet, innerProbChar_apply]

-- Proof sketch: apply `Complex.exp_eq_one_iff` to the purely imaginary number
-- `inner ℝ x t * Complex.I`, then compare real and imaginary parts.
/-- Membership in `charFunPeriodSet t` is equivalent to the phase `⟪x, t⟫` being an integral
multiple of `2π`. -/
theorem mem_charFunPeriodSet_iff_exists_int {t x : EuclideanSpace ℝ (Fin d)} :
    x ∈ charFunPeriodSet t ↔ ∃ z : ℤ, inner ℝ x t = (2 * Real.pi : ℝ) * z := sorry

-- Proof sketch: decompose `x` into its component orthogonal to `t` plus its projection onto the
-- line spanned by `t`. For `t ≠ 0`, the scalar coordinate along `t` is an integer multiple of
-- `2π / ‖t‖²` exactly when `x ∈ charFunPeriodSet t`.
/-- For `t ≠ 0`, the period set `charFunPeriodSet t` is the union of affine hyperplanes
orthogonal to `t`, translated by integer multiples of `((2π) / ‖t‖²) t`. -/
theorem charFunPeriodSet_eq_orthogonal_translate_set {t : EuclideanSpace ℝ (Fin d)} (ht : t ≠ 0) :
    charFunPeriodSet t =
      {x | ∃ y : EuclideanSpace ℝ (Fin d), ∃ z : ℤ,
        inner ℝ y t = 0 ∧ x = y + z • (((2 * Real.pi) / ‖t‖ ^ 2) • t)} := sorry

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]

-- Proof sketch: rewrite `charFun μ t = 1` as equality in the triangle inequality
-- for the unit-modulus integrand `x ↦ exp (i \langle x, t \rangle)`, deduce that this integrand
-- is `1` almost everywhere, and translate that condition to `x ∈ charFunPeriodSet t`.
/-- Exercise 15.2.1 (1): if the characteristic function of a probability law on `ℝ^d` takes the
value `1` at frequency `t`, then the law is supported on `H_t = charFunPeriodSet t`. -/
theorem measure_charFunPeriodSet_eq_one_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) :
    μ (charFunPeriodSet t) = 1 := sorry

-- Proof sketch: use the support statement above to see that `exp (i \langle x, t \rangle) = 1`
-- for `μ`-almost every `x`, then factor the integrand defining `charFun μ (t + s)`
-- as `exp (i \langle x, s \rangle) * exp (i \langle x, t \rangle)` and simplify almost
-- everywhere.
/-- Exercise 15.2.1 (2): if the characteristic function equals `1` at frequency `t`, then it is
periodic in the direction `t`, so `φ(t + s) = φ(s)` for every `s`. -/
theorem charFun_periodic_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) :
    Function.Periodic (charFun μ) t := sorry

/-- Exercise 15.2.1 (2): if the characteristic function equals `1` at frequency `t`, then it is
periodic in the direction `t`, so `φ(t + s) = φ(s)` for every `s`. -/
theorem charFun_add_eq_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) (s : EuclideanSpace ℝ (Fin d)) :
    charFun μ (t + s) = charFun μ s := by
  simpa [add_comm] using charFun_periodic_of_charFun_eq_one hφ s
