import Mathlib

noncomputable section

open Filter Bornology
open scoped Topology

/-- The kernel `z ↦ π cot (π z)` used in the residue summation formulas. -/
def exercise25PiCot (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)

/-- Helper for Exercise 25: `π cot (π z)` is the logarithmic derivative of `sin (π z)`. -/
lemma exercise25_piCot_as_logDeriv_sinPi :
    exercise25PiCot = fun z ↦ logDeriv (fun w : ℂ ↦ Complex.sin ((Real.pi : ℂ) * w)) z := by
  funext z
  -- Rewrite the composed logarithmic derivative using the chain rule for `logDeriv`.
  change exercise25PiCot z =
    logDeriv (Complex.sin ∘ fun w : ℂ ↦ (Real.pi : ℂ) * w) z
  rw [logDeriv_comp Complex.differentiableAt_sin]
  · rw [Complex.logDeriv_sin]
    -- The derivative of `w ↦ π w` is `π`, so the formula matches the kernel definition.
    simp [exercise25PiCot, mul_comm]
  · fun_prop

/-- Helper for Exercise 25: multiplying `π cot (π z)` by `z - n` removes the pole at the integer
`n`, and the resulting punctured-neighborhood limit is `1`. -/
lemma exercise25_tendsto_sub_integer_mul_piCot (n : ℤ) :
    Tendsto (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (𝓝[≠] (n : ℂ)) (𝓝 1) := by
  let sinPi : ℂ → ℂ := fun z ↦ Complex.sin ((Real.pi : ℂ) * z)
  have hsinPi_an : AnalyticAt ℂ sinPi (n : ℂ) := by
    -- The sine composition is entire, hence analytic at every integer.
    fun_prop
  have hsinPi_zero : sinPi (n : ℂ) = 0 := by
    -- Integer multiples of `π` are zeros of the sine function.
    change Complex.sin ((Real.pi : ℂ) * (n : ℂ)) = 0
    rw [mul_comm]
    simpa using Complex.sin_int_mul_pi n
  have hcos_ne : Complex.cos ((Real.pi : ℂ) * (n : ℂ)) ≠ 0 := by
    intro hcos
    have hsin : Complex.sin ((Real.pi : ℂ) * (n : ℂ)) = 0 := hsinPi_zero
    rw [Complex.cos_eq_zero_iff_sin_eq] at hcos
    rcases hcos with hcos | hcos <;> simp [hsin] at hcos
  have hsinPi_deriv_ne : deriv sinPi (n : ℂ) ≠ 0 := by
    have hderiv :
        deriv sinPi (n : ℂ) = (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * (n : ℂ)) := by
      -- Differentiate `sin (π z)` by a single chain-rule step.
      change
        deriv (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z)) (n : ℂ) =
          (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * (n : ℂ))
      calc
        deriv (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z)) (n : ℂ)
            = Complex.cos ((Real.pi : ℂ) * (n : ℂ)) * ((Real.pi : ℂ) * 1) := by
                exact
                  ((Complex.hasDerivAt_sin ((Real.pi : ℂ) * (n : ℂ))).comp (n : ℂ)
                    ((hasDerivAt_id (n : ℂ)).const_mul (Real.pi : ℂ))).deriv
        _ = (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * (n : ℂ)) := by
              ring
    rw [hderiv]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hcos_ne
  have hlimit :=
      hsinPi_an.tendsto_mul_logDeriv_simple_zero hsinPi_zero hsinPi_deriv_ne
  -- Replace the logarithmic derivative with the kernel from this exercise.
  simpa [sinPi, exercise25_piCot_as_logDeriv_sinPi] using hlimit
