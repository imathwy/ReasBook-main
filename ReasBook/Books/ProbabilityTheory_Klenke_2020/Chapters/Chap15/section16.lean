import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_15_16 (from Items/Chap15) -/
open MeasureTheory

noncomputable section

-- Proof sketch: split the series over odd and even integers, rewrite the odd part as the classical
-- Basel-type sum over `(2n + 1)⁻²`, and use `∑' n, 8 / (π^2 * (2n + 1)^2) = 1`.
private theorem oddSquarePMF_hasSum :
    HasSum (fun x : ℤ ↦ ENNReal.ofReal
      (if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0)) 1 := sorry

/-- The probability mass function on `ℤ` whose odd masses are proportional to `x⁻²` and whose
even masses vanish. -/
def oddSquarePMF : PMF ℤ :=
  ⟨fun x ↦ ENNReal.ofReal
      (if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0),
    oddSquarePMF_hasSum⟩

-- Proof sketch: unfold `oddSquarePMF`; the singleton masses are definitionally
-- the odd-square formula used to build the PMF.
/-- The masses of `oddSquarePMF` are `4 / (π^2 x^2)` on odd integers and `0` on even integers. -/
theorem oddSquarePMF_apply (x : ℤ) :
    oddSquarePMF x = ENNReal.ofReal (if Odd x then 4 / (Real.pi ^ 2 * (x : ℝ) ^ 2) else 0) := rfl

/-- The `2π`-periodic tent function from Example 15.16, written using reduction to the
fundamental domain `[-π, π)`. -/
def periodicTentFunction (t : ℝ) : ℝ :=
  1 - 2 * |toIcoMod Real.two_pi_pos (-Real.pi) t| / Real.pi

-- Proof sketch: reduce `t + 2π` and `t` to `[-π, π)` using the periodicity of `toIcoMod` with
-- period `2π`, then unfold `periodicTentFunction`.
/-- The tent function of Example 15.16 is `2π`-periodic. -/
theorem periodicTentFunction_periodic : Function.Periodic periodicTentFunction (2 * Real.pi) :=
  sorry

-- Proof sketch: if `t ∈ [-π, π)`, then `toIcoMod Real.two_pi_pos (-π) t = t`; substitute this into
-- the definition of `periodicTentFunction`.
/-- On the fundamental interval `[-π, π)`, the periodic tent function is `t ↦ 1 - 2 |t| / π`. -/
theorem periodicTentFunction_eq_on_fundamentalDomain {t : ℝ}
    (ht : t ∈ Set.Ico (-Real.pi) Real.pi) :
    periodicTentFunction t = 1 - 2 * |t| / Real.pi := sorry

-- Proof sketch: apply the discrete Fourier inversion formula on `ℤ` to the periodic tent function,
-- compute the singleton masses by partial integration, and identify the resulting probability law
-- with the pushforward of `oddSquarePMF.toMeasure` along `ℤ → ℝ`.
/-- Example 15.16: the `2π`-periodic tent function is the characteristic function of the
probability measure on `ℤ` with masses `4 / (π^2 x^2)` on odd integers and `0` on even integers. -/
theorem periodicTentFunction_eq_charFun_oddSquarePMF (t : ℝ) :
    charFun (oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)) t =
      (periodicTentFunction t : ℂ) := sorry
