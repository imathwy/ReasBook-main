import Mathlib
import ProbabilityTheory_Klenke_2020.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open BoundedContinuousFunction
open Set
open scoped BoundedContinuousFunction

universe u

noncomputable section

/-- The auxiliary function `f_t` used in the characteristic-function proof of the central limit
theorem. -/
def cltAuxiliaryFunction (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    if x = 0 then
      (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)
    else
      (((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ))

-- Proof sketch: unfold `cltAuxiliaryFunction` at `x = 0`; the definition uses the continuous
-- extension value `-t^2 / 2` at the origin.
/-- The auxiliary function `cltAuxiliaryFunction t` takes the value `-t^2 / 2` at `0`. -/
theorem cltAuxiliaryFunction_apply_zero (t : ℝ) :
    cltAuxiliaryFunction t 0 = (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := sorry

-- Proof sketch: unfold `cltAuxiliaryFunction` and simplify the defining `if` using `x ≠ 0`.
/-- Away from `0`, the auxiliary function is the textbook expression
`((1 + x^2) / x^2) * (exp (itx) - 1 - i t x / (1 + x^2))`. -/
theorem cltAuxiliaryFunction_apply_ne_zero (t x : ℝ) (hx : x ≠ 0) :
    cltAuxiliaryFunction t x =
      (((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)) := sorry

-- Proof sketch: use the Taylor expansion argument from Lemma 15.30 at the origin and the
-- textbook estimate away from the origin to prove continuity of the explicit formula.
/-- The textbook auxiliary function `f_t` is continuous on `ℝ`. -/
theorem continuous_cltAuxiliaryFunction (t : ℝ) :
    Continuous (cltAuxiliaryFunction t) := sorry

-- Proof sketch: on `|x| ≥ 1`, use the uniform estimate from the proof of Lemma 15.47; near the
-- origin, continuity gives local boundedness, so the whole range is bounded.
/-- The range of the textbook auxiliary function `f_t` is bounded in `ℂ`. -/
theorem isBounded_range_cltAuxiliaryFunction (t : ℝ) :
    Bornology.IsBounded (Set.range (cltAuxiliaryFunction t)) := sorry

-- Proof sketch: bundle the already established continuity and bounded-range statements into the
-- canonical owner object `ℝ →ᵇ ℂ` from `Definition_15_1`.
/-- Lemma 15.47: for every real `t`, the textbook auxiliary function `f_t` is canonically an
element of `C_b(ℝ, ℂ) = ℝ →ᵇ ℂ`. -/
def cltAuxiliaryFunctionBCF (t : ℝ) : ℝ →ᵇ ℂ :=
  { toContinuousMap := ⟨cltAuxiliaryFunction t, continuous_cltAuxiliaryFunction t⟩
    map_bounded' := Metric.isBounded_range_iff.1 (isBounded_range_cltAuxiliaryFunction t) }

/-- Coercing the bundled bounded continuous map from Lemma 15.47 recovers the explicit textbook
formula for `f_t`. -/
@[simp] theorem coe_cltAuxiliaryFunctionBCF (t : ℝ) :
    (cltAuxiliaryFunctionBCF t : ℝ → ℂ) = cltAuxiliaryFunction t := rfl
