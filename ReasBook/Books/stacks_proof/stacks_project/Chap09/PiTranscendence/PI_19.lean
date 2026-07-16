import Mathlib
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_15
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_16
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_17
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_18

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall tool `lean_leansearch` was unavailable in this environment; local repository
-- search found an exact analogue elsewhere, but this item keeps the source-faithful direct target
-- with the dependency chain from `PI_15` through `PI_18` available in-file.

/-- Chap09 PiTranscendence/PI 19: the real number `Real.pi` is transcendental over `ℚ`. -/
theorem transcendental_real_pi : Transcendental ℚ Real.pi := by
  -- `Transcendental ℚ Real.pi` unfolds to `¬ IsAlgebraic ℚ Real.pi`.
  intro h
  -- The complex image of `Real.pi` is algebraic over `ℚ` (PI-16), as is `Complex.I` (PI-15).
  have hπC : IsAlgebraic ℚ ((Real.pi : ℝ) : ℂ) := isAlgebraic_rat_complex_ofReal h
  have hI : IsAlgebraic ℚ Complex.I := complex_I_isAlgebraic_over_rat
  -- Algebraic numbers are closed under multiplication, so `α = (π : ℂ) * I` is algebraic.
  have hα : IsAlgebraic ℚ ((Real.pi : ℂ) * Complex.I) := hπC.mul hI
  -- `α ≠ 0` by PI-17.
  have hα0 : ((Real.pi : ℂ) * Complex.I) ≠ 0 := complex_pi_mul_I_ne_zero
  -- The weak Lindemann theorem PI-18 then forbids `exp α = -1`.
  have hne : Complex.exp ((Real.pi : ℂ) * Complex.I) ≠ -1 :=
    complex_exp_ne_neg_one_of_isAlgebraic_rat_of_ne_zero hα hα0
  -- But `exp (π * I) = -1`, a contradiction.
  exact hne Complex.exp_pi_mul_I

#print axioms transcendental_real_pi
