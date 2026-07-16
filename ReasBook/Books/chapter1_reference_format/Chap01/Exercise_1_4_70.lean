import Mathlib
import chapter1_reference_format.Chap01.Proposition_1_4_68

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Exercise 1.4.70 (1): the complex numbers are not an algebraic closure of the rationals. -/
theorem complex_not_isAlgClosure_of_rat : ¬ IsAlgClosure ℚ ℂ := by
  intro h
  let _ : IsAlgClosure ℚ ℂ := h
  obtain ⟨z, hz⟩ := Algebra.transcendental_def.mp complex_transcendental
  exact hz (Algebra.IsAlgebraic.isAlgebraic z)

/-- Exercise 1.4.70 (2): every finite field fails to be algebraically closed. -/
theorem finite_field_not_isAlgClosed (K : Type u) [Field K] [Finite K] : ¬ IsAlgClosed K := by
  intro h
  let _ : IsAlgClosed K := h
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite K)) inferInstance
