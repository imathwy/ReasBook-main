import Mathlib
-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style pass: Problem 7-22 lives in the quaternion algebra / normed division ring domain.
-- The canonical owners reused below are `mul_assoc`, `star_mul`, `Quaternion.inner_def`,
-- `norm_mul`, and the units Lie-group instance from `UnitsOfNormedAlgebra`.

open scoped Quaternion RealInnerProductSpace Manifold ContDiff

/- Problem 7-22 (1): quaternion multiplication on `ℍ` is associative. -/
#check (mul_assoc : ∀ p q r : ℍ, (p * q) * r = p * (q * r))

/-- Problem 7-22 (2): quaternion multiplication on `ℍ` is not commutative. -/
theorem quaternion_multiplication_noncommutative :
    ∃ p q : ℍ, p * q ≠ q * p := by
  let i : ℍ := ⟨0, 1, 0, 0⟩
  let j : ℍ := ⟨0, 0, 1, 0⟩
  refine ⟨i, j, ?_⟩
  intro h
  have himK : (1 : ℝ) = -1 := by
    simpa [i, j] using congrArg (fun r : ℍ ↦ r.imK) h
  norm_num at himK

/- Problem 7-22 (3): quaternion conjugation reverses the order of multiplication. -/
#check (star_mul : ∀ p q : ℍ, star (p * q) = star q * star p)

/-- Problem 7-22 (4): the textbook bilinear form agrees with the standard inner product on `ℍ`. -/
theorem quaternion_textbook_inner_eq_inner (p q : ℍ) :
    ((star p * q + star q * p).re) / 2 = inner ℝ p q := by
  have hstar : ∀ x y : ℍ, (star x * y).re = inner ℝ x y := by
    intro x y
    rw [Quaternion.inner_def]
    simp [Quaternion.re_mul]
  have hleft : (star p * q).re = inner ℝ p q := hstar p q
  have hright : (star q * p).re = inner ℝ p q := by
    simpa [real_inner_comm] using hstar q p
  calc
    ((star p * q + star q * p).re) / 2 = ((star p * q).re + (star q * p).re) / 2 := by
      simp
    _ = (inner ℝ p q + inner ℝ p q) / 2 := by rw [hleft, hright]
    _ = inner ℝ p q := by ring

/- Problem 7-22 (5): the norm on `ℍ` is multiplicative. -/
#check (norm_mul : ∀ p q : ℍ, ‖p * q‖ = ‖p‖ * ‖q‖)

/-- Problem 7-22 (6): quaternion inversion is given by the norm-square formula. -/
theorem quaternion_inv_eq_norm_sq_smul_star (p : ℍ) :
    p⁻¹ = ((‖p‖ ^ 2 : ℝ)⁻¹) • star p := by
  simpa [Quaternion.normSq_eq_norm_mul_self, pow_two] using
    (show p⁻¹ = (Quaternion.normSq p)⁻¹ • star p by rfl)

/- Problem 7-22 (7): the nonzero quaternions form a Lie group, represented canonically by
the unit group `ℍˣ`. -/
#check (inferInstance : LieGroup (𝓘(ℝ, ℍ)) ∞ ℍˣ)
