import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.BilinearForm.Properties

open LinearMap (BilinForm)

universe u

-- Mathlib recall: `QuadraticForm.sigPos` and `QuadraticForm.sigNeg` are the positive and
-- negative inertia indices, so signature zero is formalized as their equality.

namespace QuadraticForm

/-- If a nondegenerate real quadratic form has an isotropic subspace of half the ambient
dimension, then its positive and negative inertia indices agree. -/
theorem sigPos_eq_sigNeg_of_exists_isotropic_finrank_eq_half
    {M : Type u} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) (hQnondeg : Q.Nondegenerate) {W : Submodule ℝ M}
    (hWisotropic : ∀ x : W, Q x = 0)
    (hWhalf : 2 * Module.finrank ℝ W = Module.finrank ℝ M) :
    sigPos Q = sigNeg Q := by
  have hsigPos_aux : sigPos Q + Module.finrank ℝ W ≤ Module.finrank ℝ M := by
    exact
      sigPos_add_finrank_le_of_nonpos fun x hx ↦
        le_of_eq (hWisotropic ⟨x, hx⟩)
  have hsigPos_le : sigPos Q ≤ Module.finrank ℝ W := by
    rw [← hWhalf, two_mul] at hsigPos_aux
    exact Nat.le_of_add_le_add_right hsigPos_aux
  have hsigNeg_aux' : sigPos (-Q) + Module.finrank ℝ W ≤ Module.finrank ℝ M := by
    exact
      sigPos_add_finrank_le_of_nonpos fun x hx ↦ by
        exact neg_nonpos.mpr (le_of_eq (hWisotropic ⟨x, hx⟩).symm)
  have hsigNeg_aux : sigNeg Q + Module.finrank ℝ W ≤ Module.finrank ℝ M := by
    simpa only [sigNeg] using hsigNeg_aux'
  have hsigNeg_le : sigNeg Q ≤ Module.finrank ℝ W := by
    rw [← hWhalf, two_mul] at hsigNeg_aux
    exact Nat.le_of_add_le_add_right hsigNeg_aux
  have hsum : sigPos Q + sigNeg Q = 2 * Module.finrank ℝ W := by
    have hsum' : sigPos Q + sigNeg Q + Module.finrank ℝ Q.radical = Module.finrank ℝ M :=
      sigPos_add_sigNeg_add_radical
    rw [hQnondeg.radical_eq_bot] at hsum'
    simpa [hWhalf, two_mul, add_assoc, add_left_comm, add_comm] using hsum'
  have hfinrank_le_sigPos : Module.finrank ℝ W ≤ sigPos Q := by
    have haux : sigPos Q + sigNeg Q ≤ sigPos Q + Module.finrank ℝ W :=
      Nat.add_le_add_left hsigNeg_le (sigPos Q)
    rw [hsum, two_mul] at haux
    exact Nat.le_of_add_le_add_right haux
  have hfinrank_le_sigNeg : Module.finrank ℝ W ≤ sigNeg Q := by
    have haux : sigPos Q + sigNeg Q ≤ Module.finrank ℝ W + sigNeg Q :=
      Nat.add_le_add_right hsigPos_le (sigNeg Q)
    rw [hsum, two_mul] at haux
    exact Nat.le_of_add_le_add_left haux
  rw [Nat.le_antisymm hsigPos_le hfinrank_le_sigPos, Nat.le_antisymm hsigNeg_le hfinrank_le_sigNeg]

end QuadraticForm

/-- Lemma 21.5.2: if a symmetric nonsingular bilinear form over `ℝ` has an isotropic subspace of
half the ambient dimension, then the positive and negative inertia indices of
`B.toQuadraticMap` agree. -/
theorem sigPos_eq_sigNeg_of_exists_isotropic_finrank_eq_half
    {M : Type u} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (B : BilinForm ℝ M) (hBsymm : B.IsSymm) (hBnondeg : B.Nondegenerate)
    {W : Submodule ℝ M} (hWisotropic : ∀ x : W, B x x = 0)
    (hWhalf : 2 * Module.finrank ℝ W = Module.finrank ℝ M) :
    sigPos B.toQuadraticMap = sigNeg B.toQuadraticMap := by
  have hassociated : QuadraticMap.associated B.toQuadraticMap = B :=
    QuadraticMap.associated_left_inverse ℝ hBsymm.eq
  have hnondeg_assoc :
      (QuadraticMap.associated B.toQuadraticMap).Nondegenerate ↔
        B.toQuadraticMap.Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff
  apply QuadraticForm.sigPos_eq_sigNeg_of_exists_isotropic_finrank_eq_half
  · rw [← hnondeg_assoc]
    simpa [hassociated] using hBnondeg
  · intro x
    simpa using hWisotropic x
  · exact hWhalf
