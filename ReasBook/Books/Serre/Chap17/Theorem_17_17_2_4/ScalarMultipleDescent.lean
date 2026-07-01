import Mathlib

open scoped TensorProduct

noncomputable section

universe u

namespace Representation

/-- Helper for Theorem 17-17.2-4: if every target vector is hit up to a nonzero integer scalar,
then the original `ℚ`-linear map is surjective. -/
lemma surjective_of_exists_nat_smul_preimage
    {V W : Type u} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (f : V →ₗ[ℚ] W)
    (hf : ∀ w : W, ∃ N : ℕ, N ≠ 0 ∧ ∃ v, f v = (N : ℚ) • w) :
    Function.Surjective f := by
  intro w
  obtain ⟨N, hN, v, hv⟩ := hf w
  refine ⟨((N : ℚ)⁻¹) • v, ?_⟩
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    f (((N : ℚ)⁻¹) • v) = ((N : ℚ)⁻¹) • f v := by
      rw [map_smul]
    _ = ((N : ℚ)⁻¹) • ((N : ℚ) • w) := by
      rw [hv]
    _ = w := by
      rw [smul_smul, inv_mul_cancel₀ hNQ, one_smul]

end Representation
