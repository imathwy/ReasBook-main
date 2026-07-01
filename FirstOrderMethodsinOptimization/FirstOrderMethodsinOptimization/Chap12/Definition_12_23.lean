import Mathlib
import FirstOrderMethodsinOptimization.Chap12.Definition_12_21
import FirstOrderMethodsinOptimization.Chap12.Definition_12_22
import FirstOrderMethodsinOptimization.Chap12.Definition_12_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ

open IsotropicTwoDimensionalTotalVariation

local notation "ψ[" i "]" => ψ m n i

/- Definition 12.23 is a `bridge/view`: it rewrites isotropic total-variation denoising as a
three-block finite-sum model. The relevant Chapter 12 owners are already present:
- `two_dimensional_total_variation_denoising_objective TV_I` from Definitions 12.12 and 12.13 for
  the source denoising objective;
- `ψ` from Definition 12.22 for the diagonal block penalties `ψ[0]`, `ψ[1]`, and `ψ[2]`;
- `composite_model_objective` together with `finite_sum_objective` for the block finite-sum
  owner reused in Definition 12.14.

This file therefore stays at the `bridge/view` layer and reuses those owners directly rather than
redefining the same diagonal combinatorics or the same raw denoising objective. -/

/-- The real matrix space `ℝ^(m × n)` carries its canonical Frobenius norm. -/
local instance : NormedAddCommGroup Mmn := Matrix.frobeniusNormedAddCommGroup

/-- Scalar multiplication on `ℝ^(m × n)` is compatible with the Frobenius norm. -/
local instance : NormedSpace ℝ Mmn := Matrix.frobeniusNormedSpace

-- Proof sketch: unfold the Chapter 12.12 denoising owner specialized to `TV_I`, rewrite `TV_I x`
-- using `isotropic_two_dimensional_total_variation_eq_sum_ψ` from
-- Definition 12.22, and identify the result with the Chapter 12.14
-- finite-sum objective built from `denoising_data_fidelity d` and the block family `i ↦ λ ψ_i`.
/-- Definition 12.23: the isotropic total-variation denoising problem can be rewritten as the
three-block objective whose smooth term is the quadratic fidelity `x ↦ (1 / 2) ‖x - d‖_F^2` and
whose block penalties are the scaled diagonal components `λ ψ[0]`, `λ ψ[1]`, and `λ ψ[2]`. -/
theorem isotropic_two_dimensional_total_variation_denoising_fits_dual_block_model
    (d : Mmn) (lam : PosReal) :
    two_dimensional_total_variation_denoising_objective TV_I d lam =
      composite_model_objective
        (denoising_data_fidelity d)
        (finite_sum_objective
          (fun i x ↦ ↑((lam : ℝ) * ψ[i] x))) := by
  ext x
  rw [two_dimensional_total_variation_denoising_objective, denoising_problem_objective_apply,
    composite_model_objective_apply, finite_sum_objective_apply, denoising_data_fidelity_apply,
    isotropic_two_dimensional_total_variation_eq_sum_ψ]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have hleft :
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) +
          ↑((lam : ℝ) * (ψ[0] (id x) + ψ[1] (id x) + ψ[2] (id x)) : ℝ) =
        ↑((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) +
          (lam : ℝ) * (ψ[0] (id x) + ψ[1] (id x) + ψ[2] (id x))) := by
    rw [← EReal.coe_add]
  have hright :
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) +
          (↑((lam : ℝ) * ψ[0] x : ℝ) +
            ↑((lam : ℝ) * ψ[1] x : ℝ) + ↑((lam : ℝ) * ψ[2] x : ℝ)) =
        ↑((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) +
          ((lam : ℝ) * ψ[0] x + (lam : ℝ) * ψ[1] x + (lam : ℝ) * ψ[2] x)) := by
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
  rw [hleft, hright]
  have hreal :
      (‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) +
          (lam : ℝ) * (ψ[0] (id x) + ψ[1] (id x) + ψ[2] (id x)) =
        (‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) +
          ((lam : ℝ) * ψ[0] x + (lam : ℝ) * ψ[1] x + (lam : ℝ) * ψ[2] x) := by
    simp [id]
    ring
  exact_mod_cast hreal

-- Proof sketch: evaluate the canonical composite objective and finite-sum aggregate in
-- `isotropic_two_dimensional_total_variation_denoising_fits_dual_block_model`, then unfold the
-- block family to obtain the displayed sum
-- `λ ψ[0](x) + λ ψ[1](x) + λ ψ[2](x) = ∑ i : Fin 3, λ ψ[i](x)`.
/-- Evaluating the rewritten isotropic denoising objective gives the quadratic Frobenius
data-fidelity term plus the finite sum of the three scaled diagonal penalties
`∑ i : Fin 3, λ ψ[i](x)`. -/
theorem isotropic_two_dimensional_total_variation_denoising_fits_dual_block_model_apply
    (d x : Mmn) (lam : PosReal) :
    two_dimensional_total_variation_denoising_objective TV_I d lam x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) +
        ∑ i : Fin 3, ↑((lam : ℝ) * ψ[i] x) :=
      by
  rw [isotropic_two_dimensional_total_variation_denoising_fits_dual_block_model,
    composite_model_objective_apply, finite_sum_objective_apply, denoising_data_fidelity_apply]

end
