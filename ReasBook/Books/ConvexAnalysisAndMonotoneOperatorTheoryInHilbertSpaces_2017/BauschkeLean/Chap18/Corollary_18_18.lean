import BauschkeLean.Chap17.Proposition_17_36
import BauschkeLean.Chap18.Corollary_18_17

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace
open scoped Gradient

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 18.18 is the quadratic-form inequality for a self-adjoint monotone
  bounded operator.
- `core/canonical`: the chapter-level owner stack is the quadratic potential `q[L]`, together with
  `quadraticPotential_convexOn_univ_of_isMonotone`,
  `gradient_quadraticPotential_eq_of_isSelfAdjoint`, and
  `gradient_lipschitz_iff_cocoercive_of_differentiable_convex`.
- `bridge/view`: this corollary specializes the owner stack to `L` and evaluates the resulting
  cocoercivity inequality at `(x, 0)`.
-/
/-- Corollary 18.18: if a bounded operator `L : H →L[ℝ] H` is self-adjoint and monotone, then
`‖L‖ * ⟪L x, x⟫_ℝ ≥ ‖L x‖^2` for every `x`. -/
theorem norm_mul_inner_apply_ge_sq_norm_of_isSelfAdjoint_of_isMonotone
    (L : H →L[ℝ] H) (hL_self : IsSelfAdjoint L) (hL_mono : L.toLinearMap.IsMonotone) (x : H) :
    ‖L‖ * ⟪L x, x⟫_ℝ ≥ ‖L x‖ ^ (2 : ℕ) := by
  by_cases hzero : ‖L‖ = 0
  · -- In the degenerate branch, the operator itself is zero, so the inequality is trivial.
    have hL_zero : L = 0 := (ContinuousLinearMap.opNorm_zero_iff (f := L)).1 hzero
    subst hL_zero
    simp
  · -- In the positive branch, apply Corollary 18.17 to the quadratic potential `q[L]`.
    have hnorm_pos : 0 < ‖L‖ := by
      exact lt_of_le_of_ne (norm_nonneg L) (by
        intro hnorm_zero
        exact hzero hnorm_zero.symm)
    let β : Set.Ioi (0 : ℝ) := ⟨‖L‖, hnorm_pos⟩
    have hdiff : Differentiable ℝ (q[L]) := quadraticPotential_differentiable L
    have hconv : ConvexOn ℝ Set.univ (q[L]) :=
      quadraticPotential_convexOn_univ_of_isMonotone L hL_mono
    have hgrad : ∇ (q[L]) = L := gradient_quadraticPotential_eq_of_isSelfAdjoint L hL_self
    have hLip : LipschitzWith (Real.toNNReal (β : ℝ)) (∇ (q[L])) := by
      rw [hgrad]
      simpa [β, Real.toNNReal_of_nonneg (norm_nonneg L)] using L.lipschitz
    have hcoco :
        CocoerciveOn (1 / (β : ℝ)) (Set.univ : Set H) (fun y : Set.univ ↦ L y) := by
      simpa [β, hgrad] using
        (gradient_lipschitz_iff_cocoercive_of_differentiable_convex (f := q[L]) hdiff hconv β).1
          hLip
    -- Specializing cocoercivity at `(x, 0)` gives the desired one-point quadratic estimate.
    have hspecial : (1 / ‖L‖) * ‖L x‖ ^ (2 : ℕ) ≤ ⟪L x, x⟫_ℝ := by
      simpa [β, ContinuousLinearMap.map_zero, real_inner_comm] using
        hcoco.2 ⟨x, by simp⟩ ⟨0, by simp⟩
    -- Multiply through by the positive norm to recover the target surface.
    have hmul :
        ‖L‖ * ((1 / ‖L‖) * ‖L x‖ ^ (2 : ℕ)) ≤ ‖L‖ * ⟪L x, x⟫_ℝ :=
      mul_le_mul_of_nonneg_left hspecial (norm_nonneg L)
    have hresult : ‖L x‖ ^ (2 : ℕ) ≤ ‖L‖ * ⟪L x, x⟫_ℝ := by
      calc
        ‖L x‖ ^ (2 : ℕ) = ‖L‖ * ((1 / ‖L‖) * ‖L x‖ ^ (2 : ℕ)) := by
          field_simp [hnorm_pos.ne']
        _ ≤ ‖L‖ * ⟪L x, x⟫_ℝ := hmul
    simpa [ge_iff_le] using hresult

end ContinuousLinearMap
