import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_36
import LecturesConvexOptimization_Nesterov_2018.Chap06.Theorem_6_5

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

-- Proof sketch: rewrite `1 - τ k` as `α ((k : ℤ) + 1) / α ((k : ℤ) - 1)` and clear this
-- positive denominator to reduce to Theorem 6.5.
/-- Corollary 6.2.1: for a fixed index `k`, if
`λ₁,k λ₂,k = α_k α_{k-1}` and `τ_k = 1 - α_{k+1} / α_{k-1}` with
`α_{k-1}, α_{k+1} > 0`, then the step-size condition
`τ_k^2 / (1 - τ_k) ≤ λ_{1,k} λ_{2,k}` is equivalent to
`(α_{k+1} - α_{k-1})^2 ≤ α_{k+1} α_k α_{k-1}^2`. -/
theorem step_size_condition_iff_alpha_three_term_inequality
    (α : Set.Ici (-1 : ℤ) → 𝕜) (lambda₁ lambda₂ τ : ℕ → 𝕜) (k : ℕ)
    (hα_pred_pos : 0 < α (switching_parameters_pred_index k))
    (hα_succ_pos : 0 < α (switching_parameters_succ_index k))
    (hprod : lambda₁ k * lambda₂ k =
      α (switching_parameters_curr_index k) * α (switching_parameters_pred_index k))
    (hτ : τ k = 1 - α (switching_parameters_succ_index k) / α (switching_parameters_pred_index k)) :
    τ k ^ (2 : ℕ) / (1 - τ k) ≤ lambda₁ k * lambda₂ k ↔
      (α (switching_parameters_succ_index k) - α (switching_parameters_pred_index k)) ^ (2 : ℕ) ≤
        α (switching_parameters_succ_index k) * α (switching_parameters_curr_index k) *
          (α (switching_parameters_pred_index k)) ^ (2 : ℕ) := sorry

end
