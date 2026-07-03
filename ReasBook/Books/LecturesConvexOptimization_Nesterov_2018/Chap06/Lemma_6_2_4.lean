import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_36

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: the owner recurrence on `switching_parameters α` scales both coordinates at once.
-- Then inspect the appropriate coordinate according to the parity of `k`, using the owner
-- theorems from `Definition_6_36` to read off `α_{k+1}` and `α_{k-1}`.
/-- Lemma 6.2.4: if the switching-parameter sequence attached to `α_k` satisfies the contraction
rule `parameters_{k+1} = (1 - τ_k) parameters_k`, then for every `k ≥ 0`,
`α_{k+1} = (1 - τ_k) α_{k-1}`. -/
theorem alpha_succ_eq_one_sub_tau_mul_pred_of_alternating_scalar_updates
    (α : Set.Ici (-1 : ℤ) → ℝ) (τ : ℕ → ℝ)
    (hparameters :
      ∀ k : ℕ, switching_parameters α (k + 1) = (1 - τ k) • switching_parameters α k)
    (k : ℕ) :
    α (switching_parameters_succ_index k) =
      (1 - τ k) * α (switching_parameters_pred_index k) := sorry
