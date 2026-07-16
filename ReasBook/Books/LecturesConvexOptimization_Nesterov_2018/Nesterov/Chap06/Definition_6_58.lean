import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Theorem_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

/- Definition 6.58 [Constant `C_{v,t}`]: for `t ≥ 0`, the Chapter 6 constant `C_{v,t}` is
`a₀ Δ(x₀) + (1 / (1 + v)) * (∑ k = 1 to t, a_k^(1 + v) / A_k^v) * G_v * D^(1 + v)`, with
`A_k = A[a](k)`. In the chapter API this is exactly the owner
`ConditionalGradientContraction.contractionErrorTerm`, so the item is formalized as a direct
recall of that canonical definition. -/
recall ConditionalGradientContraction.contractionErrorTerm
    (Δ0 : ℝ) (a : ℕ → ℝ) (Gv D v : ℝ) (t : ℕ) :
    ℝ

end

end
