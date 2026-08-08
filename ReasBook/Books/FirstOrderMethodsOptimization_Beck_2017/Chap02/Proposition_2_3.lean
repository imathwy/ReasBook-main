import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_11
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: if `y ∈ polar_cone K`, every pairing `y x` with `x ∈ K`
-- is at most `0`, and `0 ∈ K`, so the supremum defining `support_function K y`
-- is exactly `0`. If `y ∉ polar_cone K`, choose `x ∈ K` with `0 < y x`; since
-- `K` is closed under nonnegative scaling, every `t • x` with `t > 0` also lies
-- in `K`, so the support function dominates arbitrarily large real values and
-- therefore equals `⊤`, matching the indicator of the complement of the polar
-- cone.
/-- Proposition 2.3: if `K` is closed under nonnegative scalar multiplication and contains `0`,
then the support function `σ_K` is the indicator function of the polar cone
`Kᵒ = {y | ∀ x ∈ K, y x ≤ 0}`. -/
theorem support_function_eq_indicatorFunction_polarCone
    (K : Set E) (hK : IsNonnegativeCone K) (h0 : (0 : E) ∈ K) :
    support_function K = extendedIndicator (polar_cone K) := sorry

end
