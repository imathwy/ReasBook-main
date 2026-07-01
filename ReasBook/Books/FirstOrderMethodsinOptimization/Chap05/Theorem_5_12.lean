import FirstOrderMethodsinOptimization.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ} {p : ENNReal} [Fact (1 ≤ p)]

local notation "E" => WithLp p (Fin n → ℝ)

/-
Theorem 5.12 is a `bridge/view` item. Its owner abstractions are the chapter predicate
`is_l_smooth_on`, specialized to `Set.univ`, and mathlib's Lipschitz/Fréchet-derivative API. The
only primitive mathematical data is the `C²` function `f`; the Hessian bound is the derived
pointwise estimate on
`fderiv ℝ (fderiv ℝ f)`.
-/

-- Proof sketch: for `(ii) → (i)`, integrate the derivative of `fderiv ℝ f` along each line
-- segment and bound the resulting Bochner integral by the uniform operator-norm estimate on the
-- Hessian. For `(i) → (ii)`, evaluate the `L`-Lipschitz estimate for `fderiv ℝ f` on small
-- increments `x + t • d`, divide by `t`, and pass to the limit using the `C²` hypothesis.
/-- Theorem 5.12: on the canonical `WithLp p (Fin n → ℝ)` model of `ℝ^n`, a twice continuously
differentiable function is globally `L`-smooth for the `l_p` norm if and only if its Fréchet
Hessian, viewed as the derivative of `fderiv ℝ f`, has nonnegative operator norm at most `L` at
every point. This is the canonical operator-norm rendering of the textbook bound
`‖∇² f(x)‖_{p,q} ≤ L`. -/
theorem is_l_smooth_iff_hessian_operator_norm_le
    {f : E → ℝ} {L : NNReal} (hf : ContDiff ℝ 2 f) :
    is_l_smooth_on f Set.univ L ↔
      ∀ x : E, ‖fderiv ℝ (fderiv ℝ f) x‖₊ ≤ L := sorry

end
