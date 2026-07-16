import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap05.Definition_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 5.7 is `source-facing`: its content is the quadratic upper model on a convex set. The
Chapter 5 owner abstraction for smoothness on a set is `is_l_smooth_on` from Definition 5.2, so
the convexity of `D` is kept as its own hypothesis instead of being rebundled into a local
wrapper. The source-facing linear term is the ambient gradient `∇ f x`; this matches the chapter
owner API, which controls ambient differentiability on `D`, without introducing the stronger
within-set uniqueness hypotheses that would be needed to justify `gradientWithin`. -/

-- Proof sketch: parametrize the segment from `x` to `y`, use convexity of `D` to keep the segment
-- inside the domain, differentiate `t ↦ f (x + t • (y - x))`, integrate the resulting derivative,
-- and bound the error term with Cauchy--Schwarz together with the `L`-Lipschitz control of the
-- ambient gradient field encoded by `is_l_smooth_on f D L`.
/-- Lemma 5.7: if `D` is convex and `f` is `L`-smooth on `D`, then
`f y ≤ f x + ⟪∇ f x, y - x⟫ + (L / 2) * ‖x - y‖²` for all `x, y ∈ D`. -/
theorem is_l_smooth_on_descent_lemma {L : NNReal} {D : Set E} {f : E → ℝ}
    (hD : Convex ℝ D) (hf : is_l_smooth_on f D L)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := sorry

end
