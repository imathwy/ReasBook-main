

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_7 (from Chap05) -/
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

/-! ### Proposition_5_7 (from Chap05) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-
Proposition 5.7 is `source-facing`: it records the textbook smoothness estimate for the radial
function `x ↦ √(1 + ‖x‖²)`. Domain sampling in the Chapter 5/10 neighborhood points to
`is_l_smooth_on` as the owner abstraction for the conclusion, while the ambient real
inner-product-space geometry in this project is organized around the canonical `[ProperSpace E]`
owner rather than an explicit finite-dimensionality hypothesis or a coordinate model of `ℝ^n`.
The only primitive local datum is the radial function itself; the smoothness statement is derived
API on that owner.
-/

-- Proof sketch: `φ` is `C²` because it is the square root of the everywhere-positive smooth
-- function `x ↦ 1 + ‖x‖²`. Apply the owner-level Hessian criterion from Theorem 5.12. The
-- remaining pointwise estimate is the explicit Hessian computation
-- `D²φ(x) = (1 + ‖x‖²)^(-1/2) I - (1 + ‖x‖²)^(-3/2) (x ⊗ x)`, whose operator norm is at most `1`.
/-- Proposition 5.7: on any proper real inner-product space, hence in particular on every
finite-dimensional Euclidean space `ℝ^n`, the function `x ↦ √(1 + ‖x‖²)` is globally `1`-smooth
with respect to the Euclidean norm. -/
theorem sqrt_one_add_sq_norm_is_l_smooth :
    is_l_smooth_on (fun x : E ↦ Real.sqrt (1 + ‖x‖ ^ (2 : ℕ))) Set.univ 1 := by
  sorry

end
