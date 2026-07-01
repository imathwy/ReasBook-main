import Mathlib
import Nesterov.Chap04.Definition_4_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.1 lies in the uniformly convex differentiable-analysis domain on real Hilbert
spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* `uniformConvexPowerModulus` in `Definition_4_2_8`
* `uniformConvexOn_iff_lower_tangent_power` in `Definition_4_2_8`
* `ConvexOn.of_gradient_monotone` in `Chap02/Theorem_2_3`

Best owner abstraction:
* source-facing: the power-type lower bound on the gradient monotonicity pairing
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: this theorem, which upgrades the source monotonicity inequality to the canonical
  owner predicate

Primitive data:
* the feasible set `Q`
* the objective `d`
* the power parameter `p` in the chapter regime `p ≥ 2`, and the modulus parameter `σp`
* the within-set gradient map `gradientWithin d Q`

Derived API:
* ordinary convexity of `d` on `Q`, obtainable from `ConvexOn.of_gradient_monotone`
* the power lower-tangent inequality from `uniformConvexOn_iff_lower_tangent_power`
* the uniform-convexity owner conclusion

This file therefore keeps only the source-facing monotonicity-to-owner bridge, instead of
introducing any parallel local uniform-convexity wrapper around `UniformConvexOn`. -/

section

variable {Q : Set E} {d : E → ℝ} {σp p : ℝ}

local notation "gradQ" => gradientWithin d Q

/-- Lemma 4.2.1: in the chapter regime `p ≥ 2`, if `d` is differentiable on a convex set `Q`
and its gradient satisfies the monotonicity bound
`⟪∇ d(x) - ∇ d(y), x - y⟫ ≥ σp ‖x - y‖^p`, then `d` is uniformly convex on `Q` with modulus
`r ↦ (1 / p) * σp * r^p`. -/
-- Proof sketch: integrate the monotonicity inequality along the segment from `x` to `y` to
-- recover the degree-`p` support remainder term, then use
-- `uniformConvexOn_iff_lower_tangent_power` to package the result as the canonical owner
-- predicate `UniformConvexOn`.
theorem uniformConvexOn_of_gradient_monotone
    (hp : 2 ≤ p)
    (hQ : Convex ℝ Q)
    (hd : DifferentiableOn ℝ d Q)
    (hmono :
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        σp * Real.rpow ‖x - y‖ p ≤ inner ℝ (gradQ x - gradQ y) (x - y)) :
    UniformConvexOn Q (uniformConvexPowerModulus σp p) d := sorry

end
