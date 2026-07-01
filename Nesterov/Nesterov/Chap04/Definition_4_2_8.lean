import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.8 lies in uniformly convex differentiable analysis on real Hilbert spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* mathlib `StrongConvexOn`
* Chapter 2 `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Definition_2_2`
* Chapter 3 `Definition_3_2_2`, which recalls strong convexity by the canonical owner and keeps
  the source first-order presentation as companion API

Best owner abstraction:
* source-facing: the degree-`p` uniform-convexity inequality with remainder
  `(1 / p) * σp * ‖y - x‖^p`
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: the first-order lower-support inequality phrased with `gradientWithin d Q`

Primitive data:
* a feasible set `Q`
* a function `d`
* a degree `p`
* the canonical fixed-modulus owner predicate `UniformConvexOn`
* at a fixed feasible base point, an explicit within-set gradient witness
  `HasGradientWithinAt d g Q x`

Derived API:
* existence of a positive modulus `σp` witnessing degree-`p` uniform convexity
* convexity of `Q`, already packaged by `UniformConvexOn`
* the chapter's first-order lower-support inequality with the degree-`p` remainder term
* the `gradientWithin` corollary obtained from `DifferentiableWithinAt ℝ d Q x`

This file therefore removes the duplicate local owner predicates, keeps the source-facing
degree-indexed existential surface as the main entry, reuses mathlib's fixed-modulus owner
`UniformConvexOn` as the canonical companion, and treats the `gradientWithin` statement as a
pointwise differentiability corollary of the primitive `HasGradientWithinAt` bridge. -/

/-- The degree-`p` modulus `r ↦ (1 / p) * σp * r^p` used in Definition 4.2.8. -/
abbrev uniformConvexPowerModulus (σp p : ℝ) : ℝ → ℝ :=
  fun r ↦ (1 / p) * σp * Real.rpow r p

section

variable {Q : Set E} {p : ℝ} {d : E → ℝ}

/- Definition 4.2.8: for a differentiable function on `Q`, the source-facing notion of
degree-`p` uniform convexity is that `p ≥ 2` and some positive modulus `σp` makes the canonical
fixed-modulus owner `UniformConvexOn Q (uniformConvexPowerModulus σp p) d` hold. The
first-order lower-support inequality below is the differentiable bridge for that existential
owner. -/
#check (2 ≤ p ∧ ∃ σp > 0, UniformConvexOn Q (uniformConvexPowerModulus σp p) d)

/-- Fixed-modulus first-order lower-support companion for Definition 4.2.8. -/
theorem uniformConvexOn_iff_lower_tangent_power
    {σp : ℝ}
    (hQ : Convex ℝ Q) (hd : DifferentiableOn ℝ d Q) :
    UniformConvexOn Q (uniformConvexPowerModulus σp p) d ↔
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
          uniformConvexPowerModulus σp p ‖y - x‖ := sorry

/-- Source-facing differentiable characterization of degree-`p` uniform convexity from
Definition 4.2.8. -/
theorem exists_pos_uniformConvexOn_iff_forall_lower_tangent_power
    (hQ : Convex ℝ Q) (hd : DifferentiableOn ℝ d Q) :
    (2 ≤ p ∧ ∃ σp > 0, UniformConvexOn Q (uniformConvexPowerModulus σp p) d) ↔
      2 ≤ p ∧
        ∃ σp > 0,
          ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
            d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
              uniformConvexPowerModulus σp p ‖y - x‖ := by
  constructor
  · rintro ⟨hp, σp, hσp, huniform⟩
    have hiff :
        UniformConvexOn Q (uniformConvexPowerModulus σp p) d ↔
          ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
            d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
              uniformConvexPowerModulus σp p ‖y - x‖ :=
      uniformConvexOn_iff_lower_tangent_power hQ hd
    refine ⟨hp, σp, hσp, ?_⟩
    exact hiff.mp huniform
  · rintro ⟨hp, σp, hσp, hlower⟩
    have hiff :
        UniformConvexOn Q (uniformConvexPowerModulus σp p) d ↔
          ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
            d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
              uniformConvexPowerModulus σp p ‖y - x‖ :=
      uniformConvexOn_iff_lower_tangent_power hQ hd
    refine ⟨hp, σp, hσp, ?_⟩
    exact hiff.mpr hlower

namespace UniformConvexOn

/-- A degree-`p` uniformly convex function lies above every feasible tangent plane arising from an
explicit within-set gradient witness, with the power remainder term from Definition 4.2.8. -/
theorem lower_tangent_power_of_hasGradientWithinAt
    {σp : ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (x : E) (hx : x ∈ Q) (g : E) (hgrad : HasGradientWithinAt d g Q x) (y : E) (hy : y ∈ Q) :
    d y ≥ d x + inner ℝ g (y - x) + uniformConvexPowerModulus σp p ‖y - x‖ := sorry

/-- A degree-`p` uniformly convex function lies above the tangent plane determined by its
within-set gradient at a feasible base point, with the power remainder term from Definition
4.2.8. -/
theorem lower_tangent_power
    {σp : ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (x : E) (hx : x ∈ Q) (hdiff : DifferentiableWithinAt ℝ d Q x) (y : E) (hy : y ∈ Q) :
    d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
      uniformConvexPowerModulus σp p ‖y - x‖ := by
  simpa using
    huniform.lower_tangent_power_of_hasGradientWithinAt
      x hx (gradientWithin d Q x) hdiff.hasGradientWithinAt y hy

end UniformConvexOn

end
