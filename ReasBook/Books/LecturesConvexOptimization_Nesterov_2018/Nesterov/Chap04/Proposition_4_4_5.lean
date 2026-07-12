import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Manifold

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

/- Proposition 4.4.5 lies in the local first-order smooth remainder domain for vector-valued maps
on convex subsets of real normed spaces.

Sampled owner-style declarations:
* the bundled smooth-map owner `C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯` from `Definition_4_4_8`;
* mathlib `LipschitzOnWith L (fun z ↦ fderiv ℝ f z) s`, the canonical on-set Jacobian-Lipschitz
  owner;
* mathlib `AffineMap.lineMap`, the canonical segment parameterization bridge;
* mathlib `taylor_mean_remainder_bound`, the codomain-general first-order Taylor remainder bound on
  a segment;
* mathlib `norm_image_sub_le_of_norm_deriv_le_segment'`, the one-dimensional mean-value estimate
  behind that Taylor bound.

Best owner abstraction:
* source-facing: the quadratic first-order Taylor remainder bound for a residual map with
  Jacobian Lipschitz on a convex feasible set;
* core/canonical: the bundled smooth map together with `LipschitzOnWith` on the derivative map;
* bridge/view: restriction to the affine line segment from `x` to `y`.

Primitive data:
* the smooth residual map `problem`;
* the feasible set `𝓕`;
* the derivative-Lipschitz owner `h_jacobian_lipschitz`.

Derived API:
* the pointwise quadratic remainder estimate at `x` and `y`.

The previous quantified hypothesis duplicated the owner content of `LipschitzOnWith`. This file
keeps the source-facing proposition but exposes the derivative control through the canonical
owner abstraction directly. The earlier interval-integral route would have imported the
proof-artifact hypothesis `[CompleteSpace F]` from `taylor_integral_remainder`; the proposition
itself is only about a first-order Taylor bound in an arbitrary real normed codomain, so the
ambient completeness assumption is removed from the public API. -/

namespace ContMDiffMap

-- Proof sketch: restrict `problem` to the affine segment from `x` to `y`, apply the codomain-free
-- first-order Taylor remainder bound on `[0, 1]`, use convexity of `𝓕` to keep the segment inside
-- the feasible set, and bound the second derivative along the segment by the Jacobian-Lipschitz
-- estimate coming from `h_jacobian_lipschitz`. This yields the textbook factor `1 / 2` without
-- assuming completeness of the codomain.
/-- Proposition 4.4.5: if the Jacobian of a smooth nonlinear equation problem is `L`-Lipschitz on
a convex feasible set `𝓕`, then for all `x, y ∈ 𝓕` the first-order Taylor remainder of the
residual map satisfies
`‖F(y) - F(x) - F'(x)(y - x)‖ ≤ (L / 2) * ‖y - x‖²`. -/
theorem jacobian_lipschitz_taylor_remainder_le
    (problem : SmoothMap)
    {𝓕 : Set E} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    ‖problem y - problem x - fderiv ℝ problem x (y - x)‖ ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := sorry

end ContMDiffMap
