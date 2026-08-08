import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric
open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" => fun x ↦
  (metricProjection C hC_nonempty hC_closed.isComplete hC_convex x : E)

/- Proposition 5.4 is a `bridge/view` item over the Chapter 2 owner
`euclidean_distance_potential`. The primitive object is already defined upstream; this file keeps
only the projection-gradient and Lipschitz-gradient consequences derived from
`metricProjection` and the ambient gradient API. -/

-- Proof sketch: rewrite `euclidean_distance_potential C` as
-- `x ↦ ‖x‖^2 / 2 - (Metric.infDist x C)^2 / 2`. The gradient of the quadratic term is `x`, while
-- Proposition 3.12 identifies the gradient of the distance-squared term with `x - P_C(x)`.
-- Subtracting the two gradients gives `P_C(x)`.
/-- Proposition 5.4 (1) in owner form: the Chapter 2 potential
`x ↦ (‖x‖² - d_C(x)²) / 2` has gradient witness `P_C(x)` at every point. -/
theorem hasGradientAt_euclidean_distance_potential (x : E) :
    HasGradientAt (euclidean_distance_potential C) (P x) x := sorry

/-- Proposition 5.4 (1): for a nonempty closed convex set `C` in a complete real inner product
space, the gradient of `euclidean_distance_potential C` is the metric projection `P_C(x)`. -/
theorem gradient_euclidean_distance_potential_eq_metricProjection (x : E) :
    ∇ (euclidean_distance_potential C) x = P x :=
  (hasGradientAt_euclidean_distance_potential C hC_nonempty hC_closed hC_convex x).gradient

/-- Proposition 5.4 (2) in owner form: the gradient field of
`euclidean_distance_potential C` is globally `1`-Lipschitz. -/
theorem lipschitzWith_gradient_euclidean_distance_potential
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    LipschitzWith 1 (∇ (euclidean_distance_potential C)) := by
  let p : E → E := fun x ↦
    (metricProjection C hC_nonempty hC_closed.isComplete hC_convex x : E)
  have hgrad : ∇ (euclidean_distance_potential C) = p := by
    funext x
    exact gradient_euclidean_distance_potential_eq_metricProjection
      C hC_nonempty hC_closed hC_convex x

  simpa [p, hgrad] using
    metricProjection_nonexpansive C hC_nonempty hC_closed hC_convex

/-- Proposition 5.4 (2): in a complete real inner product space,
`euclidean_distance_potential C` has `1`-Lipschitz gradient, i.e.
`‖∇ψ_C(x) - ∇ψ_C(y)‖ ≤ ‖x - y‖` for all `x, y`. -/
theorem norm_gradient_euclidean_distance_potential_sub_le
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (x y : E) :
    ‖∇ (euclidean_distance_potential C) x - ∇ (euclidean_distance_potential C) y‖ ≤ ‖x - y‖ := by
  have hL : LipschitzWith 1 (∇ (euclidean_distance_potential C)) :=
    lipschitzWith_gradient_euclidean_distance_potential C hC_nonempty hC_closed hC_convex
  simpa using hL.norm_sub_le x y

end
