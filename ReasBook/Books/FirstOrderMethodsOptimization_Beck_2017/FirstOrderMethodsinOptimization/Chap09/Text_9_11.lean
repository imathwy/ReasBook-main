import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Example_6_61
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Text 9.11 is a `bridge/view` item in the Chapter 9 Mirror-C / Chapter 6 proximal-projection
domain. The source-facing owner for the one-step Mirror-C argmin is already
`mirror_c_update_objective` from Definition 9.6, while the Chapter 6 canonical owners on the
proximal side are `prox[...]` and `prox_extendedIndicator_eq_singleton_metricProjection`. The
primitive data in this file are therefore only the Euclidean specialization
`ω(x) = ‖x‖² / 2` and the Riesz identification of the chosen subgradient with `toDualMap ℝ E
gradf`; the explicit Euclidean formula is derived API rather than a second owner definition. -/

-- Proof sketch: expand `mirror_c_update_objective` for
-- `ω(y) = ‖y‖² / 2` and `s = toDualMap ℝ E gradf`; then identify
-- `((toDualMap ℝ E gradf) x : ℝ)` with `⟪gradf, x⟫` and rewrite the derivative of
-- `y ↦ ‖y‖² / 2` at `xk` as `toDualMap ℝ E xk`.
/-- Evaluating the canonical Mirror-C owner at the Euclidean specialization gives the linear term
`⟪t • gradf - xk, x⟫`, the scaled composite penalty `t g(x)`, and the quadratic term `‖x‖² / 2`.
-/
@[simp] theorem mirror_c_update_objective_half_squared_norm_apply
    (g : E → EReal) (xk gradf x : E) (t : ℝ) :
    mirror_c_update_objective g
        (fun y : E ↦ ((((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)))
        xk (toDualMap ℝ E gradf) t x =
      ((((inner ℝ (t • gradf - xk) x : ℝ)) : EReal) + ((t : EReal) * g x)) +
        ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) := sorry

-- Proof sketch: use `mirror_c_update_objective_half_squared_norm_apply` to rewrite the canonical
-- owner as the Euclidean objective `⟪t f'(xk) - xk, x⟫ + t g(x) + ‖x‖² / 2`, complete the square,
-- and compare with the proximal objective for `(t : EReal) • g` at `xk - t • f'(xk)` up to an
-- additive constant independent of `x`.
/-- Text 9.11 (1): in a Euclidean space with distance-generating function
`ω(x) = ‖x‖² / 2`, the one-step Mirror-C update is exactly the proximal subgradient update.
Equivalently, the next iterate minimizes the Mirror-C objective if and only if it belongs to the
proximal set of the scaled nonsmooth term `(t : EReal) • g` at the forward-subgradient point
`xk - t • f'(xk)`. -/
theorem isMinOn_mirror_c_half_squared_norm_update_iff_mem_scaled_prox
    (g : E → EReal) (xk gradf xNext : E) (t : ℝ) :
    IsMinOn
        (mirror_c_update_objective g
          (fun y : E ↦ ((((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)))
          xk (toDualMap ℝ E gradf) t)
        Set.univ xNext ↔
      xNext ∈ prox[((t : EReal) • g)] (xk - t • gradf) := sorry

section Indicator

variable [CompleteSpace E]

-- Proof sketch: apply the proximal-set reformulation from part (1) with `g = extendedIndicator C`.
-- Since `t > 0`, the scaled indicator `(t : EReal) • extendedIndicator C` agrees with
-- `extendedIndicator C`.
-- Then use the Chapter 6 singleton projection theorem to identify the proximal set with the
-- singleton containing the canonical metric projection.
/-- Text 9.11 (2): if the composite term is the indicator `δ_C` of a nonempty closed convex set
`C`, then in the same Euclidean specialization the Mirror-C update is exactly the standard mirror
descent, i.e. the projected subgradient step onto `C`. -/
theorem isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (xk gradf xNext : E) {t : ℝ} (ht : 0 < t) :
    IsMinOn
        (mirror_c_update_objective (extendedIndicator C)
          (fun y : E ↦ ((((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)))
          xk (toDualMap ℝ E gradf) t)
        Set.univ xNext ↔
      xNext = Pp[C, hC_nonempty, hC_closed, hC_convex] (xk - t • gradf) := sorry

end Indicator

end
