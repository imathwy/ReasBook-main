import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_13
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Corollary 5.1.5 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical Hessian operator owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` in `Chap05/Definition_5_1_1`, the chapter owner
  for the local Hessian norm;
* `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the quantitative self-concordance owner;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` in `Chap05/Theorem_5_1_5`,
  which derives the domain membership of points satisfying the Dikin-radius hypothesis;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` in
  `Chap05/Proposition_5_0_15`, the pointwise Hessian comparison theorem in the same domain.

Source/core/bridge triage:
* source-facing: the averaged Hessian along the segment from `x` to `y` and its two comparison
  inequalities;
* core/canonical: `hessian f z`, `‖u‖[f; x]`, the interval integral
  `∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`, and `IsSelfConcordantOnWith dom Mf f`;
* bridge/view: the Dikin-radius hypothesis, which supplies both `0 < Mf` and the derived
  membership `y ∈ dom` needed for pointwise Hessian comparison along the segment.

Primitive data:
* a complete real inner-product space `E`;
* a domain `dom`, a function `f`, a self-concordance constant `Mf`, and points `x y : E`.

Derived API:
* the averaged Hessian integral `∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`;
* the admissibility hypothesis `y ∈ W⁰[f; x](1 / (Mf : ℝ))`;
* the individual lower and upper Loewner bounds obtained by projecting the paired comparison.

This file keeps the averaged Hessian as a source-facing integral expression built directly from the
canonical Hessian owner. The primitive owner-level result is the paired Loewner comparison, in
the same shape as `hessian_loewner_bounds_of_mem_openDikinEllipsoid`; the one-sided inequalities
are then exposed as derived projections rather than as parallel primitive wrappers. -/

namespace IsSelfConcordantOnWith

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

section

variable (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
variable (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))

-- Proof sketch: set `r := ‖y - x‖[f; x]` and
-- `G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`. Apply the pointwise
-- self-concordant Hessian comparison along the segment `τ ↦ x + τ • (y - x)`, derive `0 < Mf`
-- and `y ∈ dom` from the Dikin-radius hypothesis via Theorem 5.1.5(1), then integrate the
-- resulting Loewner inequalities over `τ ∈ [0, 1]`. The scalar integrals are
-- `∫_0^1 (1 - τ M_f r)^2 dτ = 1 - M_f r + (M_f^2 r^2) / 3` and
-- `∫_0^1 (1 - τ M_f r)⁻² dτ = (1 - M_f r)⁻¹`.
/-- Corollary 5.1.5: if `f` is self-concordant on `dom` with positive parameter `M_f`, `x ∈ dom`,
and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment from `x` to `y` lies
between the two explicit Loewner bounds built from `∇² f(x)`. In the source notation,
`r := ‖y - x‖_x` and `G := ∫_0^1 ∇² f(x + τ (y - x)) dτ`. The positivity of `M_f` and the
membership `y ∈ dom` are consequences of the displayed open-Dikin hypothesis. -/
theorem segmentAverageHessian_bounds
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    ((1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) • hessian f x ≤ G) ∧
      (G ≤ (1 / (1 - (Mf : ℝ) * r)) • hessian f x) := sorry

/-- Corollary 5.1.5 (lower bound): if `f` is self-concordant on `dom` with positive parameter
`M_f`, `x ∈ dom`, and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment
from `x` to `y` dominates the explicit lower Loewner bound built from `∇² f(x)`. The positivity
of `M_f` and the membership `y ∈ dom` are consequences of the displayed open-Dikin hypothesis. -/
theorem segmentAverageHessian_lower_bound
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    (1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) • hessian f x ≤ G := by
  simpa using segmentAverageHessian_bounds.1

/-- Corollary 5.1.5 (upper bound): if `f` is self-concordant on `dom` with positive parameter
`M_f`, `x ∈ dom`, and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment
from `x` to `y` is bounded above by the explicit Loewner bound built from `∇² f(x)`. The
positivity of `M_f` and the membership `y ∈ dom` are consequences of the displayed open-Dikin
hypothesis. -/
theorem segmentAverageHessian_upper_bound
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    G ≤ (1 / (1 - (Mf : ℝ) * r)) • hessian f x := by
  simpa using segmentAverageHessian_bounds.2

end

end IsSelfConcordantOnWith

end
