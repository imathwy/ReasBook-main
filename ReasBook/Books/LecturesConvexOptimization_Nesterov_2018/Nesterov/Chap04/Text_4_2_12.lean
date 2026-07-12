import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Algorithm_1_7_1
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open NewtonSystem (AdmissiblePoint step)

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.12 lies in the real-Hilbert-space Newton / Hessian-Lipschitz domain.

Sampled owner declarations:
* `StrongConvexOn` in `Chap03/Definition_3_2_2`, the chapter owner for whole-space strong
  convexity
* `strongConvexOn_iff_hessian_lower_bound` in `Chap02/Definition_2_15`, the chapter bridge from
  the textbook Hessian quadratic-form lower bound to `StrongConvexOn`
* `NewtonSystem.AdmissiblePoint` and `NewtonSystem.step` in `Chap01/Algorithm_1_7_1`, the owner
  Newton domain and update for the stationarity system `∇ f = 0`
* `HasLipschitzContinuousHessian L3 f` and the notation `f ∈ C22[L3]` in `Definition_4_2_7`,
  the chapter owner for `C²` regularity plus global Hessian-Lipschitz control

Source/core/bridge triage:
* source-facing: the quadratic-gradient threshold region and the resulting Newton-step estimate
  from Text 4.2.12
* core/canonical: `StrongConvexOn Set.univ σ2 f`, `NewtonSystem.AdmissiblePoint (∇ f)`,
  `NewtonSystem.step (∇ f)`, and `f ∈ C22[L3]`
* bridge/view: the admissibility bridge from whole-space strong convexity plus `C²` regularity to
  `AdmissiblePoint (∇ f)`, while the quadratic-decrease estimate itself still uses `f ∈ C22[L3]`

Primitive data:
* a modulus `σ2`
* a Hessian-Lipschitz constant `L3`
* a function `f`
* the owner hypotheses `StrongConvexOn Set.univ σ2 f` and `f ∈ C22[L3]`
* for the admissibility bridge only, the weaker `C²` datum supplied by `hf_hessian.contDiff`

Derived API:
* the admissible-point witness for the Newton system `∇ f = 0`, exposed at the weaker
  strong-convexity-plus-`C²` layer
* the canonical Newton update `NewtonSystem.step (∇ f)`
* the quadratic-gradient threshold region and the decrease estimate on that region

The previous file introduced a second public owner for the Hessian lower bound and rebuilt the
Newton step from a local inverse-Hessian equivalence. This refinement keeps the source-facing
threshold region, states the main result directly on the canonical strong-convexity and
Newton-system owners, and keeps the admissibility bridge at the weaker `C²` layer needed for
Hessian nondegeneracy rather than at the full `C22[L3]` layer. -/

/-- The gradient-based threshold region `𝒬_g` from Text 4.2.12, written in multiplication form so
that the degenerate case `L₃ = 0` still gives the intended whole-space threshold. -/
def quadraticGradientRegion
    (f : E → ℝ) (σ2 : ℝ) (L3 : NNReal) : Set E :=
  {x | 4 * (L3 : ℝ) * ‖∇ f x‖ ≤ σ2 ^ (2 : ℕ)}

-- Proof sketch: unfold `quadraticGradientRegion`.
/-- Membership in `quadraticGradientRegion f σ₂ L₃` is exactly the threshold inequality
`4 L₃ ‖∇ f(x)‖ ≤ σ₂²`. -/
theorem mem_quadraticGradientRegion_iff
    {f : E → ℝ} {σ2 : ℝ} {L3 : NNReal} {x : E} :
    x ∈ quadraticGradientRegion f σ2 L3 ↔
      4 * (L3 : ℝ) * ‖∇ f x‖ ≤ σ2 ^ (2 : ℕ) :=
  Iff.rfl

section

variable [FiniteDimensional ℝ E]

namespace StrongConvexOn

private theorem gradient_det_ne_zero
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x : E) :
    (fderiv ℝ (∇ f) x).det ≠ 0 := by
  sorry

/-- Whole-space strong convexity and `C²` regularity canonically place every point in the
admissible Newton domain for the stationarity system `∇ f = 0`. -/
abbrev admissiblePoint
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x : E) :
    AdmissiblePoint (∇ f) :=
  ⟨x, hf.gradient_det_ne_zero hσ2 hf_C2 x⟩

-- Proof sketch: fix `x` in the threshold region, write the Newton step as
-- `T = NewtonSystem.step (∇ f) x`, use the integral Hessian remainder formula together with the
-- `L₃`-Lipschitz bound on `x ↦ ∇² f(x)` to estimate `‖∇ f(T)‖`, and use strong convexity to
-- control the inverse Hessian norm by `σ₂⁻¹`.
/-- Text 4.2.12: if `f ∈ C22[L₃]` is `σ₂`-strongly convex on `Set.univ`, then every point `x`
in the threshold region `𝒬_g = {x : 4 L₃ ‖∇ f(x)‖ ≤ σ₂²}` satisfies the quadratic gradient
decrease estimate
`‖∇ f(T(x))‖ ≤ (4 L₃ / σ₂²) ‖∇ f(x)‖²`
for the canonical Newton step `T(x) = NewtonSystem.step (∇ f) x` at the admissible point
supplied by `hf.admissiblePoint hσ₂ hf_hessian.contDiff x`. Under `f ∈ C22[L₃]`, this is the
canonical-owner reformulation of the textbook Hessian-lower-bound statement from
Definition 2.15. In this Hilbert-space formalization the textbook dual norm is identified with
the ambient norm. -/
theorem gradient_norm_newton_step_quadratic_decrease_on_region
    {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_hessian : f ∈ C22[L3])
    (x : E) (hx : x ∈ quadraticGradientRegion f σ2 L3) :
    ‖∇ f (step (∇ f) (hf.admissiblePoint hσ2 hf_hessian.contDiff x))‖ ≤
      (4 * (L3 : ℝ) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  sorry

end StrongConvexOn

end
