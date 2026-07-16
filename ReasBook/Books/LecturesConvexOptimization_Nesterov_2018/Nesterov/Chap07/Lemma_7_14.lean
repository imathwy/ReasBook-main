import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_44
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_58
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_62

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient WithTopConvexAnalysis

universe u

/- Lemma 7.14 lies in the Chapter 7 logarithmic barrier / concave-subgradient domain.

Mandatory domain-style sampling before refinement:
- `subdifferentialWithin` and the real-valued notation `∂[Q] f(x)` in `Chap03/Theorem_3_44`, the
  canonical constrained lower-support owner for real-valued functions;
- `barrierSubgradientClass` in `Chap07/Definition_7_58`, the chapter owner for the bounded
  constrained-subgradient conclusion;
- `logarithmicTransform` in `Chap07/Definition_7_62`, the chapter owner for `x ↦ log (ψ x)`;
- mathlib `ConcaveOn.comp` together with `strictConcaveOn_log_Ioi`, the canonical concavity API
  for composing a positive concave function with `Real.log`.

Best owner abstraction:
- source-facing: the explicit gradient witness for the constrained subgradient of
  `y ↦ -logarithmicTransform ψ y` on `interior Q`, together with the bounded barrier-subgradient
  class conclusion and concavity of `logarithmicTransform ψ`;
- core/canonical: `∂[interior Q]`, `barrierSubgradientClass`, `Seminorm.dualNorm`,
  `logarithmicTransform`, and `ConcaveOn`;
- bridge/view: the sign flip from the concave logarithmic transform to the convex function
  `y ↦ -logarithmicTransform ψ y`.

Primitive data:
- the set `Q`;
- the point-indexed seminorm family `pointNorm : interior Q → Seminorm ℝ E`;
- the witnesses `hpointNorm`;
- the function `ψ`;
- the gradient existence, positivity, concavity, and canonical dual-norm bound of `ψ` on
  `interior Q`.

Derived API:
- the constrained subgradient statement together with the witness-level dual-norm bound
  `-∇ (logarithmicTransform ψ) x ∈ ∂[interior Q] (-logarithmicTransform ψ) (x)` and
  `‖-∇ (logarithmicTransform ψ) x‖ₓ* ≤ 1`;
- the bounded barrier-subgradient-class statement for `y ↦ -logarithmicTransform ψ y`;
- the concavity of `logarithmicTransform ψ` on `interior Q`.

Source/core/bridge triage:
- source-facing: the explicit logarithmic-gradient witness and the bounded barrier-subgradient
  conclusion below;
- core/canonical: `∂[interior Q]` and `barrierSubgradientClass` applied to the negated
  logarithmic transform;
- bridge/view: the sign-flip passage from the concave logarithmic transform to the constrained
  real-valued subdifferential owner.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

-- Proof sketch: differentiate `x ↦ log (ψ x)` on `interior Q`, use
-- `∇ log(ψ x) = ψ(x)⁻¹ ∇ ψ(x)`, divide the assumed dual-norm bound
-- `‖∇ ψ(x)‖ₓ* ≤ ψ(x)` by the positive value `ψ(x)`, and record the resulting witness-level bound
-- `‖-∇ (logarithmicTransform ψ) x‖ₓ* ≤ 1` for the same constrained subgradient of
-- `y ↦ -logarithmicTransform ψ y`; the barrier-subgradient-class conclusion is then the derived
-- existential corollary. For concavity, compose the concave map `ψ` on
-- `interior Q` with the concave increasing function `log` on `(0, ∞)`.
/-- Lemma 7.14: if `ψ` is concave and strictly positive on `interior Q`, and its gradient has
pointwise `pointNorm`-dual norm at most `ψ x`, then at every `x ∈ interior Q` the gradient of
`x ↦ ln (ψ x)` yields, after the standard sign flip, a constrained subgradient of
`y ↦ - ln (ψ y)` over `interior Q`, written on the chapter notation
`-∇ (logarithmicTransform ψ) x ∈
∂[interior Q] (-logarithmicTransform ψ) (x)`, and this same canonical witness has
`pointNorm`-dual norm at most `1`; equivalently the negated logarithmic transform belongs to the
barrier subgradient class with bound `1`; moreover
`x ↦ ln (ψ x)` is concave on `interior Q`. -/
theorem logarithmicTransform_has_constrained_subgradient_norm_le_one_and_concaveOn
    {Q : Set E} {ψ : E → ℝ} {pointNorm : interior Q → Seminorm ℝ E}
    (hpointNorm : ∀ x : interior Q, Seminorm.IsNorm (pointNorm x))
    (hψ_grad : ∀ x : interior Q, HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ x : interior Q, 0 < ψ x)
    (hψ_dual_bound : ∀ x : interior Q,
      let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
      (pointNorm x).dualNorm (∇ ψ x) ≤ ψ x) :
    (∀ x : interior Q,
        -∇ (logarithmicTransform ψ) x ∈
          ∂[interior Q] (-logarithmicTransform ψ) (x) ∧
          (let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
           (pointNorm x).dualNorm (-∇ (logarithmicTransform ψ) x) ≤ 1)) ∧
      (fun y ↦ -logarithmicTransform ψ y) ∈
        barrierSubgradientClass (interior Q) (interior Q) pointNorm hpointNorm 1 ∧
      ConcaveOn ℝ (interior Q) (logarithmicTransform ψ) := sorry
