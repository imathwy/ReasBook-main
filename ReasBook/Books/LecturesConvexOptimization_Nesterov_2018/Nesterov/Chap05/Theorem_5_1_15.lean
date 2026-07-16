import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_24
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_2_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement SelfConcordantAuxiliaryFunction
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.15 lies in the Chapter 5 self-concordant damped-Newton domain.

Sampled owner declarations:
* `newtonDecrement`, the notation `λ[f; x | hPos; hInv]`, and the bridge
  `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the Chapter 5 owner for the Newton
  decrement;
* `selfConcordantNewtonShift` in `Definition_5_2_1`, whose `.damped` branch is the textbook
  shift formula `ξ = M_f λ`;
* `selfConcordantNewtonNextPoint` in `Definition_5_2_1`, the chapter owner for one-step
  self-concordant Newton updates and their `.damped` specialization;
* `localNorm_taylor_upper_bound_with_selfConcordantOmegaStar` in `Theorem_5_1_9`, the chapter
  owner for the upper Taylor bound with the canonical `ω_*` remainder on an admissible step.

Best owner abstraction:
* source-facing: the one-step value decrease for the damped specialization of
  `selfConcordantNewtonNextPoint`;
* core/canonical: `selfConcordantNewtonNextPoint` together with `newtonDecrement`;
* bridge/view: the admissible damped-step norm
  `λ_f(x) / (1 + M_f λ_f(x))`, the corresponding `ω_*` upper remainder, and the Fenchel bridge
  back to the source-facing `ω(M_f λ_f(x))` term.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom`;
* Hessian nondegeneracy at `x`.

Derived API:
* the damped self-concordant Newton next point at `x` as the specialization
  `selfConcordantNewtonNextPoint f Mf .damped x hx hH`;
* the Newton decrement `λ_f(x)` supplied by `NewtonDecrement.ofDetNeZero`;
* the canonical auxiliary-function argument
  `NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH`, whose coercion is `(Mf : ℝ) * λ_f(x)`.

The previous version still depended on a parallel damped-step wrapper. This refinement states the
value decrease directly for the canonical `.damped` specialization of
`selfConcordantNewtonNextPoint`, keeps the decrement side on the Chapter 5 owner surface, and is
organized around the chapter's upper-bound `ω_*` Taylor layer rather than the lower-bound
Hessian-comparison theorem.
-/

-- Proof sketch: write the step `d = x₊ - x` as the damped inverse-Hessian gradient direction, so
-- `‖d‖_x = λ_f(x) / (1 + M_f λ_f(x))`. Theorem 5.1.9 applies directly to this admissible step,
-- giving the upper Taylor remainder `ω_*` at the damped step norm, while the gradient pairing
-- along the Newton direction is
-- `-λ_f(x)^2 / (1 + M_f λ_f(x))`. Rewriting with the Fenchel relation
-- `ω(t) = t ω'(t) - ω_*(ω'(t))` gives the canonical remainder `M_f⁻² ω(M_f λ_f(x))` when
-- `0 < M_f`; at `M_f = 0`, the limiting branch is `(1 / 2) λ_f(x)^2`.
/-- Theorem 5.1.15: the damped Newton step
`x ↦ x - (1 + M_f λ_f(x))⁻¹ (∇² f(x))⁻¹ ∇ f(x)` decreases the objective by at least
`M_f⁻² ω(M_f λ_f(x))`, interpreted as `(1 / 2) λ_f(x)^2` when `M_f = 0`. -/
theorem selfConcordant_dampedNewtonStep_value_decrease
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    f (selfConcordantNewtonNextPoint f Mf .damped x hx hH) ≤
      f x -
        (if Mf = 0 then
          δ ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH)) :=
  sorry

end
