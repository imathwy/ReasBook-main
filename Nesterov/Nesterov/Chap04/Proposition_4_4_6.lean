import Mathlib
import Nesterov.Chap01.Definition_1_3_7
import Nesterov.Chap03.Definition_3_1_1_3
import Nesterov.Chap04.Definition_4_4_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open SetConstrainedMinimizationProblem
open scoped ConvexAnalysis
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁]

/- Proposition 4.4.6 lies in the chapter's quadratic-regularized value-function domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem.unconstrained`,
  `SetConstrainedMinimizationProblem.optimalValue`, and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in `Chap01/Definition_1_3_7`,
  the Chapter 1 owner for exact optimal values, already taking values in `EReal` so that
  unbounded-below cases are represented faithfully;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the upstream owner for the
  regularized local model at fixed base point `x` and parameter `M`;
* `ModifiedGaussNewtonStep.isMinOn_apply`, `modelValue`, and the whole-space notation
  `f[step](x)` in
  `Definition_4_4_12`, the source-facing minimizing-value bridge once the whole-space minimum is
  attained;
* `extendedRealRealPart` and `dom` in `Chap03/Definition_3_1_1_3`, the chapter bridge from the
  canonical `EReal` owner to its real-valued finite part on an explicit finite domain;
* `HasDirectionalDerivAt.hasDerivWithinAt` in `Chap03/Definition_3_1_3_1`, the chapter bridge
  from a source-facing directional-derivative identity to the within-interval derivative used in
  the monotonicity half of the proposition;
* `ConcaveOn.antitoneOn_derivWithin` in mathlib, the canonical derivative-monotonicity theorem
  for differentiable concave functions on intervals;
* `Definition_4_1_3.cubicRegularizationValue`, the nearby chapter pattern where a source-facing
  value is kept as thin derived API above an owner minimization problem.

Best owner abstraction:
* source-facing: the optimal-value function `M ↦ f_M(x)` for a fixed base point `x`;
* core/canonical: the Chapter 1 whole-space owner
  `unconstrained (quadraticallyRegularizedObjective (ψ x) M x)`;
* bridge/view: the canonical finite real part
  `extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)` on
  `dom (modifiedGaussNewtonOptimalValueAt ψ x)` and the attained-value identities provided by a
  chosen `ModifiedGaussNewtonStep`.

Primitive data:
* the local model family `ψ`;
* the base point `x`.

Derived API:
* the exact optimal value `modifiedGaussNewtonOptimalValueAt ψ x M : EReal`;
* the image-form expansion supplied by the Chapter 1 owner;
* the equality between that canonical owner value and a chosen minimizing model value;
* the source-facing positive-parameter owner
  `modifiedGaussNewtonOptimalValue ψ x : NNRealˣ → ℝ`, recovered as the finite real part of the
  canonical owner in the positive regime;
* the companion theorem identifying that positive-regime owner with the model value of any chosen
  whole-space minimizing-step family;
* the derivative antitonicity inherited directly from mathlib's concavity API on the canonical
  interval owner `extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)`.

The earlier local `ℝ`-valued `sInf` owner duplicated
`SetConstrainedMinimizationProblem.optimalValue` and silently lost the `-∞` case. This
refinement keeps the textbook value function, but defines it directly from the canonical Chapter 1
whole-space owner `unconstrained (quadraticallyRegularizedObjective (ψ x) M x)`. The public
positive-regime surface is exposed separately as
`modifiedGaussNewtonOptimalValue ψ x : NNRealˣ → ℝ`, while the concavity statement itself stays on
the cleaner interval owner
`extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)` and the step-based textbook value
`f_M(x)` is recovered only through bridge lemmas from `Definition_4_4_12`.

No extra notation is introduced for `modifiedGaussNewtonOptimalValueAt`: once a minimizing step is
chosen, the existing source-facing surface `f[step](x)` is already the natural textbook notation,
while a second notation for the unattained owner would add syntax without improving inference or
readability. -/

/-- The canonical modified Gauss--Newton optimal value `f_M(x)`, represented directly by the
Chapter 1 whole-space owner in `EReal`. -/
def modifiedGaussNewtonOptimalValueAt
    (ψ : E₁ → E₁ → ℝ) (x : E₁) : ℝ → EReal :=
  fun M ↦ (unconstrained (quadraticallyRegularizedObjective (ψ x) M x)).optimalValue

/-- Expanding `modifiedGaussNewtonOptimalValueAt ψ x` gives the Chapter 1 range-form infimum of
the regularized model values at parameter `M`. -/
-- Proof sketch: unfold `modifiedGaussNewtonOptimalValueAt` and apply the Chapter 1 owner lemma
-- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image`, then rewrite the whole-space
-- image over `Set.univ` as a range.
theorem modifiedGaussNewtonOptimalValueAt_eq_sInf_range
    (ψ : E₁ → E₁ → ℝ) (x : E₁) (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt ψ x M =
      sInf (Set.range fun y : E₁ ↦ (quadraticallyRegularizedObjective (ψ x) M x y : EReal)) :=
  sorry

-- Proof sketch: package the quadratic-regularized local model as the canonical whole-space owner
-- `unconstrained (quadraticallyRegularizedObjective (ψ x) M x)`,
-- apply the Chapter 1 equality
-- `optimalValue_eq_of_isMinOn` at the minimizing point `step x`, and rewrite the objective value
-- as `step.modelValue x`.
/-- Evaluating a chosen modified Gauss--Newton minimizer at `x` realizes the canonical owner
value `f_M(x)` as the minimum of the quadratic-regularized local model. -/
theorem modifiedGaussNewtonOptimalValueAt_eq_modelValue
    {ψ : E₁ → E₁ → ℝ} {𝓕 : Set E₁} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    modifiedGaussNewtonOptimalValueAt ψ x M = step.modelValue x := sorry

/-- In the whole-space case `𝓕 = Set.univ`, the canonical owner value at `x` is the whole-space
model value of any chosen modified Gauss--Newton minimizer. -/
-- Proof sketch: specialize
-- `modifiedGaussNewtonOptimalValueAt_eq_modelValue` to the subtype point `⟨x, Set.mem_univ x⟩`
-- and rewrite `modelValue` using the whole-space notation `f[step](x)`.
theorem modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv
    {ψ : E₁ → E₁ → ℝ} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    modifiedGaussNewtonOptimalValueAt ψ x M = f[step](x) := sorry

/-- Any chosen whole-space modified Gauss--Newton minimizer makes the canonical owner value
finite at the corresponding regularization parameter `M`. -/
-- Proof sketch: use
-- `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv` to exhibit
-- `modifiedGaussNewtonOptimalValueAt ψ x M` as the `EReal` coercion of the real number
-- `f[step](x)`.
theorem modifiedGaussNewtonOptimalValueAt_mem_dom_of_step
    {ψ : E₁ → E₁ → ℝ} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    M ∈ dom (modifiedGaussNewtonOptimalValueAt ψ x) := sorry

/-- On the finite-value domain of the canonical owner, its Chapter 3 real-part bridge agrees with
the source-facing model value `f_M(x)` of any chosen whole-space minimizing step. -/
-- Proof sketch: coerce both sides to `EReal`, rewrite the left side with
-- `coe_extendedRealRealPart` using `modifiedGaussNewtonOptimalValueAt_mem_dom_of_step`, and then
-- apply `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`.
theorem extendedRealRealPart_modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv
    {ψ : E₁ → E₁ → ℝ} {M : ℝ} (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M = f[step](x) :=
  sorry

/-- In the positive-regularization regime, the source-facing modified Gauss--Newton value is the
finite real part of the canonical whole-space owner value. -/
def modifiedGaussNewtonOptimalValue
    (ψ : E₁ → E₁ → ℝ) (x : E₁) :
    NNRealˣ → ℝ :=
  fun M ↦ extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) (M : ℝ)

/-- A positive-parameter minimizing step identifies the source-facing owner
`modifiedGaussNewtonOptimalValue ψ x M` with the textbook whole-space model value `f_M(x)`. -/
@[simp] theorem modifiedGaussNewtonOptimalValue_eq_modelValueAtUniv
    {ψ : E₁ → E₁ → ℝ} (x : E₁)
    (M : NNRealˣ) (step : ModifiedGaussNewtonStep ψ Set.univ (M : ℝ)) :
    modifiedGaussNewtonOptimalValue ψ x M = f[step](x) := by
  simpa [modifiedGaussNewtonOptimalValue] using
    extendedRealRealPart_modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv step x

-- Proof sketch: for fixed `x` and `y`, the map
-- `M ↦ ψ(x; y) + (M / 2) ‖y - x‖²` is affine, hence concave, in `M`. The canonical owner
-- `modifiedGaussNewtonOptimalValueAt ψ x` is the pointwise infimum of these affine functions in
-- `EReal`; once this canonical owner is known to be finite on `(0, ∞)`, the Chapter 3 real-part
-- bridge gives the source-facing real-valued function `M ↦ f_M(x)` as the positive-parameter
-- owner `modifiedGaussNewtonOptimalValue ψ x`, and chosen minimizing steps identify that owner
-- with the textbook quantity `f[step M](x)` through the bridge above.
/-- Internal bridge: if the canonical modified Gauss--Newton optimal value is finite on `(0, ∞)`,
then its Chapter 3 finite real part is concave in the regularization parameter `M` on that
interval. -/
theorem modifiedGaussNewtonOptimalValueAt_concaveInRegularization
    {ψ : E₁ → E₁ → ℝ} {x : E₁}
    (hfinite :
      Ioi (0 : ℝ) ⊆ dom (modifiedGaussNewtonOptimalValueAt ψ x)) :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)) := sorry

/-- Proposition 4.4.6: if for each positive `M` a whole-space modified Gauss--Newton minimizer is
chosen, then the canonical interval owner for `f_M(x)` is concave in the regularization
parameter `M` on `(0, ∞)`. The step-based textbook value remains available via
`modifiedGaussNewtonOptimalValue_eq_modelValueAtUniv`. -/
-- Proof sketch: first show the canonical owner value is finite on `(0, ∞)` using the chosen
-- minimizers `step M`; then apply
-- `modifiedGaussNewtonOptimalValueAt_concaveInRegularization` and restrict the resulting
-- concavity statement to the canonical interval owner.
theorem modifiedGaussNewtonOptimalValue_concaveInRegularization
    {ψ : E₁ → E₁ → ℝ} {x : E₁}
    (step : (M : Ioi (0 : ℝ)) → ModifiedGaussNewtonStep ψ Set.univ M.1) :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)) := by
  apply modifiedGaussNewtonOptimalValueAt_concaveInRegularization
  intro M hM
  exact modifiedGaussNewtonOptimalValueAt_mem_dom_of_step (step ⟨M, hM⟩) x

-- Proof sketch: combine the antitonicity of the derivative with the pointwise identification
-- `derivWithin (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)) (Ioi (0 : ℝ)) M =
--   (1 / 2) r_M(x)^2`
-- on `(0, ∞)`, where `r_M(x)` is the residual of the chosen whole-space modified Gauss--Newton
-- step at parameter `M`; the derivative antitonicity itself is the canonical mathlib result
-- `ConcaveOn.antitoneOn_derivWithin` applied to
-- `modifiedGaussNewtonOptimalValueAt_concaveInRegularization`.
/-- Internal bridge: once the derivative identity for the canonical real-part bridge of `f_M(x)`
is available, concavity implies that `(1 / 2) r_M(x)^2` is decreasing in the regularization
parameter `M` on `(0, ∞)`. -/
theorem antitone_modifiedGaussNewtonResidualSqHalf_of_derivWithin_eq
    {ψ : E₁ → E₁ → ℝ} {x : E₁}
    (step : (M : Ioi (0 : ℝ)) → ModifiedGaussNewtonStep ψ Set.univ M.1)
    (hdiff :
      DifferentiableOn ℝ
        (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x))
        (Ioi (0 : ℝ)))
    (hderiv :
      ∀ ⦃M : ℝ⦄ (hM : M ∈ Ioi (0 : ℝ)),
        derivWithin
            (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x))
            (Ioi (0 : ℝ)) M =
          (1 / 2 : ℝ) * (r[(step ⟨M, hM⟩)](x)) ^ (2 : ℕ)) :
    Antitone
      (fun M : Ioi (0 : ℝ) ↦
        (1 / 2 : ℝ) * (r[(step M)](x)) ^ (2 : ℕ)) :=
  sorry

-- Proof sketch: first obtain the differentiability of `M ↦ f_M(x)` on `(0, ∞)` together with the
-- identity
-- `derivWithin (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)) (Ioi (0 : ℝ)) M =
--   (1 / 2) r_M(x)^2`
-- from the Chapter 3 directional-derivative bridge for the canonical `EReal` owner, then apply
-- `antitone_modifiedGaussNewtonResidualSqHalf_of_derivWithin_eq`.
/-- Proposition 4.4.6 (monotonicity half): if a whole-space modified Gauss--Newton minimizer is
chosen for each positive regularization parameter, then the source-facing residual quantity
`(1 / 2) r_M(x)^2` is decreasing in `M` on `(0, ∞)`. The derivative identity needed for this
monotonicity consequence is derived internally from the Chapter 3 directional-derivative bridge,
so it is not exposed as extra public data. -/
theorem antitone_modifiedGaussNewtonResidualSqHalf
    {ψ : E₁ → E₁ → ℝ} {x : E₁}
    (step : (M : Ioi (0 : ℝ)) → ModifiedGaussNewtonStep ψ Set.univ M.1) :
    Antitone
      (fun M : Ioi (0 : ℝ) ↦
        (1 / 2 : ℝ) * (r[(step M)](x)) ^ (2 : ℕ)) :=
  sorry

end
