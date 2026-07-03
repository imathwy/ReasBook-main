import LecturesConvexOptimization_Nesterov_2018.Chap06.Algorithm_6_5
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_53
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_55
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_59
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient TotalVariationNotation WeightSequenceNotation

universe u

namespace ConditionalGradientContraction

section HolderGradient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `HolderGradientOn v Gv Q f g` records that the chosen dual field `g` represents the
within-set derivative of `f` on `Q` at every feasible point and is `v`-Hölder there with
constant `Gv`, using mathlib's canonical on-set Hölder owner `HolderOnWith`. -/
class HolderGradientOn
    (v Gv : NNReal) (Q : Set E) (f : E → ℝ) (g : E → StrongDual ℝ E) : Prop where
  hasFDerivWithinAt {x : E} (hx : x ∈ Q) : HasFDerivWithinAt f (g x) Q x
  holderOn : HolderOnWith Gv v g Q

namespace HolderGradientOn

theorem norm_sub_le
    {v Gv : NNReal} {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E}
    (hf : HolderGradientOn v Gv Q f g) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖g x - g y‖ ≤ (Gv : ℝ) * Real.rpow ‖x - y‖ (v : ℝ) := by
  simpa [dist_eq_norm] using hf.holderOn.dist_le hx hy

end HolderGradientOn

end HolderGradient

section LinearizedCompositeGap

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The extended-valued feasible-point bridge for the Chapter 6 linearized composite gap,
obtained by viewing the canonical restricted dual value of the real-valued lift of `Ψ` in
`EReal`. -/
abbrev linearizedCompositeGap
    (S : Set E) (Ψ : E → ℝ) (g : StrongDual ℝ E) (x0 : S) : EReal :=
  withTopToEReal
    (restrictedDualFunction S (fun x ↦ (Ψ x : WithTop ℝ))
      ⟨x0, by simp [withTopEffectiveDomain, x0.property]⟩ g)

end LinearizedCompositeGap

section TotalVariationBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- In the ambient-gradient specialization, the chosen-dual gap
`linearizedCompositeGap S Ψ g x₀` reduces to the Chapter 6 total-variation owner
`δ[S, f, Ψ](x₀)`. -/
theorem linearModelTotalVariation_eq_linearizedCompositeGap
    (S : Set E) (f Ψ : E → ℝ) (x0 : S) :
    δ[S, f, Ψ](x0) =
      linearizedCompositeGap S Ψ (InnerProductSpace.toDualMap ℝ E (∇ f x0)) x0 := sorry

end TotalVariationBridge

section ContractionErrorTerm

/-- The error quantity `C_{v,t}` attached to the scalar initial gap `Δ(x₀)`, the weights `a_t`,
the canonical accumulated weights `A_t = A[a](t)`, and the Hölder data `G_v` and `D`. This is
the source-facing specialization of `linearOptimizationOracleErrorBound`, with the factor
`(1 + v)⁻¹` absorbed into the Hölder constant. -/
abbrev contractionErrorTerm
    (Δ0 : ℝ) (a : ℕ → ℝ) (Gv D v : ℝ) (t : ℕ) : ℝ :=
  linearOptimizationOracleErrorBound Δ0 a (Gv / (1 + v)) D v t

namespace ContractionErrorNotation

/- Source-facing Lean notation for the Chapter 6 constant `C_{v,t}` with the ambient data fixed
by the surrounding context. -/
scoped notation:max "C[" Δ0 ", " a ", " Gv ", " D ", " v "](" t:arg ")" =>
  contractionErrorTerm Δ0 a Gv D v t

end ContractionErrorNotation

end ContractionErrorTerm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The estimating functional sequence `φ_t` generated from the weights `a_t`, the initial model
`\tilde f`, the smooth term `f`, the chosen dual gradient field, the regularizer `Ψ`, and the
iterate sequence `x_t`. -/
def estimatingFunctionalSequence
    (a : ℕ → ℝ) (tildeF : E → ℝ) (f : E → ℝ) (gradF : E → StrongDual ℝ E) (Ψ : E → ℝ)
    (xSeq : ℕ → E) : ℕ → E → ℝ
  | 0 => fun x ↦ a 0 * tildeF x
  | t + 1 => fun x ↦
      estimatingFunctionalSequence a tildeF f gradF Ψ xSeq t x +
        a (t + 1) *
          (f (xSeq t) + gradF (xSeq t) (x - xSeq t) + Ψ x)

namespace EstimatingFunctionNotation

/- Source-facing Lean notation for the Chapter 6 estimating sequence `φ_t(x)` with all ambient
data fixed explicitly. -/
scoped notation:max "φ[" a ", " tildeF ", " f ", " gradF ", " Ψ ", " xSeq "]("
    t:arg ", " x:arg ")" =>
  estimatingFunctionalSequence a tildeF f gradF Ψ xSeq t x

end EstimatingFunctionNotation

namespace ContractedFeasibleSetTrustRegionScheme

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- The estimating functional sequence `φ_t` attached to a contracted-feasible-set trust-region
scheme and an initial model `\tilde f`. -/
abbrev estimatingFunction
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    (a : ℕ → ℝ) (tildeF : E → ℝ) : ℕ → E → ℝ :=
  estimatingFunctionalSequence
    a tildeF problem.smoothPart method.gradient (withTopRealPart problem.nonsmoothPart) method

namespace EstimatingFunctionNotation

/- Source-facing Lean notation for the specialized estimating sequence `φ_t(x)` attached to
Algorithm 6.5. -/
scoped notation:max "φ[" method ", " a ", " tildeF "](" t:arg ", " x:arg ")" =>
  ContractedFeasibleSetTrustRegionScheme.estimatingFunction method a tildeF t x

end EstimatingFunctionNotation

end ContractedFeasibleSetTrustRegionScheme

open ContractedFeasibleSetTrustRegionScheme
open scoped ContractionErrorNotation EstimatingFunctionNotation

/- Theorem 6.14 lies in the Chapter 6 contracted conditional-gradient / estimating-sequence
domain.

Mandatory domain-style sampling:
- `accumulatedWeights` / `weightCoefficient` in `Definition_6_53`, the chapter owners of
  `A[a](t)` and `τ[a](t)`;
- `ContractedFeasibleSetTrustRegionScheme` in `Algorithm_6_5`, the source-facing owner of the
  iterate, step-size, and contracted-subproblem data;
- `linearizedCompositeGap` in this file, the chosen-dual Chapter 6 gap owner attached to the
  actual linear model used by Algorithm 6.5;
- `linearModelTotalVariation` in `Definition_6_59`, the Chapter 6 owner `δ[Q, f, Ψ](x)` of the
  ambient-gradient total variation at a feasible point;
- `linearOptimizationOracleErrorBound` in `Definition_6_53`, the canonical Chapter 6 owner whose
  specialization here is the source-facing error term `C_{v,t}`;
- `HolderGradientOn.upper_model` in `Proposition_6_39`, the nearby Hölder upper-model bridge used
  to control the smooth remainder.

Best owner abstraction:
- source-facing: Theorem 6.14's weighted estimating-function bound and the one-step decrease
  bound written with the chosen-dual gap `linearizedCompositeGap`;
- core/canonical: `ContractedFeasibleSetTrustRegionScheme`, `A[a](t)`, `τ[a](t)`,
  `linearOptimizationOracleErrorBound`, `HolderGradientOn`, and the ambient-gradient owner
  `linearModelTotalVariation`;
- bridge/view: `linearModelTotalVariation_eq_linearizedCompositeGap`, which identifies the
  chosen-dual owner with `δ[Q, f, Ψ](x)` only under an explicit ambient-gradient specialization.

Primitive data:
- the ambient composite problem and Algorithm 6.5 method data;
- the weight sequence `a`, together with the positivity condition `∀ t, 0 < a t` and the
  canonical coefficient identity `method.stepSize t = τ[a](t)`;
- the Hölder-gradient owner `HolderGradientOn` and the feasible-set diameter bound.

Derived API:
- the specialized estimating sequence `estimatingFunction`;
- the theorem-surface notation `φ[method, a, \tilde f](t, x)` for that specialized sequence;
- the source-facing Chapter 6 error term `contractionErrorTerm`, together with the theorem-surface
  notation `C[Δ₀, a, Gᵥ, D, v](t)`, both derived from `linearOptimizationOracleErrorBound`;
- the weighted objective upper bound, the chosen-dual decrease estimate below, and its ambient-
  gradient specialization through `linearModelTotalVariation_eq_linearizedCompositeGap`.

Source/core/bridge triage:
- source-facing: the two statements of Theorem 6.14;
- core/canonical: the chapter owners listed above, with Theorem 6.14 (2) surfaced through the
  actual chosen-dual linear model carried by `method.gradient`;
- bridge/view: `linearizedCompositeGap`, whose defining body is exactly the canonical
  `restrictedDualFunction` bridge, and `linearModelTotalVariation_eq_linearizedCompositeGap`,
  which specializes that chosen-dual owner to `δ[Q, f, Ψ](x_t)` when the ambient gradient really
  matches the chosen field.
-/

-- Proof sketch: prove the estimate by induction on `t`. For the induction step, unfold
-- `ContractedFeasibleSetTrustRegionScheme.estimatingFunction`, apply the contracted-subproblem
-- minimizing property from `Algorithm_6_5` at step `t` to the contracted point determined by the
-- comparison vector `x ∈ Q`, then use the Hölder upper-model bound coming from `hf_holder`
-- together with the positive-weight hypothesis `ha_pos`, the diameter bound `hdiam`, and the
-- weight identity `τ_t = a_{t+1} / A_{t+1}` to absorb the remainder into
-- `contractionErrorTerm`.
/-- Theorem 6.14 (1): along Algorithm 6.5, if the initial model `\tilde f` underestimates the
initial objective up to the scalar initial-gap term `Δ(x₀)` and the weights satisfy `a_t > 0`,
then for every Hölder exponent parameter `v : NNReal`, every index `t ≥ 0`, and every
comparison point `x ∈ Q`, one has
`A_t \bar f(x_t) ≤ φ_t(x) + C_{v,t}`. -/
theorem weighted_objective_le_estimatingFunction_add_contractionError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    (a : ℕ → ℝ) (tildeF : E → ℝ) (Δ0 : ℝ) {v Gv : NNReal} {D : ℝ}
    (hinitial :
      ∀ ⦃x : E⦄, x ∈ problem.feasibleSet →
        problem.smoothPart x0 + withTopRealPart problem.nonsmoothPart x0 ≤ tildeF x + Δ0)
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) {x : E} (hx : x ∈ problem.feasibleSet) :
      A[a](t) *
          (problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) ≤
        φ[method, a, tildeF](t, x) +
          C[Δ0, a, (Gv : ℝ), D, (v : ℝ)](t) := sorry

section LinearizedCompositeGapObjectiveDrop

-- Proof sketch: compare `x_{t+1}` with the contracted candidate `(1 - τ_t) x_t + τ_t y` in the
-- local minimizing property, identify the best comparison over `y ∈ Q` with the chosen-dual gap
-- `linearizedCompositeGap problem.feasibleSet (withTopRealPart problem.nonsmoothPart)
--   (method.gradient (method t)) (method.iterates t)`,
-- and then use the Hölder upper-model estimate from `hf_holder` plus the diameter control
-- `hdiam` to bound the remainder by
-- `(G_v D^(1+v) / (1+v)) τ_t^(1+v)`.
/-- Theorem 6.14 (2): at every step of Algorithm 6.5, the composite-objective decrease
`\bar f(x_t) - \bar f(x_{t+1})` is bounded below by the step size times the chosen-dual
linearized composite gap attached to the actual linear model used at `x_t`, minus the Hölder
remainder
`(G_v D^(1+v) / (1 + v)) τ_t^(1+v)`. -/
theorem objective_drop_ge_stepSize_mul_linearizedCompositeGap_sub_holderError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) :
      (((problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            linearizedCompositeGap problem.feasibleSet
              (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
              (method.iterates t) -
          (((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
              Real.rpow (method.stepSize t) (1 + (v : ℝ)) : ℝ) : EReal) := sorry

end LinearizedCompositeGapObjectiveDrop

section TotalVariationObjectiveDrop

variable [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: apply the chosen-dual decrease theorem above and then rewrite the gap term by the
-- supplied identification with the Chapter 6 total-variation owner. This identification is the
-- one induced, for example, by `linearModelTotalVariation_eq_linearizedCompositeGap` when the
-- chosen derivative field really is the ambient gradient at `x_t`.
/-- Under the additional hypothesis that the chosen-dual gap used by Algorithm 6.5 agrees at
`x_t` with the Chapter 6 total-variation owner `δ[Q, f, Ψ](x_t)` (for instance because the chosen
derivative field agrees there with the ambient gradient), Theorem 6.14 (2) specializes to the
ambient-gradient total-variation form. -/
theorem objective_drop_ge_stepSize_mul_totalVariation_sub_holderError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ)
    (hgap :
      linearizedCompositeGap problem.feasibleSet
          (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
          (method.iterates t) =
        δ[problem.feasibleSet, problem.smoothPart,
          withTopRealPart problem.nonsmoothPart]((method.iterates t))) :
      (((problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            (δ[problem.feasibleSet, problem.smoothPart,
              withTopRealPart problem.nonsmoothPart]((method.iterates t))) -
          (((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
              Real.rpow (method.stepSize t) (1 + (v : ℝ)) : ℝ) : EReal) := by
  have hdrop :=
    objective_drop_ge_stepSize_mul_linearizedCompositeGap_sub_holderError
      method hf_holder hdiam t
  simpa [hgap] using hdrop

end TotalVariationObjectiveDrop

end ConditionalGradientContraction

end
