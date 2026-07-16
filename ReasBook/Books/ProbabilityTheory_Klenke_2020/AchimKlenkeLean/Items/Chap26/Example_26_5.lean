import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.Theorem_25_25
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.DriftIntegralProcess
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Theorem_26_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

local notation "PathSpace" => C(NNReal, ℝ)
local notation "State" => Fin 1 → ℝ
local notation "NoisePath" => EuclideanPathSpace 1
local notation "StatePath" => EuclideanPathSpace 1

private abbrev stateEquivReal : State ≃ₜ ℝ :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toHomeomorph

private abbrev pathSpaceEquivNoisePath : PathSpace ≃ NoisePath :=
  (Homeomorph.refl NNReal).continuousMapCongr stateEquivReal.symm

private def ornsteinUhlenbeckKernel (b : ℝ) (t : NNReal) : NNReal → ℝ :=
  fun s ↦ Real.exp (b * ((t : ℝ) - (s : ℝ)))

private def ornsteinUhlenbeckStrongSolutionValue
    (b σ : ℝ) (x : State) (w : NoisePath) (t : NNReal) : State :=
  fun _ ↦
    Real.exp (b * (t : ℝ)) * x 0 +
      σ * pathwiseItoIntegralAlong
        (ornsteinUhlenbeckKernel b t)
        (pathSpaceEquivNoisePath.symm w)
        dyadicPartitionSequence
        t

/- Domain-style sampling for Example 26.5:
* primary domain: one-dimensional strong solutions of SDEs driven by continuous Brownian paths,
  together with the chapter's dyadic pathwise Itô realization from Chapter 25;
* sampled project owners in this domain: `pathwiseItoIntegralAlong`,
  `StrongSolutionOperator`, `StrongSolutionOperator.realization`,
  `geometricBrownianStrongSolutionOperator`, and `pathProcess`;
* owner abstraction: the strong-solution layer is organized around `StrongSolutionOperator` /
  `StrongSolution`, while the stochastic-convolution term is canonically owned by
  `pathwiseItoIntegralAlong` rather than a bespoke dyadic-sum wrapper;
* primitive data: the OU kernel `ornsteinUhlenbeckKernel`, the pointwise path formula
  `ornsteinUhlenbeckStrongSolutionValue`, and the source-facing SDE relation;
* derived API: the canonical one-dimensional strong-solution operator, its scalar-path bridge,
  and the corresponding realization formulas.

Layer triage:
* source-facing: `ornsteinUhlenbeckStrongSolutionOperator` and `SolvesOrnsteinUhlenbeckSDE`;
* core/canonical: `pathwiseItoIntegralAlong`, `StrongSolutionOperator`, `StrongSolution`;
* bridge/view: `ornsteinUhlenbeckSolutionPath`, obtained by restricting the canonical
  one-dimensional solver to scalar initial data and scalar driving paths. -/

/-- Example 26.5, core/canonical layer: the explicit Ornstein--Uhlenbeck path formula packages as
the one-dimensional strong-solution operator from Definition 26.1. -/
def ornsteinUhlenbeckStrongSolutionOperator (b σ : ℝ) : StrongSolutionOperator 1 1 where
  toFun x w :=
    { toFun := ornsteinUhlenbeckStrongSolutionValue b σ x w
      continuous_toFun := by
        sorry }
  measurable_up_to := by
    sorry

/-- Evaluating the canonical Ornstein--Uhlenbeck strong-solution operator gives the textbook
formula in the unique coordinate. -/
theorem ornsteinUhlenbeckStrongSolutionOperator_apply
    (b σ : ℝ) (x : State) (w : NoisePath) (t : NNReal) (i : Fin 1) :
    ornsteinUhlenbeckStrongSolutionOperator b σ x w t i =
      Real.exp (b * (t : ℝ)) * x 0 +
        σ * pathwiseItoIntegralAlong
          (ornsteinUhlenbeckKernel b t)
          (pathSpaceEquivNoisePath.symm w)
          dyadicPartitionSequence
          t :=
  rfl

/-- Example 26.5, bridge/view layer: restricting the canonical one-dimensional strong-solution
operator to scalar initial data and scalar driving paths recovers the textbook scalar path. -/
abbrev ornsteinUhlenbeckSolutionPath (b σ x : ℝ) (w : PathSpace) : PathSpace :=
  pathSpaceEquivNoisePath.symm
    (ornsteinUhlenbeckStrongSolutionOperator b σ (stateEquivReal.symm x) (pathSpaceEquivNoisePath w))

/-- Evaluating the scalar-path bridge of the Ornstein--Uhlenbeck strong-solution operator gives
the textbook convolution formula. -/
theorem ornsteinUhlenbeckSolutionPath_apply
    (b σ x : ℝ) (w : PathSpace) (t : NNReal) :
    ornsteinUhlenbeckSolutionPath b σ x w t =
      Real.exp (b * (t : ℝ)) * x +
        σ * pathwiseItoIntegralAlong (ornsteinUhlenbeckKernel b t) w dyadicPartitionSequence t :=
  by
    simpa [ornsteinUhlenbeckSolutionPath, pathSpaceEquivNoisePath, stateEquivReal] using
      (ornsteinUhlenbeckStrongSolutionOperator_apply b σ (stateEquivReal.symm x)
        (pathSpaceEquivNoisePath w) t 0)

section Realization

variable {Ω : Type u}

-- Proof sketch: unfold `StrongSolutionOperator.realization`; the value at `(t, ω)` is the
-- initial datum
-- multiplied by `exp (b t)` plus `σ` times the pathwise convolution limit.
/-- Evaluating the realization of the canonical Ornstein--Uhlenbeck strong-solution operator
gives the textbook explicit formula for the Ornstein--Uhlenbeck process. -/
theorem ornsteinUhlenbeckStrongSolutionOperator_realization_apply
    (ξ : Ω → State) (b σ : ℝ) (W : Ω → NoisePath) (ω : Ω) (t : NNReal) (i : Fin 1) :
    (ornsteinUhlenbeckStrongSolutionOperator b σ).realization ξ W ω t i =
      Real.exp (b * (t : ℝ)) * ξ ω 0 +
        σ * pathwiseItoIntegralAlong
          (ornsteinUhlenbeckKernel b t)
          (pathSpaceEquivNoisePath.symm (W ω))
          dyadicPartitionSequence
          t :=
  rfl

end Realization

section StrongSolution

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The source-facing Ornstein--Uhlenbeck SDE relation on the chapter's canonical path-valued
strong-solution data. -/
def SolvesOrnsteinUhlenbeckSDE
    (μ : Measure Ω) (b σ : ℝ) (ξ : Ω → State)
    (W : Ω → NoisePath) (X : Ω → StatePath) : Prop :=
  IsBrownianMotion μ (fun t ω ↦ pathProcess W t ω 0) ∧
    (∀ ω : Ω, X ω 0 = ξ ω) ∧
    pathProcess X =
      fun t ω ↦ fun i ↦
        ξ ω i +
          σ * pathProcess W t ω 0 +
          driftIntegralProcess (fun s ω ↦ b * pathProcess X s ω i) t ω

-- Proof sketch: verify that Brownian motion gives the driving noise, evaluate the explicit
-- Ornstein--Uhlenbeck formula at time `0`, and use the stochastic Fubini calculation from the
-- example to rewrite the convolution term into the integral equation
-- `X_t = ξ + σ W_t + ∫₀ᵗ b X_s ds`.
/-- Example 26.5: for `b, σ ∈ ℝ`, the explicit Ornstein--Uhlenbeck process
`X_t = exp (b t) ξ + σ ∫₀ᵗ exp (b (t - s)) dW_s` is a strong solution of
`X₀ = ξ`, `dX_t = σ dW_t + b X_t dt`. -/
theorem ornsteinUhlenbeckProcess_isStrongSolution
    {μ : Measure Ω} {W : Ω → NoisePath}
    (hW : IsBrownianMotion μ (fun t ω ↦ pathProcess W t ω 0))
    {ξ : Ω → State} {b σ : ℝ} :
    StrongSolution 1 1 (SolvesOrnsteinUhlenbeckSDE μ b σ) ξ W
      ((ornsteinUhlenbeckStrongSolutionOperator b σ).realization ξ W) := by
  refine ⟨ornsteinUhlenbeckStrongSolutionOperator b σ, rfl, ?_⟩
  sorry

end StrongSolution

end ProbabilityTheory
