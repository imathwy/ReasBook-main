import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_18

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

/-- A `State`-valued process is a standard `d`-dimensional Brownian motion if each coordinate is a
real Brownian motion and the coordinate family is independent. -/
@[mk_iff isStandardBrownianMotionVector_iff]
class IsStandardBrownianMotionVector (μ : Measure Ω) (W : VectorProcess) : Prop where
  /-- Each coordinate process is a real Brownian motion. -/
  isBrownianMotion : ∀ i : Fin d, IsBrownianMotion μ (fun t ω ↦ W t ω i)
  /-- The coordinate family is independent. -/
  iIndepFun : iIndepFun (fun i : Fin d ↦ fun ω t ↦ W t ω i) μ

attribute [simp] isStandardBrownianMotionVector_iff

/-- A `State`-valued Brownian motion started from `x` is a process whose coordinates are
independent one-dimensional Brownian motions started from the corresponding coordinates of `x`. -/
@[mk_iff isBrownianMotionVectorStartedAt_iff]
class IsBrownianMotionVectorStartedAt
    (μ : Measure Ω) (W : VectorProcess) (x : State) : Prop where
  /-- Each coordinate process is a one-dimensional Brownian motion started at the corresponding
  coordinate of `x`. -/
  isBrownianMotionStartedAt : ∀ i : Fin d, IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω i) (x i)
  /-- The coordinate processes are independent. -/
  iIndepFun : iIndepFun (fun i : Fin d ↦ fun ω t ↦ W t ω i) μ

attribute [simp] isBrownianMotionVectorStartedAt_iff

instance (μ : Measure Ω) (W : VectorProcess) (i : Fin d)
    [hW : IsStandardBrownianMotionVector μ W] :
    IsBrownianMotion μ (fun t ω ↦ W t ω i) :=
  hW.isBrownianMotion i

instance (μ : Measure Ω) (W : VectorProcess) (x : State) (i : Fin d)
    [hW : IsBrownianMotionVectorStartedAt μ W x] :
    IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω i) (x i) :=
  hW.isBrownianMotionStartedAt i

/-- A standard `d`-dimensional Brownian motion is Brownian motion started from `0`. -/
instance (μ : Measure Ω) (W : VectorProcess) [hW : IsStandardBrownianMotionVector μ W] :
    IsBrownianMotionVectorStartedAt μ W 0 where
  isBrownianMotionStartedAt i := by
    simpa using
      (inferInstance : IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω i) 0)
  iIndepFun := hW.iIndepFun

namespace IsStandardBrownianMotionVector

/-- Every time marginal of a standard Brownian vector is strongly measurable. -/
theorem stronglyMeasurable
    {μ : Measure Ω} {W : VectorProcess} (hW : IsStandardBrownianMotionVector μ W)
    (t : NNReal) :
    StronglyMeasurable (W t) := by
  let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  rw [stronglyMeasurable_iff_measurable]
  have hcoords : Measurable (ψ ∘ W t) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa using (hW.isBrownianMotion i).stronglyMeasurable t |>.measurable
  exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords

end IsStandardBrownianMotionVector

end ProbabilityTheory
