import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_37
import ProbabilityTheory_Klenke_2020.Items.Chap25.UpperHalfSpace

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "State" => EuclideanSpace ℝ (Fin 2)
local notation "VectorProcess" => NNReal → Ω → State
local notation "upperHalfPlane" => upperHalfSpace 1

/-- Membership in the open upper half-plane `ℝ × (0, ∞)` is positivity of the second coordinate.
-/
theorem mem_upperHalfPlane_iff (x : State) :
    x ∈ upperHalfPlane ↔ 0 < x 1 := by
  simp [upperHalfSpace]

/-- The frontier of the open upper half-plane is the horizontal axis. -/
theorem mem_frontier_upperHalfPlane_iff (x : State) :
    x ∈ frontier upperHalfPlane ↔ x 1 = 0 := by
  simpa using mem_frontier_upperHalfSpace_iff 1 x

/-- Pushing the canonical harmonic measure on `frontier (upperHalfSpace 1)` forward along the
textbook boundary coordinate `z ↦ z₁` gives the real-valued boundary law of the given
frontier-valued exit map. -/
theorem map_upperHalfPlaneBoundary_harmonicMeasure
    (P : ProbabilityMeasure Ω) {x : State} (hx : x ∈ upperHalfPlane)
    (exitValue : Ω → frontier upperHalfPlane) (hExitMeas : Measurable exitValue) :
    Measure.map (fun z : frontier upperHalfPlane ↦ (z : State) 0)
        (harmonicMeasure
          (fun _ : State ↦ P)
          upperHalfPlane
          exitValue
          hExitMeas
          ⟨x, hx⟩ : Measure (frontier upperHalfPlane)) =
      Measure.map (fun ω ↦ (exitValue ω : State) 0) (P : Measure Ω) := by
  sorry

-- Proof sketch: only the second coordinate `t ↦ W t ω 1` matters, since exiting `ℝ × (0, ∞)` is
-- equivalent to the last coordinate of `x + W` hitting `(-∞, 0]`.
/-- The exit time from the upper half-plane is almost surely finite for planar Brownian motion
started at an interior point, assuming only that the second coordinate is a Brownian motion. -/
theorem upperHalfPlaneExitTime_ae_lt_top
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsBrownianMotion μ (fun t ω ↦ W t ω 1))
    {x : State} (hx : x ∈ upperHalfPlane) :
    ∀ᵐ ω ∂μ,
      hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω < ⊤ := by
  sorry

-- Proof sketch: stop the translated planar Brownian motion `t ↦ x + W_t` at the first exit time
-- from the upper half-plane and then read off the first coordinate; the resulting real-valued exit
-- law is the Cauchy distribution with location `x₁` and scale `x₂`.
/-- The first coordinate of the stopped planar Brownian path at the first exit time from the upper
half-plane has the Cauchy law with location parameter `x₁` and scale parameter `x₂`. -/
theorem upperHalfPlaneStoppedFirstCoordinate_eq_cauchyMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    Measure.map
        (fun ω ↦
          stoppedValue
              (fun t ω ↦ x + W t ω)
              (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal)) ω
            0)
        μ =
      cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
  sorry

-- Proof sketch: first push the frontier-valued harmonic measure to `ℝ` along the boundary
-- coordinate `z ↦ z₁`; then use almost-sure finiteness of the exit time and the agreement
-- hypothesis to identify that law with the first coordinate of the stopped planar Brownian path.
/-- Exercise 25.4.1: for planar Brownian motion started at `x = (x₁, x₂)` in the open upper
half-plane `G = ℝ × (0, ∞)`, the harmonic measure on the textbook boundary line `ℝ`, viewed
through the coordinate map `z ↦ z₁` on `frontier G`, is the Cauchy distribution with location
parameter `x₁` and scale parameter `x₂`, provided `exitValue` is a measurable frontier-valued exit
map that agrees with the stopped Brownian path whenever the exit time is finite. -/
theorem upperHalfPlaneHarmonicMeasure_eq_cauchyMeasure
    {P : ProbabilityMeasure Ω} {W : VectorProcess}
    {x : State} (hx : x ∈ upperHalfPlane)
    (exitValue : Ω → frontier upperHalfPlane)
    (hExitMeas : Measurable exitValue)
    (hExit :
      ∀ ω : Ω,
        hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω < ⊤ →
          (exitValue ω : State) =
            stoppedValue
              (fun t ω ↦ x + W t ω)
              (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal))
              ω)
    (hW : IsStandardBrownianMotionVector (P : Measure Ω) W) :
    Measure.map (fun z : frontier upperHalfPlane ↦ (z : State) 0)
      (harmonicMeasure
        (fun _ : State ↦ P)
        upperHalfPlane
        exitValue
        hExitMeas
        ⟨x, hx⟩ : Measure (frontier upperHalfPlane)) =
      cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
  sorry

end ProbabilityTheory
