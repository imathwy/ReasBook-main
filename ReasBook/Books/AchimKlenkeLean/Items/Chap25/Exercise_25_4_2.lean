import Mathlib
import AchimKlenkeLean.Items.Chap25.StandardBrownianMotionVector
import AchimKlenkeLean.Items.Chap25.Definition_25_37
import AchimKlenkeLean.Items.Chap25.UpperHalfSpace

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section HalfSpace

variable (n : ℕ)

local notation "State" => EuclideanSpace ℝ (Fin (n + 1))
local notation "Boundary" => EuclideanSpace ℝ (Fin n)
local notation "VectorProcess" => NNReal → Ω → State

/-- The first exit time of the translated Brownian path `t ↦ x + W_t` from the upper half-space,
encoded as `⊤` if the path never leaves. -/
def upperHalfSpaceExitTime (W : VectorProcess) (x : State) : Ω → WithTop NNReal :=
  hittingAfter (fun t ω ↦ x + W t ω) (upperHalfSpace n)ᶜ 0

/-- The boundary coordinates of the Brownian exit point from the upper half-space; when the exit
time is infinite, this is the boundary projection of the canonical stopped value. -/
def upperHalfSpaceExitLocation (W : VectorProcess) (x : State) : Ω → Boundary :=
  fun ω ↦
    upperHalfSpaceBoundaryProjection n
      (stoppedValue (fun t ω ↦ x + W t ω) (upperHalfSpaceExitTime n W x) ω)

omit [MeasurableSpace Ω] in
/-- Evaluating the exit location returns the horizontal coordinates of the stopped value of
`x + W`. -/
theorem upperHalfSpaceExitLocation_apply (W : VectorProcess) (x : State) (ω : Ω) (i : Fin n) :
    upperHalfSpaceExitLocation n W x ω i =
      (stoppedValue (fun t ω ↦ x + W t ω) (upperHalfSpaceExitTime n W x) ω) (Fin.castSucc i) := by
  simp [upperHalfSpaceExitLocation]

/-- The upper-half-space exit value as a point of `frontier (upperHalfSpace n)`, obtained from the
boundary-coordinate exit map via the inverse of the canonical boundary identification. -/
def upperHalfSpaceExitValue (W : VectorProcess) (x : State) : Ω → frontier (upperHalfSpace n) :=
  fun ω ↦ (upperHalfSpaceFrontierEquiv n).symm (upperHalfSpaceExitLocation n W x ω)

omit [MeasurableSpace Ω] in
/-- Applying the canonical boundary identification to the frontier-valued exit map recovers the
coordinate exit-location map. -/
@[simp] theorem upperHalfSpaceFrontierEquiv_exitValue (W : VectorProcess) (x : State) :
    upperHalfSpaceFrontierEquiv n ∘ upperHalfSpaceExitValue n W x =
      upperHalfSpaceExitLocation n W x := by
  funext ω
  simp [upperHalfSpaceExitValue]

/-- The squared Euclidean distance between the boundary projection of `x` and the boundary point
`y`. -/
def upperHalfSpaceBoundaryDistanceSq (x : State) (y : Boundary) : ℝ :=
  dist (upperHalfSpaceBoundaryProjection n x) y ^ (2 : ℕ)

/-- The Poisson kernel density of the upper half-space `ℝ^n × (0,∞)` evaluated at interior point
`x` and boundary point `y`. -/
def upperHalfSpacePoissonKernel (x : State) (y : Boundary) : ℝ :=
  Real.Gamma (((n + 1 : ℕ) : ℝ) / 2) /
      (Real.pi ^ (((n + 1 : ℕ) : ℝ) / 2)) *
    x (Fin.last n) /
      (upperHalfSpaceBoundaryDistanceSq n x y + x (Fin.last n) ^ (2 : ℕ)) ^
        (((n + 1 : ℕ) : ℝ) / 2)

variable {n}
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : VectorProcess}

/-- Pushing the canonical harmonic measure on `frontier (upperHalfSpace n)` forward along the
boundary identification recovers the boundary-coordinate exit law, provided the canonical
frontier-valued exit map is measurable. -/
theorem map_upperHalfSpaceFrontierEquiv_harmonicMeasure
    (W : VectorProcess) {x : State} (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x)) :
    Measure.map (upperHalfSpaceFrontierEquiv n)
        (harmonicMeasure
          (fun _ : State ↦ (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
          (upperHalfSpace n)
          (upperHalfSpaceExitValue n W x)
          hExitMeas
          ⟨x, hx⟩ : Measure (frontier (upperHalfSpace n))) =
      Measure.map (upperHalfSpaceExitLocation n W x) μ := sorry

-- Proof sketch: apply one-dimensional recurrence to the last coordinate
-- `x_{n+1} + W_t^{n+1}`, whose first hit of `(-∞,0]` is almost surely finite; exiting the
-- half-space is equivalent to that last coordinate hitting the boundary.
/-- Exercise 25.4.2 (1): if `x` lies in the upper half-space `ℝ^n × (0,∞)` and the last
coordinate of `W` is a Brownian motion, then the exit time of `x + W` from the half-space is
almost surely finite. -/
theorem upperHalfSpaceExitTime_ae_lt_top
    (hW : IsBrownianMotion μ (fun t ω ↦ W t ω (Fin.last n))) {x : State}
    (hx : x ∈ upperHalfSpace n) :
    ∀ᵐ ω ∂μ, upperHalfSpaceExitTime n W x ω < ⊤ := sorry

-- Proof sketch: identify the boundary-coordinate exit distribution of `x + W` from the half-space
-- with the classical Poisson kernel obtained by Fourier transform in the horizontal variables and
-- the one-dimensional first-hitting analysis in the vertical coordinate; this is equivalently the
-- harmonic measure pushed forward along the canonical boundary identification.
section

/-- The boundary-coordinate exit distribution of `x + W` from the upper half-space is the
pushforward of the harmonic measure along the canonical boundary identification, hence is given by
the classical Poisson kernel, provided the canonical frontier-valued exit map is measurable. -/
theorem upperHalfSpaceExitDistribution_eq_withDensity
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfSpace n)
    (hExitMeas : Measurable (upperHalfSpaceExitValue n W x)) :
    Measure.map (upperHalfSpaceExitLocation n W x) μ =
      (volume.withDensity
        (fun y ↦ ENNReal.ofReal (upperHalfSpacePoissonKernel n x y)) : Measure Boundary) := sorry

end

end HalfSpace

end ProbabilityTheory
