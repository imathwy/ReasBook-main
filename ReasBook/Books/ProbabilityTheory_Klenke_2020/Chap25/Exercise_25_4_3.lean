import Mathlib
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_38

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Topology
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {d : ℕ} [NeZero d]

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "UnitSphere" => Metric.sphere (0 : State) 1

omit [NeZero d] in
private def sphereRadiusMap (r : ℝ) (y : UnitSphere) : Metric.sphere (0 : State) |r| :=
  ⟨r • (y : State), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul]
    simp⟩

omit [NeZero d] in
private theorem continuous_sphereRadiusMap (r : ℝ) :
    Continuous (fun y : UnitSphere ↦ sphereRadiusMap r y) := by
  exact Continuous.subtype_mk
    (by simpa [sphereRadiusMap] using continuous_const.smul continuous_subtype_val)
    (fun y ↦ by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul]
      simp)

private noncomputable def sphereSurfaceMeasure (r : ℝ) :
    ProbabilityMeasure (Metric.sphere (0 : State) |r|) :=
  letI : Nonempty UnitSphere :=
    show Nonempty UnitSphere from NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let μ : ProbabilityMeasure UnitSphere :=
    FiniteMeasure.normalize
      (⟨(volume : Measure State).toSphere, inferInstance⟩ : FiniteMeasure UnitSphere)
  μ.map (continuous_sphereRadiusMap r).aemeasurable

/-- The Poisson kernel for the open ball `B_r(0)` at the interior point `x`. -/
def openBallPoissonKernel
    (r : ℝ) (x : Metric.ball (0 : State) r) (y : Metric.sphere (0 : State) |r|) : ℝ :=
  (r ^ 2 - ‖(x : State)‖ ^ 2) / (r * ‖(y : State) - x‖ ^ d)

/-- The Poisson-kernel weighting of the boundary-sphere uniform measure. -/
noncomputable def openBallPoissonMeasure
    (r : ℝ) (x : Metric.ball (0 : State) r) :
    Measure (Metric.sphere (0 : State) |r|) :=
  Measure.withDensity
    ((sphereSurfaceMeasure r : ProbabilityMeasure (Metric.sphere (0 : State) |r|)) : Measure _)
    (fun y ↦ ENNReal.ofReal (openBallPoissonKernel r x y))

instance (r : ℝ) (x : Metric.ball (0 : State) r) :
    IsFiniteMeasure (openBallPoissonMeasure r x) := sorry

section Exercise

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "VectorProcess" => NNReal → Ω → State

-- Proof sketch: identify `∂B_r(0)` with the sphere `S_r(0)` via `Homeomorph.setCongr` and
-- `frontier_ball`, and then the harmonic measure from Definition 25.37 becomes exactly the
-- Poisson-kernel boundary measure on that sphere.
/-- Exercise 25.4.3: for `x ∈ B_r(0) ⊂ ℝ^d`, the Brownian harmonic measure of the open ball,
viewed on the boundary sphere via the canonical identification `frontier (ball 0 r) ≃ sphere 0 r`,
is the Poisson-kernel boundary measure. -/
theorem openBallHarmonicMeasure_eq_openBallPoissonMeasure
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess) (r : ℝ) (hr : 0 < r)
    (exitValue : Ω → frontier (Metric.ball (0 : State) r))
    (hW : ∀ z : State, IsBrownianMotionVectorStartedAt (P z) W z)
    (hExit : ∀ ω : Ω,
      (exitValue ω : State) =
        stoppedValue W (hittingAfter W (Metric.ball (0 : State) r)ᶜ 0) ω)
    (hExitMeas : Measurable exitValue)
    (x : Metric.ball (0 : State) r) :
    Measure.map
        (Homeomorph.setCongr (by
          simpa [abs_of_pos hr] using frontier_ball (0 : State) hr.ne'))
      (harmonicMeasure
          P
          (Metric.ball (0 : State) r)
          exitValue
          hExitMeas
          x : Measure _) =
      openBallPoissonMeasure r x := by
  sorry

end Exercise

end ProbabilityTheory
