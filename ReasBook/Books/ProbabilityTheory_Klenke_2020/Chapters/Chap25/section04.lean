import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_25_4_1 (from Items/Chap25) -/
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

/-! ### Exercise_25_4_2 (from Items/Chap25) -/
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

/-! ### Exercise_25_4_3 (from Items/Chap25) -/
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

/-! ### Theorem_25_4 (from Items/Chap25) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

section Setup

variable {μ : Measure Ω}

/-- Every predictable simple process is globally square-integrable on `Ω × [0,∞)` for a
probability measure. -/
theorem predictableSimpleProcess_memLp
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ]
    (H : PredictableSimpleProcess ℱ) :
    MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ) := sorry

/-- The terminal Brownian elementary integral of a predictable simple process belongs to
`L²(μ)`. -/
theorem brownianElementaryIntegralAtInfinity_memLp
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    MemLp (brownianElementaryIntegralAtInfinity W H) 2 μ := sorry

private theorem brownianElementaryIntegralAtInfinityL2_congr
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    {H K : PredictableSimpleProcess ℱ}
    {hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    {hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    (hHK :
      (predictableSimpleProcessToL2 H hH : Lp ℝ 2 (processMeasure μ)) =
        predictableSimpleProcessToL2 K hK) :
    (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).toLp
        (brownianElementaryIntegralAtInfinity W H) =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
        (brownianElementaryIntegralAtInfinity W K) := sorry

private theorem existsUnique_brownianElementaryIntegralAtInfinityL2
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : predictableSimpleProcessL2 ℱ μ) :
    ∃! I : Lp ℝ 2 μ,
      ∀ K : PredictableSimpleProcess ℱ,
        ∀ hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ),
          (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK →
            I =
              (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
                (brownianElementaryIntegralAtInfinity W K) := by
  rcases H.2 with ⟨K, hK, hK_repr⟩
  have hK_repr' : (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK := by
    simpa using hK_repr
  refine ⟨(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
      (brownianElementaryIntegralAtInfinity W K), ?_, ?_⟩
  · intro K' hK' hK'_repr
    have hKK' :
        (predictableSimpleProcessToL2 K hK : Lp ℝ 2 (processMeasure μ)) =
          predictableSimpleProcessToL2 K' hK' :=
      hK_repr'.symm.trans hK'_repr
    exact brownianElementaryIntegralAtInfinityL2_congr hW hW_adapted hKK'
  · intro I hI
    exact hI K hK hK_repr'

private noncomputable def brownianElementaryIntegralAtInfinityL2Data
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W) :
    predictableSimpleProcessL2 ℱ μ → Lp ℝ 2 μ :=
  fun H ↦
    Classical.choose <| (existsUnique_brownianElementaryIntegralAtInfinityL2 hW hW_adapted H).exists

private theorem brownianElementaryIntegralAtInfinityL2Data_spec
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : predictableSimpleProcessL2 ℱ μ)
    {K : PredictableSimpleProcess ℱ}
    {hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    (hHK :
      (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
        (brownianElementaryIntegralAtInfinity W K) :=
  (Classical.choose_spec <|
      (existsUnique_brownianElementaryIntegralAtInfinityL2 hW hW_adapted H).exists)
    K hK hHK

private theorem brownianElementaryIntegralAtInfinityL2_map_add
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H K : predictableSimpleProcessL2 ℱ μ) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted (H + K) =
      brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H +
        brownianElementaryIntegralAtInfinityL2Data hW hW_adapted K := sorry

private theorem brownianElementaryIntegralAtInfinityL2_map_smul
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (a : ℝ) (H : predictableSimpleProcessL2 ℱ μ) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted (a • H) =
      a • brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H := sorry

private theorem brownianElementaryIntegralAtInfinityL2_norm_map
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : predictableSimpleProcessL2 ℱ μ) :
    ‖brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H‖ = ‖H‖ := sorry

/-- The canonical linear isometric `L²` lift of the terminal Brownian elementary integral from
the upstream `L²(μ ⊗ dt)` image `predictableSimpleProcessL2 ℱ μ` of predictable simple
integrands for an `ℱ`-adapted Brownian motion. This is the core/canonical owner for Theorem
25.4(i). -/
noncomputable def brownianElementaryIntegralAtInfinityLinearIsometry
    (ℱ : TimeFiltration) {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W) :
    predictableSimpleProcessL2 ℱ μ →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toLinearMap :=
    { toFun := brownianElementaryIntegralAtInfinityL2Data hW hW_adapted
      map_add' := brownianElementaryIntegralAtInfinityL2_map_add hW hW_adapted
      map_smul' := brownianElementaryIntegralAtInfinityL2_map_smul hW hW_adapted }
  norm_map' := brownianElementaryIntegralAtInfinityL2_norm_map hW hW_adapted

/-- Applying the canonical `L²` linear isometry of Theorem 25.4(i) to a concrete predictable
simple process recovers the `Lp` class of the source-facing terminal Brownian elementary integral
from Definition 25.3. -/
@[simp] theorem brownianElementaryIntegralAtInfinityLinearIsometry_apply
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    brownianElementaryIntegralAtInfinityLinearIsometry ℱ hW hW_adapted
        (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
         predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).toLp
        (brownianElementaryIntegralAtInfinity W H) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  exact brownianElementaryIntegralAtInfinityL2Data_spec hW hW_adapted
    (predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) rfl

/-- On a concrete predictable simple process, the canonical `L²` linear isometry of Theorem
25.4(i) agrees almost everywhere with the source-facing terminal Brownian elementary integral from
Definition 25.3. -/
theorem brownianElementaryIntegralAtInfinityLinearIsometry_ae_eq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    (brownianElementaryIntegralAtInfinityLinearIsometry ℱ hW hW_adapted
      (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
       predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) : Ω → ℝ) =ᵐ[μ]
        brownianElementaryIntegralAtInfinity W H := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  rw [brownianElementaryIntegralAtInfinityLinearIsometry_apply hW hW_adapted H]
  exact MemLp.coeFn_toLp (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H)

-- Proof sketch: apply the linear isometry of Theorem 25.4(i) to the canonical `L²(μ ⊗ dt)`
-- class of `H` and rewrite both sides back to the source-facing formulas from Definitions 25.2
-- and 25.3.
/-- Theorem 25.4 (i), source-facing norm identity: the terminal Brownian elementary integral from
Definition 25.3 preserves the textbook `L²(μ ⊗ dt)` norm from Definition 25.2 on predictable
simple processes, provided the Brownian motion is adapted to the filtration of the integrand. -/
theorem brownianElementaryIntegralAtInfinity_norm_eq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ =
      ENNReal.ofReal
        (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
         predictableSimpleProcessNorm μ H) := sorry

-- Proof sketch: for a predictable simple integrand `H`, the stopped Brownian elementary integral
-- is the usual Brownian Itô martingale; the Itô isometry gives the uniform `L²` bound, and the
-- Brownian sample-path continuity passes through the finite increment formula defining the
-- integral.
/-- Theorem 25.4 (ii): for every predictable simple process `H`, the stopped Brownian elementary
integral process is a continuous `𝓕`-martingale that is uniformly bounded in `L²(μ)`, provided
the Brownian motion is adapted to `𝓕`. -/
theorem brownianElementaryIntegral_isL2BoundedContinuousMartingale
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ ∧
      HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) ∧
      ∃ C : ℝ≥0, ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) :=
  sorry

/-- The stopped Brownian elementary integral of a predictable simple process is a martingale. -/
theorem brownianElementaryIntegral_martingale
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ :=
  (brownianElementaryIntegral_isL2BoundedContinuousMartingale hW hW_adapted H).1

/-- The stopped Brownian elementary integral of a predictable simple process has almost surely
continuous sample paths. -/
theorem brownianElementaryIntegral_hasAlmostSurelyContinuousPaths
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) :=
  (brownianElementaryIntegral_isL2BoundedContinuousMartingale hW hW_adapted H).2.1

/-- The stopped Brownian elementary integral of a predictable simple process is uniformly bounded
in `L²(μ)` over time. -/
theorem brownianElementaryIntegral_l2_bounded
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    ∃ C : ℝ≥0, ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) :=
  (brownianElementaryIntegral_isL2BoundedContinuousMartingale hW hW_adapted H).2.2

end Setup

end ProbabilityTheory

end
