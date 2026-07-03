import ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_5_5
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/- Exercise 17.5.2 is `source-facing`: it records the asymptotic of the first-coordinate return
probability for the continuous-time Poissonized simple random walk on `ℤ^D`.

Domain-style sampling for this item:
- `poissonConvolutionSemigroup` from Example 17.7 shows the chapter's continuous-time owner style:
  a source-facing time-indexed law family, with event probabilities derived from that owner.
- `modifiedBesselI0` from Exercise 17.5.5, used here through the pointwise notation `I₀`, is the
  source-facing owner declaration for the special-function side of the formula.

Primitive data versus derived API:
- the primitive data here is the one-dimensional law of the first coordinate at time `t`,
  realized canonically as the difference of two independent Poisson variables of rate `t / (2D)`;
- the zero-return probability `P₀[Y_t¹ = 0]` is derived from that law;
- the Bessel expression is a bridge theorem identifying the source-facing probability with the
  canonical special-function formula, not a second owner declaration. -/

private def poissonizedSimpleRandomWalkFirstCoordinatePMF
    (D : ℕ) [NeZero D] (t : ℝ≥0) : PMF ℤ :=
  (poissonPMF (t / (2 * (D : ℝ≥0)))).bind fun n ↦
    (poissonPMF (t / (2 * (D : ℝ≥0)))).map fun m ↦ (n : ℤ) - m

/-- The law of the first coordinate `Y_t¹` of the continuous-time Poissonized simple random walk on
`ℤ^D` started at `0`, represented as the difference of two independent Poisson variables of rate
`t / (2D)`. -/
def poissonizedSimpleRandomWalkFirstCoordinateLaw
    (D : ℕ) [NeZero D] (t : ℝ≥0) : ProbabilityMeasure ℤ :=
  ⟨(poissonizedSimpleRandomWalkFirstCoordinatePMF D t).toMeasure, inferInstance⟩

/-- The source-facing return probability `P₀[Y_t¹ = 0]` for the first coordinate of the
continuous-time Poissonized simple random walk on `ℤ^D`. -/
def poissonizedSimpleRandomWalkFirstCoordinateZeroProbability
    (D : ℕ) [NeZero D] (t : ℝ≥0) : ℝ :=
  (poissonizedSimpleRandomWalkFirstCoordinateLaw D t : Measure ℤ).real ({0} : Set ℤ)

-- Proof sketch: write `Y_t¹` as the difference of two independent Poisson processes of rate
-- `(2D)⁻¹ t`, expand the mass at `0` by conditioning on the common value of the two Poisson
-- counts, and recognize the resulting power series as `I₀(t / D)`.
/-- The first-coordinate return probability is the modified-Bessel expression from `(17.21)`. -/
theorem poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_eq_bessel
    (D : ℕ) [NeZero D] (t : ℝ≥0) :
    poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t =
      Real.exp (-((t : ℝ) / D)) * I₀ ((t : ℝ) / D) := sorry

-- Proof sketch: write the first coordinate as the difference of two independent Poisson
-- processes of rate `(2D)⁻¹`, rewrite the probability by
-- `poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_eq_bessel`, and then apply the
-- standard large-argument asymptotic `I₀(s) ~ exp s / sqrt (2π s)` with `s = t / D`.
/-- Exercise 17.5.2: for the continuous-time Poissonized simple random walk on `ℤ^D` started at
`0`, the first-coordinate return probability
`P₀[Y_t¹ = 0] = exp (-t / D) * I₀(t / D)` satisfies
`P₀[Y_t¹ = 0] ~ (2π / D)^(-1 / 2) t^(-1 / 2)`, formalized here in equivalent limit form. -/
theorem poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_asymptotic
    (D : ℕ) [NeZero D] :
    Tendsto
      (fun t : ℝ≥0 ↦
        (t : ℝ) ^ ((1 : ℝ) / 2) *
          poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t)
      atTop
      (nhds ((2 * Real.pi / D) ^ (-(1 : ℝ) / 2))) := sorry

end ProbabilityTheory
