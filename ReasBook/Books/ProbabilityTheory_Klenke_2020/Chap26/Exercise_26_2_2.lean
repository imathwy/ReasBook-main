import Mathlib
import ProbabilityTheory_Klenke_2020.Chap26.Example_26_11
import ProbabilityTheory_Klenke_2020.Chap26.Theorem_26_10
import ProbabilityTheory_Klenke_2020.Chap26.Theorem_26_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Topology

noncomputable section

namespace ProbabilityTheory

local notation "State1" => Fin 1 → ℝ
local notation "State2" => Fin 2 → ℝ
local notation "StatePathSpace1" => EuclideanPathSpace 1
local notation "StatePathSpace2" => EuclideanPathSpace 2
local notation "DiffusionCoeff2" => NNReal → State2 → Fin 2 → Fin 2 → ℝ
local notation "DriftCoeff2" => NNReal → State2 → Fin 2 → ℝ

/- Domain-style sampling for Exercise 26.2.2:
- primary domain: weak solutions and same-space weak realizations of Chapter 26 SDEs;
- sampled chapter owners: `cirDiffusionCoeff`, `cirDriftCoeff`, `oneDimensionalState`,
  `oneDimensionalDiffusion`, `oneDimensionalDrift`, `HasWeakSolutionRealization`, and
  `GeneralizedWeakSDESolution`;
- core/canonical owner choice: the summed one-dimensional equation is the chapter's CIR / Feller
  branching diffusion with coefficient `cirDiffusionCoeff γ` and drift `cirDriftCoeff 0 0`,
  expressed through the existing one-dimensional coefficient lifts and realization predicates;
- source-facing data kept here: the genuinely two-dimensional diagonal coefficient, deterministic
  pair initial state, and the state-sum map;
- deleted duplicate local owner layer: the previous one-dimensional square-root coefficient and
  drift wrappers, the independence alias, and the packaged
  `SummedSquareRootWeakSolution` wrapper.
-/

/-- The diagonal two-dimensional square-root diffusion coefficient with independent coordinates,
written as a coordinatewise bridge to the chapter's one-dimensional CIR / Feller branching
coefficient. -/
abbrev squareRootPairDiffusionCoeff (γ : NNReal) : DiffusionCoeff2 :=
  fun t x i j ↦ if i = j then cirDiffusionCoeff γ t (x i) else 0

-- Proof sketch: unfold `squareRootPairDiffusionCoeff`; the coefficient is diagonal, with
-- diagonal entry the chapter's CIR coefficient `cirDiffusionCoeff γ t (xᵢ)` and off-diagonal
-- entry `0`.
/-- Evaluating the two-dimensional square-root diffusion coefficient gives the diagonal formula
with coordinatewise CIR entries and vanishing off-diagonal terms. -/
theorem squareRootPairDiffusionCoeff_apply
    (γ : NNReal) (t : NNReal) (x : State2) (i j : Fin 2) :
    squareRootPairDiffusionCoeff γ t x i j =
      if i = j then cirDiffusionCoeff γ t (x i) else 0 := rfl

/-- The zero drift coefficient for the two-dimensional square-root diffusion, written
coordinatewise through the chapter's zero-CIR drift owner. -/
abbrev squareRootDrift2 : DriftCoeff2 :=
  fun t x i ↦ cirDriftCoeff 0 0 t (x i)

-- Proof sketch: unfold `squareRootDrift2`; each coordinate is the zero CIR drift
-- `cirDriftCoeff 0 0`.
/-- Evaluating the two-dimensional drift coefficient recovers the coordinatewise zero CIR drift. -/
theorem squareRootDrift2_apply
    (t : NNReal) (x : State2) (i : Fin 2) :
    squareRootDrift2 t x i = cirDriftCoeff 0 0 t (x i) := rfl

/-- The deterministic initial state `(x₀¹, x₀²)` in `ℝ²`. -/
abbrev squareRootPairInitialState (x01 x02 : ℝ) : State2 :=
  ![x01, x02]

-- Proof sketch: unfold `squareRootPairInitialState`; the first coordinate is the first component
-- of the vector notation `![x₀¹, x₀²]`.
/-- The first coordinate of the initial state is `x₀¹`. -/
theorem squareRootPairInitialState_apply_zero
    (x01 x02 : ℝ) :
    squareRootPairInitialState x01 x02 0 = x01 := by
  simp [squareRootPairInitialState]

-- Proof sketch: unfold `squareRootPairInitialState`; the second coordinate is the second
-- component of the vector notation `![x₀¹, x₀²]`.
/-- The second coordinate of the initial state is `x₀²`. -/
theorem squareRootPairInitialState_apply_one
    (x01 x02 : ℝ) :
    squareRootPairInitialState x01 x02 1 = x02 := by
  simp [squareRootPairInitialState]

-- Proof sketch: the map `x ↦ x 0 + x 1` is continuous as a sum of the two continuous coordinate
-- projections, and viewing this scalar as a `Fin 1 → ℝ`-valued function preserves continuity.
/-- The state map `x ↦ x₁ + x₂` from `ℝ²` to `ℝ` is continuous in the `Fin`-indexed model. -/
theorem sumTwoCoordinateState_continuous :
    Continuous (fun x : State2 ↦ fun _ : Fin 1 ↦ x 0 + x 1) := by
  continuity

/-- The continuous state map sending `(x₁, x₂)` to the one-dimensional state `x₁ + x₂`. -/
def sumTwoCoordinateStateMap : ContinuousMap State2 State1 :=
  ⟨fun x _ ↦ x 0 + x 1, sumTwoCoordinateState_continuous⟩

-- Proof sketch: unfold `sumTwoCoordinateStateMap`; it is the continuous map built from the
-- function `x ↦ x₁ + x₂`.
/-- Evaluating the state-sum map returns the one-dimensional state with value `x₁ + x₂`. -/
theorem sumTwoCoordinateStateMap_apply
    (x : State2) (i : Fin 1) :
    sumTwoCoordinateStateMap x i = x 0 + x 1 := rfl

/-- Summing the two coordinates of a two-dimensional continuous path gives a one-dimensional
continuous path. -/
def sumTwoCoordinatePath (x : StatePathSpace2) : StatePathSpace1 :=
  sumTwoCoordinateStateMap.comp x

-- Proof sketch: `sumTwoCoordinatePath` is defined by composing the path `x` with
-- `sumTwoCoordinateStateMap`, so evaluation at time `t` gives the sum of the two coordinates of
-- `x t`.
/-- Evaluating the summed path at time `t` gives `x_t¹ + x_t²`. -/
theorem sumTwoCoordinatePath_apply
    (x : StatePathSpace2) (t : NNReal) (i : Fin 1) :
    sumTwoCoordinatePath x t i = x t 0 + x t 1 := rfl

-- Proof sketch: regard `(X¹, X²)` as a two-dimensional weak solution with diagonal diffusion
-- coefficient. The summed path `Z = X¹ + X²` is adapted and
-- starts from `x₀¹ + x₀²`. Its quadratic variation is `γ ∫ Z_s ds`, so by Lévy's characterization
-- or the martingale representation used in Theorem 26.26, there exists a one-dimensional
-- Brownian motion `W` on the same filtered probability space such that
-- `dZ_t = √(γ Z_t) dW_t`.
/-- Exercise 26.2.2: if `(X¹, X²)` is a two-dimensional weak solution of the diagonal square-root
diffusion with initial state `(x₀¹, x₀²)`, then the summed process `Z := X¹ + X²` is a weak
solution of the one-dimensional square-root SDE with initial value `x₀¹ + x₀²`. -/
theorem squareRoot_diffusion_sum_isWeakSolution
    {x01 x02 : ℝ} {γ : NNReal}
    (L : GeneralizedWeakSDESolution
      (Measure.dirac (squareRootPairInitialState x01 x02))
      (squareRootPairDiffusionCoeff γ) squareRootDrift2) :
    ∃ W : NNReal → L.Ω → Fin 1 → ℝ,
      HasLaw (fun ω ↦ sumTwoCoordinatePath (L ω) 0)
        (Measure.dirac (oneDimensionalState (x01 + x02))) L.μ ∧
      HasWeakSolutionRealization
        (IsBrownianMotionWithFiltration L.ℱ L.μ)
        (fun ξ W X ↦
          IsGeneralizedNDimensionalDiffusion L.ℱ L.μ ξ W
            (oneDimensionalDiffusion (cirDiffusionCoeff γ))
            (oneDimensionalDrift (cirDriftCoeff 0 0))
            X)
        L.ℱ
        (fun ω ↦ sumTwoCoordinatePath (L ω) 0)
        W
        (fun t ω ↦ sumTwoCoordinatePath (L ω) t) := sorry

end ProbabilityTheory
