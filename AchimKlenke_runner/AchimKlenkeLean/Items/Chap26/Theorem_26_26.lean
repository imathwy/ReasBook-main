import Mathlib
import AchimKlenkeLean.Items.Chap17.Definition_17_3
import AchimKlenkeLean.Items.Chap17.Definition_17_12
import AchimKlenkeLean.Items.Chap26.Definition_26_20
import AchimKlenkeLean.Items.Chap26.Definition_26_23
import AchimKlenkeLean.Items.Chap26.Remark_26_2
import AchimKlenkeLean.Items.Chap26.Remark_26_14
import AchimKlenkeLean.Items.Chap26.Theorem_26_8
import AchimKlenkeLean.Items.Chap26.Theorem_26_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

noncomputable section

universe u

namespace ProbabilityTheory

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "SpatialDiffusionMatrixCoeff" => State → Fin n → Fin n → ℝ
local notation "SpatialDriftCoeff" => State → Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ
local notation "PathKernel" => Kernel State (NNReal → State)
local notation "StateKernel" => NNReal → Kernel State State

/-- The matrix-valued diffusion coefficient `a(x)` attached to an autonomous diffusion field. -/
def spatialDiffusionMatrix (a : SpatialDiffusionMatrixCoeff) (x : State) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ a x i j

/-- The coordinate derivative of a test function on `ℝⁿ` in the `i`-th variable. -/
def coordinateDerivative (i : Fin n) (f : State → ℝ) (x : State) : ℝ :=
  deriv (fun r ↦ f (Function.update x i r)) (x i)

/-- The iterated coordinate derivative in the `i`-th and `j`-th variables. -/
def coordinateSecondDerivative (i j : Fin n) (f : State → ℝ) (x : State) : ℝ :=
  deriv (fun r ↦ coordinateDerivative i f (Function.update x j r)) (x j)

/-- The generator `L_t` of the autonomous diffusion with covariance matrix field `a` and drift
field `b`, evaluated on a `C²` test function `f`. -/
def autonomousGenerator (a : DiffusionMatrixCoeff) (b : DriftCoeff) (f : State → ℝ) :
    NNReal → State → ℝ :=
  fun t x ↦
    (∑ i : Fin n, b t x i * coordinateDerivative i f x) +
      ((1 : ℝ) / 2) *
        ∑ i : Fin n, ∑ j : Fin n, a t x i j * coordinateSecondDerivative i j f x

/-- The compensated test-function process attached to a path-space candidate solution of the local
martingale problem. -/
def martingaleProblemProcess {Ω : Type u} [MeasurableSpace Ω] (a : DiffusionMatrixCoeff)
    (b : DriftCoeff) (f : State → ℝ) (X : Ω → PathSpace) : NNReal → Ω → ℝ :=
  fun t ω ↦
    f (X ω t) - f (X ω 0) -
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), autonomousGenerator a b f s.toNNReal (X ω s.toNNReal)

/-- The autonomous time-homogeneous lift of the diffusion matrix field `a(x)`. -/
def autonomousDiffusionMatrixCoeff (a : SpatialDiffusionMatrixCoeff) : DiffusionMatrixCoeff :=
  fun _ x i j ↦ a x i j

/-- The autonomous time-homogeneous lift of the drift field `b(x)`. -/
def autonomousDriftCoeff (b : SpatialDriftCoeff) : DriftCoeff :=
  fun _ x i ↦ b x i

/-- The canonical autonomous diffusion coefficient obtained from the positive square root of the
matrix field `a(x)`. -/
def autonomousDiffusionSqrtCoeff (a : SpatialDiffusionMatrixCoeff) : DiffusionCoeff :=
  fun _ x i j ↦ CFC.sqrt (spatialDiffusionMatrix a x) i j

-- Proof sketch: for each `x`, positive definiteness makes `a(x)` positive semidefinite, so its
-- square root squares back to `a(x)`. Symmetry of the positive square root converts the matrix
-- square `CFC.sqrt (a(x)) ^ 2` into the coefficient identity `σσᵀ = a`.
/-- The canonical square-root diffusion coefficient has covariance matrix field equal to `a`. -/
theorem diffusionMatrixOfCoefficient_autonomousDiffusionSqrtCoeff
    (a : SpatialDiffusionMatrixCoeff)
    (hpos : ∀ x : State, (spatialDiffusionMatrix a x).PosDef) :
    diffusionMatrixOfCoefficient (autonomousDiffusionSqrtCoeff a) =
      autonomousDiffusionMatrixCoeff a := sorry

/-- The Stroock--Varadhan hypotheses on an autonomous diffusion matrix field `a(x)` and drift
field `b(x)`: `a` is entrywise continuous, `b` is entrywise measurable, each matrix `a(x)` is
positive definite, and both coefficient families satisfy the stated growth bounds. -/
structure StroockVaradhanHypotheses
    (a : SpatialDiffusionMatrixCoeff) (b : SpatialDriftCoeff) : Prop where
  /-- Each coefficient function `x ↦ aᵢⱼ(x)` is continuous. -/
  continuous_diffusion : ∀ i j : Fin n, Continuous (fun x ↦ a x i j)
  /-- Each drift coordinate `x ↦ bᵢ(x)` is measurable. -/
  measurable_drift : ∀ i : Fin n, Measurable (fun x ↦ b x i)
  /-- The matrix `a(x)` is positive definite for every state `x`. -/
  posDef : ∀ x : State, (spatialDiffusionMatrix a x).PosDef
  /-- The matrix and drift coefficients satisfy the quadratic and linear growth estimates with a
  common constant `C`. -/
  growth_bound :
    ∃ C : ℝ,
      0 ≤ C ∧
      (∀ x : State, ∀ i j : Fin n, |a x i j| ≤ C * (1 + ‖x‖ ^ 2)) ∧
      ∀ x : State, ∀ i : Fin n, |b x i| ≤ C * (1 + ‖x‖)

/-- A state-kernel family is strong Feller if each positive-time transition operator sends bounded
measurable real-valued functions to continuous functions. -/
def HasStrongFellerProperty (κ : StateKernel) : Prop :=
  ∀ ⦃t : NNReal⦄, 0 < t → ∀ f : State → ℝ,
    Measurable f →
    (∃ C : ℝ, ∀ x : State, |f x| ≤ C) →
    Continuous (fun x ↦ ∫ y, f y ∂ κ t x)

/- Source/core/bridge triage for Theorem 26.26:
- source-facing layer kept here: the autonomous coefficient lifts, the canonical square-root
  coefficient, the Stroock--Varadhan coefficient hypotheses, and the strong-Feller conclusion for
  transition kernels;
- core/canonical owners reused directly from earlier chapters: `LocalMartingaleProblemWellPosed`,
  `HasUniqueStrongSolution`, `HasPathwiseStrongSolutionRealization`,
  `IsTimeHomogeneousMarkovProcess`, and `HasStrongMarkovProperty`;
- bridge/view layer kept minimal: `HasStrongFellerProperty` is a bounded-measurable regularity
  property of a transition-kernel family. Chapter 21 provides the weaker `IsFellerSemigroup`
  owner on `C₀`, but not this stronger bounded-measurable variant, so no parallel Feller-owner
  wrapper is introduced here.
-/

section StroockVaradhan

variable (a : SpatialDiffusionMatrixCoeff) (b : SpatialDriftCoeff)
variable (hcoeff : StroockVaradhanHypotheses a b)

-- Proof sketch: use the Stroock--Varadhan theorem for continuous uniformly elliptic diffusion
-- matrices with linear-growth measurable drift to obtain existence and uniqueness in law for every
-- Dirac initial distribution, which is exactly `LocalMartingaleProblemWellPosed`.
/-- Theorem 26.26 (1): under the Stroock--Varadhan hypotheses on the autonomous coefficients
`a(x)` and `b(x)`, the local martingale problem `LMP(a, b)` is well-posed. -/
theorem stroockVaradhan_localMartingaleProblemWellPosed
    :
    LocalMartingaleProblemWellPosed
      (autonomousDiffusionMatrixCoeff a) (autonomousDriftCoeff b) := sorry

/-- Theorem 26.26 (2): for every starting point `x ∈ ℝⁿ`, the autonomous SDE with diffusion
coefficient given by the positive square root of `a(x)` and drift `b(x)` has a unique strong
solution started from `x`. -/
theorem stroockVaradhan_hasUniqueStrongSolution
    :
    ∀ x : State,
      HasUniqueStrongSolution
        GeneralizedSDEBrownianMotion
        (SolvesStrongGeneralizedSDE
          (autonomousDiffusionSqrtCoeff a) (autonomousDriftCoeff b))
        (Measure.dirac x) := sorry

-- Proof sketch: construct the Markov family of path laws associated with the well-posed
-- martingale problem, identify it with the unique strong-solution family for the canonical
-- square-root coefficient, and use the deterministic-time and stopping-time martingale-problem
-- identities to obtain a single strong Markov realization of the solution family.
/-- Theorem 26.26 (3): the unique strong-solution family of the autonomous SDE admits a
time-homogeneous strong Markov realization. -/
theorem stroockVaradhan_existsStrongMarkovSolutionFamily
    :
    ∃ (Ω : Type u), ∃ _ : MeasurableSpace Ω,
      ∃ X : NNReal → Ω → State,
      ∃ P : State → ProbabilityMeasure Ω,
      ∃ pathKernel : PathKernel,
      ∃ W : NNReal → Ω → Fin n → ℝ,
        (∀ x : State,
          HasPathwiseStrongSolutionRealization
            (fun _ : NNReal → Ω → Fin n → ℝ ↦ True)
            (fun ξ W X ↦
              IsGeneralizedNDimensionalDiffusion
                (processFiltration X) (P x : Measure Ω) ξ W
                (autonomousDiffusionSqrtCoeff a) (autonomousDriftCoeff b) X)
            (processFiltration X) (fun _ ↦ x) W X) ∧
        IsTimeHomogeneousMarkovProcess X P pathKernel ∧
        HasStrongMarkovProperty P X pathKernel := sorry

-- Proof sketch: start from the strong Markov solution family and apply the Stroock--Varadhan
-- regularity theorem to its path kernel to obtain continuity of the time-`t` transition operators
-- on every bounded measurable test function.
/-- Theorem 26.26 (4): the transition kernel of the strong Markov solution family is strong
Feller; equivalently, for every `t > 0` and bounded measurable `f : ℝⁿ → ℝ`, the map
`x ↦ 𝔼_x[f(X_t)]` is continuous. -/
theorem stroockVaradhan_existsStrongFellerSolutionFamily
    :
    ∃ (Ω : Type u), ∃ _ : MeasurableSpace Ω,
      ∃ X : NNReal → Ω → State,
      ∃ P : State → ProbabilityMeasure Ω,
      ∃ pathKernel : PathKernel,
      ∃ W : NNReal → Ω → Fin n → ℝ,
        (∀ x : State,
          HasPathwiseStrongSolutionRealization
            (fun _ : NNReal → Ω → Fin n → ℝ ↦ True)
            (fun ξ W X ↦
              IsGeneralizedNDimensionalDiffusion
                (processFiltration X) (P x : Measure Ω) ξ W
                (autonomousDiffusionSqrtCoeff a) (autonomousDriftCoeff b) X)
            (processFiltration X) (fun _ ↦ x) W X) ∧
        IsTimeHomogeneousMarkovProcess X P pathKernel ∧
        HasStrongMarkovProperty P X pathKernel ∧
        HasStrongFellerProperty (transitionKernel pathKernel) := sorry

end StroockVaradhan

end ProbabilityTheory
