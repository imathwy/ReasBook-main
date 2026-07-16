import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_70
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Remark_26_2
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Remark_26_3
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Remark_26_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "VectorProcess" => NNReal → Ω → Fin n → ℝ
local notation "ScalarProcess" => NNReal → Ω → ℝ
local notation "ScalarBrownianProcess" => NNReal → Ω → Fin 1 → ℝ
local notation "ScalarState" => Fin 1 → ℝ
local notation "ScalarStateProcess" => NNReal → Ω → ScalarState

/-- The squared Euclidean norm `‖x‖² = ∑ᵢ xᵢ²` on `ℝⁿ`, written in coordinates. -/
def euclideanSquaredNorm (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (x i) ^ 2

-- Proof sketch: unfold `euclideanSquaredNorm`; it is defined to be the finite coordinate sum
-- `∑ i, x i ^ 2`.
/-- Evaluating `euclideanSquaredNorm` gives the coordinate formula `∑ᵢ xᵢ²`. -/
theorem euclideanSquaredNorm_def (x : Fin n → ℝ) :
    euclideanSquaredNorm x = ∑ i : Fin n, (x i) ^ 2 := sorry

/-- The Brownian motion started at `y` obtained by adding the deterministic initial point `y` to a
standard vector Brownian driver `B`. -/
def shiftedBrownianProcess (y : Fin n → ℝ) (B : VectorProcess) : VectorProcess :=
  fun t ω i ↦ y i + B t ω i

-- Proof sketch: unfold `shiftedBrownianProcess`; its `i`-th coordinate is `y i + B_t^i`.
/-- Evaluating `shiftedBrownianProcess y B` adds the starting point `y` coordinatewise to `B`. -/
theorem shiftedBrownianProcess_apply (y : Fin n → ℝ) (B : VectorProcess)
    (t : NNReal) (ω : Ω) (i : Fin n) :
    shiftedBrownianProcess y B t ω i = y i + B t ω i := sorry

/-- The squared radial process `X_t = ‖B_t‖²` associated with an `ℝⁿ`-valued process `B`. -/
def squaredNormProcess (B : VectorProcess) : ScalarProcess :=
  fun t ω ↦ euclideanSquaredNorm (B t ω)

-- Proof sketch: unfold `squaredNormProcess`; at time `t` and sample point `ω`, it is the squared
-- Euclidean norm of the vector `B t ω`.
/-- Evaluating `squaredNormProcess B` gives the squared Euclidean norm of `B_t`. -/
theorem squaredNormProcess_apply (B : VectorProcess) (t : NNReal) (ω : Ω) :
    squaredNormProcess B t ω = euclideanSquaredNorm (B t ω) := sorry

/-- The one-dimensional squared-Bessel diffusion coefficient in the integral equation
`X_t = x + δ t + ∫₀ᵗ sqrt (X_s) dW_s`, represented in the chapter's `Fin 1 → ℝ` state format. -/
def squaredBesselDiffusionCoeff : NNReal → ScalarState → Fin 1 → Fin 1 → ℝ :=
  fun _ x _ _ ↦ Real.sqrt (x 0)

-- Proof sketch: unfold `squaredBesselDiffusionCoeff`; it depends only on the unique state
-- coordinate and equals `sqrt (x 0)`.
/-- Evaluating `squaredBesselDiffusionCoeff` gives `sqrt (x 0)`. -/
theorem squaredBesselDiffusionCoeff_apply
    (t : NNReal) (x : ScalarState) (i j : Fin 1) :
    squaredBesselDiffusionCoeff t x i j = Real.sqrt (x 0) := sorry

/-- The constant drift coefficient `δ` of the one-dimensional squared-Bessel equation, in the
chapter's `Fin 1 → ℝ` state format. -/
def squaredBesselDriftCoeff (δ : ℕ) : NNReal → ScalarState → Fin 1 → ℝ :=
  fun _ _ _ ↦ (δ : ℝ)

-- Proof sketch: unfold `squaredBesselDriftCoeff`; it is the constant drift process with value
-- `δ`.
/-- Evaluating `squaredBesselDriftCoeff δ` gives the constant value `δ`. -/
theorem squaredBesselDriftCoeff_apply
    (δ : ℕ) (t : NNReal) (x : ScalarState) (i : Fin 1) :
    squaredBesselDriftCoeff δ t x i = (δ : ℝ) := sorry

private def SolvesSquaredBesselSDE
    (n : ℕ)
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (Ω → ScalarState) → ScalarBrownianProcess → ScalarStateProcess → Prop :=
  fun ξ W X ↦
    IsGeneralizedNDimensionalDiffusion ℱ μ ξ W squaredBesselDiffusionCoeff
      (squaredBesselDriftCoeff n) X

/-- A scalar local martingale `W` realizes the squared radial process of the shifted Brownian
motion as a weak solution of the one-dimensional squared-Bessel equation with dimension `n`. -/
structure IsWeakSquaredBesselRealization
    (ℱ : TimeFiltration) (μ : Measure Ω) (y : Fin n → ℝ) (B : VectorProcess)
    [IsProbabilityMeasure μ] (W : ScalarProcess) : Prop where
  /-- The scalar driver is a continuous local martingale. -/
  local_martingale : IsContinuousLocalMartingale ℱ μ W
  /-- The quadratic variation of `W` is the identity clock. -/
  quadratic_variation :
    IsContinuousSquareVariationProcess ℱ μ W (fun t _ ↦ (t : ℝ))
  /-- The squared radial process solves the squared-Bessel SDE with this driver. -/
  weak_solution :
    HasWeakSolutionRealization
      (fun _ : ScalarBrownianProcess ↦ True)
      (SolvesSquaredBesselSDE n ℱ μ)
      ℱ
      (fun _ ↦ fun _ : Fin 1 ↦ euclideanSquaredNorm y)
      (fun t ω _ ↦ W t ω)
      (fun t ω _ ↦ squaredNormProcess (shiftedBrownianProcess y B) t ω)

-- Proof sketch: apply Itô's formula to the squared norm of the shifted Brownian motion
-- `t ↦ y + B_t`, identify the radial martingale term, compute its bracket as `t`, and then
-- package the resulting one-dimensional integral equation in the chapter's
-- `HasWeakSolutionRealization` interface.
/-- Example 26.16: if `B` is a standard `n`-dimensional Brownian driver and
`X_t = ‖y + B_t‖²`, then there exists a scalar continuous local martingale `W` with bracket
`⟨W⟩_t = t` realizing `X` as a one-dimensional weak solution of the squared-radial equation with
initial value `‖y‖²`, diffusion coefficient `sqrt (x)`, and drift `n`. -/
theorem shiftedBrownian_squaredNorm_hasWeakSquaredBesselRealization
    {ℱ : TimeFiltration} {B : VectorProcess}
    (y : Fin n → ℝ) (hB : IsBrownianMotionWithFiltration ℱ μ B) :
    ∃ W : ScalarProcess,
      IsWeakSquaredBesselRealization ℱ μ y B W := sorry

end ProbabilityTheory
