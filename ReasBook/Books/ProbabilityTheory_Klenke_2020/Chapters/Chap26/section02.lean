import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_26_2_1 (from Items/Chap26) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

section SemigroupRealizations

local notation "State" => Fin 1 → ℝ
local notation "PathSpace" => EuclideanPathSpace 1

/-- A weak solution of the one-dimensional SDE with coefficients `σ` and `b`, started from the
deterministic state `x`. -/
abbrev OneDimensionalWeakSolution (x : ℝ) (σ b : NNReal → ℝ → ℝ) :=
  @GeneralizedWeakSDESolution 1 1
    (Measure.dirac (oneDimensionalState x))
    inferInstance
    (oneDimensionalDiffusion σ)
    (oneDimensionalDrift b)

/-- A kernel family on `ℝ` is the transition semigroup of a one-dimensional diffusion with
coefficients `σ` and `b` if its scalar transition probabilities come from a time-homogeneous
strong Markov family on the chapter's one-dimensional state space, and the corresponding path
kernel rows are exactly the path laws of weak solutions unique in law for each deterministic
initial state. -/
def HasOneDimensionalDiffusionSemigroup
    (κ : NNReal → Kernel ℝ ℝ) (σ b : NNReal → ℝ → ℝ) : Prop :=
  ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω)
    (X : NNReal → Ω → State) (P : State → @ProbabilityMeasure Ω mΩ)
    (pathKernel : Kernel State (NNReal → State)),
      let _ : MeasurableSpace Ω := mΩ
      IsTimeHomogeneousMarkovProcess X P pathKernel ∧
      HasStrongMarkovProperty P X pathKernel ∧
    (∀ x : ℝ,
      ∃ L : OneDimensionalWeakSolution.{u} x σ b,
        L.IsWeaklyUnique ∧
          pathKernel (oneDimensionalState x) =
            L.statePathLaw.map ((↑) : PathSpace → NNReal → State)) ∧
    ∀ x : ℝ, ∀ t : NNReal,
      (transitionKernel pathKernel t (oneDimensionalState x)).map
          (fun y ↦ y 0) =
        κ t x

/-- Time-homogeneous one-dimensional diffusion coefficients induce the corresponding source-facing
transition-semigroup predicate. -/
abbrev HasAutonomousOneDimensionalDiffusionSemigroup
    (κ : NNReal → Kernel ℝ ℝ) (σ b : ℝ → ℝ) : Prop :=
  HasOneDimensionalDiffusionSemigroup.{u} κ (fun _ x ↦ σ x) (fun _ x ↦ b x)

/-- A kernel family on `ℝ` is the Ornstein--Uhlenbeck transition semigroup if it is the
time-homogeneous semigroup of the autonomous diffusion with constant diffusion coefficient `σ` and
linear drift `x ↦ b x`. -/
abbrev HasOrnsteinUhlenbeckSemigroup
    (κ : NNReal → Kernel ℝ ℝ) (b σ : ℝ) : Prop :=
  HasAutonomousOneDimensionalDiffusionSemigroup.{u} κ (fun _ ↦ σ) (fun x ↦ b * x)

end SemigroupRealizations

section OneDimensionalDiffusion

variable (C x₀ : ℝ) (σ b : ℝ → ℝ)

/-- The textbook candidate stationary density for a one-dimensional time-homogeneous diffusion
with drift `b`, diffusion coefficient `σ`, reference point `x₀`, and normalizing constant `C`.
-/
def oneDimensionalDiffusionStationaryDensity
    : ℝ → ℝ :=
  fun x ↦
    (1 / C) * (1 / (σ x) ^ 2) *
      Real.exp (∫ r in x₀..x, (2 * b r) / (σ r) ^ 2)

/-- Evaluating the candidate stationary density gives the textbook formula
`C⁻¹ σ(x)⁻² exp (∫_{x₀}^x 2 b(r) / σ(r)^2 dr)`. -/
@[simp]
theorem oneDimensionalDiffusionStationaryDensity_apply
    (x : ℝ) :
    oneDimensionalDiffusionStationaryDensity C x₀ σ b x =
      (1 / C) * (1 / (σ x) ^ 2) *
        Real.exp (∫ r in x₀..x, (2 * b r) / (σ r) ^ 2) :=
  rfl

/-- The measure on `ℝ` with the textbook stationary density for the one-dimensional diffusion. -/
def oneDimensionalDiffusionStationaryMeasure
    : Measure ℝ :=
  volume.withDensity
    (fun x ↦ ENNReal.ofReal (oneDimensionalDiffusionStationaryDensity C x₀ σ b x))

variable {C x₀ : ℝ} {σ b : ℝ → ℝ}

-- Proof sketch: integrate the displayed density over `ℝ`, use the normalization identity
-- `∫ σ(x)⁻² exp (...) dx = C`, and divide by `C`.
/-- The textbook normalizing constant turns the candidate stationary measure into a probability
measure. -/
theorem oneDimensionalDiffusionStationaryMeasure_isProbabilityMeasure
    (hC : 0 < C)
    (hCeq : ∫ x, oneDimensionalDiffusionStationaryDensity C x₀ σ b x = C) :
    IsProbabilityMeasure (oneDimensionalDiffusionStationaryMeasure C x₀ σ b) := sorry

/-- The normalized stationary distribution attached to the textbook speed density. -/
abbrev oneDimensionalDiffusionStationaryDistribution
    (C x₀ : ℝ) (σ b : ℝ → ℝ) (hC : 0 < C)
    (hCeq : ∫ x, oneDimensionalDiffusionStationaryDensity C x₀ σ b x = C) :
    ProbabilityMeasure ℝ :=
  ⟨oneDimensionalDiffusionStationaryMeasure C x₀ σ b,
    oneDimensionalDiffusionStationaryMeasure_isProbabilityMeasure hC hCeq⟩

end OneDimensionalDiffusion

section OrnsteinUhlenbeck

/-- The stationary variance `σ^2 / (-2b)` of the Ornstein--Uhlenbeck diffusion in the regime
`b < 0`. -/
def ornsteinUhlenbeckStationaryVariance (b σ : ℝ) (hb : b < 0) : NNReal :=
  ⟨σ ^ 2 / (-2 * b), by
    have hden : 0 ≤ -2 * b := by
      nlinarith
    exact div_nonneg (sq_nonneg σ) hden⟩

end OrnsteinUhlenbeck

section CIR

variable (a b γ : ℝ)

-- Proof sketch: positivity of the Gamma shape parameter follows from positivity of `a`, `b`,
-- and `γ`.
/-- The Gamma shape parameter of the CIR stationary law is positive under the natural positivity
assumptions. -/
theorem cirStationaryShape_pos (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ) :
    0 < (2 * a * b) / γ := sorry

-- Proof sketch: positivity of the Gamma rate parameter follows from positivity of `a` and `γ`.
/-- The Gamma rate parameter of the CIR stationary law is positive under the natural positivity
assumptions. -/
theorem cirStationaryRate_pos (ha : 0 < a) (hγ : 0 < γ) :
    0 < (2 * a) / γ := sorry

end CIR

section Jacobi

variable (γ c θ : ℝ)

-- Proof sketch: positivity of the left Beta shape parameter follows from positivity of `c`,
-- `γ`, and `θ`.
/-- The left Beta shape parameter in the Jacobi stationary law is positive. -/
theorem jacobiStationaryLeftShape_pos
    (hγ : 0 < γ) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 1) :
    0 < (2 * c * θ) / γ := sorry

-- Proof sketch: positivity of the right Beta shape parameter follows from positivity of `c`,
-- `γ`, and `1 - θ`, where `0 < 1 - θ` comes from `0 < θ < 1`.
/-- The right Beta shape parameter in the Jacobi stationary law is positive. -/
theorem jacobiStationaryRightShape_pos
    (hγ : 0 < γ) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 1) :
    0 < (2 * c * (1 - θ)) / γ := sorry

end Jacobi

-- Proof sketch: verify the adjoint stationary equation for the density
-- `C⁻¹ σ(x)⁻² exp (∫_{x₀}^x 2 b(r) / σ(r)^2 dr)` and then use the normalization theorem above to
-- view the resulting measure as a probability measure invariant under every time slice `κ t`.
/-- Exercise 26.2.1 (1): for the transition semigroup `κ` of the one-dimensional diffusion
`dX_t = σ(X_t) dW_t + b(X_t) dt`, the normalized density
`C⁻¹ σ(x)⁻² exp (∫_{x₀}^x 2 b(r) / σ(r)^2 dr)` defines an invariant distribution. -/
theorem oneDimensionalDiffusion_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    {C x₀ : ℝ} {σ b : ℝ → ℝ} (hC : 0 < C)
    (hκ : HasAutonomousOneDimensionalDiffusionSemigroup κ σ b)
    (hCeq : ∫ x, oneDimensionalDiffusionStationaryDensity C x₀ σ b x = C) :
    IsInvariantDistributionForSemigroup κ
      (oneDimensionalDiffusionStationaryDistribution C x₀ σ b hC hCeq) := sorry

-- Proof sketch: compute the stationary density of the Ornstein--Uhlenbeck semigroup from the
-- general speed-density formula; for the nondegenerate Ornstein--Uhlenbeck diffusion with
-- `σ > 0`, integrability at infinity is equivalent to the quadratic exponent being negative,
-- which is exactly the condition `b < 0`.
/-- Exercise 26.2.1 (2): for the Ornstein--Uhlenbeck diffusion with `σ > 0`, the transition
semigroup has an invariant distribution if and only if the drift coefficient satisfies `b < 0`. -/
theorem ornsteinUhlenbeck_hasInvariantDistribution_iff
    (κ : NNReal → Kernel ℝ ℝ) (b σ : ℝ) (hσ : 0 < σ)
    (hκ : HasOrnsteinUhlenbeckSemigroup κ b σ) :
    (∃ π : ProbabilityMeasure ℝ, IsInvariantDistributionForSemigroup κ π) ↔ b < 0 := sorry

-- Proof sketch: specialize the general stationary-density formula to constant diffusion
-- coefficient `σ` and linear drift `x ↦ b x`, obtaining the centered Gaussian density with
-- variance `σ^2 / (-2 b)`.
/-- Exercise 26.2.1 (3): when `b < 0`, the invariant distribution of the Ornstein--Uhlenbeck
semigroup is the centered Gaussian law with variance `σ^2 / (-2 b)`. -/
theorem ornsteinUhlenbeck_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    (b σ : ℝ) (hb : b < 0)
    (hκ : HasOrnsteinUhlenbeckSemigroup κ b σ) :
    IsInvariantDistributionForSemigroup κ
      (⟨gaussianReal 0 (ornsteinUhlenbeckStationaryVariance b σ hb), inferInstance⟩ :
        ProbabilityMeasure ℝ) := sorry

-- Proof sketch: specialize the stationary-density formula to the CIR coefficients
-- `cirDiffusionCoeff` and `cirDriftCoeff` from Example 26.11, then identify the resulting
-- normalized density with the Gamma density having shape `2ab / γ` and rate `2a / γ`.
/-- Exercise 26.2.1 (4): the invariant distribution of the Cox--Ingersoll--Ross diffusion is the
Gamma distribution with shape `2ab / γ` and rate `2a / γ`. -/
theorem cir_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ)
    (hκ :
      HasOneDimensionalDiffusionSemigroup κ
        (cirDiffusionCoeff (Real.toNNReal γ))
        (cirDriftCoeff (Real.toNNReal a) (Real.toNNReal b))) :
    IsInvariantDistributionForSemigroup κ
      (⟨gammaMeasure ((2 * a * b) / γ) ((2 * a) / γ),
        isProbabilityMeasure_gammaMeasure
          (cirStationaryShape_pos a b γ ha hb hγ)
          (cirStationaryRate_pos a γ ha hγ)⟩ : ProbabilityMeasure ℝ) := sorry

-- Proof sketch: apply the one-dimensional stationary-density formula on `(0, 1)` to the Jacobi
-- coefficients `σ(x) = sqrt (γ x (1 - x))` and `b(x) = c (θ - x)`, then identify the normalized
-- density with the displayed Beta law.
/-- Exercise 26.2.1 (5): for the diffusion on `[0,1]` with coefficients
`σ(x) = sqrt (γ x (1 - x))` and `b(x) = c (θ - x)`, the invariant distribution is the Beta law
`β_(2 c θ / γ, 2 c (1 - θ) / γ)`. -/
theorem jacobi_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    (γ c θ : ℝ) (hγ : 0 < γ) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 1)
    (hκ :
      HasAutonomousOneDimensionalDiffusionSemigroup κ
        (fun x ↦ Real.sqrt (γ * x * (1 - x)))
        (fun x ↦ c * (θ - x))) :
    IsInvariantDistributionForSemigroup κ
      (⟨betaMeasure ((2 * c * θ) / γ) ((2 * c * (1 - θ)) / γ),
        isProbabilityMeasureBeta
          (jacobiStationaryLeftShape_pos γ c θ hγ hc hθ)
          (jacobiStationaryRightShape_pos γ c θ hγ hc hθ)⟩ : ProbabilityMeasure ℝ) := sorry

end ProbabilityTheory

/-! ### Exercise_26_2_2 (from Items/Chap26) -/
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

/-! ### Remark_26_2 (from Items/Chap26) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {n m : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => Fin n → ℝ
local notation "StateProcess" => NNReal → Ω → State
local notation "BrownianProcess" => NNReal → Ω → Fin m → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

variable {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An `m`-dimensional Brownian process with filtration `ℱ` is a standard vector Brownian motion
whose coordinates are adapted to `ℱ`. -/
def IsBrownianMotionWithFiltration
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : BrownianProcess) : Prop :=
  IsStandardBrownianMotionVector μ W.toEuclidean ∧
    Adapted ℱ W

/-- The coefficients of the SDE are time-independent when their values depend only on the state
variable and not on the time parameter. -/
def TimeIndependentCoefficients (σ : DiffusionCoeff) (b : DriftCoeff) : Prop :=
  (∀ t₁ t₂ x, σ t₁ x = σ t₂ x) ∧
    ∀ t₁ t₂ x, b t₁ x = b t₂ x

/-- A generalized `n`-dimensional diffusion with initial state `ξ` is an `n`-dimensional process
driven by an `m`-dimensional Brownian motion whose coordinates admit the Itô decomposition with
coefficients `σ(t, X_t)` and `b(t, X_t)`. The Brownian martingale term is expressed through the
canonical vector bridge `IsMatrixBrownianLocalItoIntegral`, so the auxiliary scalar coordinate
realizations remain internal. -/
def IsGeneralizedNDimensionalDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → State) (W : BrownianProcess) (σ : DiffusionCoeff) (b : DriftCoeff)
    (X : StateProcess) : Prop :=
  IsBrownianMotionWithFiltration ℱ μ W ∧
    ∃ N : StateProcess,
      IsMatrixBrownianLocalItoIntegral
        ℱ
        μ
        W.toEuclidean
        (fun t ω i j ↦ σ t (X t ω) i j)
        N.toEuclidean ∧
      (∀ i, ProgMeasurable ℱ (fun t ω ↦ b t (X t ω) i)) ∧
      (∀ i T, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦ |b s.toNNReal (X s.toNNReal ω) i|)
          (Set.Icc (0 : ℝ) (T : ℝ))) ∧
      X =
        fun t ω i ↦
          ξ ω i +
            N t ω i +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X s.toNNReal ω) i

/-- An `n`-dimensional diffusion is a generalized `n`-dimensional diffusion whose coefficients are
time-independent. -/
def IsNDimensionalDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → State) (W : BrownianProcess) (σ : DiffusionCoeff) (b : DriftCoeff)
    (X : StateProcess) : Prop :=
  IsGeneralizedNDimensionalDiffusion ℱ μ ξ W σ b X ∧
    TimeIndependentCoefficients σ b

section StrongSolutionRealization

variable {ξ : Ω → State} {W : BrownianProcess} {σ : DiffusionCoeff} {b : DriftCoeff}
variable {X : StateProcess}

local notation "SolvesGeneralizedDiffusion" =>
  fun ξ' W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ μ ξ' W' σ b X'

/- Source/core/bridge triage for Remark 26.2:
- source-facing owner declarations in this file: `IsBrownianMotionWithFiltration`,
  `TimeIndependentCoefficients`, `IsGeneralizedNDimensionalDiffusion`, and
  `IsNDimensionalDiffusion`;
- core/canonical owner reused in the remark: `HasPathwiseStrongSolutionRealization`;
- derived API reused from `Remark_26_14`: `HasPathwiseStrongSolutionRealization.solvesSDE`,
  which is the direct canonical recall for the generalized-diffusion clause and avoids a duplicate
  local theorem shell.
-/

/- Remark 26.2: every strong-solution realization of the SDE determines a generalized
`n`-dimensional diffusion with initial state `ξ`; this is the specialization of the canonical
owner theorem `HasPathwiseStrongSolutionRealization.solvesSDE` to
`SolvesGeneralizedDiffusion`. -/
recall HasPathwiseStrongSolutionRealization.solvesSDE

-- Proof sketch: combine the canonical recall
-- `HasPathwiseStrongSolutionRealization.solvesSDE` with the time-independence assumption on the
-- coefficients.
/- A strong solution with time-independent diffusion and drift coefficients is an
`n`-dimensional diffusion in the autonomous sense. -/
set_option linter.unusedVariables false in
theorem strongSolution_is_n_dimensional_diffusion_of_timeIndependentCoefficients
    (hX : HasPathwiseStrongSolutionRealization
      (fun _ : BrownianProcess ↦ True)
      SolvesGeneralizedDiffusion
      ℱ ξ W X)
    (hcoeff : TimeIndependentCoefficients σ b) :
    IsNDimensionalDiffusion ℱ μ ξ W σ b X :=
  ⟨HasPathwiseStrongSolutionRealization.solvesSDE hX, hcoeff⟩

end StrongSolutionRealization

end ProbabilityTheory
