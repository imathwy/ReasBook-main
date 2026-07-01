import Mathlib
import AchimKlenkeLean.Items.Chap17.Definition_17_12
import AchimKlenkeLean.Items.Chap17.Theorem_17_8
import AchimKlenkeLean.Items.Chap25.StandardBrownianMotionVector
import AchimKlenkeLean.Items.Chap26.Definition_26_4
import AchimKlenkeLean.Items.Chap26.Remark_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {n m : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => Fin n → ℝ
local notation "StatePath" => EuclideanPathSpace n
local notation "NoisePath" => EuclideanPathSpace m
local notation "StateProcess" => NNReal → Ω → State
local notation "BrownianProcess" => NNReal → Ω → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ

/- Domain-style sampling for Theorem 26.8:
* primary domain: strong solutions of multidimensional SDEs on filtered probability spaces, with
  Brownian drivers and Markov-property consequences;
* sampled owner declarations in this domain: `HasUniqueStrongSolution` and
  `StrongSolutionOperator.IsUniqueStrongSolution` from `Definition_26_4`,
  `HasPathwiseStrongSolutionRealization` from `Remark_26_14`,
  `IsBrownianMotionWithFiltration` and `IsGeneralizedNDimensionalDiffusion` from `Remark_26_2`,
  and `HasNaturalMarkovProperty` from `Theorem_17_8`;
* owner abstraction: the chapter organizes the theorem around
  `HasUniqueStrongSolution GeneralizedSDEBrownianMotion (SolvesStrongGeneralizedSDE σ b) μ₀`
  globally and `HasPathwiseStrongSolutionRealization` on fixed filtered spaces;
* primitive data in this file: the coefficient hypotheses
  `SDESpaceLipschitzWith` / `SDELinearGrowthWith`;
* bridge/view data: the path-valued Brownian/SDE predicates
  `GeneralizedSDEBrownianMotion` / `SolvesStrongGeneralizedSDE` and the evaluation map
  `pathProcess`;
* derived API: the deterministic-initial-value and Markov-property corollaries expressed through
  `HasPathwiseStrongSolutionRealization`.

Layer triage:
* source-facing: the coefficient hypotheses and the three textbook consequences recorded below;
* core/canonical: `HasUniqueStrongSolution`, `HasPathwiseStrongSolutionRealization`, and the
  generalized-diffusion owner from Chapter 26;
* bridge/view: `GeneralizedSDEBrownianMotion`, `SolvesStrongGeneralizedSDE`, and `pathProcess`.
-/

/-- The process obtained by evaluating a path-valued random variable at time `t`. -/
abbrev pathProcess {d : ℕ} (Y : Ω → EuclideanPathSpace d) : NNReal → Ω → Fin d → ℝ :=
  fun t ω ↦ Y ω t

/-- The coefficients `b` and `σ` are globally Lipschitz in the spatial variable with constant
`K`, uniformly in time. -/
def SDESpaceLipschitzWith (K : ℝ) (b : DriftCoeff) (σ : DiffusionCoeff) : Prop :=
  ∀ x x' : State, ∀ t : NNReal,
    ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖

/-- The coefficients `b` and `σ` satisfy the linear-growth estimate with constant `K`,
uniformly in time. -/
def SDELinearGrowthWith (K : ℝ) (b : DriftCoeff) (σ : DiffusionCoeff) : Prop :=
  ∀ x : State, ∀ t : NNReal,
    ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2)

/-- The path-valued Brownian-driver condition used by the canonical strong-solution owner for the
generalized SDE with `m`-dimensional noise. -/
abbrev GeneralizedSDEBrownianMotion :
    {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) →
      (Ω → NoisePath) → Prop :=
  fun {_} _ P ℱ W ↦
    ∃ _ : IsProbabilityMeasure P,
      IsBrownianMotionWithFiltration ℱ P (pathProcess W)

/-- The path-valued strong-solution relation for the generalized SDE with coefficients `(σ, b)`.
This is the primitive solution predicate paired with `GeneralizedSDEBrownianMotion` in the
canonical `HasUniqueStrongSolution` owner. -/
def SolvesStrongGeneralizedSDE (σ : DiffusionCoeff) (b : DriftCoeff) :
    {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) →
      (Ω → State) → (Ω → NoisePath) → (Ω → StatePath) → Prop :=
  fun {_} _ P ℱ ξ W X ↦
    ∃ _ : IsProbabilityMeasure P,
      IsGeneralizedNDimensionalDiffusion ℱ P ξ (pathProcess W) σ b (pathProcess X)

section GeneralizedStrongSolutions

variable (b : DriftCoeff) (σ : DiffusionCoeff)

/- Source/core/bridge triage for Theorem 26.8:
- source-facing declarations kept below: the coefficient hypotheses and the fixed-space/Markov
  corollaries;
- core/canonical owner: `HasUniqueStrongSolution GeneralizedSDEBrownianMotion
  (SolvesStrongGeneralizedSDE σ b)` for the generalized SDE with initial law `Measure.dirac x`
  and `HasPathwiseStrongSolutionRealization` on fixed filtered spaces;
- bridge/view layer: the path-valued generalized Brownian/solution predicates, used only to feed
  the global owner and no longer exposed as the fixed-space corollary surface;
- deleted duplicate owner layer: the path-valued Brownian and equation predicates are expressed
  directly through the chapter-owned `GeneralizedSDEBrownianMotion` and
  `SolvesStrongGeneralizedSDE`.
-/

-- Proof sketch: solve the generalized SDE by Picard iteration under the global Lipschitz and
-- linear-growth bounds, then use Gronwall's lemma to obtain pathwise uniqueness. This is exactly
-- the Chapter 26 owner-level notion of a unique strong solution for the Dirac initial law at `x`.
/-- Theorem 26.8: if `b` and `σ` are globally Lipschitz in the spatial variable and satisfy the
linear-growth condition, then for every deterministic initial point `x ∈ ℝ^n` the generalized SDE
has a unique strong solution in the canonical Chapter 26 sense. -/
theorem hasUniqueStrongSolution_of_lipschitz_linearGrowth
    {K : ℝ} (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ) (x : State) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE σ b)
      (Measure.dirac x) := sorry

end GeneralizedStrongSolutions

-- Proof sketch: construct the solution by Picard iteration using the chosen Brownian driver and
-- the owner-level pathwise solver from `hasUniqueStrongSolution_of_lipschitz_linearGrowth`, then
-- specialize it to the deterministic initial datum `x` on the filtered probability space
-- `(Ω, μ, ℱ)` carrying `W`.
/-- Fixed-space corollary of Theorem 26.8: on a given filtered probability space carrying the
Brownian driver `W`, there is a unique pathwise strong solution with deterministic initial
state `x`. -/
theorem existsUnique_strongSdeSolution_of_lipschitz_linearGrowth
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : TimeFiltration)
    (b : DriftCoeff) (σ : DiffusionCoeff) (W : BrownianProcess)
    (hW : IsBrownianMotionWithFiltration ℱ μ W) {K : ℝ}
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ)
    (x : State) :
    ∃! X : StateProcess,
      HasPathwiseStrongSolutionRealization
        (IsBrownianMotionWithFiltration ℱ μ)
        (fun ξ W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ μ ξ W' σ b X')
        ℱ
        (fun _ ↦ x)
        W
        X := sorry

-- Proof sketch: the strong solution is obtained from a pathwise solver acting on the Brownian
-- increments, so the future evolution after time `s` depends on the past only through the current
-- state `X_s`; this yields the Markov conditional-probability identity for the natural past
-- sigma-algebra.
/-- Any strong solution furnished by Theorem 26.8 is a Markov process for its natural past
sigma-algebra. -/
theorem strongSdeSolution_hasMarkovProperty
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : TimeFiltration)
    (b : DriftCoeff) (σ : DiffusionCoeff) {x : State}
    {W : BrownianProcess} {X : StateProcess}
    (hX : HasPathwiseStrongSolutionRealization
      (IsBrownianMotionWithFiltration ℱ μ)
      (fun ξ W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ μ ξ W' σ b X')
      ℱ
      (fun _ ↦ x)
      W
      X) :
    HasNaturalMarkovProperty μ X := sorry

-- Proof sketch: when the coefficients are time-independent, the same pathwise solver can be used
-- after every finite stopping time because restarting the equation at the stopped state does not
-- change the coefficient family. Combining this restart invariance with the Brownian strong
-- Markov property of the driver yields the stopped-path kernel identity for the solution family.
/-- For time-independent coefficients, a family of strong solutions started from each initial state
obeys the canonical strong Markov stopped-path identity. -/
theorem timeIndependent_strongSdeSolutionFamily_hasStrongMarkovProperty
    (P : State → ProbabilityMeasure Ω)
    (ℱ : TimeFiltration)
    (b : DriftCoeff) (σ : DiffusionCoeff) (W : BrownianProcess)
    (X : State → StateProcess) (κ : Kernel State (NNReal → State))
    (h_timeIndependent : TimeIndependentCoefficients σ b)
    (hX : ∀ x : State,
      HasPathwiseStrongSolutionRealization
        (IsBrownianMotionWithFiltration ℱ (P x : Measure Ω))
        (fun ξ W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ (P x : Measure Ω) ξ W' σ b X')
        ℱ
        (fun _ ↦ x)
        W
        (X x))
    (hκ : ∀ x : State, κ x = (P x : Measure Ω).map (processPath (X x))) :
    ∀ (x : State) (τ : Ω → WithTop NNReal)
      (hτ : IsStoppingTime (processFiltration (X x)) τ)
      (hτ_finite : ∀ᵐ ω ∂(P x : Measure Ω), τ ω ≠ ⊤)
      (f : (NNReal → State) → ℝ),
      Measurable f →
      (∃ C : ℝ, ∀ y, |f y| ≤ C) →
      (P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime (X x) τ ω) |
        hτ.measurableSpace] =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ∫ y, f y ∂ κ (stoppedValue (X x) τ ω) := sorry

end ProbabilityTheory
