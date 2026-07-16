import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_3
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_12
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_2
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_8
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_66
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_70
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.DriftIntegralProcess
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Remark_26_2
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Remark_26_3
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Remark_26_14
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Theorem_26_18

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => Fin 1 → ℝ
local notation "ScalarProcess" => NNReal → Ω → ℝ
local notation "StateProcess" => NNReal → Ω → State
local notation "BrownianProcess" => NNReal → Ω → Fin 1 → ℝ
local notation "ScalarPathKernel" => Kernel ℝ (NNReal → ℝ)

/- Domain-style sampling for Theorem 26.10:
* primary domain: one-dimensional strong solutions of SDEs driven by scalar Brownian motions;
* sampled owner declarations in this domain: `IsBrownianMotionWithFiltration`,
  `HasPathwiseStrongSolutionRealization`, `IsTimeHomogeneousMarkovProcess`,
  and `HasStrongMarkovProperty`;
* owner abstraction: the chapter's canonical public owner is
  `HasUniqueStrongSolution GeneralizedSDEBrownianMotion (SolvesStrongGeneralizedSDE ... )`;
  the scalar `ℝ`-valued process formulation is a bridge/view used for the fixed-space corollary
  and the strong-Markov existence theorem, while the `Fin 1 → ℝ` model remains internal bridge
  data;
* primitive data: the scalar coefficients `b` and `σ`, the scalar initial state, and the scalar
  Brownian and solution processes, together with a scalar Markov family of laws and its path
  kernel for the strong-Markov clause;
* derived API: the `Fin 1 → ℝ` lift maps, the scalar bridge predicates below, and the scalar
  fixed-space strong-solution bridge.

Layer triage:
* source-facing: `SatisfiesYamadaWatanabeCondition`,
  `IsOneDimensionalBrownianMotionWithFiltration`,
  `HasPathwiseStrongOneDimensionalSolutionRealization`;
* core/canonical: `HasUniqueStrongSolution`, `IsTimeHomogeneousMarkovProcess`,
  and `HasStrongMarkovProperty`;
* bridge/view: `HasPathwiseStrongSolutionRealization`,
  `oneDimensionalState`, `oneDimensionalRandomVariable`, `oneDimensionalProcess`,
  `oneDimensionalDrift`, and `oneDimensionalDiffusion`.
-/

/-- Bridge/view: the scalar state `x` as the chapter's one-dimensional `Fin 1 → ℝ` state. -/
abbrev oneDimensionalState (x : ℝ) : State :=
  fun _ ↦ x

/-- Evaluating `oneDimensionalState x` at its unique coordinate recovers `x`. -/
theorem oneDimensionalState_apply (x : ℝ) (i : Fin 1) :
    oneDimensionalState x i = x := rfl

/-- Bridge/view: a scalar random variable as the chapter's one-dimensional state-valued random
variable. -/
abbrev oneDimensionalRandomVariable (ξ : Ω → ℝ) : Ω → State :=
  fun ω ↦ oneDimensionalState (ξ ω)

/-- Bridge/view: a scalar process as the chapter's one-dimensional state process. -/
abbrev oneDimensionalProcess (X : ScalarProcess) : StateProcess :=
  fun t ω ↦ oneDimensionalState (X t ω)

/-- The drift coefficient `b(t,x)` of a one-dimensional SDE, viewed as a `Fin 1`-valued drift
field on `ℝ¹`. -/
abbrev oneDimensionalDrift (b : NNReal → ℝ → ℝ) : NNReal → State → Fin 1 → ℝ :=
  fun t x _ ↦ b t (x 0)

-- Proof sketch: unfold `oneDimensionalDrift`; in dimension one the unique coordinate of the
-- lifted drift field is exactly `b t (x 0)`.
/-- Evaluating the lifted one-dimensional drift field recovers the scalar drift coefficient. -/
theorem oneDimensionalDrift_apply (b : NNReal → ℝ → ℝ) (t : NNReal) (x : State) (i : Fin 1) :
    oneDimensionalDrift b t x i = b t (x 0) := rfl

/-- The diffusion coefficient `σ(t,x)` of a one-dimensional SDE, viewed as a `1 × 1` diffusion
matrix field on `ℝ¹`. -/
abbrev oneDimensionalDiffusion (σ : NNReal → ℝ → ℝ) :
    NNReal → State → Fin 1 → Fin 1 → ℝ :=
  fun t x _ _ ↦ σ t (x 0)

-- Proof sketch: unfold `oneDimensionalDiffusion`; in dimension one the single matrix entry is the
-- scalar coefficient `σ t (x 0)`.
/-- Evaluating the lifted one-dimensional diffusion matrix recovers the scalar diffusion
coefficient. -/
theorem oneDimensionalDiffusion_apply
    (σ : NNReal → ℝ → ℝ) (t : NNReal) (x : State) (i j : Fin 1) :
    oneDimensionalDiffusion σ t x i j = σ t (x 0) := rfl

/-- The scalar Brownian-driver condition for Theorem 26.10: `W` is a one-dimensional Brownian
motion and is adapted to the filtration `ℱ`. -/
def IsOneDimensionalBrownianMotionWithFiltration
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ScalarProcess) : Prop :=
  IsBrownianMotion μ W ∧ Adapted ℱ W

/-- Bridge to the Chapter 26 Brownian-with-filtration owner on `Fin 1 → ℝ`. -/
theorem IsOneDimensionalBrownianMotionWithFiltration.toIsBrownianMotionWithFiltration
    {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ] {W : ScalarProcess}
    (hW : IsOneDimensionalBrownianMotionWithFiltration ℱ μ W) :
    IsBrownianMotionWithFiltration ℱ μ (oneDimensionalProcess W) := sorry

/-- The Yamada--Watanabe assumptions: the drift is globally Lipschitz in space with some uniform
Lipschitz constant, and the diffusion is globally Hölder-continuous of order `α ∈ [1/2, 1]` with
the source-faithful unit Hölder bound `|σ(t, x) - σ(t, x')| ≤ |x - x'|^α`, uniformly in time. -/
def SatisfiesYamadaWatanabeCondition (b σ : NNReal → ℝ → ℝ) : Prop :=
  (∃ K : NNReal, ∀ t : NNReal, LipschitzWith K (b t)) ∧
    ∃ α : NNReal, (1 / 2 : NNReal) ≤ α ∧ α ≤ 1 ∧
      ∀ t : NNReal, HolderWith 1 α (σ t)

/-- The scalar pathwise-strong realization predicate for one-dimensional SDEs. This is the
source-facing scalar view of the canonical Chapter 26 owner
`HasPathwiseStrongSolutionRealization`. -/
def HasPathwiseStrongOneDimensionalSolutionRealization
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ] (b σ : NNReal → ℝ → ℝ)
    (ξ : Ω → ℝ) (W X : ScalarProcess) : Prop :=
  HasPathwiseStrongSolutionRealization
    (IsBrownianMotionWithFiltration ℱ μ)
    (fun ξ' W' X' ↦
      IsGeneralizedNDimensionalDiffusion ℱ μ ξ' W'
        (oneDimensionalDiffusion σ) (oneDimensionalDrift b) X')
    ℱ
    (oneDimensionalRandomVariable ξ)
    (oneDimensionalProcess W)
    (oneDimensionalProcess X)

/- Source/core/bridge triage for Theorem 26.10:
- source-facing declarations kept here: `SatisfiesYamadaWatanabeCondition`,
  `IsOneDimensionalBrownianMotionWithFiltration`, and
  `HasPathwiseStrongOneDimensionalSolutionRealization`;
- core/canonical owner reused as the main theorem below: `HasUniqueStrongSolution` with
  `GeneralizedSDEBrownianMotion` and `SolvesStrongGeneralizedSDE`;
- core/canonical strong-Markov existence surface: the rowwise scalar realizations are stated
  directly together with the Chapter 17 owners `IsTimeHomogeneousMarkovProcess` and
  `HasStrongMarkovProperty`;
- bridge/view corollary: the fixed filtered-space scalar realization statement, expressed through
  `HasPathwiseStrongOneDimensionalSolutionRealization`;
- bridge/view declarations kept internal to the chapter API: the `Fin 1 → ℝ` lift maps
  `oneDimensionalState`, `oneDimensionalRandomVariable`, `oneDimensionalProcess`,
  `oneDimensionalDrift`, and `oneDimensionalDiffusion`.
-/

section OneDimensionalStrongSolutions

variable (ℱ : TimeFiltration) (μ : Measure Ω) (b σ : NNReal → ℝ → ℝ)

-- Proof sketch: this is the one-dimensional Yamada--Watanabe theorem, stated directly in the
-- chapter's canonical owner language for strong solutions with deterministic initial law
-- `δ_{x₀}`.
/-- Theorem 26.10: under the Yamada--Watanabe coefficient assumptions, the one-dimensional SDE
`dX_t = σ(t, X_t) dW_t + b(t, X_t) dt` has a unique strong solution in the canonical Chapter 26
sense for the deterministic initial law `δ_{x₀}`. -/
theorem hasUniqueStrongSolution_of_yamadaWatanabeCondition
    (hcoeff : SatisfiesYamadaWatanabeCondition b σ) (x₀ : ℝ) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE
        (oneDimensionalDiffusion σ) (oneDimensionalDrift b))
      (Measure.dirac (oneDimensionalState x₀)) := sorry

-- Proof sketch: realize simultaneously the strong solutions started from all deterministic
-- states on a common measurable path space, then apply the Chapter 17 strong-Markov owners to
-- this canonical family. This is the owner-level form of the textbook clause saying that the
-- one-dimensional Yamada--Watanabe solution is a strong Markov process.
/-- Strong-Markov companion of Theorem 26.10: under the Yamada--Watanabe coefficient
assumptions, the one-dimensional SDE admits a scalar strong-Markov solution family started from
every deterministic state. -/
theorem yamadaWatanabe_existsStrongMarkovSolutionFamily
    (hcoeff : SatisfiesYamadaWatanabeCondition b σ) :
    ∃ (Ω : Type u), ∃ _ : MeasurableSpace Ω,
      ∃ X : NNReal → Ω → ℝ,
      ∃ P : ℝ → ProbabilityMeasure Ω,
      ∃ pathKernel : Kernel ℝ (NNReal → ℝ),
      ∃ W : NNReal → Ω → ℝ,
        (∀ x₀ : ℝ,
          HasPathwiseStrongOneDimensionalSolutionRealization
            (processFiltration X) (P x₀ : Measure Ω) b σ (fun _ ↦ x₀) W X) ∧
        IsTimeHomogeneousMarkovProcess X P pathKernel ∧
        HasStrongMarkovProperty P X pathKernel := sorry

-- Proof sketch: specialize the canonical unique-strong-solution owner from
-- `hasUniqueStrongSolution_of_yamadaWatanabeCondition` to the fixed filtered probability space
-- `(Ω, μ, ℱ)` carrying the given Brownian motion `W`.
/-- Fixed-space corollary of Theorem 26.10: on a filtered probability space carrying the Brownian
driver `W`, the one-dimensional SDE admits a unique pathwise strong solution realization started
from the deterministic state `x₀`. -/
theorem existsUnique_strongSolution_of_yamadaWatanabeCondition
    [IsProbabilityMeasure μ]
    (W : ScalarProcess) (hW : IsOneDimensionalBrownianMotionWithFiltration ℱ μ W)
    (hcoeff : SatisfiesYamadaWatanabeCondition b σ) (x₀ : ℝ) :
    ∃! X : ScalarProcess,
      HasPathwiseStrongOneDimensionalSolutionRealization
        ℱ μ b σ (fun _ ↦ x₀) W X := sorry

end OneDimensionalStrongSolutions

end ProbabilityTheory
