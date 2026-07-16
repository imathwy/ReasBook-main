import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.Corollary_25_19
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.StandardBrownianMotionVector

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix.Norms.Frobenius

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n m : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => EuclideanSpace ℝ (Fin n)
local notation "DriverState" => EuclideanSpace ℝ (Fin m)
local notation "ScalarProcess" => NNReal → Ω → ℝ
local notation "VectorProcess" => NNReal → Ω → State
local notation "BrownianProcess" => NNReal → Ω → DriverState
local notation "MatrixProcess" => NNReal → Ω → Matrix (Fin n) (Fin m) ℝ

variable {ℱ : TimeFiltration}

/- Source/core/bridge triage for Lemma 26.7:
- core/canonical owners in the sampled domain: `IsBrownianLocalItoIntegral` for scalar Itô
  integrals and `IsStandardBrownianMotionVector` for the Brownian driver;
- bridge/view introduced here: `IsMatrixBrownianLocalItoIntegral`, which exposes the intrinsic
  `State`-valued stochastic integral while keeping the auxiliary coordinate realizations internal.
-/
/-- A `State`-valued process `N` realizes the matrix-valued Brownian Itô integral of `H` against
the vector Brownian driver `W` when `N` is assembled coordinatewise from scalar Brownian local Itô
integrals. This is a bridge/view over the scalar owner `IsBrownianLocalItoIntegral`; the
auxiliary coordinate realizations are intentionally hidden inside the proposition so that
downstream statements can speak directly about the vector process `N`. -/
def IsMatrixBrownianLocalItoIntegral
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : BrownianProcess) (H : MatrixProcess)
    (N : VectorProcess) : Prop :=
  ∃ Nij : Fin n → Fin m → ScalarProcess,
    (∀ i : Fin n, ∀ j : Fin m,
      IsBrownianLocalItoIntegral ℱ μ (fun t ω ↦ W t ω j) (fun t ω ↦ H t ω i j) (Nij i j)) ∧
      ∀ t : NNReal, ∀ ω : Ω, ∀ i : Fin n, N t ω i = ∑ j : Fin m, Nij i j t ω

-- Proof sketch: apply the one-dimensional Itô isometry to each scalar bridge integral `Nij i j`,
-- using the deterministic-horizon finite-second-moment hypotheses `hH_second`; sum the resulting
-- identities over `j` and then over `i`, use the independence already packaged in the Brownian
-- owner `IsStandardBrownianMotionVector` to eliminate cross terms, identify the Euclidean norm on
-- `State` with the sum of the squares of the coordinates via `EuclideanSpace.real_norm_sq_eq`,
-- and identify the squared Hilbert--Schmidt norm with the squared Frobenius norm of the
-- matrix-valued integrand `H`.
/-- Lemma 26.7: if `H` is a progressively measurable `n × m`-valued integrand whose entries have
finite expected time-integrated squares on every deterministic interval `[0,T]`, then the
terminal `ℝⁿ`-valued Brownian Itô integral `N` of the matrix integrand `H` has second moment
equal to the expected time integral of the squared Hilbert--Schmidt norm of `H`, expressed
canonically as the squared Frobenius norm of the matrix-valued integrand. The bridge predicate
`IsMatrixBrownianLocalItoIntegral` keeps the coordinate scalar realizations internal, while the
deterministic-horizon square-integrability assumptions remain explicit through
`HasFiniteStoppedSecondMoment`, since they are not part of the scalar owner
`IsBrownianLocalItoIntegral`. -/
theorem matrix_brownianItoIntegral_secondMoment_eq_hilbertSchmidt_energy
    {W : BrownianProcess} {H : MatrixProcess} {N : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hN : IsMatrixBrownianLocalItoIntegral ℱ μ W H N)
    (hH_second :
      ∀ i : Fin n, ∀ j : Fin m, ∀ T : NNReal, 0 < T →
        HasFiniteStoppedSecondMoment μ (fun t ω ↦ H t ω i j) fun _ ↦ (T : ENNReal))
    (T : NNReal)
    :
    ∫ ω, ‖N T ω‖ ^ 2 ∂μ =
      ∫ ω, ∫ s in Set.Icc (0 : ℝ) (T : ℝ), ‖H s.toNNReal ω‖ ^ 2 ∂volume ∂μ := sorry

end ProbabilityTheory
