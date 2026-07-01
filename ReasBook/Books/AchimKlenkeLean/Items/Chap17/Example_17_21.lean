import AchimKlenkeLean.Items.Chap11.Theorem_11_10
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap17.Definition_17_12
import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap17.Lemma_17_45
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/- Example 17.21 is `source-facing`: it is Wright's discrete evolution model on the finite
frequency state space `{0, 1 / N, ..., 1}`. The primitive data is the one-step binomial
transition matrix on `Fin (N + 1)` together with the frequency coordinate. The `core/canonical`
owner layer is the Chapter 17 kernel realization API
`IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n) P X`,
the kernel harmonicity predicate `IsHarmonic`, and the Chapter 11 martingale-limit owner
`Filtration.limitProcess`. Endpoint absorption and the
identification of the canonical martingale limit with `{0, 1}` are `bridge/view` consequences of
the source model, not new owner objects. -/

variable (N : ℕ+)

/-- The type-`A` gene frequency corresponding to the count state `i ∈ {0, ..., N}`. -/
def wrightFrequency (i : Fin (N + 1)) : ℝ :=
  (i : ℝ) / N

-- Proof sketch: `i ≤ N` for `i : Fin (N + 1)`, so dividing by the positive population size `N`
-- gives a number in `[0, 1]`.
/-- The Wright frequency lies in the unit interval. -/
theorem wrightFrequency_le_one (i : Fin (N + 1)) :
    Real.toNNReal (wrightFrequency N i) ≤ 1 := sorry

/-- Example 17.21: in Wright's evolution model with population size `N`, if the current type-`A`
frequency is `x = i / N`, then the next generation count has the canonical binomial law
`PMF.binomial x N`. This gives the one-step transition matrix on the finite state space
`Fin (N + 1)`. -/
def wrightTransitionMatrix : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞ :=
  fun i j ↦ PMF.binomial (Real.toNNReal (wrightFrequency N i)) (wrightFrequency_le_one N i) N j

/-- Expanding `wrightTransitionMatrix` gives the canonical binomial row law of Wright's model. -/
theorem wrightTransitionMatrix_def (i j : Fin (N + 1)) :
    wrightTransitionMatrix N i j =
      PMF.binomial (Real.toNNReal (wrightFrequency N i)) (wrightFrequency_le_one N i) N j :=
  rfl

-- Proof sketch: each row is the `PMF.binomial` distribution on `Fin (N + 1)`, so its total mass
-- is `1`.
/-- The Wright transition matrix is stochastic. -/
theorem wrightTransitionMatrix_isStochasticMatrix :
    IsStochasticMatrix (wrightTransitionMatrix N) := sorry

-- Proof sketch: at frequency `0`, the binomial law is concentrated at `0`.
/-- The zero-frequency state is absorbing for Wright's model. -/
theorem wrightTransitionMatrix_isAbsorbing_zero :
    IsAbsorbingState (wrightTransitionMatrix N) 0 := sorry

-- Proof sketch: at frequency `1`, the binomial law is concentrated at the maximal count state.
/-- The full-frequency state is absorbing for Wright's model. -/
theorem wrightTransitionMatrix_isAbsorbing_one :
    IsAbsorbingState (wrightTransitionMatrix N) (Fin.last N) := sorry

-- Proof sketch: `wrightFrequency N` takes values in `[0, 1]`, so its image is a bounded subset
-- of `ℝ`.
/-- The Wright frequency has bounded range on the finite state space. -/
theorem wrightFrequency_isBounded :
    Bornology.IsBounded (Set.range (wrightFrequency N)) := sorry

-- Proof sketch: if the current frequency is `x = i / N`, then the next generation count is
-- `Bin(N, x)`, whose mean is `Nx`; dividing by `N` shows that the one-step expected next
-- frequency equals the current one.
/-- The Wright frequency is harmonic for the Wright transition matrix. -/
theorem wrightFrequency_isHarmonic :
    IsHarmonic (discreteMatrixKernel (wrightTransitionMatrix N)) (wrightFrequency N) := sorry

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Fin (N + 1) → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → Fin (N + 1)}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n) P X]

local notation "M" => fun n ω ↦ wrightFrequency N (X n ω)
local notation "ℱ" => processFiltration X

/-- For any realization of Wright's model, the gene-frequency process is a martingale. -/
theorem wrightFrequency_martingale
    (i : Fin (N + 1)) :
    Martingale M ℱ (P i : Measure Ω) :=
  harmonicFunction_comp_martingale
    (wrightFrequency_isBounded N)
    (wrightFrequency_isHarmonic N) i

-- Proof sketch: apply the Chapter 11 bounded-`L²` martingale convergence theorem to the bounded
-- martingale `M`; the canonical limit is `Filtration.limitProcess M ℱ (P i : Measure Ω)`.
/-- The Wright frequency process converges almost surely to its canonical martingale limit. -/
theorem wrightFrequency_ae_tendsto_limitProcess
    (i : Fin (N + 1)) :
    ∀ᵐ ω ∂(P i : Measure Ω),
      Tendsto (fun n ↦ M n ω) atTop
        (nhds (Filtration.limitProcess M ℱ (P i : Measure Ω) ω)) := sorry

-- Proof sketch: the bounded martingale `M` converges almost surely; because `M` takes values in
-- the finite set `{0, 1 / N, ..., 1}`, every convergent sample path is eventually constant.
-- Any eventual constant value must be an absorbing state of `wrightTransitionMatrix N`, and the
-- only absorbing states are `0` and `1`.
/-- The canonical almost-sure limit of Wright's frequency martingale takes values in `{0, 1}`. -/
theorem wrightFrequency_limitProcess_ae_mem_endpoints
    (i : Fin (N + 1)) :
    ∀ᵐ ω ∂(P i : Measure Ω),
      Filtration.limitProcess M ℱ (P i : Measure Ω) ω ∈ ({0, 1} : Set ℝ) := sorry

-- Proof sketch: combine the canonical martingale-limit convergence theorem with the endpoint
-- identification of the canonical limit random variable.
/-- Example 17.21: in Wright's evolution model, the type-`A` gene frequency is a martingale and
converges almost surely to a limit taking only the absorbing values `0` and `1`. -/
theorem wrightFrequency_ae_tendsto_zero_or_one
    (i : Fin (N + 1)) :
    (∀ᵐ ω ∂(P i : Measure Ω),
      Tendsto (fun n ↦ M n ω) atTop
        (nhds (Filtration.limitProcess M ℱ (P i : Measure Ω) ω))) ∧
      (∀ᵐ ω ∂(P i : Measure Ω),
        Filtration.limitProcess M ℱ (P i : Measure Ω) ω ∈ ({0, 1} : Set ℝ)) := by
  exact ⟨wrightFrequency_ae_tendsto_limitProcess N i,
    wrightFrequency_limitProcess_ae_mem_endpoints N i⟩

end

end ProbabilityTheory
