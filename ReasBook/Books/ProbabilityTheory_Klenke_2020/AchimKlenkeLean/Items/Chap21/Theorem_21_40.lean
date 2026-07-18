import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_39

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

universe u

local notation "PathSpace" => BrownianPathSpace

-- Use the canonical Borel measurable structure on the continuous path space `C([0, ∞), ℝ)`.
local instance theorem2140MeasurableSpacePathSpace : MeasurableSpace PathSpace := borel _

-- The local measurable structure on `PathSpace` is its Borel `σ`-algebra.
local instance theorem2140BorelSpacePathSpace : BorelSpace PathSpace := ⟨rfl⟩

/-- Tightness of the family of initial-value laws attached to a family of path laws. -/
def initial_value_laws_tight {ι : Type u} (P : ι → ProbabilityMeasure PathSpace) : Prop :=
  IsTightMeasureSet (Set.range fun i ↦
    (((P i).map (continuous_eval_const (0 : NNReal)).aemeasurable : ProbabilityMeasure ℝ) :
      Measure ℝ))

/-- Tightness of the initial-value laws is equivalent to the textbook tail estimate
`P_i {|ω(0)| > K} ≤ ε` uniformly in `i`. -/
-- Proof sketch: apply the characterization of `IsTightMeasureSet` by compact sets to the family
-- of pushforwards on `ℝ`, replace compact sets by large closed intervals `[-K, K]`, and then use
-- `ProbabilityMeasure.map_apply` for evaluation at `0` to rewrite the complements as the events
-- `{ω | K < |ω 0|}`.
theorem initial_value_laws_tight_iff {ι : Type u} (P : ι → ProbabilityMeasure PathSpace) :
    initial_value_laws_tight P ↔
      ∀ ε : NNReal, 0 < ε → ∃ K : NNReal, 0 < K ∧ ∀ i, P i {ω | K < |ω 0|} ≤ ε := sorry

/-- Uniform control of compact-interval oscillation probabilities for a family of path laws. -/
def uniformly_small_compact_interval_path_oscillation_probabilities {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) : Prop :=
  ∀ η ε : NNReal, 0 < η → 0 < ε → ∀ N : ℕ,
    ∃ δ : NNReal, 0 < δ ∧
      ∀ i, P i {ω | η < compactIntervalOscillation N ω δ} ≤ ε

/-- Theorem 21.40: a family of probability measures on `C([0,∞))`, represented here by
`ContinuousMap NNReal ℝ`, is weakly relatively compact iff the initial-value laws are tight and
the compact-interval oscillation probabilities are uniformly small. -/
-- Proof sketch: for the forward implication, combine Prokhorov tightness with the compact-set
-- characterization of relatively compact subsets of the continuous path space via Arzelà--Ascoli.
-- For the reverse implication, use the two stated bounds to build compact subsets capturing all
-- but `ε` mass uniformly in the family, and conclude by Prokhorov's theorem.
theorem continuous_path_measure_family_weakly_relatively_compact_iff {ι : Type u}
    (P : ι → ProbabilityMeasure PathSpace) :
    IsCompact (closure (Set.range P)) ↔
      initial_value_laws_tight P ∧
        uniformly_small_compact_interval_path_oscillation_probabilities P := sorry
