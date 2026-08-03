module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.DiscreteSubset

public section

open Filter Set Topology

namespace UnitIntervalUniformPower

/-- The zero endpoint of the closed unit interval. -/
def zero : Icc (0 : ℝ) 1 :=
  ⟨0, le_rfl, zero_le_one⟩

/-- The one endpoint of the closed unit interval. -/
def one : Icc (0 : ℝ) 1 :=
  ⟨1, zero_le_one, le_rfl⟩

/-- The unit-interval-valued sequence that is `1` at coordinate `n` and `0` elsewhere. -/
def spike (n : ℕ) : UniformFun ℕ (Icc (0 : ℝ) 1) :=
  UniformFun.ofFun fun k ↦
    if k = n then one else zero

/-- Evaluation of a unit-interval coordinate spike. -/
theorem spike_apply (n k : ℕ) :
    spike n k = if k = n then one else zero := by
  -- The type alias and its conversion equivalence compute pointwise.
  rfl

/-- Helper for Exercise 28.1: distinct coordinate spikes are uniformly at least
distance one apart. -/
lemma spike_pairwise_one_le_dist :
    Pairwise fun n m : ℕ ↦ (1 : ℝ) ≤ dist (spike n) (spike m) := by
  intro n m hnm
  -- At coordinate `n`, the two spikes take the opposite endpoints of the unit interval.
  calc
    (1 : ℝ) = dist (UniformFun.toFun (spike n) n) (UniformFun.toFun (spike m) n) := by
      simp only [spike, UniformFun.toFun_ofFun, if_pos, hnm]
      norm_num [one, zero, Subtype.dist_eq]
    -- Evaluation is one-Lipschitz for the uniform metric.
    _ ≤ dist (spike n) (spike m) := by
      simpa using (UniformFun.lipschitzWith_eval n).dist_le_mul (spike n) (spike m)

/-- Helper for Exercise 28.1: the coordinate-spike map is a closed embedding. -/
lemma isClosedEmbedding_spike : IsClosedEmbedding spike := by
  -- Uniform separation converts the discrete index set into a closed embedded copy.
  exact Metric.isClosedEmbedding_of_pairwise_le_dist zero_lt_one spike_pairwise_one_le_dist

/-- The explicit subset of the uniformly topologized space
`UniformFun ℕ (Icc (0 : ℝ) 1)` consisting of the coordinate unit spikes. -/
def spikes : Set (UniformFun ℕ (Icc (0 : ℝ) 1)) :=
  Set.range spike

/-- The set of unit-interval coordinate spikes is infinite. -/
theorem spikes_infinite : spikes.Infinite := by
  -- Injectivity of the closed embedding makes its range infinite.
  exact Set.infinite_range_of_injective isClosedEmbedding_spike.injective

/-- Helper for Exercise 28.1: a closed discrete subset has no accumulation point. -/
lemma not_accPt_principal_of_isClosed_isDiscrete {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsClosed s) (hdiscrete : IsDiscrete s) (x : X) :
    ¬ AccPt x (Filter.principal s) := by
  intro hacc
  rw [accPt_iff_nhds] at hacc
  by_cases hx : x ∈ s
  · -- A discrete neighborhood meets the subset only at `x`.
    obtain ⟨U, hU, hU_inter⟩ := nhds_inter_eq_singleton_of_mem_discrete hdiscrete hx
    obtain ⟨y, hy, hyne⟩ := hacc U hU
    rw [hU_inter] at hy
    exact hyne hy
  · -- Outside the closed subset, its open complement is a disjoint neighborhood.
    have hcompl : sᶜ ∈ 𝓝 x := hs.isOpen_compl.mem_nhds hx
    obtain ⟨y, hy, _⟩ := hacc sᶜ hcompl
    exact hy.1 hy.2

/-- The set of unit-interval coordinate spikes has no limit point. -/
theorem spikes_no_accPt (x : UniformFun ℕ (Icc (0 : ℝ) 1)) :
    ¬ AccPt x (Filter.principal spikes) := by
  -- The closed embedding supplies both closedness and discreteness of its range.
  apply not_accPt_principal_of_isClosed_isDiscrete isClosedEmbedding_spike.isClosed_range
  exact isClosedEmbedding_spike.isInducing.isDiscrete_range

/-- Exercise 28.1: In the uniform topology on `[0, 1]ℕ`, there is an infinite subset
with no limit point. -/
theorem exists_infinite_set_no_accPt :
    ∃ s : Set (UniformFun ℕ (Icc (0 : ℝ) 1)),
      s.Infinite ∧ ∀ x, ¬ AccPt x (Filter.principal s) :=
  ⟨spikes, spikes_infinite, spikes_no_accPt⟩

end UnitIntervalUniformPower
