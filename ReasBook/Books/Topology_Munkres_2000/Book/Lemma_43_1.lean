module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Defs

public section

universe u

/-- Lemma 43.1: A metric space is complete if every Cauchy sequence in it has a
convergent subsequence. -/
theorem completeSpace_of_cauchySeq_subseq_tendsto {X : Type u} [MetricSpace X]
    (h : ∀ u : ℕ → X, CauchySeq u →
      ∃ a : X, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Filter.Tendsto (u ∘ φ) Filter.atTop (nhds a)) :
    CompleteSpace X := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨a, φ, hφ, ha⟩ := h u hu
  exact ⟨a, tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop ha⟩
