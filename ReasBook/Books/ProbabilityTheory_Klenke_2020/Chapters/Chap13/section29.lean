import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_13_29 (from Items/Chap13) -/
open Filter MeasureTheory Set
open scoped Topology

universe u

namespace MeasureTheory
namespace FiniteMeasure

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

-- Proof sketch: apply tightness to the range of an arbitrary sequence in `ℱ` to obtain compact
-- sets with uniformly small complement mass, then use the Prokhorov compactness argument for
-- subprobability finite measures to extract a weakly convergent subsequence.
/-- Theorem 13.29 (1): a tight family of subprobability finite measures on a metric space is weakly
relatively sequentially compact for the weak topology on `FiniteMeasure E`. -/
theorem isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet
    (ℱ : Set (FiniteMeasure E)) (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1)
    (h_tight : IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' ℱ)) :
    ∀ μs : ℕ → FiniteMeasure E, (∀ n, μs n ∈ ℱ) →
      ∃ μ : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := sorry

-- Proof sketch: assuming `E` is Polish, use the sequential compactness hypothesis to obtain a
-- weak limit from any carefully chosen sequence in `ℱ`, apply the Polish-space tightness of single
-- finite measures together with Portmanteau control on closed complements, and derive uniform
-- compact containment for the whole family.
/-- Theorem 13.29 (2): on a Polish space, a weakly relatively sequentially compact family of
subprobability finite measures is tight. -/
theorem isTightMeasureSet_of_isWeaklyRelativelySequentiallyCompactFamily [PolishSpace E]
    (ℱ : Set (FiniteMeasure E)) (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1)
    (h_seq : ∀ μs : ℕ → FiniteMeasure E, (∀ n, μs n ∈ ℱ) →
      ∃ μ : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ)) :
    IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' ℱ) := sorry

end FiniteMeasure
end MeasureTheory
