import chapter1_reference_format.Chap01.Definition_1_2_13

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {α : Type u} [PseudoMetricSpace α]

/-- Proposition 1.2.14: a pseudo-metric space is complete if and only if every sequence whose
successive distances form a summable series converges. For the textbook normed-field statement,
apply this to the metric induced by the norm. -/
-- Proof sketch: If `K` is complete, a sequence with summable successive distances is Cauchy by
-- `cauchySeq_of_summable_dist`, hence converges by `cauchySeq_tendsto_of_complete`. Conversely,
-- from a Cauchy sequence extract a subsequence with summable successive distances using
-- `Metric.exists_subseq_summable_dist_of_cauchySeq`; the hypothesis gives a limit for the
-- subsequence, and then the original Cauchy sequence converges by
-- `Metric.complete_of_cauchySeq_tendsto`.
theorem completeSpace_iff_tendsto_of_summable_dist :
    CompleteSpace α ↔
      ∀ x : ℕ → α, Summable (fun n ↦ dist (x (n + 1)) (x n)) →
        ∃ a : α, Tendsto x atTop (𝓝 a) := by
  constructor
  · intro h x hx
    let _ : CompleteSpace α := h
    exact cauchySeq_tendsto_of_complete <| cauchySeq_of_summable_dist <| by
      simpa [Nat.succ_eq_add_one, dist_comm] using hx
  · intro h
    refine Metric.complete_of_cauchySeq_tendsto fun x hx ↦ ?_
    obtain ⟨f, hf, hxf⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq x hx
    obtain ⟨a, ha⟩ := h (x ∘ f) <| by
      simpa [Function.comp_apply] using hxf
    exact ⟨a, tendsto_nhds_of_cauchySeq_of_subseq hx hf.tendsto_atTop ha⟩
