module

public import Topology_Munkres_2000.Book.Definition_27_3.LebesgueNumber

public section

/-- Helper for Lemma 27.5: a bounded set of sufficiently small diameter lies in a
ball centered at any of its points. -/
private lemma subset_ball_of_mem_of_diam_lt {X : Type u} [PseudoMetricSpace X]
    {B : Set X} {x : X} {δ : ℝ} (hx : x ∈ B) (hB : Bornology.IsBounded B)
    (hdiam : Metric.diam B < δ) : B ⊆ Metric.ball x δ := by
  -- Compare each point to the chosen center through the diameter bound.
  intro y hy
  rw [Metric.mem_ball]
  exact (Metric.dist_le_diam_of_mem hB hy hx).trans_lt hdiam

/-- Lemma 27.5 (The Lebesgue number lemma). Every open cover of a compact metric
space admits a Lebesgue number. -/
theorem lebesgueNumberLemma {X : Type u} [PseudoMetricSpace X] [CompactSpace X]
    (𝒜 : Set (Set X)) (h_open : ∀ U ∈ 𝒜, IsOpen U) (h_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ δ, IsLebesgueNumber 𝒜 δ := by
  -- Compactness supplies one radius whose balls refine the given open cover.
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric_sUnion
    CompactSpace.isCompact_univ h_open h_cover.ge
  refine ⟨δ, (isLebesgueNumber_iff.mpr ⟨hδ, ?_⟩)⟩
  intro B hB_nonempty hB_bounded hdiam
  obtain ⟨x, hx⟩ := hB_nonempty
  obtain ⟨U, hU, hballU⟩ := hballs x (Set.mem_univ x)
  -- Centering at a point of B turns its diameter bound into the required inclusion.
  exact ⟨U, hU, (subset_ball_of_mem_of_diam_lt hx hB_bounded hdiam).trans hballU⟩
