

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_2_43 (from Items/Chap02) -/
open Set MeasureTheory

universe u

variable {Ω : Type u} {d : ℕ}

/-- The event that the origin lies in an infinite open cluster is contained in the event that
percolation occurs somewhere in the lattice. -/
theorem originInInfiniteClusterEvent_subset_percolationOccurs
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    originInInfiniteClusterEvent cluster ⊆ percolationOccurs cluster := by
  intro ω hω
  exact ⟨0, by simpa [originInInfiniteClusterEvent] using hω⟩

variable [MeasurableSpace Ω]

/-- The origin-percolation probability is bounded above by the percolation probability. -/
theorem originPercolationProbability_le_percolationProbability
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    originPercolationProbability μ cluster ≤ percolationProbability μ cluster := by
  simpa [ProbabilityMeasure.coeFn_def, originPercolationProbability, percolationProbability] using
    (measure_mono (originInInfiniteClusterEvent_subset_percolationOccurs cluster) :
      (μ : Measure Ω) (originInInfiniteClusterEvent cluster) ≤
        (μ : Measure Ω) (percolationOccurs cluster))

/-- If the origin-percolation probability vanishes and the infinite-cluster marginals are
translation invariant, then the percolation probability also vanishes. -/
theorem percolationProbability_eq_zero_of_originPercolationProbability_eq_zero
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d))
    [HasTranslationInvariantInfiniteClusterMarginals μ cluster]
    (h_origin : originPercolationProbability μ cluster = 0) :
    percolationProbability μ cluster = 0 := by
  have h_origin_toNNReal :
      ((μ : Measure Ω) (originInInfiniteClusterEvent cluster)).toNNReal = 0 := by
    simpa [ProbabilityMeasure.coeFn_def, originPercolationProbability] using h_origin
  have h_origin_measure : (μ : Measure Ω) (originInInfiniteClusterEvent cluster) = 0 := by
    rcases (ENNReal.toNNReal_eq_zero_iff _).1 h_origin_toNNReal with h_zero | h_top
    · exact h_zero
    · exact False.elim
        ((measure_ne_top (μ : Measure Ω) (originInInfiniteClusterEvent cluster)) h_top)
  have h_site_zero :
      ∀ y : LatticePoint d, (μ : Measure Ω) {ω | Set.Infinite (cluster y ω)} = 0 := by
    intro y
    have h_site_measure :
        (μ : Measure Ω) {ω | Set.Infinite (cluster y ω)} =
          (μ : Measure Ω) (originInInfiniteClusterEvent cluster) := by
      simpa [ProbabilityMeasure.coeFn_def, originPercolationProbability,
        ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using
          (originPercolationProbability_eq_site μ cluster y).symm
    rw [h_site_measure]
    exact h_origin_measure
  have h_union :
      percolationOccurs cluster = ⋃ y : LatticePoint d, {ω | Set.Infinite (cluster y ω)} := by
    ext ω
    simp [percolationOccurs]
  have h_perc_measure : (μ : Measure Ω) (percolationOccurs cluster) = 0 := by
    rw [h_union]
    exact measure_iUnion_null h_site_zero
  simpa [ProbabilityMeasure.coeFn_def, percolationProbability] using
    congrArg ENNReal.toNNReal h_perc_measure

/-- Theorem 2.43: under translation invariance of the infinite-cluster marginals, the percolation
probability vanishes when the origin-percolation probability vanishes, and it equals `1` when the
origin-percolation probability is strictly positive. -/
theorem percolationProbability_zero_or_one_of_originPercolationProbability
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d))
    [HasTranslationInvariantInfiniteClusterMarginals μ cluster]
    (h_zero_or_one :
      percolationProbability μ cluster = 0 ∨ percolationProbability μ cluster = 1) :
    (originPercolationProbability μ cluster = 0 →
        percolationProbability μ cluster = 0) ∧
      (0 < originPercolationProbability μ cluster →
        percolationProbability μ cluster = 1) := sorry
