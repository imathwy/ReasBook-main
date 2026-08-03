module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Sequences

public section

/-- Helper for Exercise 28.6: every iterate of a self-isometry is an isometry. -/
lemma Isometry.iterate {X : Type u} [MetricSpace X] {f : X → X}
    (hf : Isometry f) (n : ℕ) : Isometry (f^[n]) := by
  -- Build the iterate by composing the original isometry at each successor step.
  induction n with
  | zero =>
      simpa only [Function.iterate_zero] using (isometry_id : Isometry (id : X → X))
  | succ n hn =>
      rw [Function.iterate_succ']
      exact hf.comp hn

/-- Helper for Exercise 28.6: canceling a common initial iterate preserves orbit distance. -/
lemma Isometry.dist_iterate_iterate_add {X : Type u} [MetricSpace X] {f : X → X}
    (hf : Isometry f) (a : X) (n k : ℕ) :
    dist ((f^[n]) a) ((f^[n + k]) a) = dist a ((f^[k]) a) := by
  -- Rewrite the later orbit point and cancel the common isometric iterate.
  rw [Function.iterate_add_apply]
  exact (hf.iterate n).dist_eq a ((f^[k]) a)

/-- Helper for Exercise 28.6: a point uniformly separated from the range has a separated orbit. -/
lemma Isometry.dist_iterate_le_of_range_separated {X : Type u} [MetricSpace X]
    {f : X → X} (hf : Isometry f) {a : X} {ε : ℝ}
    (hsep : ∀ x, ε ≤ dist a (f x)) {n m : ℕ} (hnm : n < m) :
    ε ≤ dist ((f^[n]) a) ((f^[m]) a) := by
  -- Express the larger index as a positive offset from the smaller index.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
  rw [show n + k + 1 = n + (k + 1) by omega]
  rw [hf.dist_iterate_iterate_add a n (k + 1)]
  rw [Function.iterate_succ_apply']
  exact hsep ((f^[k]) a)

/-- Exercise 28.6: An isometry from a compact metric space to itself is surjective. -/
theorem Isometry.surjective_of_compact {X : Type u} [MetricSpace X] [CompactSpace X]
    {f : X → X} (hf : Isometry f) : Function.Surjective f := by
  -- If surjectivity fails, choose a point outside the compact, hence closed, range.
  classical
  by_contra hsurj
  rw [Function.Surjective] at hsurj
  push Not at hsurj
  obtain ⟨a, ha⟩ := hsurj
  have ha_range : a ∉ Set.range f := by
    intro ha'
    obtain ⟨x, hx⟩ := ha'
    exact ha x hx
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hnhds : (Set.range f)ᶜ ∈ nhds a := hclosed.isOpen_compl.mem_nhds ha_range
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hsep : ∀ x, ε ≤ dist a (f x) := by
    intro x
    apply not_lt.mp
    intro hlt
    have hmem : f x ∈ Metric.ball a ε := by
      rw [Metric.mem_ball]
      simpa only [dist_comm] using hlt
    exact hball hmem ⟨x, rfl⟩
  -- Compactness gives a convergent subsequence of the forward orbit.
  obtain ⟨b, φ, hφ, hconv⟩ :=
    CompactSpace.tendsto_subseq (fun n ↦ (f^[n]) a)
  have hcauchy : CauchySeq ((fun n ↦ (f^[n]) a) ∘ φ) := hconv.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hcauchy) ε hε
  have hclose : dist ((f^[φ N]) a) ((f^[φ (N + 1)]) a) < ε := by
    simpa only [Function.comp_apply] using hN N le_rfl (N + 1) (Nat.le_succ N)
  -- Consecutive subsequence terms are also orbit terms with distinct indices.
  have hfar : ε ≤ dist ((f^[φ N]) a) ((f^[φ (N + 1)]) a) :=
    hf.dist_iterate_le_of_range_separated hsep (hφ (Nat.lt_succ_self N))
  exact (not_lt_of_ge hfar) hclose

/-- Exercise 28.6 (1): An isometry from a compact metric space to itself is bijective. -/
theorem Isometry.bijective_of_compact {X : Type u} [MetricSpace X] [CompactSpace X]
    {f : X → X} (hf : Isometry f) : Function.Bijective f :=
  ⟨hf.injective, hf.surjective_of_compact⟩

/-- Exercise 28.6 (2): An isometry from a compact metric space to itself is a homeomorphism. -/
theorem Isometry.isHomeomorph_of_compact {X : Type u} [MetricSpace X] [CompactSpace X]
    {f : X → X} (hf : Isometry f) : IsHomeomorph f :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hf.isEmbedding, hf.surjective_of_compact⟩
