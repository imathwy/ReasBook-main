module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.WithTopology

public section

namespace BoxRealSequence

/-- The set of bounded real sequences in real sequence space with the box topology. -/
def boundedSequences : Set BoxRealSequence :=
  {a | Bornology.IsBounded (Set.range a.ofTopology)}

/-- Membership in `boundedSequences` means that the underlying real sequence has bounded range. -/
@[simp] theorem mem_boundedSequences (a : BoxRealSequence) :
    a ∈ boundedSequences ↔ Bornology.IsBounded (Set.range a.ofTopology) := Iff.rfl

/-- Helper for Example 23.6: uniformly close functions have bounded ranges simultaneously. -/
private lemma isBounded_range_iff_of_uniformlyClose {ι α : Type*} [PseudoMetricSpace α]
    {f g : ι → α} (hclose : ∃ D, ∀ i, dist (f i) (g i) ≤ D) :
    Bornology.IsBounded (Set.range f) ↔ Bornology.IsBounded (Set.range g) := by
  -- Transfer a pairwise bound across the two uniformly bounded endpoint errors.
  obtain ⟨D, hD⟩ := hclose
  constructor
  · intro hf
    rw [Metric.isBounded_range_iff] at hf ⊢
    obtain ⟨C, hC⟩ := hf
    refine ⟨C + 2 * D, fun i j ↦ ?_⟩
    calc
      dist (g i) (g j) ≤ dist (g i) (f i) + dist (f i) (f j) + dist (f j) (g j) :=
        dist_triangle4 _ _ _ _
      _ ≤ C + 2 * D := by
        rw [dist_comm (g i) (f i)]
        linarith [hD i, hC i j, hD j]
  · intro hg
    rw [Metric.isBounded_range_iff] at hg ⊢
    obtain ⟨C, hC⟩ := hg
    refine ⟨C + 2 * D, fun i j ↦ ?_⟩
    calc
      dist (f i) (f j) ≤ dist (f i) (g i) + dist (g i) (g j) + dist (g j) (f j) :=
        dist_triangle4 _ _ _ _
      _ ≤ C + 2 * D := by
        rw [dist_comm (g j) (f j)]
        linarith [hD i, hC i j, hD j]

/-- Helper for Example 23.6: membership in the centered radius-one box gives a
coordinatewise distance bound. -/
private lemma dist_lt_one_of_mem_centeredBox {a b : ℕ → ℝ}
    (hb : b ∈ Set.pi Set.univ (fun n ↦ Set.Ioo (a n - 1) (a n + 1))) :
    ∀ n, dist (b n) (a n) < 1 := by
  -- Convert the two interval inequalities into the absolute-value distance formula.
  intro n
  have hn := hb n (Set.mem_univ n)
  rw [Set.mem_Ioo] at hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hn.1]
  · linarith [hn.2]

/-- Helper for Example 23.6: the bounded-sequence subset contains the zero sequence. -/
private lemma boundedSequences_nonempty : boundedSequences.Nonempty := by
  -- The zero sequence has pairwise distance bounded by zero.
  refine ⟨ofSequence (fun _ : ℕ ↦ 0), ?_⟩
  rw [mem_boundedSequences, Metric.isBounded_range_iff]
  refine ⟨0, fun n m ↦ ?_⟩
  rw [ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology]
  simp

/-- Helper for Example 23.6: the natural-number sequence has unbounded range. -/
private lemma natCastSequence_not_mem_boundedSequences :
    ofSequence (fun n : ℕ ↦ (n : ℝ)) ∉ boundedSequences := by
  -- A pairwise bound fails between zero and a sufficiently large natural number.
  intro hbounded
  rw [mem_boundedSequences, Metric.isBounded_range_iff] at hbounded
  obtain ⟨C, hC⟩ := hbounded
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hdist := hC n 0
  rw [ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology] at hdist
  norm_num [Real.dist_eq] at hdist
  linarith

/-- Example 23.6 (1): The bounded real sequences form a clopen subset of `ℕ → ℝ`
with the box topology. -/
theorem boundedSequences_isClopen : IsClopen boundedSequences := by
  -- Around each sequence, the radius-one coordinate box preserves boundedness.
  have hopen : IsOpen boundedSequences := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    let U : ℕ → Set ℝ := fun n ↦ Set.Ioo (x.ofTopology n - 1) (x.ofTopology n + 1)
    refine ⟨{y | y.ofTopology ∈ Set.pi Set.univ U}, ?_, ?_, ?_⟩
    · intro y hy
      rw [mem_boundedSequences] at hx ⊢
      have hclose : ∃ D, ∀ n, dist (y.ofTopology n) (x.ofTopology n) ≤ D := by
        refine ⟨1, fun n ↦ ?_⟩
        exact (dist_lt_one_of_mem_centeredBox hy n).le
      exact (isBounded_range_iff_of_uniformlyClose hclose).mpr hx
    · rw [WithTopology.isOpen_iff]
      have hbox :=
        @Pi.isOpen_box ℕ (fun _ ↦ ℝ) (fun _ ↦ inferInstance) U fun _ ↦ isOpen_Ioo
      have heq :
          WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) ⁻¹'
              {y | y.ofTopology ∈ Set.pi Set.univ U} =
            Set.pi Set.univ U := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rwa [heq]
    · intro n hn
      dsimp [U]
      constructor
      · linarith
      · linarith
  have hopen_compl : IsOpen boundedSequencesᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    let U : ℕ → Set ℝ := fun n ↦ Set.Ioo (x.ofTopology n - 1) (x.ofTopology n + 1)
    refine ⟨{y | y.ofTopology ∈ Set.pi Set.univ U}, ?_, ?_, ?_⟩
    · intro y hy hybounded
      apply hx
      rw [Set.mem_compl_iff] at hx
      rw [mem_boundedSequences] at hybounded ⊢
      have hclose : ∃ D, ∀ n, dist (y.ofTopology n) (x.ofTopology n) ≤ D := by
        refine ⟨1, fun n ↦ ?_⟩
        exact (dist_lt_one_of_mem_centeredBox hy n).le
      exact (isBounded_range_iff_of_uniformlyClose hclose).mp hybounded
    · rw [WithTopology.isOpen_iff]
      have hbox :=
        @Pi.isOpen_box ℕ (fun _ ↦ ℝ) (fun _ ↦ inferInstance) U fun _ ↦ isOpen_Ioo
      have heq :
          WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) ⁻¹'
              {y | y.ofTopology ∈ Set.pi Set.univ U} =
            Set.pi Set.univ U := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rwa [heq]
    · intro n hn
      dsimp [U]
      constructor
      · linarith
      · linarith
  -- Openness of the complement supplies the closed half of clopenness.
  exact ⟨isOpen_compl_iff.mp hopen_compl, hopen⟩

/-- Example 23.6 (2): The countable Cartesian power `ℕ → ℝ` is not connected in the
box topology. -/
theorem not_connected : ¬ConnectedSpace BoxRealSequence := by
  -- Connectedness would force the nonempty clopen bounded-sequence set to be universal.
  intro hconnected
  letI : ConnectedSpace BoxRealSequence := hconnected
  have huniv : boundedSequences = Set.univ :=
    boundedSequences_isClopen.eq_univ boundedSequences_nonempty
  -- The explicit natural-number sequence contradicts that universality.
  apply natCastSequence_not_mem_boundedSequences
  rw [huniv]
  exact Set.mem_univ _

end BoxRealSequence
