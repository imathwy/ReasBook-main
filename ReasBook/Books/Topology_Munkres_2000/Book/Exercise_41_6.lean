module

public import Topology_Munkres_2000.Book.Exercise_41_6.BoxTopology
public import Topology_Munkres_2000.Book.Exercise_33_9
public import Topology_Munkres_2000.Book.Theorem_19_1
public import Topology_Munkres_2000.Book.Proposition_19_1
public import Topology_Munkres_2000.Book.Theorem_41_5.Paracompact
public import Mathlib.Topology.Compactness.SigmaCompact

public section

universe u v

/-- Exercise 41.6 (1). A regular space covered by countably many compact subspaces
is paracompact. -/
theorem ParacompactSpace.ofCountableCompactCover {X : Type u} [TopologicalSpace X] [T3Space X]
    {ι : Type v} [Countable ι] (K : ι → Set X)
    (h_compact : ∀ i, IsCompact (K i)) (h_cover : ⋃ i, K i = Set.univ) :
    ParacompactSpace X := by
  -- The compact cover first supplies σ-compactness, hence Lindelöfness.
  letI : SigmaCompactSpace X := by
    refine SigmaCompactSpace.of_countable (Set.range K) (Set.countable_range K) ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact h_compact i
    · rw [Set.sUnion_range, h_cover]
  -- Regular Lindelöf spaces are paracompact.
  infer_instance

namespace SigmaCompactSpace

/-- A space covered by a countable indexed family of compact subsets is σ-compact. -/
theorem ofCountableCompactCover {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Countable ι] (K : ι → Set X)
    (h_compact : ∀ i, IsCompact (K i)) (h_cover : ⋃ i, K i = Set.univ) :
    SigmaCompactSpace X := by
  refine SigmaCompactSpace.of_countable (Set.range K) (Set.countable_range K) ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact h_compact i
  · rw [Set.sUnion_range, h_cover]

end SigmaCompactSpace

namespace EventuallyZeroRealBox

/-- Helper for Exercise 41.6: extend a function on `Fin n` by zero to all natural indices. -/
private def finiteBoxExtensionSequence (n : ℕ) (y : Fin n → ℝ) : ℕ → ℝ :=
  fun i ↦ if h : i < n then y ⟨i, h⟩ else 0

/-- Helper for Exercise 41.6: zero extension from `Fin n` has finite support. -/
private lemma finiteBoxExtension_hasFiniteSupport (n : ℕ) (y : Fin n → ℝ) :
    (finiteBoxExtensionSequence n y).HasFiniteSupport := by
  -- Every nonzero coordinate lies in the finite initial segment `Finset.range n`.
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range n)) ?_
  intro i hi
  simp only [Function.mem_support, finiteBoxExtensionSequence] at hi ⊢
  by_contra hin
  have hnot : ¬i < n := by
    intro hlt
    exact hin (Finset.mem_range.mpr hlt)
  simp only [hnot, ↓reduceDIte, ne_eq, not_true_eq_false] at hi

/-- Helper for Exercise 41.6: package finite-coordinate zero extension as an
eventually-zero sequence. -/
private def finiteBoxExtension (n : ℕ) (y : Fin n → ℝ) : EventuallyZeroRealBox :=
  WithTopology.toTopology eventuallyZeroRealBoxTopology
    ⟨finiteBoxExtensionSequence n y,
      mem_eventuallyZeroRealSequences.mpr (finiteBoxExtension_hasFiniteSupport n y)⟩

/-- Helper for Exercise 41.6: the canonical inclusion into the ambient real box is an embedding. -/
private lemma eventuallyZeroRealBox_isEmbedding :
    Topology.IsEmbedding
      (fun x : EventuallyZeroRealBox ↦
        (WithTopology.toTopology (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)
          x.ofTopology.1 :
          WithTopology (ℕ → ℝ) (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ))) := by
  -- Both wrapper topologies unfold to the same iterated induced topology.
  refine ⟨⟨?_⟩, ?_⟩
  · rw [WithTopology.topology_eq_induced]
    calc
      TopologicalSpace.induced WithTopology.ofTopology eventuallyZeroRealBoxTopology =
          TopologicalSpace.induced
            (Subtype.val ∘ WithTopology.ofTopology)
            (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ) := by
              rw [eventuallyZeroRealBoxTopology_def,
                induced_compose]
      _ = TopologicalSpace.induced
          (fun x : EventuallyZeroRealBox ↦
            WithTopology.toTopology (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)
              x.ofTopology.1)
          (TopologicalSpace.induced WithTopology.ofTopology
            (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)) := by
              rw [induced_compose]
              rfl
      _ = TopologicalSpace.induced
          (fun x : EventuallyZeroRealBox ↦
            WithTopology.toTopology (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)
              x.ofTopology.1)
          (WithTopology.instTopologicalSpace (ℕ → ℝ)
            (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)) := by
              rw [WithTopology.topology_eq_induced]
  · intro x y hxy
    apply WithTopology.ext
    apply Subtype.ext
    exact congrArg WithTopology.ofTopology hxy

/-- Helper for Exercise 41.6: finite-coordinate zero extension is continuous into the
raw box topology. -/
private lemma continuous_finiteBoxExtensionSequence (n : ℕ) :
    @Continuous (Fin n → ℝ) (ℕ → ℝ) Pi.topologicalSpace
      (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ) (finiteBoxExtensionSequence n) := by
  -- It suffices to calculate preimages of full coordinate boxes.
  refine (@TopologicalSpace.IsTopologicalBasis.continuous_iff
    (Fin n → ℝ) (ℕ → ℝ) Pi.topologicalSpace
    (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)
    (Pi.boxBasis fun _ : ℕ ↦ ℝ) Pi.isTopologicalBasis_boxBasis
    (finiteBoxExtensionSequence n)).mpr ?_
  intro s hs
  obtain ⟨U, hU, rfl⟩ := (Pi.mem_boxBasis s).mp hs
  by_cases houtside : ∀ i, n ≤ i → 0 ∈ U i
  · -- When all outside coordinates contain zero, only the first `n` coordinates matter.
    have hpreimage :
        finiteBoxExtensionSequence n ⁻¹' Set.pi Set.univ U =
          ⋂ j : Fin n, (fun y : Fin n → ℝ ↦ y j) ⁻¹' U j := by
      ext y
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_iInter]
      constructor
      · intro hy j
        simpa only [finiteBoxExtensionSequence, j.isLt, ↓reduceDIte] using hy j
      · intro hy i
        by_cases hi : i < n
        · simpa only [finiteBoxExtensionSequence, hi, ↓reduceDIte] using hy ⟨i, hi⟩
        · simp only [finiteBoxExtensionSequence, hi, ↓reduceDIte]
          exact houtside i (Nat.le_of_not_gt hi)
    rw [hpreimage]
    exact isOpen_iInter_of_finite fun j ↦ (hU j).preimage (continuous_apply j)
  · -- If an outside coordinate excludes zero, the preimage is empty.
    push Not at houtside
    obtain ⟨i, hi, hzero⟩ := houtside
    have hpreimage : finiteBoxExtensionSequence n ⁻¹' Set.pi Set.univ U = ∅ := by
      ext y
      constructor
      · intro hy
        have hnot : ¬i < n := Nat.not_lt.mpr hi
        have hyi := hy i (Set.mem_univ i)
        simp only [finiteBoxExtensionSequence, hnot, ↓reduceDIte] at hyi
        exact (hzero hyi).elim
      · intro hy
        exact hy.elim
    rw [hpreimage]
    exact isOpen_empty

/-- Helper for Exercise 41.6: the packaged finite-coordinate extension is continuous. -/
private lemma continuous_finiteBoxExtension (n : ℕ) :
    Continuous (finiteBoxExtension n) := by
  -- Test continuity after the inducing inclusion into the ambient box space.
  rw [eventuallyZeroRealBox_isEmbedding.isInducing.continuous_iff]
  exact @Continuous.comp
    (Fin n → ℝ)
    (ℕ → ℝ)
    (WithTopology (ℕ → ℝ) (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ))
    Pi.topologicalSpace
    (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)
    _ _ _ continuous_coinduced_rng (continuous_finiteBoxExtensionSequence n)

/-- Helper for Exercise 41.6: sequences supported below `n` and bounded coordinatewise by `m`. -/
private def finiteSupportBoundedBox (n m : ℕ) : Set EventuallyZeroRealBox :=
  {x | (∀ i, n ≤ i → x.ofTopology.1 i = 0) ∧ ∀ i, |x.ofTopology.1 i| ≤ m}

/-- Helper for Exercise 41.6: bounded finite-support boxes are images of finite cubes. -/
private lemma finiteSupportBoundedBox_eq_image (n m : ℕ) :
    finiteSupportBoundedBox n m =
      finiteBoxExtension n '' Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (-(m : ℝ)) m) := by
  -- A point in the image vanishes off the initial segment and satisfies the cube bounds.
  ext x
  constructor
  · intro hx
    let y : Fin n → ℝ := fun j ↦ x.ofTopology.1 j
    refine ⟨y, ?_, ?_⟩
    · intro j hj
      constructor
      · exact (abs_le.mp (hx.2 j)).1
      · exact (abs_le.mp (hx.2 j)).2
    · apply WithTopology.ext
      apply Subtype.ext
      funext i
      by_cases hi : i < n
      · simp only [finiteBoxExtension, finiteBoxExtensionSequence, hi, ↓reduceDIte, y]
      · simp only [finiteBoxExtension, finiteBoxExtensionSequence, hi, ↓reduceDIte]
        exact (hx.1 i (Nat.le_of_not_gt hi)).symm
  · rintro ⟨y, hy, rfl⟩
    constructor
    · intro i hi
      have hnot : ¬i < n := Nat.not_lt.mpr hi
      simp only [finiteBoxExtension, finiteBoxExtensionSequence, hnot, ↓reduceDIte]
    · intro i
      by_cases hi : i < n
      · let j : Fin n := ⟨i, hi⟩
        have hj : j.val = i := rfl
        have hyi : -(m : ℝ) ≤ y j ∧ y j ≤ m := by
          exact hy j (Set.mem_univ j)
        have hji : (⟨i, hi⟩ : Fin n) = j := by
          apply Fin.ext
          exact hj.symm
        simp only [finiteBoxExtension, finiteBoxExtensionSequence, hi, ↓reduceDIte]
        rw [hji]
        exact abs_le.mpr hyi
      · simp only [finiteBoxExtension, finiteBoxExtensionSequence, hi, ↓reduceDIte, abs_zero]
        exact_mod_cast Nat.zero_le m

/-- Helper for Exercise 41.6: each bounded finite-support box is compact. -/
private lemma isCompact_finiteSupportBoundedBox (n m : ℕ) :
    IsCompact (finiteSupportBoundedBox n m) := by
  -- The finite cube is compact, and the zero-extension map is continuous.
  rw [finiteSupportBoundedBox_eq_image]
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).image (continuous_finiteBoxExtension n)

/-- Helper for Exercise 41.6: bounded finite-support boxes exhaust the eventually-zero sequences. -/
private lemma iUnion_finiteSupportBoundedBox :
    ⋃ p : ℕ × ℕ, finiteSupportBoundedBox p.1 p.2 = Set.univ := by
  -- Choose an initial segment containing the support, then a natural bound for its finite sum.
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hsupport : (Function.support x.ofTopology.1).Finite :=
    mem_eventuallyZeroRealSequences.mp x.ofTopology.property
  obtain ⟨n, hn⟩ := hsupport.toFinset.exists_nat_subset_range
  obtain ⟨m, hm⟩ := exists_nat_ge (∑ i ∈ Finset.range n, |x.ofTopology.1 i|)
  refine Set.mem_iUnion.mpr ⟨(n, m), ?_⟩
  constructor
  · intro i hi
    by_contra hne
    have hisupport : i ∈ hsupport.toFinset := by
      simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hne
    have hirange := hn hisupport
    exact (Nat.not_lt.mpr hi) (Finset.mem_range.mp hirange)
  · intro i
    by_cases hi : i < n
    · have hterm : |x.ofTopology.1 i| ≤ ∑ j ∈ Finset.range n, |x.ofTopology.1 j| :=
        Finset.single_le_sum (fun j _ ↦ abs_nonneg (x.ofTopology.1 j))
          (Finset.mem_range.mpr hi)
      exact hterm.trans hm
    · have hzero : x.ofTopology.1 i = 0 := by
        by_contra hne
        have hisupport : i ∈ hsupport.toFinset := by
          simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hne
        exact hi (Finset.mem_range.mp (hn hisupport))
      rw [hzero, abs_zero]
      exact_mod_cast Nat.zero_le m

/-- Exercise 41.6 (2): the eventually-zero real sequences are paracompact
with the topology induced from the box topology on `ℕ → ℝ`. -/
instance _root_.EventuallyZeroRealBox.instParacompactSpace :
    ParacompactSpace EventuallyZeroRealBox := by
  -- The induced topology inherits regularity from the ambient real box space.
  letI : T3Space EventuallyZeroRealBox := eventuallyZeroRealBox_isEmbedding.t3Space
  -- Apply part (1) to the countable compact exhaustion indexed by `ℕ × ℕ`.
  exact ParacompactSpace.ofCountableCompactCover
    (fun p : ℕ × ℕ ↦ finiteSupportBoundedBox p.1 p.2)
    (fun p ↦ isCompact_finiteSupportBoundedBox p.1 p.2)
    iUnion_finiteSupportBoundedBox

end EventuallyZeroRealBox
