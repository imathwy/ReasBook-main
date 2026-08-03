module

public import Topology_Munkres_2000.Book.Exercise_19_7.EventuallyZero
public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open scoped Topology

/-- Helper for Exercise 19.7: a real sequence with infinite support has a box-open
neighborhood disjoint from the eventually-zero sequences. -/
private lemma exists_boxNeighborhood_disjoint_eventuallyZero (x : ℕ → ℝ)
    (hx : ¬ x.HasFiniteSupport) :
    ∃ U : Set (ℕ → ℝ), IsOpen[Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)] U ∧
      x ∈ U ∧ U ∩ eventuallyZeroRealSequences = ∅ := by
  classical
  -- Require every coordinate that is nonzero in `x` to remain nonzero.
  let U : Set (ℕ → ℝ) :=
    Set.pi Set.univ fun i ↦ if x i = 0 then Set.univ else ({0} : Set ℝ)ᶜ
  refine ⟨U, ?_, ?_, ?_⟩
  · dsimp only [U]
    exact Pi.isOpen_box _ fun i ↦ by
      by_cases hxi : x i = 0
      · rw [if_pos hxi]
        exact isOpen_univ
      · rw [if_neg hxi]
        exact isOpen_compl_singleton
  · -- The center belongs to the box by its coordinatewise definition.
    dsimp only [U]
    intro i hi
    by_cases hxi : x i = 0
    · dsimp only
      rw [if_pos hxi]
      exact Set.mem_univ _
    · dsimp only
      rw [if_neg hxi]
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxi
  · -- Any eventually-zero point in the box would force `x` to have finite support.
    apply Set.eq_empty_of_forall_notMem
    intro y hy
    obtain ⟨hyU, hyFinite⟩ := hy
    apply hx
    rw [mem_eventuallyZeroRealSequences] at hyFinite
    exact hyFinite.subset fun i hxi ↦ by
      have hyi := hyU i (Set.mem_univ i)
      change x i ≠ 0 at hxi
      change y i ≠ 0
      dsimp only [U] at hyi
      rw [if_neg hxi] at hyi
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hyi

/-- Helper for Exercise 19.7: box-closure membership forces a real sequence to be
eventually zero. -/
private lemma mem_eventuallyZero_of_mem_boxClosure (x : ℕ → ℝ)
    (hx : x ∈ closure[Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)]
      eventuallyZeroRealSequences) :
    x ∈ eventuallyZeroRealSequences := by
  -- Separate any point of infinite support by the box constructed above.
  by_contra hxEventuallyZero
  have hxInfinite : ¬ x.HasFiniteSupport := by
    simpa only [mem_eventuallyZeroRealSequences] using hxEventuallyZero
  obtain ⟨U, hUOpen, hxU, hUDisjoint⟩ :=
    exists_boxNeighborhood_disjoint_eventuallyZero x hxInfinite
  have hInter :=
    ((@mem_closure_iff (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) x
      eventuallyZeroRealSequences).mp hx) U hUOpen hxU
  rw [hUDisjoint] at hInter
  exact Set.not_nonempty_empty hInter

/-- Exercise 19.7: in the box topology, the closure of the eventually zero
real sequences is the set itself. -/
theorem boxClosure_eventuallyZeroRealSequences :
    closure[Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)] eventuallyZeroRealSequences =
      eventuallyZeroRealSequences := by
  -- The separating box gives one inclusion; every set lies in its closure for the other.
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_eventuallyZero_of_mem_boxClosure x hx
  · exact @subset_closure (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
      eventuallyZeroRealSequences

/-- The eventually-zero real sequences form a closed set in the box topology. -/
theorem isClosed_eventuallyZeroRealSequences_box :
    IsClosed[Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)] eventuallyZeroRealSequences := by
  simpa only [closure_eq_iff_isClosed] using boxClosure_eventuallyZeroRealSequences

/-- Helper for Exercise 19.7: truncating a real sequence to a finite set of coordinates
produces an eventually-zero sequence. -/
private lemma finsetPiecewise_mem_eventuallyZero (I : Finset ℕ) (x : ℕ → ℝ) :
    I.piecewise x 0 ∈ eventuallyZeroRealSequences := by
  -- Outside `I`, the piecewise truncation is zero, so its support is contained in `I`.
  rw [mem_eventuallyZeroRealSequences]
  exact I.finite_toSet.subset fun i hi ↦ by
    by_contra hiI
    have hzero : I.piecewise x 0 i = 0 := I.piecewise_eq_of_notMem x 0 hiI
    exact hi hzero

/-- Helper for Exercise 19.7: every real sequence belongs to the product-topology
closure of the eventually-zero sequences. -/
private lemma mem_productClosure_eventuallyZero (x : ℕ → ℝ) :
    x ∈ closure eventuallyZeroRealSequences := by
  -- A product neighborhood controls finitely many coordinates, so a finite truncation suffices.
  rw [mem_closure_iff]
  intro U hUOpen hxU
  obtain ⟨I, hI⟩ :=
    exists_finset_piecewise_mem_of_mem_nhds (hUOpen.mem_nhds hxU) (fun _ ↦ 0)
  exact ⟨I.piecewise x 0, hI, finsetPiecewise_mem_eventuallyZero I x⟩

/-- The product-topology conclusion of Exercise 19.7: the eventually zero real
sequences are dense in the space of all real sequences. -/
theorem productClosure_eventuallyZeroRealSequences :
    closure eventuallyZeroRealSequences = (Set.univ : Set (ℕ → ℝ)) := by
  -- Every point has just been shown to lie in the closure.
  apply Set.eq_univ_of_forall
  exact mem_productClosure_eventuallyZero

/-- The eventually-zero real sequences are dense in the product topology. -/
theorem dense_eventuallyZeroRealSequences_product :
    Dense eventuallyZeroRealSequences := by
  rw [dense_iff_closure_eq]
  exact productClosure_eventuallyZeroRealSequences
