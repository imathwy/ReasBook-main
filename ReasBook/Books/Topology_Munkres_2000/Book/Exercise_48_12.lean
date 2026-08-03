module

public import Topology_Munkres_2000.Book.Definition_20_9.UniformMetric
public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Topology_Munkres_2000.Book.Proposition_21_3.UniformConvergence
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular

public section

universe u

namespace Pi

open TopologicalSpace

/-- Helper for Exercise 48.12: a coordinatewise decreasing family with a compact tail in each
coordinate has a simultaneous point in all its members. -/
private lemma exists_mem_antitoneEventuallyCompact {J X : Type*} [TopologicalSpace X] [T2Space X]
    (C : ℕ → J → Set X) (hCanti : ∀ n j, C (n + 1) j ⊆ C n j)
    (hCnonempty : ∀ n j, (C n j).Nonempty) (hCclosed : ∀ n j, IsClosed (C n j))
    (hCcompact : ∀ j, (∃ N, IsCompact (C N j)) ∨ ∀ n, C n j = Set.univ) :
    ∃ x : J → X, ∀ n j, x j ∈ C n j := by
  classical
  -- Treat each coordinate separately, shifting to its first available compact stage.
  have hcoordinate (j : J) : (⋂ n, C n j).Nonempty := by
    have hanti : Antitone (fun n ↦ C n j) :=
      antitone_nat_of_succ_le (fun n ↦ hCanti n j)
    rcases hCcompact j with ⟨N, hNcompact⟩ | h_univ
    · have htailCompact : IsCompact (C (0 + N) j) := by
        simpa only [Nat.zero_add] using hNcompact
      have htail : (⋂ n, C (n + N) j).Nonempty :=
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
          (fun n ↦ C (n + N) j)
          (fun n ↦ hanti (Nat.add_le_add_right (Nat.le_succ n) N))
          (fun n ↦ hCnonempty (n + N) j) htailCompact
          (fun n ↦ hCclosed (n + N) j)
      rwa [hanti.iInter_nat_add N] at htail
    · simpa only [h_univ, Set.iInter_univ] using hCnonempty 0 j
  choose x hx using hcoordinate
  -- Membership in the coordinate intersections is exactly the desired simultaneous membership.
  refine ⟨x, fun n j ↦ ?_⟩
  exact Set.mem_iInter.mp (hx j) n

/-- Helper for Exercise 48.12: every nonempty box-open set contains a box of positive compact
real sets. -/
private lemma exists_compactBox_subset_open {J : Type*} {U : Set (J → ℝ)}
    (hUopen : @IsOpen (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)) U)
    (hUnonempty : U.Nonempty) :
    ∃ K : J → PositiveCompacts ℝ,
      Set.pi Set.univ (fun j ↦ (K j : Set ℝ)) ⊆ U := by
  classical
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace (fun _ : J ↦ ℝ)
  -- The generating open boxes form a basis because they contain `univ` and are intersection-closed.
  have hBasis :
      (boxTopologicalSpace (fun _ : J ↦ ℝ)).IsTopologicalBasis
        (boxBasis (fun _ : J ↦ ℝ)) := by
    have hWithUniv :=
      TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
        (t := boxTopologicalSpace (fun _ : J ↦ ℝ)) rfl
        (fun _ hs _ ht ↦ inter_mem_boxBasis hs ht)
    simpa only [Set.insert_eq_of_mem (univ_mem_boxBasis (fun _ : J ↦ ℝ))] using hWithUniv
  obtain ⟨x, hxU⟩ := hUnonempty
  obtain ⟨V, hVbasis, hxV, hVU⟩ := hBasis.exists_subset_of_mem_open hxU hUopen
  obtain ⟨W, hWopen, rfl⟩ := (mem_boxBasis V).mp hVbasis
  -- Refine each coordinate neighborhood independently by a positive compact set.
  choose K hK using fun j ↦
    exists_positiveCompacts_subset (hWopen j) ⟨x j, hxV j (Set.mem_univ j)⟩
  refine ⟨K, ?_⟩
  exact (Set.pi_mono fun j _ ↦ hK j).trans hVU

/-- Helper for Exercise 48.12: dense box-open sets admit a decreasing sequence of positive compact
boxes, starting inside any prescribed nonempty box-open set. -/
private lemma exists_antitoneCompactBoxes {J : Type*} (f : ℕ → Set (J → ℝ))
    (hfopen : ∀ n, @IsOpen (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)) (f n))
    (hfdense : ∀ n, @Dense (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)) (f n))
    {U : Set (J → ℝ)}
    (hUopen : @IsOpen (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)) U)
    (hUnonempty : U.Nonempty) :
    ∃ K : ℕ → J → PositiveCompacts ℝ,
      (∀ n j, (K (n + 1) j : Set ℝ) ⊆ K n j) ∧
      Set.pi Set.univ (fun j ↦ (K 0 j : Set ℝ)) ⊆ U ∧
      ∀ n, Set.pi Set.univ (fun j ↦ (K (n + 1) j : Set ℝ)) ⊆ f n := by
  classical
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace (fun _ : J ↦ ℝ)
  obtain ⟨K₀, hK₀U⟩ := exists_compactBox_subset_open hUopen hUnonempty
  -- At every stage, density meets the open box of coordinate interiors.
  have hnext (n : ℕ) (K : J → PositiveCompacts ℝ) :
      ∃ K' : J → PositiveCompacts ℝ,
        Set.pi Set.univ (fun j ↦ (K' j : Set ℝ)) ⊆
          f n ∩ Set.pi Set.univ (fun j ↦ interior (K j : Set ℝ)) := by
    have hinteriorOpen :
        @IsOpen (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))
          (Set.pi Set.univ (fun j ↦ interior (K j : Set ℝ))) :=
      isOpen_box _ (fun _ ↦ isOpen_interior)
    have hinteriorNonempty :
        (Set.pi Set.univ (fun j ↦ interior (K j : Set ℝ))).Nonempty :=
      Set.univ_pi_nonempty_iff.mpr (fun j ↦ (K j).interior_nonempty)
    apply exists_compactBox_subset_open ((hfopen n).inter hinteriorOpen)
    rw [Set.inter_comm]
    exact (hfdense n).inter_open_nonempty _ hinteriorOpen hinteriorNonempty
  choose Knext hKnext using hnext
  let K : ℕ → J → PositiveCompacts ℝ := Nat.rec K₀ Knext
  -- Read the recursive containment as both coordinate antitonicity and membership in each target.
  refine ⟨K, ?_, ?_, ?_⟩
  · intro n j
    have hbox : Set.pi (Set.univ : Set J) (fun i : J ↦ (K (n + 1) i).carrier) ⊆
        Set.pi (Set.univ : Set J) (fun i : J ↦ (K n i).carrier) := by
      refine (hKnext n (K n)).trans (Set.inter_subset_right.trans ?_)
      have hinteriorSubset (i : J) : interior (K n i).carrier ⊆ (K n i).carrier :=
        interior_subset
      exact Set.pi_mono fun i _ ↦ hinteriorSubset i
    rcases Set.univ_pi_subset_univ_pi_iff.mp hbox with hcoordinate | hempty
    · exact hcoordinate j
    · obtain ⟨i, hi⟩ := hempty
      exact ((K (n + 1) i).nonempty.ne_empty hi).elim
  · exact hK₀U
  · intro n
    exact (hKnext n (K n)).trans Set.inter_subset_left

/-- Helper for Exercise 48.12: the raw real function space with the box topology is Baire. -/
private theorem boxRealBaireSpace (J : Type*) :
    @BaireSpace (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)) := by
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace (fun _ : J ↦ ℝ)
  constructor
  intro f hfopen hfdense
  -- Test density of the countable intersection against an arbitrary nonempty open set.
  rw [dense_iff_inter_open]
  intro U hUopen hUnonempty
  obtain ⟨K, hKanti, hK0U, hKf⟩ :=
    exists_antitoneCompactBoxes f hfopen hfdense hUopen hUnonempty
  obtain ⟨x, hx⟩ := exists_mem_antitoneEventuallyCompact
    (fun n j ↦ (K n j : Set ℝ)) hKanti
    (fun n j ↦ (K n j).nonempty) (fun n j ↦ (K n j).isCompact.isClosed)
    (fun j ↦ Or.inl ⟨0, (K 0 j).isCompact⟩)
  -- The common coordinatewise point lies in `U` and in every dense open set.
  refine ⟨x, hK0U (fun j _ ↦ hx 0 j), ?_⟩
  exact Set.mem_iInter.mpr fun n ↦ hKf n (fun j _ ↦ hx (n + 1) j)

/-- Exercise 48.12 (1). The space `J → ℝ` is a Baire space in the box topology. -/
instance instBoxRealBaireSpace (J : Type u) :
    BaireSpace (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))) := by
  -- Transfer the raw box result across the canonical topology wrapper.
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace (fun _ : J ↦ ℝ)
  letI : BaireSpace (J → ℝ) := boxRealBaireSpace J
  let h : (J → ℝ) ≃ₜ WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)) :=
    { (WithTopology.equiv (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))).symm with
      continuous_toFun := WithTopology.continuous_toTopology _
      continuous_invFun := WithTopology.continuous_ofTopology _ }
  exact h.baireSpace

/-- Helper for Exercise 48.12: a compact cylinder has compact coordinate sets on a finite support
and unrestricted coordinates elsewhere. -/
private structure CompactCylinder (J : Type*) where
  carrier : J → Set ℝ
  compact_or_univ : ∀ j, IsCompact (carrier j) ∨ carrier j = Set.univ
  interior_nonempty : ∀ j, (interior (carrier j)).Nonempty
  interiorBox_open : IsOpen (Set.pi Set.univ (fun j ↦ interior (carrier j)))

/-- Helper for Exercise 48.12: the closed box underlying a compact cylinder. -/
private def CompactCylinder.box {J : Type*} (C : CompactCylinder J) : Set (J → ℝ) :=
  Set.pi Set.univ C.carrier

/-- Helper for Exercise 48.12: the open box of coordinate interiors of a compact cylinder. -/
private def CompactCylinder.interiorBox {J : Type*} (C : CompactCylinder J) : Set (J → ℝ) :=
  Set.pi Set.univ (fun j ↦ interior (C.carrier j))

/-- Helper for Exercise 48.12: every nonempty product-open set contains a finite-support compact
cylinder. -/
private lemma exists_compactCylinder_subset_open {J : Type*} {U : Set (J → ℝ)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty) :
    ∃ C : CompactCylinder J, C.box ⊆ U := by
  classical
  -- Refine the open set to a standard finite-support product-basis neighborhood.
  have hBasis :=
    isTopologicalBasis_pi (X := fun _ : J ↦ ℝ)
      (fun _ : J ↦ TopologicalSpace.isTopologicalBasis_opens)
  obtain ⟨x, hxU⟩ := hUnonempty
  obtain ⟨B, hBbasis, hxB, hBU⟩ := hBasis.exists_subset_of_mem_open hxU hUopen
  obtain ⟨V, F, hVopen, rfl⟩ := hBbasis
  change ∀ j, j ∈ F → IsOpen (V j) at hVopen
  choose K hK using fun j (hj : j ∈ F) ↦
    exists_positiveCompacts_subset (hVopen j hj) ⟨x j, hxB j hj⟩
  let C : J → Set ℝ := fun j ↦ if hj : j ∈ F then (K j hj : Set ℝ) else Set.univ
  have hcompact (j : J) : IsCompact (C j) ∨ C j = Set.univ := by
    by_cases hj : j ∈ F
    · left
      simpa only [C, dif_pos hj] using (K j hj).isCompact
    · right
      simp only [C, dif_neg hj]
  have hinteriorNonempty (j : J) : (interior (C j)).Nonempty := by
    by_cases hj : j ∈ F
    · simpa only [C, dif_pos hj] using (K j hj).interior_nonempty
    · simpa only [C, dif_neg hj, interior_univ] using
        (Set.univ_nonempty : (Set.univ : Set ℝ).Nonempty)
  have hinteriorOpen : IsOpen (Set.pi Set.univ (fun j ↦ interior (C j))) := by
    apply hBasis.isOpen
    refine ⟨fun j ↦ interior (C j), F, ?_, ?_⟩
    · intro j hj
      change IsOpen (interior (C j))
      exact isOpen_interior
    · ext y
      simp only [Set.mem_pi, Set.mem_univ, true_implies, C]
      constructor
      · exact fun hy j hj ↦ hy j
      · intro hy j
        by_cases hj : j ∈ F
        · simpa only [dif_pos hj] using hy j hj
        · simp only [dif_neg hj, interior_univ, Set.mem_univ]
  have hsubset : Set.pi Set.univ C ⊆ (F : Set J).pi V := by
    intro y hy j hj
    have hjF : j ∈ F := hj
    have hCj : C j = (K j hjF : Set ℝ) := by
      simp only [C, dif_pos hjF]
    have hyC : y j ∈ C j := hy j (Set.mem_univ j)
    rw [hCj] at hyC
    exact hK j hjF hyC
  -- Package the finite-support coordinate data behind the compact-cylinder interface.
  refine ⟨{
    carrier := C
    compact_or_univ := hcompact
    interior_nonempty := hinteriorNonempty
    interiorBox_open := hinteriorOpen }, ?_⟩
  exact hsubset.trans hBU

/-- Helper for Exercise 48.12: dense product-open sets admit decreasing compact cylinders whose
coordinates are eventually compact or remain unrestricted. -/
private lemma exists_antitoneCompactCylinders {J : Type*} (f : ℕ → Set (J → ℝ))
    (hfopen : ∀ n, IsOpen (f n)) (hfdense : ∀ n, Dense (f n)) {U : Set (J → ℝ)}
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty) :
    ∃ C : ℕ → J → Set ℝ,
      (∀ n j, C (n + 1) j ⊆ C n j) ∧
      (∀ n j, (C n j).Nonempty) ∧
      (∀ n j, IsClosed (C n j)) ∧
      (∀ j, (∃ N, IsCompact (C N j)) ∨ ∀ n, C n j = Set.univ) ∧
      Set.pi Set.univ (C 0) ⊆ U ∧
      ∀ n, Set.pi Set.univ (C (n + 1)) ⊆ f n := by
  classical
  obtain ⟨C₀, hC₀U⟩ := exists_compactCylinder_subset_open hUopen hUnonempty
  -- Recursively refine inside the intersection of `f n` with the current interior box.
  have hnext (n : ℕ) (C : CompactCylinder J) :
      ∃ C' : CompactCylinder J, C'.box ⊆ f n ∩ C.interiorBox := by
    apply exists_compactCylinder_subset_open
    · exact (hfopen n).inter C.interiorBox_open
    · rw [Set.inter_comm]
      exact (hfdense n).inter_open_nonempty _ C.interiorBox_open
        (Set.univ_pi_nonempty_iff.mpr C.interior_nonempty)
  choose Cnext hCnext using hnext
  let D : ℕ → CompactCylinder J := Nat.rec C₀ Cnext
  have hstep (n : ℕ) : (D (n + 1)).box ⊆ f n ∩ (D n).interiorBox := by
    simpa only [D] using hCnext n (D n)
  have hanti (n : ℕ) (j : J) : (D (n + 1)).carrier j ⊆ (D n).carrier j := by
    have hbox : (D (n + 1)).box ⊆ (D n).box := by
      refine (hstep n).trans (Set.inter_subset_right.trans ?_)
      exact Set.pi_mono fun i _ ↦ interior_subset
    rcases Set.univ_pi_subset_univ_pi_iff.mp hbox with hcoordinate | hempty
    · exact hcoordinate j
    · obtain ⟨i, hi⟩ := hempty
      exact ((D (n + 1)).interior_nonempty i).mono interior_subset |>.ne_empty hi |>.elim
  -- Expose only the coordinatewise invariants needed by the common intersection lemma.
  refine ⟨fun n ↦ (D n).carrier, hanti, ?_, ?_, ?_, hC₀U, ?_⟩
  · exact fun n j ↦ ((D n).interior_nonempty j).mono interior_subset
  · intro n j
    rcases (D n).compact_or_univ j with hcompact | h_univ
    · exact hcompact.isClosed
    · simpa only [h_univ] using isClosed_univ
  · intro j
    by_cases hcompact : ∃ N, IsCompact ((D N).carrier j)
    · exact Or.inl hcompact
    · right
      intro n
      rcases (D n).compact_or_univ j with hn | hn
      · exact (hcompact ⟨n, hn⟩).elim
      · exact hn
  · intro n
    exact (hstep n).trans Set.inter_subset_left

/-- Companion to Exercise 48.12 (2): the space `J → ℝ` is Baire in the product topology. -/
instance instRealBaireSpace (J : Type u) : BaireSpace (J → ℝ) := by
  constructor
  intro f hfopen hfdense
  -- Test density against an open set and construct the nested compact cylinders there.
  rw [dense_iff_inter_open]
  intro U hUopen hUnonempty
  obtain ⟨C, hCanti, hCnonempty, hCclosed, hCcompact, hC0U, hCf⟩ :=
    exists_antitoneCompactCylinders f hfopen hfdense hUopen hUnonempty
  obtain ⟨x, hx⟩ := exists_mem_antitoneEventuallyCompact
    C hCanti hCnonempty hCclosed hCcompact
  -- The simultaneous coordinatewise point belongs to the requested intersection.
  refine ⟨x, hC0U (fun j _ ↦ hx 0 j), ?_⟩
  exact Set.mem_iInter.mpr fun n ↦ hCf n (fun j _ ↦ hx (n + 1) j)

end Pi

namespace UniformMetric

/-- Companion to Exercise 48.12 (3): the space `J → ℝ` is Baire in the uniform topology. -/
instance instBaireSpace (J : Type u) : BaireSpace (WithTopology (J → ℝ) (topology J)) := by
  -- The canonical uniform-function model is completely pseudometrizable and hence Baire.
  exact (functionSpaceHomeomorph J).symm.baireSpace

end UniformMetric
