module

public import Topology_Munkres_2000.Book.Definition_23_1.Separation

public section

open Set Set.Notation

universe u

/-- Helper for Exercise 23.12: an open subset of a subtype is the trace of an
ambient open set. -/
lemma IsOpen.exists_inter_eq_of_preimage_val {X : Type u} [TopologicalSpace X]
    {s t : Set X} (h : IsOpen (s ↓∩ t)) :
    ∃ v : Set X, IsOpen v ∧ s ∩ v = s ∩ t := by
  -- First represent the subtype-open set as the image of an ambient open set.
  obtain ⟨v, hv, himage⟩ := h.image_val
  refine ⟨v, hv, ?_⟩
  -- Then identify that image with the corresponding trace on the subtype carrier.
  calc
    s ∩ v = v ∩ s := inter_comm s v
    _ = Subtype.val '' (s ↓∩ t) := himage.symm
    _ = s ∩ t := Subtype.image_preimage_coe s t

/-- Helper for Exercise 23.12: a preconnected set covered by two open sets with
empty internal overlap lies entirely in one member of the cover. -/
lemma IsPreconnected.subset_or_subset_of_inter_empty {X : Type u} [TopologicalSpace X]
    {s v w : Set X} (hs : IsPreconnected s) (hv : IsOpen v) (hw : IsOpen w)
    (hcover : s ⊆ v ∪ w) (hinter : s ∩ (v ∩ w) = ∅) :
    s ⊆ v ∨ s ⊆ w := by
  -- If either side misses `s`, the cover forces `s` into the other side.
  obtain hsv | hsv := (s ∩ v).eq_empty_or_nonempty
  · right
    intro x hx
    rcases hcover hx with hxv | hxw
    · have hxempty : x ∈ (∅ : Set X) := hsv ▸ ⟨hx, hxv⟩
      exact hxempty.elim
    · exact hxw
  obtain hsw | hsw := (s ∩ w).eq_empty_or_nonempty
  · left
    intro x hx
    rcases hcover hx with hxv | hxw
    · exact hxv
    · have hxempty : x ∈ (∅ : Set X) := hsw ▸ ⟨hx, hxw⟩
      exact hxempty.elim
  -- Otherwise preconnectedness produces a point in the forbidden overlap.
  have hnonempty := hs v w hv hw hcover hsv hsw
  rw [hinter] at hnonempty
  exact (Set.not_nonempty_empty hnonempty).elim

/-- Helper for Exercise 23.12: if the connected complement pieces separate
outside `Y`, then an open cover of `Y ∪ A` whose left side contains `Y` must
overlap whenever both sides meet `Y ∪ A`. -/
lemma Set.IsSeparation.inter_nonempty_of_compl_cover_of_subset_left
    {X : Type u} [TopologicalSpace X] [PreconnectedSpace X] {Y A B v w : Set X}
    (hsep : (Yᶜ ↓∩ A).IsSeparation (Yᶜ ↓∩ B))
    (hv : IsOpen v) (hw : IsOpen w) (hcover : Y ∪ A ⊆ v ∪ w)
    (hYv : Y ⊆ v) (hmeetv : ((Y ∪ A) ∩ v).Nonempty)
    (hmeetw : ((Y ∪ A) ∩ w).Nonempty) :
    ((Y ∪ A) ∩ (v ∩ w)).Nonempty := by
  -- Choose ambient open representatives for the two pieces outside `Y`.
  obtain ⟨VA, hVAopen, hVA⟩ := hsep.isOpen_left.exists_inter_eq_of_preimage_val
  obtain ⟨VB, hVBopen, hVB⟩ := hsep.isOpen_right.exists_inter_eq_of_preimage_val
  obtain ⟨x, hxYA, hxw⟩ := hmeetw
  by_cases hxY : x ∈ Y
  · -- A point of `Y` on the right already lies in the overlap.
    exact ⟨x, Or.inl hxY, hYv hxY, hxw⟩
  have hxA : x ∈ A := hxYA.resolve_left hxY
  have hxtrace : x ∈ Yᶜ ∩ A := ⟨hxY, hxA⟩
  rw [← hVA] at hxtrace
  have hxVA : x ∈ VA := hxtrace.2
  have hrightNonempty : (Set.univ ∩ (w ∩ VA)).Nonempty :=
    ⟨x, Set.mem_univ x, hxw, hxVA⟩
  have hleftNonempty : (Set.univ ∩ (v ∪ VB)).Nonempty := by
    obtain ⟨y, -, hyv⟩ := hmeetv
    exact ⟨y, Set.mem_univ y, Or.inl hyv⟩
  have hglobalCover : Set.univ ⊆ (v ∪ VB) ∪ (w ∩ VA) := by
    -- Points of `Y` lie on the left; outside `Y`, use the given separation.
    intro y _
    by_cases hyY : y ∈ Y
    · exact Or.inl (Or.inl (hYv hyY))
    · have hycomp : y ∈ Yᶜ := hyY
      have hysep : (⟨y, hycomp⟩ : {x : X // x ∈ Yᶜ}) ∈ (Yᶜ ↓∩ A) ∪ (Yᶜ ↓∩ B) := by
        rw [hsep.union_eq_univ]
        exact Set.mem_univ _
      rcases hysep with hyA | hyB
      · rcases hcover (Or.inr hyA) with hyv | hyw
        · exact Or.inl (Or.inl hyv)
        · have hytrace : y ∈ Yᶜ ∩ A := ⟨hycomp, hyA⟩
          rw [← hVA] at hytrace
          have hyVA : y ∈ VA := hytrace.2
          exact Or.inr ⟨hyw, hyVA⟩
      · have hytrace : y ∈ Yᶜ ∩ B := ⟨hycomp, hyB⟩
        rw [← hVB] at hytrace
        have hyVB : y ∈ VB := hytrace.2
        exact Or.inl (Or.inr hyVB)
  have hglobalInter := isPreconnected_univ (v ∪ VB) (w ∩ VA)
    (hv.union hVBopen) (hw.inter hVAopen) hglobalCover hleftNonempty hrightNonempty
  obtain ⟨z, -, hzleft, hzw, hzVA⟩ := hglobalInter
  rcases hzleft with hzv | hzVB
  · -- A left-cover point is in `Y ∪ A`, using the trace equation outside `Y`.
    by_cases hzY : z ∈ Y
    · exact ⟨z, Or.inl hzY, hzv, hzw⟩
    · have hztrace : z ∈ Yᶜ ∩ VA := ⟨hzY, hzVA⟩
      rw [hVA] at hztrace
      have hzA : z ∈ A := hztrace.2
      exact ⟨z, Or.inr hzA, hzv, hzw⟩
  · by_cases hzY : z ∈ Y
    · -- If the added complement piece meets `Y`, containment of `Y` supplies `v`.
      exact ⟨z, Or.inl hzY, hYv hzY, hzw⟩
    · -- Outside `Y`, simultaneous membership in both traces contradicts separation.
      have hzcomp : z ∈ Yᶜ := hzY
      have hzAtrace : z ∈ Yᶜ ∩ A := by
        rw [← hVA]
        exact ⟨hzcomp, hzVA⟩
      have hzBtrace : z ∈ Yᶜ ∩ B := by
        rw [← hVB]
        exact ⟨hzcomp, hzVB⟩
      have hzA : (⟨z, hzcomp⟩ : {x : X // x ∈ Yᶜ}) ∈ Yᶜ ↓∩ A := hzAtrace.2
      have hzB : (⟨z, hzcomp⟩ : {x : X // x ∈ Yᶜ}) ∈ Yᶜ ↓∩ B := hzBtrace.2
      exact (Set.disjoint_left.mp hsep.disjoint hzA hzB).elim

/-- Exercise 23.12: the preconnectedness conclusion for the left side of the separation. -/
theorem IsPreconnected.union_left_of_compl_separation {X : Type u} [TopologicalSpace X]
    [PreconnectedSpace X] {Y A B : Set X} (hY : IsPreconnected Y)
    (hsep : (Yᶜ ↓∩ A).IsSeparation (Yᶜ ↓∩ B)) :
    IsPreconnected (Y ∪ A) := by
  -- Test an arbitrary open cover of `Y ∪ A` meeting both sides.
  intro v w hv hw hcover hmeetv hmeetw
  by_contra hinter
  rw [Set.not_nonempty_iff_eq_empty] at hinter
  have hYcover : Y ⊆ v ∪ w := (Set.subset_union_left.trans hcover)
  have hYinter : Y ∩ (v ∩ w) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hxY, hxv, hxw⟩
    have hx : x ∈ (Y ∪ A) ∩ (v ∩ w) := ⟨Or.inl hxY, hxv, hxw⟩
    rw [hinter] at hx
    exact hx
  -- Connectedness places `Y` wholly on one side of the cover.
  rcases hY.subset_or_subset_of_inter_empty hv hw hYcover hYinter with hYv | hYw
  · have hnonempty := hsep.inter_nonempty_of_compl_cover_of_subset_left
      hv hw hcover hYv hmeetv hmeetw
    rw [hinter] at hnonempty
    exact (Set.not_nonempty_empty hnonempty).elim
  · -- Exchange the cover sides and apply the same augmented-cover argument.
    have hnonempty := hsep.inter_nonempty_of_compl_cover_of_subset_left
      hw hv (by simpa only [union_comm] using hcover) hYw hmeetw hmeetv
    obtain ⟨x, hxYA, hxw, hxv⟩ := hnonempty
    have hx : x ∈ (Y ∪ A) ∩ (v ∩ w) := ⟨hxYA, hxv, hxw⟩
    rw [hinter] at hx
    exact hx

/-- The preconnectedness part of Exercise 23.12 for the right side of the separation. -/
theorem IsPreconnected.union_right_of_compl_separation {X : Type u} [TopologicalSpace X]
    [PreconnectedSpace X] {Y A B : Set X} (hY : IsPreconnected Y)
    (hsep : (Yᶜ ↓∩ A).IsSeparation (Yᶜ ↓∩ B)) :
    IsPreconnected (Y ∪ B) := by
  exact hY.union_left_of_compl_separation hsep.symm

/-- The connectedness companion for Exercise 23.12 on the left side of the separation. -/
theorem IsPreconnected.isConnected_union_left_of_compl_separation
    {X : Type u} [TopologicalSpace X] [PreconnectedSpace X] {Y A B : Set X}
    (hY : IsPreconnected Y) (hsep : (Yᶜ ↓∩ A).IsSeparation (Yᶜ ↓∩ B)) :
    IsConnected (Y ∪ A) := by
  refine ⟨?_, hY.union_left_of_compl_separation hsep⟩
  obtain ⟨x, hx⟩ := hsep.left_nonempty
  exact ⟨x, Or.inr hx⟩

/-- Exercise 23.12 (2): If `X` and `Y` are connected and `A` and `B` form a
separation of `Yᶜ`, then `Y ∪ B` is connected. -/
theorem IsPreconnected.isConnected_union_right_of_compl_separation
    {X : Type u} [TopologicalSpace X] [PreconnectedSpace X] {Y A B : Set X}
    (hY : IsPreconnected Y) (hsep : (Yᶜ ↓∩ A).IsSeparation (Yᶜ ↓∩ B)) :
    IsConnected (Y ∪ B) := by
  exact hY.isConnected_union_left_of_compl_separation hsep.symm
