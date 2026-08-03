module

public import Topology_Munkres_2000.Book.Definition_50_8.Partition
public import Mathlib.Topology.ShrinkingLemma

public section

open Set TopologicalSpace

universe u v

/-- Helper for Definition 50.8: preservation of nonempty finite intersections transfers an
indexwise multiplicity bound from a source family to the range of a target family. -/
lemma hasOrderLE_of_finiteIntersection_preserving
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {q : ℕ}
    (K E : ι → Set X)
    (hKorder : ∀ x : X, Set.encard {i | x ∈ K i} ≤ q)
    (hnerve : ∀ s : Finset ι,
      (⋂ i ∈ s, closure (E i)).Nonempty → (⋂ i ∈ s, K i).Nonempty) :
    (Set.range E).HasOrderLE q := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- At a point of the target family, collect the finitely many incident indices.
  rw [Set.hasOrderLE_iff]
  intro x
  let s : Finset ι := Finset.univ.filter fun i ↦ x ∈ E i
  have hxclosures : (⋂ i ∈ s, closure (E i)).Nonempty := by
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro i hxi
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hxi
    exact subset_closure hxi
  obtain ⟨y, hy⟩ := hnerve s hxclosures
  have hyK : ∀ i ∈ s, y ∈ K i := by
    simpa only [Set.mem_iInter] using hy
  -- Distinct incident target sets are images of incident indices, all of which meet at `y` in
  -- the source family.
  calc
    Set.encard {U ∈ Set.range E | x ∈ U}
        ≤ Set.encard (E '' {i | x ∈ E i}) := by
          apply Set.encard_le_encard
          rintro U ⟨⟨i, rfl⟩, hxi⟩
          exact ⟨i, hxi, rfl⟩
    _ ≤ Set.encard {i | x ∈ E i} := Set.encard_image_le E _
    _ ≤ Set.encard {i | y ∈ K i} := by
      apply Set.encard_le_encard
      intro i hxi
      apply hyK i
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxi
    _ ≤ q := hKorder y

/-- Helper for Definition 50.8: a finite closed family with empty intersection has open
neighborhoods whose closures still have empty intersection. -/
lemma existsOpen_superset_closure_biInter_eq_empty
    {X : Type u} [TopologicalSpace X] [NormalSpace X] {ι : Type v}
    (s : Finset ι) (K : ι → Set X) (hKclosed : ∀ i ∈ s, IsClosed (K i))
    (hKempty : ⋂ i ∈ s, K i = ∅) :
    ∃ U : ι → Set X,
      (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧ ⋂ i ∈ s, closure (U i) = ∅ := by
  classical
  -- Apply the shrinking lemma to the complementary open cover indexed by `s`.
  let A : s → Set X := fun i ↦ (K i.1)ᶜ
  have hAopen : ∀ i, IsOpen (A i) := fun i ↦ (hKclosed i.1 i.2).isOpen_compl
  have hAcover : ⋃ i, A i = Set.univ := by
    rw [eq_univ_iff_forall]
    intro x
    by_contra hx
    have hxK : x ∈ ⋂ i ∈ s, K i := by
      simp only [Set.mem_iInter]
      intro i hi
      by_contra hxi
      exact hx <| Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    have hxempty : x ∈ (∅ : Set X) := hKempty ▸ hxK
    exact hxempty
  have hAfin : ∀ x, {i | x ∈ A i}.Finite := fun _ ↦ Set.toFinite _
  obtain ⟨V, hVcover, hVopen, hVclosure⟩ :=
    exists_iUnion_eq_closure_subset hAopen hAfin hAcover
  let U : ι → Set X := fun i ↦ if hi : i ∈ s then (closure (V ⟨i, hi⟩))ᶜ else Set.univ
  refine ⟨U, ?_, ?_, ?_⟩
  · -- Complements of the selected closed shrinkings are open; unused indices are unrestricted.
    intro i
    simp only [U]
    split_ifs
    · exact isClosed_closure.isOpen_compl
    · exact isOpen_univ
  · -- The shrinking inclusion for the complementary cover puts each closed source set inside
    -- its selected neighborhood.
    intro i x hxi
    simp only [U]
    split_ifs with hi
    · exact fun hxclosure ↦ hVclosure ⟨i, hi⟩ hxclosure hxi
    · exact Set.mem_univ x
  · -- A point in every selected closure would avoid every member of the shrinking cover.
    apply Set.Subset.antisymm
    · intro x hx
      exfalso
      have hxclosures : ∀ i ∈ s, x ∈ closure (U i) := by
        simpa only [Set.mem_iInter] using hx
      have hxnotV : ∀ i : s, x ∉ V i := by
        intro i hxi
        have hxclosure : x ∈ closure (U i.1) := hxclosures i.1 i.2
        have hU : U i.1 = (closure (V i))ᶜ := by simp [U, i.2]
        have hxnotInterior : x ∉ interior (closure (V i)) := by
          rw [hU, closure_compl] at hxclosure
          exact hxclosure
        exact hxnotInterior (hVopen i |>.subset_interior_closure hxi)
      have hxunion : x ∈ ⋃ i, V i := hVcover.symm ▸ Set.mem_univ x
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxunion
      exact hxnotV i hxi
    · exact Set.empty_subset _

/-- Helper for Definition 50.8: a finite closed family in a normal space can be swollen inside
prescribed open parents while preserving every empty finite intersection. -/
lemma existsOpenSwelling_preservingFiniteIntersections
    {X : Type u} [TopologicalSpace X] [NormalSpace X] {ι : Type v} [Finite ι]
    (K A : ι → Set X) (hKclosed : ∀ i, IsClosed (K i)) (hAopen : ∀ i, IsOpen (A i))
    (hKA : ∀ i, K i ⊆ A i) :
    ∃ E : ι → Set X,
      (∀ i, IsOpen (E i)) ∧ (∀ i, K i ⊆ E i) ∧ (∀ i, closure (E i) ⊆ A i) ∧
        ∀ s : Finset ι,
          (⋂ i ∈ s, K i = ∅) → ⋂ i ∈ s, closure (E i) = ∅ := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- First choose parent-controlled neighborhoods; later intersections will only shrink them.
  have hparent (i : ι) :
      ∃ W : Set X, IsOpen W ∧ K i ⊆ W ∧ closure W ⊆ A i :=
    normal_exists_closure_subset (hKclosed i) (hAopen i) (hKA i)
  choose W hWopen hKW hWclosure using hparent
  let bad : Finset (Finset ι) :=
    Finset.univ.powerset.filter fun s ↦ ⋂ i ∈ s, K i = ∅
  have hforbidden (s : bad) :
      ∃ U : ι → Set X,
        (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
          ⋂ i ∈ s.1, closure (U i) = ∅ := by
    apply existsOpen_superset_closure_biInter_eq_empty s.1 K
    · intro i _
      exact hKclosed i
    · exact (Finset.mem_filter.mp s.2).2
  choose U hUopen hKU hUempty using hforbidden
  let E : ι → Set X := fun i ↦ W i ∩ ⋂ s : bad, U s i
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · -- Only finitely many forbidden intersections occur, so the accumulated intersection is open.
    intro i
    exact (hWopen i).inter <| isOpen_iInter_of_finite fun s ↦ hUopen s i
  · -- Every constraint neighborhood contains its source closed set.
    intro i x hxi
    refine ⟨hKW i hxi, ?_⟩
    exact Set.mem_iInter.mpr fun s ↦ hKU s i hxi
  · -- The initial parent-controlled neighborhood supplies the ambient containment.
    intro i
    exact (closure_mono Set.inter_subset_left).trans (hWclosure i)
  · -- For a forbidden subfamily, use its dedicated simultaneous neighborhood constraint.
    intro s hs
    have hsbad : s ∈ bad := by
      simp only [bad, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ s), hs⟩
    let t : bad := ⟨s, hsbad⟩
    apply Set.Subset.antisymm
    · intro x hx
      have hxE : ∀ i ∈ s, x ∈ closure (E i) := by
        simpa only [Set.mem_iInter] using hx
      have hxU : x ∈ ⋂ i ∈ s, closure (U t i) := by
        simp only [Set.mem_iInter]
        intro i hi
        apply closure_mono ?_ (hxE i hi)
        intro y hy
        exact Set.mem_iInter.mp hy.2 t
      exact hUempty t ▸ hxU
    · exact Set.empty_subset _

/-- Helper for Definition 50.8: an order-bounded finite cover of a closed subtype, together with
a closure-controlled shrinking, swells to an ambient open family with the same order bound. -/
lemma existsAmbientOpenSwelling_of_closedSubtypeCover
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
    {L : Set X} (hL : IsClosed L) {ι : Type v} [Finite ι] {q : ℕ}
    (B C : ι → Opens L) (hCcover : IsOpenCover C)
    (hBorder : (Set.range fun i ↦ (B i : Set L)).HasOrderLE q)
    (hBinjective : Function.Injective fun i ↦ (B i : Set L))
    (hCclosure : ∀ i, closure (C i : Set L) ⊆ B i)
    (A : ι → Set X) (hAopen : ∀ i, IsOpen (A i))
    (hBA : ∀ i, Subtype.val '' (B i : Set L) ⊆ A i) :
    ∃ E : ι → Set X,
      (∀ i, IsOpen (E i)) ∧ L ⊆ ⋃ i, E i ∧ (∀ i, closure (E i) ⊆ A i) ∧
        (Set.range E).HasOrderLE q := by
  classical
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL.isCompact
  let K : ι → Set X := fun i ↦ Subtype.val '' closure (C i : Set L)
  have hKclosed : ∀ i, IsClosed (K i) := by
    intro i
    exact (isClosed_closure.isCompact.image continuous_subtype_val).isClosed
  have hKA : ∀ i, K i ⊆ A i := by
    intro i
    exact Set.image_mono (hCclosure i) |>.trans (hBA i)
  obtain ⟨E, hEopen, hKE, hEclosure, hnerveEmpty⟩ :=
    existsOpenSwelling_preservingFiniteIntersections K A hKclosed hAopen hKA
  have hKorder : ∀ x : X, Set.encard {i | x ∈ K i} ≤ q := by
    intro x
    by_cases hx : {i | x ∈ K i}.Nonempty
    · obtain ⟨i, zi, hzi, rfl⟩ := hx
      calc
        Set.encard {j | (zi : X) ∈ K j}
            = Set.encard ((fun j ↦ (B j : Set L)) '' {j | (zi : X) ∈ K j}) :=
              (hBinjective.encard_image _).symm
        _ ≤ Set.encard {U ∈ Set.range (fun j ↦ (B j : Set L)) | zi ∈ U} := by
          apply Set.encard_le_encard
          rintro U ⟨j, hj, rfl⟩
          obtain ⟨zj, hzj, hzjval⟩ := hj
          have hzjeq : zj = zi := Subtype.ext hzjval
          exact ⟨⟨j, rfl⟩, hCclosure j (hzjeq ▸ hzj)⟩
        _ ≤ q := Set.hasOrderLE_iff.mp hBorder zi
    · rw [Set.not_nonempty_iff_eq_empty.mp hx, Set.encard_empty]
      exact bot_le
  have hEorder : (Set.range E).HasOrderLE q := by
    apply hasOrderLE_of_finiteIntersection_preserving K E hKorder
    intro s hs
    by_contra hKempty
    have hKempty' : ⋂ i ∈ s, K i = ∅ := Set.not_nonempty_iff_eq_empty.mp hKempty
    obtain ⟨x, hx⟩ := hs
    have hxempty : x ∈ (∅ : Set X) := hnerveEmpty s hKempty' ▸ hx
    exact hxempty
  refine ⟨E, hEopen, ?_, hEclosure, hEorder⟩
  -- The closed seeds contain the original shrinking, so their swellings cover the closed locus.
  intro x hxL
  let z : L := ⟨x, hxL⟩
  have hzcover : z ∈ ⋃ i, (C i : Set L) :=
    hCcover.iSup_set_eq_univ.symm ▸ Set.mem_univ z
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzcover
  exact Set.mem_iUnion.mpr ⟨i, hKE i ⟨z, subset_closure hzi, rfl⟩⟩

end
