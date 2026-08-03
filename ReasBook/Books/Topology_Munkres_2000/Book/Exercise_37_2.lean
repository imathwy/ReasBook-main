module

public import Topology_Munkres_2000.Book.Exercise_37_2.CountableIntersection
import all Topology_Munkres_2000.Book.Exercise_37_2.CountableIntersection
public import Mathlib.Topology.Compactness.Lindelof

public section

open Set Topology

universe u v

namespace Set.CountableIntersectionProperty

/-- Helper for Exercise 37.2: a range has the countable intersection property
exactly when every countable subfamily of indices has nonempty intersection. -/
theorem range_iff {X : Type u} {ι : Type v} (A : ι → Set X) :
    (Set.range A).CountableIntersectionProperty ↔
      ∀ s : Set ι, s.Countable → (⋂ i ∈ s, A i).Nonempty := by
  classical
  constructor
  · intro hA s hs
    -- The image of the countable index set is a countable subcollection of the range.
    have hImage : (A '' s).Countable := hs.image A
    have hImageRange : A '' s ⊆ Set.range A := Set.image_subset_range A s
    simpa only [Set.sInter_image] using hA hImageRange hImage
  · intro hIndexed 𝒞 h𝒞 hCountable
    -- Choose one index representing each member of the countable subcollection.
    letI : Countable 𝒞 := hCountable.to_subtype
    choose index hIndex using fun C : 𝒞 ↦ h𝒞 C.property
    obtain ⟨x, hx⟩ := hIndexed (Set.range index) (Set.countable_range index)
    refine ⟨x, Set.mem_sInter.mpr ?_⟩
    intro C hC
    -- Membership in the indexed intersection transfers along the chosen representative.
    have hxIndex : x ∈ A (index ⟨C, hC⟩) :=
      Set.mem_iInter₂.mp hx (index ⟨C, hC⟩) ⟨⟨C, hC⟩, rfl⟩
    simpa only [hIndex ⟨C, hC⟩] using hxIndex

end Set.CountableIntersectionProperty

/-- Helper for Exercise 37.2: if a Lindelöf set meets every countable
subintersection of a family, then it meets the intersection of all closures. -/
theorem IsLindelof.inter_iInter_closure_nonempty_of_countable
    {X : Type u} [TopologicalSpace X] {s : Set X} {ι : Type v}
    (hs : IsLindelof s) (A : ι → Set X)
    (hA : ∀ t : Set ι, t.Countable → (s ∩ ⋂ i ∈ t, A i).Nonempty) :
    (s ∩ ⋂ i, closure (A i)).Nonempty := by
  classical
  by_contra hClosures
  rw [Set.not_nonempty_iff_eq_empty] at hClosures
  -- Lindelöfness reduces the empty closed intersection to a countable subfamily.
  obtain ⟨t, ht, hEmpty⟩ := hs.elim_countable_subfamily_closed
    (fun i ↦ closure (A i)) (fun _ ↦ isClosed_closure) hClosures
  obtain ⟨x, hx⟩ := hA t ht
  -- The same point lies in every selected closure, contradicting emptiness.
  have hxClosures : x ∈ s ∩ ⋂ i ∈ t, closure (A i) := by
    constructor
    · exact hx.1
    · refine Set.mem_iInter₂.mpr ?_
      intro i hi
      exact subset_closure (Set.mem_iInter₂.mp hx.2 i hi)
  exact (Set.mem_empty_iff_false x).mp (hEmpty ▸ hxClosures)

/-- Exercise 37.2. A topological space is Lindelöf if and only if the closures
of every collection with the countable intersection property have nonempty
intersection. -/
theorem lindelofSpace_iff_iInter_closure_nonempty
    {X : Type u} [TopologicalSpace X] :
    LindelofSpace X ↔
      ∀ 𝒜 : Set (Set X), 𝒜.CountableIntersectionProperty →
        (⋂ A ∈ 𝒜, closure A).Nonempty := by
  constructor
  · intro hX 𝒜 h𝒜
    -- Regard the collection as a family indexed by its subtype.
    have hRange :
        (Set.range ((↑) : 𝒜 → Set X)).CountableIntersectionProperty := by
      simpa only [Subtype.range_coe] using h𝒜
    have hIndexed := Set.CountableIntersectionProperty.range_iff
      ((↑) : 𝒜 → Set X) |>.mp hRange
    -- Apply the Lindelöf closed-family argument to the ambient set `univ`.
    have hClosedIntersection :
        ((Set.univ : Set X) ∩ ⋂ A : 𝒜, closure (A : Set X)).Nonempty := by
      refine IsLindelof.inter_iInter_closure_nonempty_of_countable
        (isLindelof_univ_iff.mpr hX) ((↑) : 𝒜 → Set X) ?_
      intro t ht
      simpa only [Set.univ_inter] using hIndexed t ht
    simpa only [Set.univ_inter, Set.biInter_eq_iInter] using hClosedIntersection
  · intro hIntersection
    -- Use the countable closed-subfamily criterion for Lindelöf spaces.
    refine lindelofSpace_of_countable_subfamily_closed ?_
    intro ι A hClosed hEmpty
    by_contra hCountableSubfamily
    have hIndexed : ∀ t : Set ι, t.Countable → (⋂ i ∈ t, A i).Nonempty := by
      intro t ht
      rw [Set.nonempty_iff_ne_empty]
      intro htEmpty
      exact hCountableSubfamily ⟨t, ht, htEmpty⟩
    have hRange : (Set.range A).CountableIntersectionProperty :=
      Set.CountableIntersectionProperty.range_iff A |>.mpr hIndexed
    obtain ⟨x, hx⟩ := hIntersection (Set.range A) hRange
    -- Closedness removes the closures, recovering a point in the assumed empty intersection.
    have hxOriginal : x ∈ ⋂ i, A i := by
      rw [Set.biInter_range] at hx
      refine Set.mem_iInter.mpr ?_
      intro i
      rw [← (hClosed i).closure_eq]
      exact Set.mem_iInter.mp hx i
    exact (Set.mem_empty_iff_false x).mp (hEmpty ▸ hxOriginal)

/-- In a Lindelöf space, the closures of a family with the countable intersection
property have nonempty intersection. -/
theorem LindelofSpace.iInter_closure_nonempty {X : Type u} [TopologicalSpace X]
    [LindelofSpace X] (𝒜 : Set (Set X)) (h𝒜 : 𝒜.CountableIntersectionProperty) :
    (⋂ A ∈ 𝒜, closure A).Nonempty :=
  lindelofSpace_iff_iInter_closure_nonempty.mp inferInstance 𝒜 h𝒜

/-- The closure-intersection characterization of Lindelöf spaces, as a constructor
for the corresponding typeclass instance. -/
theorem LindelofSpace.of_iInter_closure_nonempty {X : Type u} [TopologicalSpace X]
    (h : ∀ 𝒜 : Set (Set X), 𝒜.CountableIntersectionProperty →
      (⋂ A ∈ 𝒜, closure A).Nonempty) :
    LindelofSpace X :=
  lindelofSpace_iff_iInter_closure_nonempty.mpr h
