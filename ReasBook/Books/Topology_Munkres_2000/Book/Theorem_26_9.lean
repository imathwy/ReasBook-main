module

public import Mathlib.Topology.Compactness.Compact
public import Topology_Munkres_2000.Book.Definition_26_5.FiniteIntersection

public section

open Set

universe u

/-- Helper for Theorem 26.9: finite nonempty intersections of an indexed family
give the finite intersection property for its range. -/
lemma rangeFiniteIntersectionProperty {X : Type u} {ι : Type v} (t : ι → Set X)
    (hfinite : ∀ s : Finset ι, (⋂ i ∈ s, t i).Nonempty) :
    (Set.range t).FiniteIntersectionProperty := by
  classical
  rw [Set.FiniteIntersectionProperty.finset_iff]
  intro s hs
  -- Choose an index representing each set in the finite subfamily.
  have hexists : ∀ A ∈ s, ∃ i, t i = A := by
    intro A hA
    exact hs A hA
  choose rep hrep using hexists
  let indices := s.attach.image fun A ↦ rep A.1 A.2
  obtain ⟨x, hx⟩ := hfinite indices
  refine ⟨x, ?_⟩
  -- The common point for the chosen indices lies in every represented set.
  simp only [mem_iInter] at hx ⊢
  intro A hA
  have hrep_indices : rep A hA ∈ indices := by
    exact Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach s ⟨A, hA⟩, rfl⟩
  rw [← hrep A hA]
  exact hx (rep A hA) hrep_indices

/-- Helper for Theorem 26.9: the closed-family intersection principle produces
a finite empty intersection from an empty indexed intersection. -/
lemma existsFiniteSubfamilyWithEmptyIntersection {X : Type u} [TopologicalSpace X]
    (hclosedFamily : ∀ 𝒞 : Set (Set X),
      (∀ C ∈ 𝒞, IsClosed C) →
        𝒞.FiniteIntersectionProperty → (⋂₀ 𝒞).Nonempty)
    {ι : Type u} (t : ι → Set X) (ht : ∀ i, IsClosed (t i))
    (hinter : (⋂ i, t i) = ∅) :
    ∃ s : Finset ι, (⋂ i ∈ s, t i) = ∅ := by
  by_contra hfinite
  push Not at hfinite
  -- If no finite intersection is empty, the range has the finite intersection property.
  have hrange : (Set.range t).FiniteIntersectionProperty :=
    rangeFiniteIntersectionProperty t hfinite
  have hrangeClosed : ∀ C ∈ Set.range t, IsClosed C := by
    intro C hC
    obtain ⟨i, rfl⟩ := hC
    exact ht i
  have hnonempty := hclosedFamily (Set.range t) hrangeClosed hrange
  -- The total intersection of the range is the indexed intersection, contradicting emptiness.
  rw [Set.sInter_range, hinter] at hnonempty
  exact Set.not_nonempty_empty hnonempty

/-- Theorem 26.9. A topological space is compact if and only if every collection
of closed sets with the finite intersection property has nonempty intersection. -/
theorem compactSpace_iff_closed_finiteIntersectionProperty
    (X : Type u) [TopologicalSpace X] :
    CompactSpace X ↔
      ∀ 𝒞 : Set (Set X),
        (∀ C ∈ 𝒞, IsClosed C) →
          𝒞.FiniteIntersectionProperty → (⋂₀ 𝒞).Nonempty := by
  constructor
  · intro hcompact 𝒞 hclosed hfinite
    letI : CompactSpace X := hcompact
    -- Compactness turns the finite intersection property into total nonemptiness.
    refine CompactSpace.nonempty_sInter hclosed ?_
    intro 𝒟 h𝒟 h𝒟finite
    have hfinset := Set.FiniteIntersectionProperty.finset_iff.mp hfinite
    have hnonempty := hfinset h𝒟finite.toFinset fun C hC ↦
      h𝒟 (h𝒟finite.mem_toFinset.mp hC)
    simpa only [← Finset.set_biInter_coe, h𝒟finite.coe_toFinset,
      sInter_eq_biInter] using hnonempty
  · intro hclosedFamily
    rw [← isCompact_univ_iff]
    -- Use the finite-closed-subfamily characterization of compactness for `Set.univ`.
    refine isCompact_of_finite_subfamily_closed ?_
    intro ι t ht hinter
    have hinter' : (⋂ i, t i) = ∅ := by
      simpa only [univ_inter] using hinter
    obtain ⟨s, hs⟩ :=
      existsFiniteSubfamilyWithEmptyIntersection hclosedFamily t ht hinter'
    refine ⟨s, ?_⟩
    simpa only [univ_inter] using hs
