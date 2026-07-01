import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {α : Type u}

namespace Set

private abbrev partOn (s : Set α) (t : Set α) : Set s :=
  ((↑) : s → α) ⁻¹' t

private abbrev subtypeParts (s : Set α) (P : Set (Set α)) : Set (Set s) :=
  partOn s '' P

private theorem injOn_subtypeParts {s : Set α} {P : Set (Set α)}
    (hsub : ∀ ⦃t⦄, t ∈ P → t ⊆ s) :
    P.InjOn (partOn s) := by
  intro t ht u hu htu
  ext x
  constructor
  · intro hx
    have hxs : x ∈ s := hsub ht hx
    have hxt : (⟨x, hxs⟩ : s) ∈ partOn s t := by simpa [partOn]
    rw [htu] at hxt
    simpa using hxt
  · intro hx
    have hxs : x ∈ s := hsub hu hx
    have hxu : (⟨x, hxs⟩ : s) ∈ partOn s u := by simpa [partOn]
    rw [← htu] at hxu
    simpa using hxu

/-- Definition 1.1.10: a partition of a set `s` is a family of subsets of `s` whose induced
family on the subtype `s` is a canonical `Setoid.IsPartition`. Equivalently, the members of `P`
are pairwise disjoint nonempty subsets whose union is exactly `s`. -/
def IsPartition (s : Set α) (P : Set (Set α)) : Prop :=
  (∀ ⦃t⦄, t ∈ P → t ⊆ s) ∧ Setoid.IsPartition (subtypeParts s P)

/-- Every part of a partition of `s` is contained in `s`. -/
theorem IsPartition.subset_ground {s : Set α} {P : Set (Set α)} (hP : IsPartition s P)
    {t : Set α} (ht : t ∈ P) : t ⊆ s :=
  hP.1 ht

/-- Distinct parts of a partition are disjoint. -/
theorem IsPartition.pairwiseDisjoint {s : Set α} {P : Set (Set α)} (hP : IsPartition s P) :
    P.PairwiseDisjoint id := by
  have hinj : P.InjOn (partOn s) := injOn_subtypeParts hP.1
  have hpair : P.PairwiseDisjoint (partOn s) := by
    have himage : (subtypeParts s P).PairwiseDisjoint id ↔ P.PairwiseDisjoint (partOn s) := by
      simpa [subtypeParts, Function.comp] using
        (show (partOn s '' P).PairwiseDisjoint id ↔ P.PairwiseDisjoint (id ∘ partOn s) from
          hinj.pairwiseDisjoint_image)
    exact himage.1 hP.2.pairwiseDisjoint
  intro t ht u hu htu
  refine Set.disjoint_left.2 fun x hxt hxu ↦ ?_
  have hxs : x ∈ s := hP.subset_ground ht hxt
  have hxt' : (⟨x, hxs⟩ : s) ∈ partOn s t := by simpa [partOn]
  have hxu' : (⟨x, hxs⟩ : s) ∈ partOn s u := by simpa [partOn]
  exact (hpair ht hu htu).le_bot ⟨hxt', hxu'⟩

/-- Every part of a partition is nonempty. -/
theorem IsPartition.nonempty {s : Set α} {P : Set (Set α)} (hP : IsPartition s P) {t : Set α}
    (ht : t ∈ P) : t.Nonempty := by
  rcases Setoid.nonempty_of_mem_partition hP.2 ⟨t, ht, rfl⟩ with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- The union of all parts of a partition is the ground set. -/
theorem IsPartition.sUnion_eq {s : Set α} {P : Set (Set α)} (hP : IsPartition s P) :
    ⋃₀ P = s := by
  ext x
  constructor
  · rintro ⟨t, ht, hxt⟩
    exact hP.subset_ground ht hxt
  · intro hx
    have hx' : (⟨x, hx⟩ : s) ∈ ⋃₀ subtypeParts s P := by
      rw [hP.2.sUnion_eq_univ]
      trivial
    rcases mem_sUnion.1 hx' with ⟨t, ht, hxt⟩
    rcases ht with ⟨u, hu, rfl⟩
    exact mem_sUnion.2 ⟨u, hu, hxt⟩

/-- A source-facing characterization of `Set.IsPartition` in terms of pairwise disjoint nonempty
subsets whose union is the ground set. -/
theorem isPartition_iff {s : Set α} {P : Set (Set α)} :
    IsPartition s P ↔
      P.PairwiseDisjoint id ∧ (∀ ⦃t⦄, t ∈ P → t.Nonempty) ∧ ⋃₀ P = s := by
  constructor
  · intro hP
    exact ⟨hP.pairwiseDisjoint, fun _ ht ↦ hP.nonempty ht, hP.sUnion_eq⟩
  · rintro ⟨hdis, hnonempty, hsUnion⟩
    refine ⟨?_, ?_⟩
    · intro t ht x hx
      rw [← hsUnion]
      exact mem_sUnion.2 ⟨t, ht, hx⟩
    · have hsub : ∀ ⦃t⦄, t ∈ P → t ⊆ s := by
        intro t ht x hx
        rw [← hsUnion]
        exact mem_sUnion.2 ⟨t, ht, hx⟩
      have hinj : P.InjOn (partOn s) := injOn_subtypeParts hsub
      have hpair : (subtypeParts s P).PairwiseDisjoint id := by
        have hpre : P.PairwiseDisjoint (partOn s) := by
          intro t ht u hu htu
          exact (hdis ht hu htu).preimage ((↑) : s → α)
        have himage : (subtypeParts s P).PairwiseDisjoint id ↔ P.PairwiseDisjoint (partOn s) := by
          simpa [subtypeParts, Function.comp] using
            (show (partOn s '' P).PairwiseDisjoint id ↔ P.PairwiseDisjoint (id ∘ partOn s) from
              hinj.pairwiseDisjoint_image)
        exact himage.2 hpre
      refine hpair.isPartition_of_exists_of_ne_empty ?_ ?_
      · intro x
        have hx : x.1 ∈ ⋃₀ P := by
          rw [hsUnion]
          exact x.2
        rcases mem_sUnion.1 hx with ⟨t, ht, hxt⟩
        exact ⟨partOn s t, ⟨t, ht, rfl⟩, by simpa [partOn] using hxt⟩
      · rintro ⟨t, ht, ht0⟩
        rcases hnonempty ht with ⟨x, hx⟩
        have hxs : x ∈ s := hsub ht hx
        have : (⟨x, hxs⟩ : s) ∈ partOn s t := by simpa [partOn]
        rw [ht0] at this
        exact this

/-- The empty family is a partition of the empty set. -/
instance : IsPartition (∅ : Set α) (∅ : Set (Set α)) := by
  rw [isPartition_iff]
  simp

end Set
