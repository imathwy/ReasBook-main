module

public import Mathlib.Topology.Connected.Basic

public section

/-- A preconnected set meeting a set and its complement also meets its frontier. -/
theorem IsPreconnected.inter_frontier_nonempty {X : Type u} [TopologicalSpace X]
    {A C : Set X} (hC : IsPreconnected C) (hCA : (C ∩ A).Nonempty)
    (hCAc : (C ∩ Aᶜ).Nonempty) : (C ∩ frontier A).Nonempty := by
  -- If `C` avoids the frontier, it lies in the two disjoint open interiors.
  by_contra hfrontier
  rw [Set.not_nonempty_iff_eq_empty] at hfrontier
  have hdisjoint : Disjoint C (frontier A) :=
    Set.disjoint_iff_inter_eq_empty.mpr hfrontier
  have hcover : C ⊆ interior A ∪ interior Aᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact hdisjoint.subset_compl_right
  have hinteriors : Disjoint (interior A) (interior Aᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  -- Preconnectedness forces `C` into one interior, contradicting the opposite witness.
  obtain hCin | hCin := hC.subset_or_subset isOpen_interior isOpen_interior hinteriors hcover
  · obtain ⟨x, hxC, hxAc⟩ := hCAc
    exact hxAc (interior_subset (hCin hxC))
  · obtain ⟨x, hxC, hxA⟩ := hCA
    exact (interior_subset (hCin hxC)) hxA

/-- Exercise 23.6: A connected subset that meets both a set and its complement
also meets the frontier of the set. -/
theorem IsConnected.inter_frontier_nonempty {X : Type u} [TopologicalSpace X]
    {A C : Set X} (hC : IsConnected C) (hCA : (C ∩ A).Nonempty)
    (hCAc : (C ∩ Aᶜ).Nonempty) : (C ∩ frontier A).Nonempty :=
  hC.isPreconnected.inter_frontier_nonempty hCA hCAc
