module

public import Mathlib.Topology.Connected.Basic

public section

open Set

universe u v

/-- Helper for Exercise 23.9: a vertical fiber and a horizontal fiber through a common
point form a connected cross. -/
lemma isConnected_verticalFiber_union_horizontalFiber {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace X] [ConnectedSpace Y]
    (x : X) (y : Y) :
    IsConnected (({x} ×ˢ (univ : Set Y)) ∪ ((univ : Set X) ×ˢ {y})) := by
  -- The two connected product fibers meet at `(x, y)`.
  refine IsConnected.union ?_ (isConnected_singleton.prod isConnected_univ)
    (isConnected_univ.prod isConnected_singleton)
  exact ⟨(x, y), ⟨⟨rfl, mem_univ y⟩, ⟨mem_univ x, rfl⟩⟩⟩

/-- Helper for Exercise 23.9: a cross whose distinguished coordinates avoid `A` and `B`
lies in the complement of `A ×ˢ B`. -/
lemma verticalHorizontalCross_subset_compl_prod {X : Type u} {Y : Type v}
    {A : Set X} {B : Set Y} {x : X} {y : Y} (hx : x ∉ A) (hy : y ∉ B) :
    ({x} ×ˢ (univ : Set Y)) ∪ ((univ : Set X) ×ˢ {y}) ⊆ (A ×ˢ B)ᶜ := by
  -- Membership in either fiber forces one coordinate to be the excluded point.
  rintro ⟨x', y'⟩ hcross hprod
  rcases hcross with hvertical | hhorizontal
  · rw [mem_prod, mem_singleton_iff] at hvertical
    exact hx (hvertical.1 ▸ hprod.1)
  · rw [mem_prod, mem_singleton_iff] at hhorizontal
    exact hy (hhorizontal.2 ▸ hprod.2)

/-- Exercise 23.9: If `A` and `B` are proper subsets of connected spaces `X` and
`Y`, then `(A ×ˢ B)ᶜ` is connected in `X × Y`. -/
theorem isConnected_compl_prod {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [ConnectedSpace X] [ConnectedSpace Y] {A : Set X} {B : Set Y}
    (hA : A ⊂ univ) (hB : B ⊂ univ) : IsConnected ((A ×ˢ B)ᶜ) := by
  -- Choose one excluded coordinate in each factor to obtain a fixed basepoint.
  obtain ⟨a, _, ha⟩ := Set.exists_of_ssubset hA
  obtain ⟨b, _, hb⟩ := Set.exists_of_ssubset hB
  constructor
  · exact ⟨(a, b), fun hab ↦ ha hab.1⟩
  -- Join each point to `(a, b)` by a connected cross contained in the complement.
  refine isPreconnected_of_forall (a, b) ?_
  rintro ⟨x, y⟩ hxy
  by_cases hx : x ∈ A
  · have hy : y ∉ B := fun hy ↦ hxy ⟨hx, hy⟩
    refine ⟨({a} ×ˢ (univ : Set Y)) ∪ ((univ : Set X) ×ˢ {y}),
      verticalHorizontalCross_subset_compl_prod ha hy, ?_, ?_, ?_⟩
    · exact Or.inl ⟨rfl, mem_univ b⟩
    · exact Or.inr ⟨mem_univ x, rfl⟩
    · exact (isConnected_verticalFiber_union_horizontalFiber a y).isPreconnected
  · refine ⟨({x} ×ˢ (univ : Set Y)) ∪ ((univ : Set X) ×ˢ {b}),
      verticalHorizontalCross_subset_compl_prod hx hb, ?_, ?_, ?_⟩
    · exact Or.inr ⟨mem_univ a, rfl⟩
    · exact Or.inl ⟨rfl, mem_univ y⟩
    · exact (isConnected_verticalFiber_union_horizontalFiber x b).isPreconnected
