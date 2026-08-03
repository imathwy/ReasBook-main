module

public import Mathlib.Topology.Connected.Basic

public section

/-- Exercise 23.3: A connected subset together with an arbitrary family of
connected subsets that each meet it has connected union. -/
theorem isConnected_union_iUnion {X : Type u} [TopologicalSpace X] {ι : Type v}
    (A : Set X) (B : ι → Set X) (hA : IsConnected A)
    (hB : ∀ i, IsConnected (B i)) (h_inter : ∀ i, (A ∩ B i).Nonempty) :
    IsConnected (A ∪ ⋃ i, B i) := by
  let coreFamily : Option ι → Set X := fun o ↦ o.elim A (fun i ↦ A ∪ B i)
  -- Each enlarged family member is connected because it meets the connected core `A`.
  have h_coreFamily_connected : ∀ o, IsConnected (coreFamily o) := by
    intro o
    cases o with
    | none =>
        exact hA
    | some i =>
        exact hA.union (h_inter i) (hB i)
  -- A point of `A` is a common point of every member of the enlarged family.
  obtain ⟨x, hx⟩ := hA.nonempty
  have h_coreFamily_iInter : (⋂ o, coreFamily o).Nonempty := by
    refine ⟨x, Set.mem_iInter.2 ?_⟩
    intro o
    cases o with
    | none =>
        exact hx
    | some i =>
        exact Set.mem_union_left (B i) hx
  -- The common point lets us take the full indexed union without losing preconnectedness.
  have h_coreFamily_preconnected : IsPreconnected (⋃ o, coreFamily o) :=
    isPreconnected_iUnion h_coreFamily_iInter fun o ↦ (h_coreFamily_connected o).isPreconnected
  -- The auxiliary union normalizes to the union stated in the exercise.
  have h_coreFamily_iUnion : (⋃ o, coreFamily o) = A ∪ ⋃ i, B i := by
    rw [Set.iUnion_option]
    simp only [coreFamily, Option.elim_none, Option.elim_some]
    ext y
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hy | ⟨i, hy | hy⟩)
      · exact Or.inl hy
      · exact Or.inl hy
      · exact Or.inr ⟨i, hy⟩
    · rintro (hy | ⟨i, hy⟩)
      · exact Or.inl hy
      · exact Or.inr ⟨i, Or.inr hy⟩
  -- Transport both nonemptiness and preconnectedness across this normalization.
  rw [← h_coreFamily_iUnion]
  exact ⟨⟨x, Set.mem_iUnion.2 ⟨none, hx⟩⟩, h_coreFamily_preconnected⟩
