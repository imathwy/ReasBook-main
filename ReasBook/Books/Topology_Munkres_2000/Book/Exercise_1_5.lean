module

public import Mathlib.Order.SetNotation

public section

/- Exercise 1.5 (1): Membership in `⋃₀ 𝒜` is equivalent to membership in at
least one member of `𝒜`. -/
#check Set.mem_sUnion

/-- Exercise 1.5 (2): Membership in the union need not imply membership in
every member of a nonempty collection. -/
theorem mem_sUnion_not_forall_counterexample :
    ¬(true ∈ ⋃₀ ({{true}, {false}} : Set (Set Bool)) →
      ∀ A ∈ ({{true}, {false}} : Set (Set Bool)), true ∈ A) := by
  intro h
  have hUnion : true ∈ ⋃₀ ({{true}, {false}} : Set (Set Bool)) :=
    Set.mem_sUnion.mpr ⟨{true}, Or.inl rfl, rfl⟩
  have hFalse := h hUnion {false} (Or.inr rfl)
  exact Bool.noConfusion hFalse

/-- Exercise 1.5 (3): If an element belongs to every member of a nonempty
collection, then it belongs to the union of that collection. -/
theorem mem_sUnion_of_forall_mem {α : Type u} {𝒜 : Set (Set α)}
    (h𝒜 : 𝒜.Nonempty) {x : α} (hx : ∀ A ∈ 𝒜, x ∈ A) : x ∈ ⋃₀ 𝒜 := by
  obtain ⟨A, hA⟩ := h𝒜
  exact Set.mem_sUnion.mpr ⟨A, hA, hx A hA⟩

/-- Exercise 1.5 (4): Membership in the intersection of a nonempty collection
implies membership in at least one member of the collection. -/
theorem exists_member_of_mem_sInter {α : Type u} {𝒜 : Set (Set α)}
    (h𝒜 : 𝒜.Nonempty) {x : α} (hx : x ∈ ⋂₀ 𝒜) : ∃ A ∈ 𝒜, x ∈ A := by
  obtain ⟨A, hA⟩ := h𝒜
  exact ⟨A, hA, Set.mem_sInter.mp hx A hA⟩

/-- Exercise 1.5 (5): Membership in one member of a nonempty collection need
not imply membership in the intersection of the collection. -/
theorem exists_member_not_sInter_counterexample :
    ¬((∃ A ∈ ({{true}, {false}} : Set (Set Bool)), true ∈ A) →
      true ∈ ⋂₀ ({{true}, {false}} : Set (Set Bool))) := by
  intro h
  have hMember : ∃ A ∈ ({{true}, {false}} : Set (Set Bool)), true ∈ A :=
    ⟨{true}, Or.inl rfl, rfl⟩
  have hFalse := Set.mem_sInter.mp (h hMember) {false} (Or.inr rfl)
  exact Bool.noConfusion hFalse

/- Exercise 1.5 (6): Membership in `⋂₀ 𝒜` is equivalent to membership in
every member of `𝒜`. -/
#check Set.mem_sInter
