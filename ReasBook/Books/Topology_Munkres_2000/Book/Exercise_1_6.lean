module

public import Mathlib.Order.SetNotation

public section

universe u

/-- Exercise 1.6 (1): If `x` belongs to no member of `𝒜`, then it does not
belong to `⋃₀ 𝒜`. This is the contrapositive of Exercise 1.5 (1). -/
theorem not_mem_sUnion_of_forall_not_mem {α : Type u} {𝒜 : Set (Set α)} {x : α}
    (hx : ∀ A ∈ 𝒜, x ∉ A) : x ∉ ⋃₀ 𝒜 := by
  intro hxUnion
  obtain ⟨A, hA, hxA⟩ := Set.mem_sUnion.mp hxUnion
  exact hx A hA hxA

/-- Exercise 1.6 (2): The contrapositive of Exercise 1.5 (2) is false: an
element may be absent from one member of a collection while belonging to its union. -/
theorem exists_not_mem_imp_not_mem_sUnion_counterexample :
    ¬((∃ A ∈ ({{true}, {false}} : Set (Set Bool)), true ∉ A) →
      true ∉ ⋃₀ ({{true}, {false}} : Set (Set Bool))) := by
  intro h
  have hMissing : ∃ A ∈ ({{true}, {false}} : Set (Set Bool)), true ∉ A :=
    ⟨{false}, Or.inr rfl, fun hEq ↦ Bool.noConfusion hEq⟩
  have hUnion : true ∈ ⋃₀ ({{true}, {false}} : Set (Set Bool)) :=
    Set.mem_sUnion.mpr ⟨{true}, Or.inl rfl, rfl⟩
  exact h hMissing hUnion

/-- Exercise 1.6 (3): If `x` belongs to no member of a nonempty collection
`𝒜`, then it does not belong to `⋂₀ 𝒜`. This is the contrapositive of Exercise 1.5 (3). -/
theorem not_mem_sInter_of_forall_not_mem {α : Type u} {𝒜 : Set (Set α)}
    (h𝒜 : 𝒜.Nonempty) {x : α} (hx : ∀ A ∈ 𝒜, x ∉ A) : x ∉ ⋂₀ 𝒜 := by
  obtain ⟨A, hA⟩ := h𝒜
  exact fun hxInter ↦ hx A hA (Set.mem_sInter.mp hxInter A hA)

/-- Exercise 1.6 (4): If `x` is absent from some member of `𝒜`, then it does
not belong to `⋂₀ 𝒜`. This is the contrapositive of Exercise 1.5 (4). -/
theorem not_mem_sInter_of_exists_not_mem {α : Type u} {𝒜 : Set (Set α)} {x : α}
    (hx : ∃ A ∈ 𝒜, x ∉ A) : x ∉ ⋂₀ 𝒜 := by
  obtain ⟨A, hA, hxA⟩ := hx
  exact fun hxInter ↦ hxA (Set.mem_sInter.mp hxInter A hA)
