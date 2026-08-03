module

public import Topology_Munkres_2000.Book.Example_12_4.CocountableTopology

public section

open Set

universe u

/- Exercise 13.3 (1). The collection consisting of the empty set and the sets with
countable complement is the collection of open sets of `CocountableTopology X`. -/
#check (CocountableTopology.isOpen_iff' :
  ∀ {X : Type u} {U : Set (CocountableTopology X)},
    IsOpen U ↔ U = ∅ ∨ Uᶜ.Countable)

/-- The collection of subsets whose complements are infinite, empty, or the whole space. -/
def infiniteComplSets (X : Type u) : Set (Set X) :=
  {U | Uᶜ.Infinite ∨ Uᶜ = ∅ ∨ Uᶜ = Set.univ}

/-- Membership in `infiniteComplSets X` restates its three defining alternatives. -/
@[simp]
theorem mem_infiniteComplSets {X : Type u} {U : Set X} :
    U ∈ infiniteComplSets X ↔ Uᶜ.Infinite ∨ Uᶜ = ∅ ∨ Uᶜ = Set.univ := Iff.rfl

/-- Helper for Exercise 13.3: on a finite type, `infiniteComplSets X` consists only of
the empty set and the whole space. -/
lemma infiniteComplSets_eq_indiscreteOpens {X : Type u} [Finite X] :
    infiniteComplSets X = {U : Set X | U = ∅ ∨ U = Set.univ} := by
  -- Eliminate the impossible infinite-complement case and complement the two equalities.
  ext U
  simp only [mem_infiniteComplSets, Set.mem_setOf_eq]
  constructor
  · intro hU
    rcases hU with hU | hU | hU
    · exact False.elim (hU (Set.toFinite Uᶜ))
    · right
      simpa only [compl_compl, compl_empty] using
        congrArg (fun V : Set X ↦ Vᶜ) hU
    · left
      simpa only [compl_compl, compl_univ] using
        congrArg (fun V : Set X ↦ Vᶜ) hU
  · intro hU
    rcases hU with rfl | rfl
    · exact Or.inr (Or.inr compl_empty)
    · exact Or.inr (Or.inl compl_univ)

/-- Helper for Exercise 13.3: every singleton has infinite complement in an infinite type. -/
lemma singleton_mem_infiniteComplSets {X : Type u} [Infinite X] (x : X) :
    ({x} : Set X) ∈ infiniteComplSets X := by
  -- The singleton is finite, so its complement is infinite.
  rw [mem_infiniteComplSets]
  exact Or.inl (Set.finite_singleton x).infinite_compl

/-- Helper for Exercise 13.3: the union of the singletons away from `a` is `{a}ᶜ`. -/
lemma iUnion_singletons_ne {X : Type u} (a : X) :
    (⋃ x : {x : X // x ≠ a}, ({x.1} : Set X)) = ({a} : Set X)ᶜ := by
  -- Membership on either side says exactly that the point differs from `a`.
  ext y
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_compl_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hya
    exact ⟨⟨y, hya⟩, rfl⟩

/-- Helper for Exercise 13.3: the complement of a singleton is excluded from
`infiniteComplSets X` when `X` is infinite. -/
lemma compl_singleton_not_mem_infiniteComplSets {X : Type u} [Infinite X] (a : X) :
    ({a} : Set X)ᶜ ∉ infiniteComplSets X := by
  -- Its complement is the finite, nonempty singleton, which cannot be the whole infinite type.
  rw [mem_infiniteComplSets]
  simp only [compl_compl]
  intro h
  rcases h with h | h | h
  · exact h (Set.finite_singleton a)
  · exact Set.singleton_ne_empty a h
  · have huniv : (Set.univ : Set X).Finite := h ▸ Set.finite_singleton a
    exact not_finite_iff_infinite.mpr inferInstance (Set.finite_univ_iff.mp huniv)

/-- Exercise 13.3 (2). The sets whose complements are infinite, empty, or the whole space
are exactly the open sets of a topology on `X` if and only if `X` is finite. -/
theorem infiniteCompl_isTopology_iff_finite (X : Type u) :
    (∃ t : TopologicalSpace X, t.IsOpen = infiniteComplSets X) ↔ Finite X := by
  constructor
  · rintro ⟨t, ht⟩
    -- If `X` were infinite, union closure would make the punctured space open.
    by_contra hX
    letI : Infinite X := not_finite_iff_infinite.mp hX
    letI : TopologicalSpace X := t
    let a : X := Classical.choice (inferInstance : Nonempty X)
    have hopenSingleton (x : {x : X // x ≠ a}) : IsOpen ({x.1} : Set X) := by
      change t.IsOpen ({x.1} : Set X)
      rw [ht]
      exact singleton_mem_infiniteComplSets x.1
    have hopenUnion : IsOpen (⋃ x : {x : X // x ≠ a}, ({x.1} : Set X)) :=
      isOpen_iUnion hopenSingleton
    have hmemUnion : (⋃ x : {x : X // x ≠ a}, ({x.1} : Set X)) ∈ infiniteComplSets X := by
      change infiniteComplSets X (⋃ x : {x : X // x ≠ a}, ({x.1} : Set X))
      rw [← ht]
      exact hopenUnion
    rw [iUnion_singletons_ne] at hmemUnion
    exact compl_singleton_not_mem_infiniteComplSets a hmemUnion
  · intro hX
    letI : Finite X := hX
    -- On a finite type the collection is the open-set predicate of the indiscrete topology.
    refine ⟨⊤, ?_⟩
    rw [infiniteComplSets_eq_indiscreteOpens]
    funext U
    exact propext (TopologicalSpace.isOpen_top_iff U)
