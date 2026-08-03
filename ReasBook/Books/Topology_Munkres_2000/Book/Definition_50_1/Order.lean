module

public import Mathlib.Data.Set.Card

public section

universe u

namespace Set

/-- A collection has order at most `n` when every point belongs to at most `n`
members of the collection. -/
def HasOrderLE {X : Type u} (𝒜 : Set (Set X)) (n : ℕ) : Prop :=
  ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n

/-- The pointwise cardinality characterization of `Set.HasOrderLE`. -/
theorem hasOrderLE_iff {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} :
    𝒜.HasOrderLE n ↔ ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n := by
  rfl

namespace HasOrderLE

/-- An upper bound on the order remains valid after increasing the bound. -/
theorem mono {X : Type u} {𝒜 : Set (Set X)} {n k : ℕ}
    (h : 𝒜.HasOrderLE n) (hnk : n ≤ k) :
    𝒜.HasOrderLE k := fun x ↦ (h x).trans (by simpa using hnk)

end HasOrderLE

/-- A collection has order `n` when some point belongs to exactly `n` members
and every point belongs to at most `n` members. -/
def HasOrder {X : Type u} (𝒜 : Set (Set X)) (n : ℕ) : Prop :=
  (∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n) ∧ 𝒜.HasOrderLE n

/-- The attained pointwise cardinality characterization of `Set.HasOrder`. -/
theorem hasOrder_iff {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} :
    𝒜.HasOrder n ↔
      (∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n) ∧
        ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n := by
  rfl

namespace HasOrder

/-- Exact order gives the corresponding upper bound. -/
theorem le {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} (h : 𝒜.HasOrder n) :
    𝒜.HasOrderLE n := h.2

/-- Exact order is attained at some point. -/
theorem exists_eq {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} (h : 𝒜.HasOrder n) :
    ∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n := h.1

end HasOrder

end Set
