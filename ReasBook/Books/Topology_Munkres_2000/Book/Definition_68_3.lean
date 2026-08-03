module

public import Topology_Munkres_2000.Book.Definition_68_3.FreeProduct
public import Mathlib.Data.List.ChainOfFn

public section

namespace Subgroup

open scoped FreeProduct

universe u v

variable {G : Type u} {ι : Type v} [Group G]

/-- Characterization from Definition 68.3 (1): For a pairwise disjoint family of subgroups, to
say that `G` is their free product is to say that every element has a unique reduced-word
representation; this property already implies that the family generates `G`. -/
theorem isFreeProduct_iff_uniqueRepresentation (H : ι → Subgroup G)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j))) :
    G = *ᵢ H ↔ ∀ x : G, ∃! w : ReducedWord H, w.prod = x := by
  constructor
  · exact fun h_free ↦ (isFreeProduct_iff H).mp h_free |>.2
  · exact IsFreeProduct.ofUniqueRepresentation H h_disjoint

/-- Consequence of Definition 68.3 (2): In a free product, every nonidentity letter belongs to a
unique subgroup in the family. -/
theorem IsFreeProduct.existsUnique_mem {H : ι → Subgroup G} (h_free : G = *ᵢ H)
    {x : G} (h_ne_one : x ≠ 1) (h_mem : ∃ i, x ∈ H i) :
    ∃! i, x ∈ H i :=
  existsUnique_mem_of_pairwise_disjoint h_free.pairwise_disjoint h_ne_one h_mem

/-- Helper for Definition 68.3: two specified nonidentity letters share no family subgroup
exactly when their specified subgroup indices differ. -/
lemma noCommonSubgroup_iff_indices_ne {H : ι → Subgroup G}
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    {x y : G} {i j : ι} (hx : x ∈ H i) (hy : y ∈ H j)
    (hx_ne_one : x ≠ 1) (hy_ne_one : y ≠ 1) :
    (∀ k, ¬ (x ∈ H k ∧ y ∈ H k)) ↔ i ≠ j := by
  constructor
  · intro h_no_common hij
    -- Equal specified indices immediately provide a common subgroup.
    subst j
    exact h_no_common i ⟨hx, hy⟩
  · intro hij k hk
    -- Uniqueness of subgroup membership identifies both specified indices with `k`.
    have hx_unique : ∃! a, x ∈ H a :=
      existsUnique_mem_of_pairwise_disjoint h_disjoint hx_ne_one ⟨i, hx⟩
    have hy_unique : ∃! a, y ∈ H a :=
      existsUnique_mem_of_pairwise_disjoint h_disjoint hy_ne_one ⟨j, hy⟩
    have hik : i = k := hx_unique.unique hx hk.1
    have hjk : j = k := hy_unique.unique hy hk.2
    exact hij (hik.trans hjk.symm)

/-- Definition 68.3 (3): For explicitly indexed nonidentity letters in subgroups of a free
product, reducedness is equivalent to adjacent indices being distinct. -/
theorem IsFreeProduct.reduced_iff_adjacent_indices_ne {n : ℕ} {H : ι → Subgroup G}
    (h_free : G = *ᵢ H)
    (letters : Fin n → G) (indices : Fin n → ι)
    (h_mem : ∀ i, letters i ∈ H (indices i))
    (h_ne_one : ∀ i, letters i ≠ 1) :
    (List.ofFn letters).IsChain (fun x y ↦ ∀ i, ¬ (x ∈ H i ∧ y ∈ H i)) ↔
      (List.ofFn indices).IsChain (· ≠ ·) := by
  -- Normalize both chain conditions to the same adjacent positions in the two arrays.
  rw [List.isChain_ofFn, List.isChain_ofFn]
  constructor
  · intro h_reduced i hi
    -- The subgroup bridge converts separation of these letters into index inequality.
    exact (noCommonSubgroup_iff_indices_ne h_free.pairwise_disjoint
      (h_mem ⟨i, Nat.lt_of_succ_lt hi⟩) (h_mem ⟨i + 1, hi⟩)
      (h_ne_one ⟨i, Nat.lt_of_succ_lt hi⟩) (h_ne_one ⟨i + 1, hi⟩)).mp
      (h_reduced i hi)
  · intro h_indices i hi
    -- Conversely, distinct adjacent indices rule out any common family subgroup.
    exact (noCommonSubgroup_iff_indices_ne h_free.pairwise_disjoint
      (h_mem ⟨i, Nat.lt_of_succ_lt hi⟩) (h_mem ⟨i + 1, hi⟩)
      (h_ne_one ⟨i, Nat.lt_of_succ_lt hi⟩) (h_ne_one ⟨i + 1, hi⟩)).mpr
      (h_indices i hi)

end Subgroup
