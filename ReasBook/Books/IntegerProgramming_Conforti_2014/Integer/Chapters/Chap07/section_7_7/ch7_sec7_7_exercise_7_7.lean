import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix
open SequenceIndependentLifting

noncomputable section

section Exercise77

universe u

variable {ι : Type u} [DecidableEq ι]

/-- The slice used to compute the next sequential lifting coefficient of `x_j` after the
variables in `L` have already been lifted: the point lies in `S`, it satisfies `x_j = 1`, and
every still-unlifted variable outside `C ∪ L ∪ {j}` is fixed to `0`. -/
def sequential_lifting_slice
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (j : ι) : Set (ι → ℝ) :=
  {x | x ∈ S ∧ x j = 1 ∧ ∀ k, k ∉ insert j (C ∪ L) → x k = 0}

/-- Membership in `sequential_lifting_slice S C L j` means belonging to `S`, setting `x_j = 1`,
and forcing every as-yet-unlifted coordinate outside `C ∪ L ∪ {j}` to vanish. -/
theorem mem_sequential_lifting_slice_iff
    {S : Set (ι → ℝ)}
    {C L : Finset ι}
    {j : ι}
    {x : ι → ℝ} :
    x ∈ sequential_lifting_slice S C L j ↔
      x ∈ S ∧ x j = 1 ∧ ∀ k, k ∉ insert j (C ∪ L) → x k = 0 := Iff.rfl

/-- The next coefficient assigned to `x_j` by the sequential lifting procedure after the
variables in `L` have already been lifted with current coefficient vector `c`. -/
def next_sequential_lifting_coefficient
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (c : ι → ℝ)
    (β : ℝ)
    (j : ι) : ℝ :=
  β - sSup ((fun x ↦ c ⬝ᵥ x) '' sequential_lifting_slice S C L j)

/-- Expanding `next_sequential_lifting_coefficient S C L c β j` recovers the usual sequential
lifting formula `β - sup {c x | x ∈ S, x_j = 1, x_k = 0 for the still-unlifted variables}`. -/
theorem next_sequential_lifting_coefficient_eq
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (c : ι → ℝ)
    (β : ℝ)
    (j : ι) :
    next_sequential_lifting_coefficient S C L c β j =
      β - sSup ((fun x ↦ c ⬝ᵥ x) '' sequential_lifting_slice S C L j) := rfl

/-- The recursive coefficient vector produced by sequentially lifting the variables listed in
`σ`, starting from the base inequality supported on `C`. -/
private def sequential_lifting_coefficientsAux
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ : List ι) : ι → ℝ :=
  match σ with
  | [] => c
  | j :: τ =>
      let αj := next_sequential_lifting_coefficient S C L c β j
      sequential_lifting_coefficientsAux S C β (insert j L) (Function.update c j αj) τ

/-- The coefficient vector obtained by sequentially lifting the complement variables in the order
`σ`, starting from the base coefficients on `C`. -/
def sequential_lifting_coefficients
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (σ : List ι) : ι → ℝ :=
  sequential_lifting_coefficientsAux S C β ∅ (base_coefficients C α) σ

/-- With no variables left to lift, the sequential lifting coefficient vector is the original
base coefficient vector. -/
theorem sequential_lifting_coefficients_nil
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ) :
    sequential_lifting_coefficients S C α β [] = base_coefficients C α := rfl

/-- A sequential lifting order is a duplication-free list containing exactly the variables
outside the base support `C`. -/
def IsSequentialLiftingOrder
    [Fintype ι]
    (C : Finset ι)
    (σ : List ι) : Prop :=
  σ.Nodup ∧ σ.toFinset = Finset.univ \ C

/-- `IsSequentialLiftingOrder C σ` means that `σ` is duplication-free and its underlying finite
set is exactly the complement of `C`. -/
theorem isSequentialLiftingOrder_iff
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι} :
    IsSequentialLiftingOrder C σ ↔
      σ.Nodup ∧ σ.toFinset = Finset.univ \ C := Iff.rfl

namespace IsSequentialLiftingOrder

/-- A sequential lifting order has no repeated indices. -/
theorem nodup
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ) :
    σ.Nodup :=
  hσ.1

/-- The finite support of a sequential lifting order is exactly the complement of `C`. -/
theorem toFinset_eq
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ) :
    σ.toFinset = Finset.univ \ C :=
  hσ.2

/-- In a sequential lifting order for `C`, an index appears exactly when it lies outside `C`. -/
theorem mem_iff
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ)
    {j : ι} :
    j ∈ σ ↔ j ∉ C := by
  rw [← List.mem_toFinset, hσ.toFinset_eq]
  simp

/-- Moving a variable `j ∉ C` to the front of an admissible sequential lifting order preserves
admissibility. -/
theorem cons_erase
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ)
    {j : ι}
    (hj : j ∉ C) :
    IsSequentialLiftingOrder C (j :: σ.erase j) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_cons]
    constructor
    · simp [hσ.nodup.mem_erase_iff]
    · simpa using hσ.nodup.erase j
  · ext k
    by_cases hk : k = j
    · simp [hk, hj]
    · simp [hk, hσ.nodup.mem_erase_iff, hσ.mem_iff]

/-- Moving a variable `j ∉ C` to the end of an admissible sequential lifting order preserves
admissibility. -/
theorem erase_append_single
    [Fintype ι]
    {C : Finset ι}
    {σ : List ι}
    (hσ : IsSequentialLiftingOrder C σ)
    {j : ι}
    (hj : j ∉ C) :
    IsSequentialLiftingOrder C (σ.erase j ++ [j]) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨by simpa using hσ.nodup.erase j, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = j := by simpa using hb
    subst hb'
    simpa using (hσ.nodup.mem_erase_iff.1 ha).1
  · ext k
    by_cases hk : k = j
    · simp [hk, hj]
    · simp [hk, hσ.nodup.mem_erase_iff, hσ.mem_iff]

end IsSequentialLiftingOrder

/-- Exercise 7.7 (1). For the sequential lifting procedure applied to a binary set `S` and a
valid base inequality supported on `C`, the coefficient of `x_j` is largest when `x_j` is lifted
first in the order. Equivalently, moving `j` to the front of any admissible lifting order can
only increase the lifted coefficient assigned to `j`. -/
theorem exercise_7_7_lifting_coefficient_maximal_when_first
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (hS_binary : S ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
    (hbase :
      is_valid_inequality
        {x | x ∈ S ∧ ∀ k, k ∉ C → x k = 0}
        (base_coefficients C α)
        β)
    {j : ι}
    (hj : j ∉ C)
    (σ : List ι)
    (hσ : IsSequentialLiftingOrder C σ) :
    (sequential_lifting_coefficients S C α β σ) j ≤
      (sequential_lifting_coefficients S C α β (j :: σ.erase j)) j := sorry

/-- Exercise 7.7 (2). Under the same hypotheses, the coefficient of `x_j` is smallest when
`x_j` is lifted last in the order. Equivalently, moving `j` to the end of any admissible lifting
order can only decrease the lifted coefficient assigned to `j`. -/
theorem exercise_7_7_lifting_coefficient_minimal_when_last
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (hS_binary : S ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
    (hbase :
      is_valid_inequality
        {x | x ∈ S ∧ ∀ k, k ∉ C → x k = 0}
        (base_coefficients C α)
        β)
    {j : ι}
    (hj : j ∉ C)
    (σ : List ι)
    (hσ : IsSequentialLiftingOrder C σ) :
    (sequential_lifting_coefficients S C α β (σ.erase j ++ [j])) j ≤
      (sequential_lifting_coefficients S C α β σ) j := sorry

end Exercise77
