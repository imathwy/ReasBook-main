module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Nat.Pairing
public import Mathlib.SetTheory.Cardinal.Order

public section

/-- Helper for Exercise 7.8: membership in a countable set is recovered from its
enumeration range together with the membership status of the default value. -/
lemma mem_iff_mem_range_enumerateCountable {α : Type*} {s : Set α} (hs : s.Countable)
    (a x : α) :
    x ∈ s ↔ x ∈ Set.range (Set.enumerateCountable hs a) ∧ (x ≠ a ∨ a ∈ s) := by
  -- Every member appears in the enumeration, and the second condition separates the default.
  constructor
  · intro hx
    refine ⟨Set.subset_range_enumerate hs a hx, ?_⟩
    by_cases hxa : x = a
    · exact Or.inr (hxa ▸ hx)
    · exact Or.inl hxa
  · rintro ⟨hxRange, hxDefault⟩
    -- The enumeration can only add the default point to the original set.
    have hxInsert : x ∈ insert a s := Set.range_enumerateCountable_subset hs a hxRange
    rcases hxDefault with hxNe | ha
    · exact (Set.mem_insert_iff.mp hxInsert).resolve_left hxNe
    · rw [Set.range_enumerateCountable_of_mem hs ha] at hxRange
      exact hxRange

/-- Helper for Exercise 7.8: encode a countable set of binary sequences by a
membership flag followed by a paired enumeration of all its sequence entries. -/
noncomputable def countableBinarySubsetCode :
    {s : Set (ℕ → Fin 2) // s.Countable} → ℕ → Fin 2 :=
  fun s n ↦
    match n with
    | 0 =>
        @ite (Fin 2) ((fun _ : ℕ ↦ (0 : Fin 2)) ∈ s.1)
          (Classical.propDecidable _) 1 0
    | k + 1 =>
        Set.enumerateCountable s.property (fun _ : ℕ ↦ (0 : Fin 2))
          (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2

/-- Helper for Exercise 7.8: the first coordinate is one when the constant-zero
binary sequence belongs to the encoded set. -/
lemma countableBinarySubsetCode_zero_of_mem
    (s : {s : Set (ℕ → Fin 2) // s.Countable})
    (hs : (fun _ : ℕ ↦ (0 : Fin 2)) ∈ s.1) :
    countableBinarySubsetCode s 0 = 1 := by
  -- The membership flag selects the positive branch.
  simp only [countableBinarySubsetCode, hs, if_pos]

/-- Helper for Exercise 7.8: the first coordinate is zero when the constant-zero
binary sequence does not belong to the encoded set. -/
lemma countableBinarySubsetCode_zero_of_not_mem
    (s : {s : Set (ℕ → Fin 2) // s.Countable})
    (hs : (fun _ : ℕ ↦ (0 : Fin 2)) ∉ s.1) :
    countableBinarySubsetCode s 0 = 0 := by
  -- The membership flag selects the negative branch.
  simp only [countableBinarySubsetCode, hs, ite_false]

/-- Helper for Exercise 7.8: paired successor coordinates of the code recover
the corresponding bit of the canonical countable enumeration. -/
lemma countableBinarySubsetCode_succPair
    (s : {s : Set (ℕ → Fin 2) // s.Countable}) (i j : ℕ) :
    countableBinarySubsetCode s (Nat.pairEquiv (i, j) + 1) =
      Set.enumerateCountable s.property (fun _ : ℕ ↦ (0 : Fin 2)) i j := by
  -- Pairing and unpairing cancel at every tail coordinate.
  simp only [countableBinarySubsetCode, Equiv.symm_apply_apply]

/-- Helper for Exercise 7.8: the flag-and-enumeration encoding of countable
sets of binary sequences is injective. -/
lemma countableBinarySubsetCode_injective : Function.Injective countableBinarySubsetCode := by
  -- Equality of codes first recovers membership of the distinguished default sequence.
  intro s t hCode
  have hDefault :
      (fun _ : ℕ ↦ (0 : Fin 2)) ∈ s.1 ↔ (fun _ : ℕ ↦ (0 : Fin 2)) ∈ t.1 := by
    by_cases hs : (fun _ : ℕ ↦ (0 : Fin 2)) ∈ s.1
    · by_cases ht : (fun _ : ℕ ↦ (0 : Fin 2)) ∈ t.1
      · exact ⟨fun _ ↦ ht, fun _ ↦ hs⟩
      · have hFlag := congrFun hCode 0
        rw [countableBinarySubsetCode_zero_of_mem s hs,
          countableBinarySubsetCode_zero_of_not_mem t ht] at hFlag
        simp at hFlag
    · by_cases ht : (fun _ : ℕ ↦ (0 : Fin 2)) ∈ t.1
      · have hFlag := congrFun hCode 0
        rw [countableBinarySubsetCode_zero_of_not_mem s hs,
          countableBinarySubsetCode_zero_of_mem t ht] at hFlag
        simp at hFlag
      · exact ⟨fun h ↦ (hs h).elim, fun h ↦ (ht h).elim⟩
  have hEnumeration :
      Set.enumerateCountable s.property (fun _ : ℕ ↦ (0 : Fin 2)) =
        Set.enumerateCountable t.property (fun _ : ℕ ↦ (0 : Fin 2)) := by
    -- Every enumerated sequence agrees bitwise by evaluating the code at paired successors.
    funext i j
    calc
      Set.enumerateCountable s.property (fun _ : ℕ ↦ (0 : Fin 2)) i j =
          countableBinarySubsetCode s (Nat.pairEquiv (i, j) + 1) :=
        (countableBinarySubsetCode_succPair s i j).symm
      _ = countableBinarySubsetCode t (Nat.pairEquiv (i, j) + 1) := congrFun hCode _
      _ = Set.enumerateCountable t.property (fun _ : ℕ ↦ (0 : Fin 2)) i j :=
        countableBinarySubsetCode_succPair t i j
  -- The recovered enumeration and flag determine membership in the original sets.
  apply Subtype.ext
  ext x
  rw [mem_iff_mem_range_enumerateCountable s.property,
    mem_iff_mem_range_enumerateCountable t.property, hEnumeration, hDefault]

/-- Exercise 7.8: The binary sequence space `ℕ → Fin 2` and the type of its
countable subsets have the same cardinality. -/
theorem binarySequences_cardinality_eq_countableSubsets :
    Cardinal.mk (ℕ → Fin 2) = Cardinal.mk {s : Set (ℕ → Fin 2) // s.Countable} := by
  -- Singleton sets embed binary sequences into the countable-subset type.
  apply le_antisymm
  · refine Cardinal.mk_le_of_injective
      (f := fun x ↦ ⟨{x}, Set.countable_singleton x⟩) ?_
    intro x y hxy
    simpa using congrArg Subtype.val hxy
  · -- The explicit code supplies the reverse cardinal inequality.
    exact Cardinal.mk_le_of_injective countableBinarySubsetCode_injective
