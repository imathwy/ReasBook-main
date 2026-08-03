module

public import Topology_Munkres_2000.Book.Definition_68_1

public section

namespace Subgroup

universe u v

variable {G : Type u} {ι : Type v} [Group G]

/-- A word relative to a family of subgroups is reduced when its letters are nonidentity and
no specified subgroup contains two adjacent letters. -/
structure ReducedWord (H : ι → Subgroup G) extends Word H where
  /-- No letter is the identity element. -/
  ne_one : ∀ x ∈ toList, x ≠ 1
  /-- No specified subgroup contains two adjacent letters. -/
  chain_separated :
    toList.IsChain (fun x y ↦ ∀ i, ¬ (x ∈ H i ∧ y ∈ H i))

namespace ReducedWord

variable (H : ι → Subgroup G)

/-- The empty reduced word. -/
@[expose]
def empty : ReducedWord H where
  toWord := Word.empty H
  ne_one := by simp
  chain_separated := by simp

/-- The word underlying the empty reduced word is the empty word. -/
@[simp]
theorem toWord_empty : (empty H).toWord = Word.empty H := rfl

/-- The empty reduced word supplies the canonical inhabitant. -/
instance instInhabited : Inhabited (ReducedWord H) :=
  ⟨ReducedWord.empty H⟩

/-- The ordered product represented by a reduced word. -/
@[expose]
def prod (w : ReducedWord H) : G :=
  w.toWord.prod

/-- Evaluation of a reduced word is the product of its underlying list. -/
theorem prod_def (w : ReducedWord H) : w.prod = w.toList.prod := Word.prod_def w.toWord

/-- The empty reduced word represents the identity element. -/
@[simp]
theorem prod_empty : (ReducedWord.empty H).prod = 1 := Word.prod_empty H

/-- Helper for Definition 68.2: package list-level reducedness data as a reduced word. -/
@[expose]
def ofList (l : List G) (mem_subgroup : ∀ x ∈ l, ∃ i, x ∈ H i)
    (ne_one : ∀ x ∈ l, x ≠ 1)
    (chain_separated : l.IsChain (fun x y ↦ ∀ i, ¬ (x ∈ H i ∧ y ∈ H i))) :
    ReducedWord H :=
  { toWord := { toList := l, mem_subgroup := mem_subgroup }
    ne_one := ne_one
    chain_separated := chain_separated }

/-- Helper for Definition 68.2: `ofList` has the prescribed underlying list. -/
@[simp]
theorem toList_ofList (l : List G) (mem_subgroup : ∀ x ∈ l, ∃ i, x ∈ H i)
    (ne_one : ∀ x ∈ l, x ≠ 1)
    (chain_separated : l.IsChain (fun x y ↦ ∀ i, ¬ (x ∈ H i ∧ y ∈ H i))) :
    (ofList H l mem_subgroup ne_one chain_separated).toList = l := rfl

/-- Helper for Definition 68.2: every subgroup word list has an equal-product reduced word
whose length is no larger. -/
theorem exists_prod_eq_listProd_length_le (l : List G)
    (h_mem : ∀ x ∈ l, ∃ i, x ∈ H i) :
    ∃ w : ReducedWord H, w.prod = l.prod ∧ w.toList.length ≤ l.length := by
  classical
  induction h_length : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
      -- Normalize the tail first, so adjacency is tested against its actual surviving head.
      cases l with
      | nil =>
          refine ⟨empty H, ?_, ?_⟩
          · simp only [prod_empty, List.prod_nil]
          · simp only [toWord_empty, Word.toList_empty, List.length_nil]
            exact Nat.zero_le n
      | cons x xs =>
          have h_mem_xs : ∀ z ∈ xs, ∃ i, z ∈ H i := by
            intro z hz
            exact h_mem z (List.mem_cons_of_mem x hz)
          have h_xs_length : xs.length < n := by
            rw [← h_length]
            exact Nat.lt_succ_self xs.length
          obtain ⟨r, hr_prod, hr_length⟩ := ih xs.length h_xs_length xs h_mem_xs rfl
          by_cases hx_one : x = 1
          · -- An identity leading letter disappears without changing the product.
            refine ⟨r, ?_, ?_⟩
            · simpa only [List.prod_cons, hx_one, one_mul] using hr_prod
            · exact hr_length.trans (Nat.le_of_lt h_xs_length)
          · cases h_toList : r.toList with
            | nil =>
                have h_tail_prod : xs.prod = 1 := by
                  calc
                    xs.prod = r.prod := hr_prod.symm
                    _ = r.toList.prod := prod_def H r
                    _ = 1 := by simp only [h_toList, List.prod_nil]
                have h_single_mem : ∀ z ∈ [x], ∃ i, z ∈ H i := by
                  intro z hz
                  simp only [List.mem_singleton] at hz
                  subst z
                  exact h_mem x List.mem_cons_self
                have h_single_ne : ∀ z ∈ [x], z ≠ 1 := by
                  intro z hz
                  simp only [List.mem_singleton] at hz
                  subst z
                  exact hx_one
                have h_single_chain :
                    [x].IsChain (fun a b ↦ ∀ i, ¬ (a ∈ H i ∧ b ∈ H i)) := by
                  simp only [List.isChain_singleton]
                let w := ofList H [x] h_single_mem h_single_ne h_single_chain
                refine ⟨w, ?_, ?_⟩
                · calc
                    w.prod = [x].prod := prod_def H w
                    _ = x * xs.prod := by
                      simp only [List.prod_cons, List.prod_nil, h_tail_prod, mul_one]
                    _ = (x :: xs).prod := by simp only [List.prod_cons]
                · rw [← h_length]
                  simp only [w, toList_ofList, List.length_cons, List.length_nil]
                  exact Nat.succ_le_succ (Nat.zero_le xs.length)
            | cons y ys =>
                by_cases h_shared : ∃ i, x ∈ H i ∧ y ∈ H i
                · -- Merge adjacent letters from one subgroup and recurse on the shorter list.
                  obtain ⟨i, hxi, hyi⟩ := h_shared
                  have h_merged_mem : ∀ z ∈ (x * y) :: ys, ∃ j, z ∈ H j := by
                    intro z hz
                    simp only [List.mem_cons] at hz
                    rcases hz with hz | hz
                    · subst z
                      exact ⟨i, (H i).mul_mem hxi hyi⟩
                    · exact r.toWord.mem_subgroup z (h_toList ▸ List.mem_cons_of_mem y hz)
                  have h_merged_length : ((x * y) :: ys).length < (x :: xs).length := by
                    calc
                      ((x * y) :: ys).length = r.toList.length := by
                        simp only [h_toList, List.length_cons]
                      _ ≤ xs.length := hr_length
                      _ < (x :: xs).length := Nat.lt_succ_self xs.length
                  have h_merged_lt_n : ((x * y) :: ys).length < n := by
                    rw [← h_length]
                    exact h_merged_length
                  obtain ⟨w, hw_prod, hw_length⟩ :=
                    ih ((x * y) :: ys).length h_merged_lt_n ((x * y) :: ys) h_merged_mem rfl
                  refine ⟨w, ?_, ?_⟩
                  · calc
                      w.prod = ((x * y) :: ys).prod := hw_prod
                      _ = x * (y :: ys).prod := by simp only [List.prod_cons, mul_assoc]
                      _ = x * r.prod := by rw [prod_def H r, h_toList]
                      _ = x * xs.prod := by rw [hr_prod]
                      _ = (x :: xs).prod := by simp only [List.prod_cons]
                  · exact hw_length.trans (Nat.le_of_lt h_merged_lt_n)
                · -- Otherwise prepend the letter; the tail supplies all later conditions.
                  have h_cons_mem : ∀ z ∈ x :: y :: ys, ∃ i, z ∈ H i := by
                    intro z hz
                    simp only [List.mem_cons] at hz
                    rcases hz with hz | hz
                    · subst z
                      exact h_mem x List.mem_cons_self
                    · have hz_tail : z ∈ y :: ys := by
                        simpa only [List.mem_cons] using hz
                      apply r.toWord.mem_subgroup z
                      rw [h_toList]
                      exact hz_tail
                  have h_cons_ne : ∀ z ∈ x :: y :: ys, z ≠ 1 := by
                    intro z hz
                    simp only [List.mem_cons] at hz
                    rcases hz with hz | hz
                    · subst z
                      exact hx_one
                    · have hz_tail : z ∈ y :: ys := by
                        simpa only [List.mem_cons] using hz
                      apply r.ne_one z
                      rw [h_toList]
                      exact hz_tail
                  have h_head_separated : ∀ i, ¬ (x ∈ H i ∧ y ∈ H i) := by
                    intro i hxy
                    exact h_shared ⟨i, hxy⟩
                  have h_cons_chain :
                      (x :: y :: ys).IsChain (fun a b ↦ ∀ i, ¬ (a ∈ H i ∧ b ∈ H i)) := by
                    rw [List.isChain_cons_cons]
                    exact ⟨h_head_separated, h_toList ▸ r.chain_separated⟩
                  let w := ofList H (x :: y :: ys) h_cons_mem h_cons_ne h_cons_chain
                  refine ⟨w, ?_, ?_⟩
                  · calc
                      w.prod = (x :: y :: ys).prod := prod_def H w
                      _ = x * (y :: ys).prod := by simp only [List.prod_cons]
                      _ = x * r.prod := by rw [prod_def H r, h_toList]
                      _ = x * xs.prod := by rw [hr_prod]
                      _ = (x :: xs).prod := by simp only [List.prod_cons]
                  · rw [← h_length]
                    simp only [w, toList_ofList, List.length_cons]
                    have hr_length' : (y :: ys).length ≤ xs.length := by
                      rw [← h_toList]
                      exact hr_length
                    exact Nat.succ_le_succ hr_length'

end ReducedWord

end Subgroup
