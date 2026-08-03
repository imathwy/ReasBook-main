module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Countable.Defs
public import Mathlib.Order.PiLex

public section

/-- The countably infinite product of positive integers, equipped with the
dictionary order. -/
abbrev DictionarySequence := Lex (ℕ+ → ℕ+)

namespace DictionarySequence

/-- Helper for Definition 10.2: no sequence indexed by `ℕ` enumerates all
positive-integer sequences. -/
private lemma natToDictionarySequence_not_surjective
    (f : ℕ → DictionarySequence) : ¬ Function.Surjective f := by
  -- Diagonalize by changing the value at the coordinate assigned to each row.
  let diagonal : DictionarySequence :=
    toLex fun i : ℕ+ ↦ if f i.natPred i = 1 then 2 else 1
  intro hf
  obtain ⟨n, hn⟩ := hf diagonal
  -- At coordinate `n + 1`, the alleged diagonal row differs from itself.
  have hcoordinate := congrArg (fun x : DictionarySequence ↦ x n.succPNat) hn
  by_cases hvalue : f n n.succPNat = 1
  · simp [diagonal, hvalue] at hcoordinate
  · simp [diagonal, hvalue] at hcoordinate

/-- Definition 10.2: The countably infinite product of positive integers is
uncountable. -/
instance instUncountableDictionarySequence : Uncountable DictionarySequence := by
  -- The diagonal lemma rules out every proposed enumeration by natural numbers.
  rw [uncountable_iff_forall_not_surjective]
  exact natToDictionarySequence_not_surjective

/-- Two positive-integer sequences are ordered by their first differing
coordinate. -/
theorem lt_iff (a b : DictionarySequence) :
    a < b ↔ ∃ n : ℕ+, (∀ i, i < n → a i = b i) ∧ a n < b n := Iff.rfl

/-- Helper for Definition 10.2: moving one exceptional larger value to a later
coordinate strictly decreases a lexicographically ordered function. -/
private lemma strictAnti_toLex_update_const {iota beta : Type*}
    [LinearOrder iota] [WellFoundedLT iota] [PartialOrder beta] {c a : beta} (hca : c < a) :
    StrictAnti (fun i : iota ↦ toLex (Function.update (fun _ : iota ↦ c) i a)) := by
  -- The earlier update coordinate is the first place where the two functions differ.
  intro m n hmn
  refine ⟨m, ?_, ?_⟩
  · intro j hjm
    have hjm_ne : j ≠ m := ne_of_lt hjm
    have hjn_ne : j ≠ n := ne_of_lt (hjm.trans hmn)
    simp only [Pi.toLex_apply, Function.update_of_ne hjn_ne,
      Function.update_of_ne hjm_ne]
  · have hmn_ne : m ≠ n := ne_of_lt hmn
    simp only [Pi.toLex_apply, Function.update_of_ne hmn_ne, Function.update_self]
    exact hca

/- The dictionary order is the canonical lexicographic linear order. -/
#check (inferInstance : LinearOrder DictionarySequence)

/-- The dictionary order on infinite positive-integer
sequences is not a well-order. -/
theorem not_wellFounded : ¬ WellFoundedLT DictionarySequence := by
  -- Successively move the unique `2` to the right to obtain an infinite descent.
  intro hwellFounded
  let chain : ℕ → DictionarySequence := fun n ↦
    toLex (Function.update (fun _ : ℕ+ ↦ (1 : ℕ+)) n.succPNat 2)
  have hone_lt_two : (1 : ℕ+) < 2 := by
    exact PNat.lt_succ_self 1
  have hdescending : ∀ n, chain (n + 1) < chain n := by
    intro n
    exact strictAnti_toLex_update_const hone_lt_two
      (Nat.succPNat_lt_succPNat.mpr (Nat.lt_succ_self n))
  -- Well-founded relations admit no such descending chain.
  have hnoChain := wellFounded_iff_isEmpty_descending_chain.mp hwellFounded.wf
  exact hnoChain.false ⟨chain, hdescending⟩

/-- The set of sequences with exactly one coordinate equal to `2` and every
other coordinate equal to `1`. -/
def singleTwo : Set DictionarySequence :=
  Set.range fun n : ℕ+ ↦
    toLex (Function.update (fun _ : ℕ+ ↦ (1 : ℕ+)) n 2)

/-- Membership in `singleTwo` is witnessed by the coordinate updated from `1`
to `2`. -/
theorem mem_singleTwo (x : DictionarySequence) :
    x ∈ singleTwo ↔
      ∃ n : ℕ+, x = toLex (Function.update (fun _ : ℕ+ ↦ (1 : ℕ+)) n 2) := by
  simp [singleTwo, eq_comm]

/-- Helper for Definition 10.2: every member of `singleTwo` has a strictly
smaller member of `singleTwo`. -/
private lemma singleTwoHasSmaller (x : DictionarySequence) (hx : x ∈ singleTwo) :
    ∃ y ∈ singleTwo, y < x := by
  -- Move the unique `2` from its current coordinate to the next coordinate.
  obtain ⟨n, rfl⟩ := (mem_singleTwo x).mp hx
  let y : DictionarySequence :=
    toLex (Function.update (fun _ : ℕ+ ↦ (1 : ℕ+)) (n + 1) 2)
  refine ⟨y, ?_, ?_⟩
  · exact (mem_singleTwo y).mpr ⟨n + 1, rfl⟩
  · have hone_lt_two : (1 : ℕ+) < 2 := by
      exact PNat.lt_succ_self 1
    have hn : n < n + 1 := by
      exact PNat.lt_add_right n 1
    exact strictAnti_toLex_update_const hone_lt_two hn

/-- The set `singleTwo` has no least element in the dictionary order. -/
theorem singleTwo_no_least : ¬ ∃ x, IsLeast singleTwo x := by
  -- A least member cannot have the strictly smaller member supplied above.
  rintro ⟨x, hx, hleast⟩
  obtain ⟨y, hy, hyx⟩ := singleTwoHasSmaller x hx
  exact (not_le_of_gt hyx) (hleast hy)

end DictionarySequence
