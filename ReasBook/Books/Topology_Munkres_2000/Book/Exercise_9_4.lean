module

public import Topology_Munkres_2000.Book.Theorem_7_1

import Mathlib.Data.Set.Countable

public section

universe u v

/- Exercise 9.4 (1): The theorem in §7 whose proof makes infinitely many
arbitrary choices is Theorem 7.5, on countable unions of countable sets. -/
#check Set.countable_iUnion

/-- Exercise 9.4 (2): The use of the axiom of choice in the proof of Theorem 7.5
is the simultaneous selection of a surjection `ℕ+ → A j` for every nonempty
countable type in the indexed family `A`. -/
theorem exists_surjective_pnat_family {J : Type u} (A : J → Type v)
    [∀ j, Nonempty (A j)] [∀ j, Countable (A j)] :
    ∃ f : (j : J) → ℕ+ → A j, ∀ j, Function.Surjective (f j) := by
  apply Classical.axiomOfChoice
  intro j
  exact (countable_iff_exists_surjective_pnat (A j)).mp inferInstance
