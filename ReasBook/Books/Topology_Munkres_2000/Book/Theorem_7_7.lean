module

public import Mathlib.Data.Countable.Defs

public section

/-- Helper for Theorem 7.7: flipping either element of `Fin 2` changes it. -/
lemma binaryDiagonalFlip_ne (a : Fin 2) : (if a = 0 then 1 else 0) ≠ a := by
  -- The two cases identify `a` with one of the two elements of `Fin 2`.
  refine Fin.cases ?_ (fun b ↦ ?_) a
  · simp
  · have hb : b = 0 := Subsingleton.elim _ _
    subst b
    simp

/-- Theorem 7.7: The set of infinite sequences in the two-element type `Fin 2` is
uncountable. -/
instance binarySequences_uncountable : Uncountable (ℕ → Fin 2) := by
  -- It suffices to show that every proposed enumeration misses a sequence.
  rw [uncountable_iff_forall_not_surjective]
  intro g hg
  let y : ℕ → Fin 2 := fun n ↦ if g n n = 0 then 1 else 0
  obtain ⟨n, hn⟩ := hg y
  -- At the alleged preimage, equality of sequences contradicts the flipped diagonal entry.
  have hdiag : y n = g n n := (congrFun hn n).symm
  have hflip : (if g n n = 0 then 1 else 0) = g n n := by
    simpa [y] using hdiag
  exact binaryDiagonalFlip_ne (g n n) hflip
