import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Construction_24_6_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_6_5

-- Semantic recall via `lean_leansearch`: `HSpace` is the canonical mathlib owner for an H-space,
-- and Construction 24.6.3 already provides the bridge `hopfConstructionMapOfHSpace` from an
-- `HSpace` structure on `S^(n - 1)` to the corresponding Hopf map `S^(2n - 1) → S^n`.

/-- If `S^(n - 1)` is an `HSpace`, then the associated Hopf construction has Hopf invariant `1`
or `-1`. -/
theorem hSpaceSphere_hopfInvariantOneOrNegOne
    (n : ℕ+) [HSpace (TopCat.sphere ((n : ℕ) - 1))] :
    IsHopfInvariant (hopfConstructionMapOfHSpace n) 1 ∨
      IsHopfInvariant (hopfConstructionMapOfHSpace n) (-1) := sorry

/-- Theorem 24.6.6. If `S^(n - 1)` is an `HSpace`, then `n = 1`, `n = 2`, `n = 4`, or `n = 8`. -/
theorem hSpaceSphere_possibleDimensions
    (n : ℕ+) [HSpace (TopCat.sphere ((n : ℕ) - 1))] :
    (n : ℕ) = 1 ∨ (n : ℕ) = 2 ∨ (n : ℕ) = 4 ∨ (n : ℕ) = 8 := sorry

namespace HSpace

/-- Companion to Theorem 24.6.6 on the canonical owner `HSpace`: if `S^m` is an `HSpace`, then
the sphere dimension itself is `0`, `1`, `3`, or `7`. -/
theorem sphere_possibleDimensions (m : ℕ) [HSpace (TopCat.sphere m)] :
    m = 0 ∨ m = 1 ∨ m = 3 ∨ m = 7 := by
  let n : ℕ+ := ⟨m + 1, Nat.succ_pos _⟩
  letI : HSpace (TopCat.sphere ((n : ℕ) - 1)) := by
    simpa [n] using (inferInstance : HSpace (TopCat.sphere m))
  rcases hSpaceSphere_possibleDimensions n with h | h | h | h
  · exact Or.inl (by simpa [n] using h)
  · exact Or.inr (Or.inl (by simpa [n] using h))
  · exact Or.inr (Or.inr (Or.inl (by simpa [n] using h)))
  · exact Or.inr (Or.inr (Or.inr (by simpa [n] using h)))

end HSpace
