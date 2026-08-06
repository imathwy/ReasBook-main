import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_6_1

-- Semantic recall via `lean_leansearch`: no canonical mathlib owner for the Hopf-invariant-one
-- dimension restriction surfaced in the current environment, so this item is stated directly on
-- the local Chapter 24 owners `HopfSphereMap` and `IsHopfInvariant`.

namespace IsHopfInvariant

/-- If `f : S^(2n - 1) → S^n` has Hopf invariant `h` with `h = 1` or `h = -1`, then
`n = 2`, `n = 4`, or `n = 8`. This companion keeps the reusable dimension restriction attached to
the source-facing owner `IsHopfInvariant`. -/
theorem possibleDimensions
    {n : ℕ} {f : HopfSphereMap n} {h : ℤ}
    (hf : IsHopfInvariant f h) (hh : h = 1 ∨ h = -1) :
    n = 2 ∨ n = 4 ∨ n = 8 := by
  sorry

end IsHopfInvariant

/-- Theorem 24.6.5. If a map `S^(2n - 1) → S^n` has Hopf invariant `1` or `-1`, then
`n = 2`, `n = 4`, or `n = 8`. -/
theorem hopfInvariantOneOrNegOne_possibleDimensions
    {n : ℕ} {f : HopfSphereMap n}
    (hf : IsHopfInvariant f 1 ∨ IsHopfInvariant f (-1)) :
    n = 2 ∨ n = 4 ∨ n = 8 := by
  rcases hf with hf | hf
  · exact IsHopfInvariant.possibleDimensions hf (Or.inl rfl)
  · exact IsHopfInvariant.possibleDimensions hf (Or.inr rfl)
