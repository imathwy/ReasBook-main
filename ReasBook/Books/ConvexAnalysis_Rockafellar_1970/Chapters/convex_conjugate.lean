import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part2

section RockafellarShared

/-- The canonical convex conjugate `f*`, defined as the Fenchel conjugate
`x* ↦ sup_x (⟪x, x*⟫ - f x)`. -/
noncomputable abbrev convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fenchelConjugate n f

end RockafellarShared
