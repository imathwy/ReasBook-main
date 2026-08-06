import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_5

noncomputable section

open scoped IteratedSuspension

/-- The pointed two-point space used as the concrete `S⁰` for suspension-generated spheres. -/
abbrev sphereZeroPointedSpace : PointedCompactlyGenerated :=
  PointedCompactlyGenerated.of (CompactlyGenerated.of Bool) false

/-- The chosen basepoint of `sphereZeroPointedSpace` is `false`. -/
@[simp] theorem sphereZeroPointedSpace_point :
    sphereZeroPointedSpace.point = false := rfl

/-- The suspension-generated pointed sphere `Σ^n S⁰`, used as the Chapter 11 sphere owner. -/
abbrev suspensionSphere (n : ℕ) : PointedCompactlyGenerated :=
  Σ^n sphereZeroPointedSpace
