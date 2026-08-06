import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ComplexKTheoryAdams

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ComplexKTheoryAdams

-- Semantic recall via `lean_leansearch` did not surface a canonical mathlib Adams-uniqueness
-- theorem for the local Chapter 24 `complexKTheory` owner, so this file records the
-- source-faithful uniqueness statement on `ComplexKTheoryAdamsFamily`.

/-- Remark 24.5.2. The splitting principle makes the Adams operations unique with their
prescribed behavior on line bundles. Equivalently, any two Adams-operation families satisfying the
Chapter 24 Adams axioms coincide. -/
theorem complexKTheoryAdams_unique
    {ψ ψ' : ComplexKTheoryAdamsFamily}
    (hψ : IsComplexKTheoryAdams ψ) (hψ' : IsComplexKTheoryAdams ψ') :
    ψ = ψ' := sorry

/-- Adams-operation families satisfying the Chapter 24 axioms form a subsingleton. -/
instance : Subsingleton { ψ : ComplexKTheoryAdamsFamily // IsComplexKTheoryAdams ψ } := by
  refine ⟨?_⟩
  intro ψ ψ'
  apply Subtype.ext
  exact complexKTheoryAdams_unique ψ.property ψ'.property

/-- Two Adams-operation families on `complexKTheory` that satisfy the Chapter 24 Adams axioms
agree on each operation `ψ ^[k] : K(X) → K(X)`. -/
theorem complexKTheoryAdams_ext
    {ψ ψ' : ComplexKTheoryAdamsFamily}
    (hψ : IsComplexKTheoryAdams ψ) (hψ' : IsComplexKTheoryAdams ψ')
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    (k : NonzeroInt) :
    (ψ ^[k] : complexKTheory X →+* complexKTheory X) = ψ' ^[k] := by
  simpa using congrArg (fun φ : ComplexKTheoryAdamsFamily ↦ φ X k)
    (complexKTheoryAdams_unique hψ hψ')
