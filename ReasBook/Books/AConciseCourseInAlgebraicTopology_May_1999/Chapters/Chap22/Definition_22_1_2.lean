import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2

open CategoryTheory

universe u w

-- Semantic recall: `lean_leansearch` did not surface a canonical prespectrum owner in the
-- current environment. This project already formalizes based spaces by
-- `PointedCompactlyGenerated` and reduced suspension by `reducedSuspension`, so the source
-- definition is stated directly with that local API.

/-- Definition 22.1.2: a prespectrum is a sequence `T n` of based compactly generated spaces
equipped with structure maps `Σ(T n) ⟶ T (n + 1)`, formalized here using
`PointedCompactlyGenerated` and `reducedSuspension`. -/
structure Prespectrum where
  spaces : ℕ → PointedCompactlyGenerated.{u, w}
  structureMap : ∀ n : ℕ, Σ (spaces n) ⟶ spaces (n + 1)

namespace Prespectrum

/-- A prespectrum can be evaluated at `n` to recover its `n`th based space. -/
instance : CoeFun (Prespectrum.{u, w}) (fun _ ↦ ℕ → PointedCompactlyGenerated.{u, w}) where
  coe T := T.spaces

/-- Evaluating a prespectrum as a function returns its underlying sequence of based spaces. -/
@[simp] theorem coe_apply (T : Prespectrum.{u, w}) (n : ℕ) :
    T n = T.spaces n := rfl

/-- The degree-`n` structure map of a prespectrum. -/
abbrev sigma (T : Prespectrum.{u, w}) (n : ℕ) :
    Σ (T n) ⟶ T (n + 1) :=
  T.structureMap n

/-- The `sigma` abbreviation recovers the stored degree-`n` structure map. -/
@[simp] theorem sigma_eq_structureMap (T : Prespectrum.{u, w}) (n : ℕ) :
    T.sigma n = T.structureMap n := rfl

end Prespectrum
