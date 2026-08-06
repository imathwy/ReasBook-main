import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_1
import Mathlib.AlgebraicTopology.SingularSet

open CategoryTheory Simplicial

universe u

-- `TopCat.toSSetObjEquiv` in `Mathlib.AlgebraicTopology.SingularSet` identifies the `n`-simplices
-- of the singular simplicial set of `X` with continuous maps `Δ^n → X`.

/-- Definition 16.1.3. A singular `n`-simplex of `X` is a continuous map `Δ^n → X`; using
Definition 16.1.1, the textbook set `S_n X` is canonically the type of continuous maps
`Δ^n → X`. -/
abbrev singularSimplex (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  ContinuousMap (Δ^n) X

/-- Unfolding `singularSimplex n X` recovers the continuous-map model `C(Δ^n, X)`. -/
theorem singularSimplex_def (n : ℕ) (X : Type u) [TopologicalSpace X] :
    singularSimplex n X = ContinuousMap (Δ^n) X :=
  rfl

/-- The `n`-simplices of the canonical singular simplicial set `TopCat.toSSet.obj X` are exactly
the singular `n`-simplices `Δ^n → X`. -/
noncomputable abbrev singularSimplexEquiv (n : ℕ) (X : TopCat.{u}) :
    (TopCat.toSSet.obj X) _⦋n⦌ ≃ singularSimplex n X :=
  TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)
