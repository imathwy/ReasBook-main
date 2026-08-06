import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1

open CategoryTheory
open AlgebraicTopology
open scoped MonoidalCategory SingularChains

noncomputable section

-- Semantic recall via `lean_leansearch`: `AlgebraicTopology.singularChainComplexFunctor` and
-- `AlgebraicTopology.singularHomologyFunctor` are the canonical owners for singular chains and
-- singular homology, while Chapter 20 already provides the repository's generic
-- `singularHomologyWithCoefficients`. This file keeps the Chapter 16 source-facing surface as the
-- integral specialization of that generic owner to `C_*(X)` from Construction 16.1.6 and an
-- Abelian coefficient group `π` concentrated in degree `0`. As in Definition 13.3.7, the needed
-- monoidal structure on `ModuleCat ℤ` is available here only in the small universe, so the
-- statement is recorded for `X : TopCat` and `π : Type`.

/-- Definition 16.1.7. Singular homology with coefficients `π` is `H_*(C_*(X) ⊗ π)`, where
`C_*(X)` is the integral singular chain complex of `X` from Construction 16.1.6 and `π` is
concentrated in degree `0`. -/
abbrev topologicalSingularHomologyWithCoefficients
    (X : TopCat) (π : Type) [AddCommGroup π] :
    ℕ → ModuleCat ℤ :=
  singularHomologyWithCoefficients ℤ X (ModuleCat.of ℤ π)

/-- Lean notation for the singular homology group `H_n(X; π)`. -/
scoped[SingularHomology] notation "H[" n "](" X "; " π ")" =>
  topologicalSingularHomologyWithCoefficients X π n

open scoped SingularHomology

/-- Evaluating `H[n](X; π)` recovers the degree-`n` homology object of the tensor product complex
`C_*(X) ⊗ coefficientComplex ℤ (ModuleCat.of ℤ π)`, with `π` concentrated in degree `0`. -/
@[simp] theorem topologicalSingularHomologyWithCoefficients_apply
    (X : TopCat) (π : Type) [AddCommGroup π] (n : ℕ) :
    H[n](X; π) =
      (C_*(X) ⊗ coefficientComplex ℤ (ModuleCat.of ℤ π)).homology n :=
  rfl

/-- `topologicalSingularHomologyWithCoefficients X π` is the graded family `n ↦ H[n](X; π)`. -/
theorem topologicalSingularHomologyWithCoefficients_def
    (X : TopCat) (π : Type) [AddCommGroup π] :
    topologicalSingularHomologyWithCoefficients X π = fun n ↦ H[n](X; π) :=
  rfl
