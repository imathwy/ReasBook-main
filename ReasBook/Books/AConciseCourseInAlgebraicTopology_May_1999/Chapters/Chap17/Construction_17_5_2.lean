import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_5_1

noncomputable section

open CategoryTheory

universe u

-- Semantic recall via `lean_leansearch`: `ModuleCat.monoidalClosedHomEquiv` and
-- `CategoryTheory.ihom.ev` expose the canonical evaluation/currying pattern. In this chapter,
-- `chainTensorHomAdjunction` is the source-facing owner for the chain-complex version.

/-- Construction 17.5.2. The algebraic relation between tensor products, Hom complexes, and
evaluation is formalized by the canonical evaluation morphism
`tensorObj (chainHomComplex R B M) B ⟶ M`, obtained by adjoint-transposing the identity of the
Hom complex. This is the chain-level source of the cup and cap products constructed later. -/
noncomputable def chainHomEvaluation (R : Type u) [CommRing R]
    (B M : ChainComplex (ModuleCat R) ℤ) :
    HomologicalComplex.tensorObj (chainHomComplex R B M) B ⟶ M :=
  (chainTensorHomAdjunction R (chainHomComplex R B M) B M).symm (𝟙 _)

/-- Applying `chainTensorHomAdjunction` to `chainHomEvaluation R B M` recovers the identity of
`chainHomComplex R B M`. -/
@[simp] theorem chainHomEvaluation_spec (R : Type u) [CommRing R]
    (B M : ChainComplex (ModuleCat R) ℤ) :
    chainTensorHomAdjunction R (chainHomComplex R B M) B M (chainHomEvaluation R B M) =
      𝟙 (chainHomComplex R B M) := by
  simpa only [chainHomEvaluation] using
    (chainTensorHomAdjunction R (chainHomComplex R B M) B M).apply_symm_apply
      (𝟙 (chainHomComplex R B M))
