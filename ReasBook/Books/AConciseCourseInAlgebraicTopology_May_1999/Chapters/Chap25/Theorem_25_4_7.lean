import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_7.Milnor

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced only the general `MvPolynomial`/`AlgEquiv` API,
-- with no ready-made Milnor polynomial-presentation owner for the dual Steenrod algebra in the
-- current repo. This file therefore keeps the source-facing existential theorem, while the
-- reusable Milnor-generator and presentation API lives in
-- `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_7.Milnor`.

/-- Theorem 25.4.7. The fixed dual Steenrod algebra
`A_* = modTwoSteenrodAlgebraGradedDual` admits a commutative ring structure, a `ZMod 2`-algebra
structure compatible with its existing additive commutative group as in
`ModTwoSteenrodAlgebraDualAlgebra`, generators `ξ_r` for `r ≥ 1`, and a polynomial algebra
equivalence from `MvPolynomial ℕ+ (ZMod 2)` sending `X r` to `ξ_r`, where each `ξ_r` is dual to
the special admissible Steenrod monomial `[2^(r - 1), 2^(r - 2), ..., 2, 1]` from
Theorem 25.4.5. -/
theorem modTwoSteenrodAlgebraDualMilnorPresentation :
    ∃ (AStar : ModTwoSteenrodAlgebraDualAlgebra)
      (hComm : ModTwoSteenrodAlgebraDualAlgebra.IsCommutative AStar)
      (ξ : ℕ+ → modTwoSteenrodAlgebraGradedDual)
      (algEquiv : ModTwoSteenrodAlgebraDualMilnorAlgEquiv AStar),
      IsMilnorPolynomialPresentationOn AStar ξ algEquiv := sorry
