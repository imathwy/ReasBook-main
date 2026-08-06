import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_1_3

/- Corollary 25.5.5. Thom's polynomial description of the unoriented cobordism algebra:
`N_*` is a polynomial `ZMod 2`-algebra on one generator `u_i` in every degree `i > 1` not of
the form `2^r - 1`.

The conclusion reuses the canonical source-facing presentation predicate from Theorem 25.1.3;
this labeled declaration records an actual proposition rather than merely checking the name of
that earlier theorem. -/
theorem thomUnorientedCobordismPolynomialAlgebra_corollary :
    ∃ A : ThomUnorientedCobordismPolynomialAlgebra,
      IsThomUnorientedCobordismPolynomialPresentationOn
        A.toCommRing A.toAlgebra A.generators A.algEquiv := by
  exact exists_thomUnorientedCobordismPolynomialAlgebra
