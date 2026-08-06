import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_11.PolynomialPresentation

noncomputable section

open scoped SingularCohomologyNotation

section BO

variable {R : Type} [CommRing R] [Invertible (2 : R)]
variable {n : ℕ}
variable {BO : Type} [TopologicalSpace BO]
variable {γ : BO → Type}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)]
variable [FiberBundle (Fin n → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)]
variable [∀ b, Module ℝ (γ b)]
variable [RealPlaneBundleClassifyingSpace n BO γ]

/-- Theorem 23.7.11 (1). Over a coefficient ring `R` in which `2` is invertible, for a fixed
canonical singular cohomology algebra structure on `H^*(BO(n); R)` and for a fixed universal
Pontryagin family on `BO(n)`, the cohomology ring admits a polynomial `R`-algebra presentation
on the universal Pontryagin generators in degrees `4 * i`, indexed by `1 ≤ i ≤ ⌊n / 2⌋`. -/
theorem boPontryaginPolynomialPresentation
    [CommRing (H^*(TopCat.of BO; R))] [Algebra R (H^*(TopCat.of BO; R))]
    [IsCanonicalSingularCohomologyAlgebra R (TopCat.of BO)]
    (universalPontryagin : UniversalPontryaginFamily R (TopCat.of BO) n)
    (hUniversalPontryagin : IsUniversalBOPontryaginFamily R BO γ universalPontryagin) :
    ∃ algEquiv : pontryaginPolynomialEquiv R n (TopCat.of BO),
      IsPontryaginPolynomialPresentationOn
        R (TopCat.of BO) n universalPontryagin algEquiv := sorry

end BO

section BSOOdd

variable {R : Type} [CommRing R] [Invertible (2 : R)]
variable {m : ℕ}
variable {ESO : Type} [TopologicalSpace ESO]
variable [MulAction (SO(oddOrientedRank m)) ESO]
variable [ContinuousSMul (SO(oddOrientedRank m)) ESO]

/-- Theorem 23.7.11 (2). Over a coefficient ring `R` in which `2` is invertible, for a fixed
canonical singular cohomology algebra structure on `H^*(BSO(2m + 1); R)` and for a fixed
universal Pontryagin family on that space, the cohomology ring admits a polynomial
`R`-algebra presentation on the universal Pontryagin generators in degrees `4 * i`, indexed by
`1 ≤ i ≤ m`. -/
theorem bsoOddPontryaginPolynomialPresentation
    [CommRing (H^*(TopCat.of BSO[oddOrientedRank m, ESO]; R))]
    [Algebra R (H^*(TopCat.of BSO[oddOrientedRank m, ESO]; R))]
    [IsCanonicalSingularCohomologyAlgebra R (TopCat.of BSO[oddOrientedRank m, ESO])]
    (universalPontryagin :
      UniversalPontryaginFamily R (TopCat.of BSO[oddOrientedRank m, ESO]) (oddOrientedRank m))
    (hUniversalPontryagin : IsUniversalBSOPontryaginFamily R universalPontryagin) :
    ∃ algEquiv :
      pontryaginPolynomialEquiv R (oddOrientedRank m) (TopCat.of BSO[oddOrientedRank m, ESO]),
      IsPontryaginPolynomialPresentationOn
        R (TopCat.of BSO[oddOrientedRank m, ESO]) (oddOrientedRank m)
        universalPontryagin algEquiv := sorry

end BSOOdd

section BSOEven

variable {R : Type} [CommRing R] [Invertible (2 : R)]
variable {m : ℕ+}
variable {ESO : Type} [TopologicalSpace ESO]
variable [MulAction (SO(evenOrientedRank m)) ESO]
variable [ContinuousSMul (SO(evenOrientedRank m)) ESO]

/-- Theorem 23.7.11 (3). Over a coefficient ring `R` in which `2` is invertible, for a fixed
canonical singular cohomology algebra structure on `H^*(BSO(2m); R)`, together with fixed
universal Pontryagin and Euler classes on that space, the cohomology ring admits a polynomial
`R`-algebra presentation on the lower Pontryagin generators `p_i` for `0 < i < m` together with
the Euler generator `e` in degree `2 * m`, and the top Pontryagin generator satisfies the Euler
relation `p_m = e * e`. -/
theorem bsoEvenPontryaginEulerPresentation
    [CommRing (H^*(TopCat.of BSO[evenOrientedRank m, ESO]; R))]
    [Algebra R (H^*(TopCat.of BSO[evenOrientedRank m, ESO]; R))]
    [IsCanonicalSingularCohomologyAlgebra R (TopCat.of BSO[evenOrientedRank m, ESO])]
    (universalPontryagin :
      UniversalPontryaginFamily R (TopCat.of BSO[evenOrientedRank m, ESO]) (evenOrientedRank m))
    (universalEuler : UniversalEulerClass R (TopCat.of BSO[evenOrientedRank m, ESO]) m)
    (hUniversalPontryaginEuler :
      IsUniversalBSOPontryaginEulerFamily R m universalPontryagin universalEuler) :
    ∃ algEquiv :
      evenOrientedPontryaginEulerPolynomialEquiv R m (TopCat.of BSO[evenOrientedRank m, ESO]),
      IsEvenOrientedPontryaginEulerPresentationOn
        R (TopCat.of BSO[evenOrientedRank m, ESO]) m
        universalPontryagin universalEuler algEquiv := sorry

end BSOEven
