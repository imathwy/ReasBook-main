import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.3.56: the textbook elementary symmetric polynomials `Sigma_k` are the canonical
multivariable polynomials `MvPolynomial.esymm`; specialized to `K[X_1, ..., X_n]`, the polynomial
`MvPolynomial.esymm (Fin n) K k` is the sum of all squarefree degree-`k` monomials
`sum_{i_1 < ... < i_k} X_{i_1} ... X_{i_k}`. The textbook's "elementary symmetric polynomials"
are precisely these polynomials for `1 <= k <= n`. -/
recall MvPolynomial.esymm (σ : Type u) (K : Type v) [CommSemiring K] [Fintype σ] (k : ℕ) :
  MvPolynomial σ K

/- The squarefree-monomial expansion in the textbook is the canonical theorem
`MvPolynomial.esymm_eq_sum_monomial`. -/
recall MvPolynomial.esymm_eq_sum_monomial {σ : Type u} {K : Type v} [CommSemiring K] [Fintype σ]
    (k : ℕ) :
    MvPolynomial.esymm σ K k =
      ∑ t ∈ Finset.powersetCard k Finset.univ,
        MvPolynomial.monomial (∑ i ∈ t, Finsupp.single i 1) 1
