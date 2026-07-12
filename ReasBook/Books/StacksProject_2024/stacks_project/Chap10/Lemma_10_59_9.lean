import Mathlib
import StacksProject_2024.Chap10.Definition_10_59_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter Ideal IsLocalRing
open scoped Ideal

section

variable {R : Type u} {M : Type v}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

namespace Ideal

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]

-- Source/core/bridge triage:
-- * source-facing: compare eventual Hilbert-Samuel `χ`-polynomials of `M` and a finite-colength
--   submodule `N ⊆ M`;
-- * core/canonical: the owner invariant `hilbertSamuelPolynomialDegree`;
-- * bridge/view: the first theorem is the polynomial-representative comparison, while the second
--   theorem pushes that comparison down to the owner invariant.

-- Proof sketch: apply Lemma 10.59.2 to compare the `χ`-functions of `M` and `N` up to an
-- additive constant and a finite shift. After converting the finite lengths to rational-valued
-- functions, the difference of the two eventual Hilbert-Samuel polynomials is eventually bounded,
-- so elementary polynomial growth shows that `P - P'` has strictly smaller degree than both `P`
-- and `P'`.
/-- Lemma 10.59.9: if `R` is a Noetherian local ring, `I` is an ideal of definition, `M` is a
finite `R`-module of infinite length, and `N ⊆ M` has finite colength, then the difference of any
two Hilbert-Samuel polynomials attached to `χ_{I,M}` and `χ_{I,N}` has degree strictly smaller
than the degree of either polynomial. -/
theorem degree_sub_lt_degree_of_finiteColength
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hM : ¬ IsFiniteLength R M) (hquot : IsFiniteLength R (M ⧸ N))
    {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((χ_ I N n).toNat : ℚ)) :
    (P - P').degree < P.degree ∧ (P - P').degree < P'.degree := sorry

end Ideal

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]

/-- Canonical corollary of Lemma 10.59.9: a finite-colength submodule of an infinite-length finite
module has the same Hilbert-Samuel degree. -/
theorem hilbertSamuelPolynomialDegree_eq_of_finiteColength
    (N : Submodule R M) (hM : ¬ IsFiniteLength R M) (hquot : IsFiniteLength R (M ⧸ N)) :
    hilbertSamuelPolynomialDegree R N = hilbertSamuelPolynomialDegree R M := by
  let P := hilbertSamuelChiPolynomial R M
  let Q := hilbertSamuelChiPolynomial R N
  have hP :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ) :=
    hilbertSamuelChiPolynomial_eventuallyEq R M
  have hQ :
      ∀ᶠ n : ℕ in atTop,
        Q.eval (n : ℚ) = ((χ_(maximalIdeal R) N n).toNat : ℚ) :=
    hilbertSamuelChiPolynomial_eventuallyEq R N
  have hdeg :
      (P - Q).degree < P.degree ∧ (P - Q).degree < Q.degree :=
    Ideal.degree_sub_lt_degree_of_finiteColength (maximalIdeal R)
      Ideal.maximalIdeal_isIdealOfDefinition N hM hquot hP hQ
  rw [hilbertSamuelPolynomialDegree_eq_degree R N hQ,
    hilbertSamuelPolynomialDegree_eq_degree R M hP]
  refine le_antisymm ?_ ?_
  · refine le_of_not_gt ?_
    intro hlt
    exact (Polynomial.degree_sub_eq_right_of_degree_lt hlt).not_lt hdeg.2
  · refine le_of_not_gt ?_
    intro hlt
    exact (Polynomial.degree_sub_eq_left_of_degree_lt hlt).not_lt hdeg.1

end
