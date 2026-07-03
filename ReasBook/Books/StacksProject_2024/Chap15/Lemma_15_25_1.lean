import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import StacksProject_2024.Chap15.Remark_15_25_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u w

section

variable {R : Type u} [CommRing R]
variable (n : ℕ)
variable {M : Type w} [AddCommGroup M]
variable [Module (MvPolynomial (Fin n) R) M] [Module R M]
variable [IsScalarTower R (MvPolynomial (Fin n) R) M]
variable [Module.Finite (MvPolynomial (Fin n) R) M] [Module.Flat R M]

/- Domain-style sampling:
* primary domain: finite-presentation descent for flat finite modules over polynomial algebras from
  prime-local finite-presentation data;
* sampled owner declarations:
  - `Module.FinitePresentation`,
  - `module_finitePresentation_of_localizationAway`,
  - `primeLocalizationsDetectEquality`,
  - `MvPolynomial.algebraTensorAlgEquiv`,
  - the chapter-local weighted graded specialization
    `finitePresentation_of_local_flat_finite_weighted_graded_mvPolynomial_module`;
* best owner abstraction: the canonical predicate
  `Module.FinitePresentation (MvPolynomial (Fin n) R) M`;
* primitive data: the polynomial-module structure on `M`, finite generation over
  `MvPolynomial (Fin n) R`, flatness over `R`, and the prime-local tensor-product base changes
  `((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M`;
* derived API: only the global finite-presentation conclusion.

Source/core/bridge triage:
* `source-facing`: the descent theorem below;
* `core/canonical`: `Module.FinitePresentation` together with the localization owners behind
  tensor-product base change;
* `bridge/view`: `MvPolynomial.algebraTensorAlgEquiv`, identifying the tensor-base-change algebra
  `Localization.AtPrime p.asIdeal ⊗[R] MvPolynomial (Fin n) R` with the textbook polynomial ring
  `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`.
-/

-- Proof sketch: choose a finite presentation of `M` by a finite free `S`-module and let `K` be the
-- kernel. Use the local finite-presentation hypotheses to find a finitely generated submodule of
-- `K` that agrees with `K` after passing to the prime-local tensor-product base changes over
-- `Localization.AtPrime p.asIdeal ⊗[R] MvPolynomial (Fin n) R`, equivalently over
-- `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`, at the distinguished finitely
-- many primes and at the prime under a chosen prime of `S`. Replace `M` by the resulting
-- finite-presentation quotient,
-- use openness of flatness to preserve `R`-flatness after inverting one element of `S`, and then
-- apply injectivity of `R → ∏ R_{p_j}` together with flatness to deduce the quotient map is an
-- isomorphism after localizing away from that element. Conclude by the standard local criterion for
-- finite presentation.
/-- Lemma 15.25.1: let `S = R[x₁, …, xₙ]` and let `M` be a finite `S`-module that is flat over
`R` via the restricted scalar action along `R → S`. If there is a finite family of primes of `R`
whose product of localizations detects equality in `R`, and if for every prime `p` of `R` the
canonical tensor-product base change
`((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M`,
equivalently the textbook localized module over `Rₚ[x₁, …, xₙ]`, is of finite presentation over
`(Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R`, then `M` is of finite
presentation over `S`. -/
theorem finitePresentation_of_flat_of_localized_finitePresentation
    (hdetect : primeLocalizationsDetectEquality R)
    (hloc :
      ∀ p : PrimeSpectrum R,
        Module.FinitePresentation
          ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
          (((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := sorry

end
