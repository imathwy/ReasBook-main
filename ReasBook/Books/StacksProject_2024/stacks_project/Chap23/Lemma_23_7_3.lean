import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_83_2
import StacksProject_2024.stacks_project.Chap23.Lemma_23_7_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped BigOperators

universe uR uR'

attribute [local instance] HasDerivedCategory.standard

/- Semantic search note: `lean_leansearch` did not surface a relevant owner for this obstruction
statement. The final owner choice was verified against local Chapter 15 precedent:
`ModuleHasFiniteTorDimension` for the base-module formulation and
`RingHom.IsPerfectRingMap` for the companion perfect-algebra formulation. -/

section

variable {R : Type uR} {R' : Type uR'} {S : Type uR}
variable [CommRing R] [CommRing R'] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing R']

/-- Lemma 23.7.3: let `R' → R` be a square-zero principal extension of Noetherian rings, let
`S ≃ R[x₁, ..., xₙ] / (f₁, ..., fₘ)`, and suppose a relation `∑ rⱼ fⱼ = 0` whose coefficients lie
in the annihilator ideal of the kernel generator admits lifts `r'ⱼ`, `f'ⱼ`, and `g'` with
`∑ r'ⱼ f'ⱼ = f g'`. If the resulting class of `g'` in `S/IS` is not nilpotent, then `S` does not
have finite tor dimension over `R`. -/
theorem not_moduleHasFiniteTorDimension_of_liftedRelation_obstruction
    (extension : SquareZeroPrincipalExtension R' R)
    {n m : ℕ}
    (rels : Fin m → MvPolynomial (Fin n) R)
    (presentation :
      S ≃ₐ[R]
        MvPolynomial (Fin n) R ⧸ polynomialPresentationIdeal rels)
    (coeffs : Fin m → MvPolynomial (Fin n) R)
    (relation : ∑ j : Fin m, coeffs j * rels j = 0)
    (liftedCoeffs : Fin m → MvPolynomial (Fin n) R')
    (liftedRels : Fin m → MvPolynomial (Fin n) R')
    (lift_coeffs :
      ∀ j : Fin m, MvPolynomial.map extension.toRingHom (liftedCoeffs j) = coeffs j)
    (lift_rels :
      ∀ j : Fin m, MvPolynomial.map extension.toRingHom (liftedRels j) = rels j)
    (gLift : MvPolynomial (Fin n) R')
    (liftedRelation :
      ∑ j : Fin m, liftedCoeffs j * liftedRels j =
        MvPolynomial.C extension.generator * gLift)
    (coeff_mem_annihilator :
      ∀ j : Fin m, ∀ d, MvPolynomial.coeff d (coeffs j) ∈ extension.annihilator)
    (g_not_nilpotent :
      ¬ IsNilpotent (liftedRelationTargetClass extension rels presentation gLift)) :
    ¬ ModuleHasFiniteTorDimension (ModuleCat.of R S) := sorry

/-- The obstruction of Lemma 23.7.3 forces the quotient algebra map `R → S` to fail to be a
perfect ring map. -/
theorem not_isPerfectRingMap_of_liftedRelation_obstruction
    (extension : SquareZeroPrincipalExtension R' R)
    {n m : ℕ}
    (rels : Fin m → MvPolynomial (Fin n) R)
    (presentation :
      S ≃ₐ[R]
        MvPolynomial (Fin n) R ⧸ polynomialPresentationIdeal rels)
    (coeffs : Fin m → MvPolynomial (Fin n) R)
    (relation : ∑ j : Fin m, coeffs j * rels j = 0)
    (liftedCoeffs : Fin m → MvPolynomial (Fin n) R')
    (liftedRels : Fin m → MvPolynomial (Fin n) R')
    (lift_coeffs :
      ∀ j : Fin m, MvPolynomial.map extension.toRingHom (liftedCoeffs j) = coeffs j)
    (lift_rels :
      ∀ j : Fin m, MvPolynomial.map extension.toRingHom (liftedRels j) = rels j)
    (gLift : MvPolynomial (Fin n) R')
    (liftedRelation :
      ∑ j : Fin m, liftedCoeffs j * liftedRels j =
        MvPolynomial.C extension.generator * gLift)
    (coeff_mem_annihilator :
      ∀ j : Fin m, ∀ d, MvPolynomial.coeff d (coeffs j) ∈ extension.annihilator)
    (g_not_nilpotent :
      ¬ IsNilpotent (liftedRelationTargetClass extension rels presentation gLift)) :
    ¬ RingHom.IsPerfectRingMap (algebraMap R S) := sorry

end
