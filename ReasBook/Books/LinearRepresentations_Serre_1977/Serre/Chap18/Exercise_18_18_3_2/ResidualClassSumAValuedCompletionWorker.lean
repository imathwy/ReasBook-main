import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.OrthogonalityResidualDirectCompletionWorker

/-!
Residual class-sum A-valuedness completion boundary for task D.

The unconditional part below is the Exercise 18.4/projective-envelope dual readback: pairing a
projective-envelope row with the inverse prime-to-p indicator is the `A`-basis coefficient of that
indicator, hence is visibly in the image of `A`.

The remaining source API is then isolated one step upstream from
`coordinateNormalizedBrauerBasisResidualClassSumAValued`: after subtracting this projective-dual
coefficient from the residual class-sum coefficient, the result should be `A`-valued.  This file
proves that this smaller residual A-valuedness closes both the class-sum target and the existing
point-mass/pairing-residual targets, without using Cartan cokernel/product/Smith/determinant
endpoints.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ResidualClassSumAValuedCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance residualClassSumAValuedCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance residualClassSumAValuedCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Unconditional Exercise 18.4/projective-envelope dual readback.

The projective-envelope pairing against the inverse prime-to-p indicator is the corresponding
canonical Brauer-basis coefficient, so this part of the class-sum expression is already
`A`-valued. -/
theorem projectiveEnvelopeRegularPairingSum_inversePrimeToPIndicator_AValued
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (c d : PRegularConjClass G p) :
    let f :=
      primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
    ∃ a : A,
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) f =
        algebraMap A K a := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let f :=
    primeToP_regular_indicator
      (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
  refine ⟨(bA.repr f) c, ?_⟩
  simpa [hπ_pairwise, hπ_complete, bA, f, canonicalDVRBrauerBasis] using
    projectiveEnvelopeRegularPairingSum_primeToPIndicator_eq_repr
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope c d

/-- The precise remaining source API after the unconditional projective-dual readback.

For each residual row `b_c - 1_c`, subtract the projective-envelope dual coefficient of the
inverse prime-to-p indicator.  The missing Serre 18.5(a) source input is that this smaller
residual class-sum coefficient is `A`-valued. -/
def coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    let f :=
      primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
    ∃ a : A,
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          (fun e =>
            bA c e -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
          f -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) f =
        algebraMap A K a

/-- The projective-dual residual source API closes the class-sum A-valuedness target. -/
theorem coordinateNormalizedBrauerBasisResidualClassSumAValued_of_projectiveDualResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hdual :
      coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    coordinateNormalizedBrauerBasisResidualClassSumAValued
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  have hdual' :
      ∀ c d : PRegularConjClass G p,
        let f :=
          primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
        ∃ a : A,
          regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
              (fun e =>
                bA c e -
                  ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
              f -
            projectiveEnvelopeRegularPairingSum
              (p := p) (A := A) (K := K) (G := G) (P c) f =
            algebraMap A K a := by
    simpa [coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued,
      hπ_pairwise, hπ_complete, bA] using hdual
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
            (fun e =>
              bA c e -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
          algebraMap A K a
  intro c d
  let f :=
    primeToP_regular_indicator
      (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
  let coeff : A := (bA.repr f) c
  rcases hdual' c d with ⟨a, ha⟩
  have hproj :
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) f =
        algebraMap A K coeff := by
    simpa [hπ_pairwise, hπ_complete, bA, f, coeff, canonicalDVRBrauerBasis] using
      projectiveEnvelopeRegularPairingSum_primeToPIndicator_eq_repr
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  refine ⟨a + coeff, ?_⟩
  calc
    regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
        (fun e =>
          bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))
        =
      (regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          (fun e =>
            bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
          f -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) f) +
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) f := by
          simp [f]
    _ = algebraMap A K a + algebraMap A K coeff := by
          rw [ha, hproj]
    _ = algebraMap A K (a + coeff) := by
          rw [map_add]

/-- The same projective-dual residual source API closes the point-mass source congruence via the
existing class-sum denominator theorem. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_projectiveDualResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hdual :
      coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  exact
    orthogonalityPairingSumPointMassSourceCongruence_of_residualClassSumAValued
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisResidualClassSumAValued_of_projectiveDualResidual
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hdual)

/-- The projective-dual residual source API also closes the fixed-family pairing residual. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveDualResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hdual :
      coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residualClassSumAValued
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisResidualClassSumAValued_of_projectiveDualResidual
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hdual)

end ResidualClassSumAValuedCompletionWorker

end Representation
