import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PrimeToPIndicatorBasisCoefficientWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PairingResidualDirectWorker

/-!
Coefficient-side completion helpers for the inverse prime-to-`p` indicator route.

This file stays on the Exercise `18.4` A-basis / projective-envelope orthogonality route.  It
does not use Cartan range, cokernel, product, determinant, or endpoint arguments.

The available non-circular data closes the coefficient route under the same source input already
used by the direct row proof: the projective-character lattice row congruence.  The stronger
pointwise equality

```
  bA c d - delta_cd =
    centralizerPPart(d) * bA.repr (primeToP_regular_indicator (d^{-1})) c
```

is recorded below as coming from a zero projective-envelope row residual.  That zero residual is
strictly stronger than the divisibility input and is the remaining exact-equality obstruction.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PrimeToPIndicatorCoefficientCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance primeToPIndicatorCoefficientCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance primeToPIndicatorCoefficientCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The proposed exact coefficient readback is stronger than the residual divisibility used by
the point-mass source congruence: it gives the residual with witness `0`. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_of_exact
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hexact :
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
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c)) :
    inversePrimeToPIndicatorCoefficientResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
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
  intro c d
  let z : A := ConjClasses.centralizerPPart p d.1
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
  refine ⟨0, ?_⟩
  have hrow : bA c d - deltaA = z * coeff := by
    simpa [hπ_pairwise, hπ_complete, bA, z, deltaA, coeff] using hexact c d
  calc
    bA c d - deltaA - z * coeff = z * coeff - z * coeff := by
      rw [hrow]
    _ = z * 0 := by
      ring

/-- Projective-character lattice row congruence closes the inverse-indicator coefficient
residual, via the existing Exercise `18.4` pairing residual API. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_of_projectiveCharacter_lattice
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    inversePrimeToPIndicatorCoefficientResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pairingResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice_rows
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hlattice)

/-- Coefficient-route closure of the point-mass source congruence from the
projective-character lattice row congruence. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_projectiveCharacter_lattice_via_inversePrimeToPIndicatorCoefficient
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  classical
  exact
    (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
      (inversePrimeToPIndicatorCoefficientResidualDivisibility_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hlattice)

/-- If the projective-envelope row residual vanishes pointwise in the fraction field, then the
strong exact coefficient readback follows by the Exercise `18.4` readback formula and
fraction-field injectivity. -/
theorem inversePrimeToPIndicatorCoefficientExact_of_projectiveEnvelope_row_exact
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
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
    (hrow :
      ∀ c d : PRegularConjClass G p,
        FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d) :
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
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) := by
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
  change
    ∀ c d : PRegularConjClass G p,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c)
  intro c d
  let z : A := ConjClasses.centralizerPPart p d.1
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
  have hfield :
      (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
          algebraMap A K (bA c d - deltaA - z * coeff) := by
    simpa [hπ_pairwise, hπ_complete, bA, z, deltaA, coeff] using
      (canonicalDVRBrauerBasis_projectiveEnvelope_residual_algebraMap_eq
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  have hmap_zero : algebraMap A K (bA c d - deltaA - z * coeff) = 0 := by
    rw [← hfield]
    rw [hrow c d]
    ring
  have hzero : bA c d - deltaA - z * coeff = 0 := by
    apply IsFractionRing.injective A K
    simpa using hmap_zero
  calc
    bA c d - deltaA = (bA c d - deltaA - z * coeff) + z * coeff := by
      ring
    _ = z * coeff := by
      rw [hzero]
      simp

/-- The same zero-residual hypothesis closes the point-mass congruence through the existing
exact-coefficient API. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_projectiveEnvelope_row_exact
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
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
    (hrow :
      ∀ c d : PRegularConjClass G p,
        FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  classical
  exact
    orthogonalityPairingSumPointMassSourceCongruence_of_inversePrimeToPIndicatorCoefficientExact
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (inversePrimeToPIndicatorCoefficientExact_of_projectiveEnvelope_row_exact
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hrow)

end PrimeToPIndicatorCoefficientCompletionWorker

end Representation
