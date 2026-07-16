import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CentralizerUnitDenominatorWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PairingFunctionalPointMassRowWorker

/-!
Pairing-functional readout completion boundary.

This file does not close the unconditional Serre `18.5(a)` point-mass congruence.  It records the
sharp local equivalence for the pairing-functional readout and a denominator-cancellation reduction
that matches the remaining class-sum computation: after the projective-envelope functional is
identified with `delta`, the readout is exactly the point-mass row congruence modulo the target
centralizer `p`-part.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PairingFunctionalReadoutCompletionWorker

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

local instance pairingFunctionalReadoutCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pairingFunctionalReadoutCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Converse to the closure theorem in `PairingFunctionalPointMassRowWorker`: once the pure
point-mass source congruence is known, the pairing-functional readout follows by substituting the
projective-envelope functional value `delta`. -/
theorem projectiveEnvelopePairingFunctionalPointMassReadout_of_pointMassSourceCongruence
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
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    projectiveEnvelopePairingFunctionalPointMassReadout
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
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
      ∃ a : A,
        algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum
              (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)
  intro c d
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let z : A := ConjClasses.centralizerPPart p d.1
  rcases hsource c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdelta :
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
        algebraMap A K deltaA := by
    simpa [hπ_pairwise, hπ_complete, bA, deltaA] using
      projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d
  have ha' : bA c d - deltaA = z * a := by
    simpa [orthogonalityPairingSumPointMassSourceCongruence, hπ_pairwise, hπ_complete,
      bA, canonicalDVRBrauerBasis, deltaA, z] using ha
  calc
    algebraMap A K (bA c d) -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c)
        = algebraMap A K (bA c d) - algebraMap A K deltaA := by
            rw [hdelta]
    _ = algebraMap A K (bA c d - deltaA) := by
            simp [map_sub]
    _ = algebraMap A K (z * a) := by
            rw [ha']

/-- Exact fixed-family boundary: the pairing-functional readout is equivalent to the pure
point-mass source congruence.  The forward direction was already available; this theorem packages
the converse proved above. -/
theorem projectiveEnvelopePairingFunctionalPointMassReadout_iff_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    projectiveEnvelopePairingFunctionalPointMassReadout
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P ↔
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  constructor
  · intro hreadout
    exact
      orthogonalityPairingSumPointMassSourceCongruence_of_pairingFunctionalReadout
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hreadout
  · intro hsource
    exact
      projectiveEnvelopePairingFunctionalPointMassReadout_of_pointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hsource

/-- Denominator-cancellation reduction for the desired readout.

It is enough to show that the point-mass row error divided by the full centralizer order is
represented by an element of `A`; the prime-to-`p` denominator is then a unit, so only the
centralizer `p`-part remains. -/
theorem projectiveEnvelopePairingFunctionalPointMassReadout_of_centralizerCardDenominator
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
    (hden :
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
        ∃ coeff : A,
          algebraMap A K coeff =
            algebraMap A K
                (bA c d -
                  ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) *
              (algebraMap A K (ConjClasses.centralizerCard d.1 : A))⁻¹) :
    projectiveEnvelopePairingFunctionalPointMassReadout
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
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
  have hsource :
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
    change
      ∀ c d : PRegularConjClass G p,
        ∃ a : A,
          bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
            (ConjClasses.centralizerPPart p d.1 : A) * a
    intro c d
    let rowDiff : A :=
      bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
    rcases hden c d with ⟨coeff, hcoeff⟩
    have hcoeff' :
        algebraMap A K coeff =
          algebraMap A K rowDiff *
            (algebraMap A K (ConjClasses.centralizerCard d.1 : A))⁻¹ := by
      simpa [hπ_pairwise, hπ_complete, bA, rowDiff] using hcoeff
    simpa [rowDiff] using
      exists_eq_centralizerPPart_mul_of_pairingCoefficient_eq_mul_centralizerCard_inv
        (p := p) (A := A) (K := K) (G := G)
        d (rowDiff := rowDiff) (coeff := coeff) hcoeff'
  exact
    projectiveEnvelopePairingFunctionalPointMassReadout_of_pointMassSourceCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hsource

end PairingFunctionalReadoutCompletionWorker

end Representation
