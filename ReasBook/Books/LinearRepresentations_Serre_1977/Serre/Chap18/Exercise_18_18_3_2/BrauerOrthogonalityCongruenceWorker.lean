import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFromPairing
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityResidualMicroWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerOrthogonalityCongruenceWorker

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

local instance brauerOrthogonalityCongruenceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerOrthogonalityCongruenceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Reverse bridge for `OrthogonalityResidualMicroWorker`: once the pure `A`-side basis residual
is known, the explicit Serre pairing-sum congruence follows by replacing the two visible pairing
sums with the projective-envelope orthogonality value and the Exercise `18.4` coefficient
readback.  This is the converse direction to
`basisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence`. -/
theorem orthogonalityPairingSumResidualCongruence_of_basisResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hresidual :
      let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
      let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
      let bA :=
        exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
          (p := p) (A := A) liftA hliftA
          (residue_primeToPRoot_canonicalLift (p := p) (A := A))
          π hπ_pairwise hπ_complete
      ∀ c d : PRegularConjClass G p,
        ∃ a : A,
          bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            (ConjClasses.centralizerPPart p d.1 : A) *
              (bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G)
                  (inversePRegularConjClass (p := p) d)) c) =
            (ConjClasses.centralizerPPart p d.1 : A) * a) :
    orthogonalityPairingSumResidualCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
  classical
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c) (bA d) -
          algebraMap A K (ConjClasses.centralizerPPart p d.1 : A) *
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c)
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)
  intro c d
  rcases hresidual c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  let z : A := ConjClasses.centralizerPPart p d.1
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d))) c
  have hdelta :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c) (bA d) =
        algebraMap A K deltaA := by
    simpa [liftA, hliftA, bA, deltaA] using
      projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have hcoeff :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c)
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G)
            (inversePRegularConjClass (p := p) d)) =
        algebraMap A K coeff := by
    simpa [liftA, hliftA, bA, coeff] using
      projectiveEnvelopeRegularPairingSum_primeToPIndicator_eq_repr
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have ha' : bA c d - deltaA - z * coeff = z * a := by
    simpa [liftA, hliftA, bA, z, deltaA, coeff] using ha
  have hmap : algebraMap A K (bA c d - deltaA - z * coeff) =
      algebraMap A K (z * a) := by
    exact congrArg (fun x : A => algebraMap A K x) ha'
  calc
    algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) -
        algebraMap A K z *
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c)
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d))
        =
      algebraMap A K (bA c d) - algebraMap A K deltaA -
        algebraMap A K z * algebraMap A K coeff := by
          rw [hdelta, hcoeff]
    _ = algebraMap A K (bA c d - deltaA - z * coeff) := by
          simp [map_sub, map_mul]
    _ = algebraMap A K (z * a) := hmap

/-- Coordinate-normalized provider for the explicit pairing-sum congruence, conditional only on
the already-isolated pure `A`-side pairing residual.  Thus the pairing-sum frontier is not a new
gap: after Exercise `18.4` and `<Φ_E, φ_E'> = δ`, it is exactly the same residual used by the
readback route. -/
theorem orthogonalityPairingSumResidualCongruence_of_coordinateNormalizedPairingResidual
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
    (hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumResidualCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  exact
    orthogonalityPairingSumResidualCongruence_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope
      (by
        simpa [coordinateNormalizedBrauerBasisPairingResidualDivisibility,
          canonicalDVRBrauerBasis, hπ_pairwise, hπ_complete] using hresidual)

/-- For a coordinate-normalized family with chosen projective envelopes, the explicit pairing-sum
congruence is equivalent to the pure `A`-side pairing residual.  The forward direction is
`coordinateNormalizedBasisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence`;
the reverse direction is the worker theorem above. -/
theorem orthogonalityPairingSumResidualCongruence_iff_coordinateNormalizedPairingResidual
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
    (let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) ↔
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hcongr
    have hpoint :=
      coordinateNormalizedBasisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hcongr
    simpa [coordinateNormalizedBrauerBasisPairingResidualDivisibility,
      canonicalDVRBrauerBasis] using hpoint
  · exact
      orthogonalityPairingSumResidualCongruence_of_coordinateNormalizedPairingResidual
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope

end BrauerOrthogonalityCongruenceWorker

end Representation
