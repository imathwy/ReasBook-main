import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.FixedRowReadbackCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityInputSourceProofWorker

/-!
Source proof boundary for the fixed-row readout input.

The nontrivial fixed-row readout is not a new downstream Cartan assertion.  After applying the
Exercise `18.4` projective-envelope orthogonality readout
`<Phi_E, phi_E'> = delta_EE'`, it is exactly the point-mass row congruence.  The only apparent
difference is that `fixedRowPairingFunctionalNontrivialReadout` asks only for columns with
nontrivial centralizer `p`-part; the omitted columns have `centralizerPPart = 1`, hence are
automatic by taking the row difference itself as the quotient.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalFixedRowReadoutSourceProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance fixedRowReadoutSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fixedRowReadoutSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The existing point-mass source congruence proves the nontrivial fixed-row readout after
substituting the projective-envelope orthogonality functional value. -/
theorem fixedRowPairingFunctionalNontrivialReadout_of_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    fixedRowPairingFunctionalNontrivialReadout
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
      ConjClasses.centralizerPPart p d.1 ≠ 1 →
        ∃ a : A,
          algebraMap A K (bA c d) -
              projectiveEnvelopeRegularPairingSum
                (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
            algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)
  intro c d _hd
  rcases hsource c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdelta :
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
        algebraMap A K
          (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
    simpa [hπ_pairwise, hπ_complete, bA] using
      projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d
  have ha' :
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a := by
    simpa [orthogonalityPairingSumPointMassSourceCongruence, hπ_pairwise, hπ_complete,
      bA, canonicalDVRBrauerBasis] using ha
  calc
    algebraMap A K (bA c d) -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c)
        = algebraMap A K (bA c d) -
            algebraMap A K
              (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
            rw [hdelta]
    _ = algebraMap A K
          (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
            simp [map_sub]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
            rw [ha']

/-- Conversely, the nontrivial fixed-row readout recovers the full point-mass source congruence.
The columns with centralizer `p`-part equal to one are automatic. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_fixedRowPairingFunctionalNontrivialReadout
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hreadout :
      fixedRowPairingFunctionalNontrivialReadout
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
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
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a
  intro c d
  by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
  · refine ⟨bA c d -
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A), ?_⟩
    simp [hd]
  · rcases hreadout c d hd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply IsFractionRing.injective A K
    have hdelta :
        projectiveEnvelopeRegularPairingSum
            (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
          algebraMap A K
            (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
      simpa [hπ_pairwise, hπ_complete, bA] using
        projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord P hP_envelope c d
    calc
      algebraMap A K
          (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
          =
            algebraMap A K (bA c d) -
              projectiveEnvelopeRegularPairingSum
                (p := p) (A := A) (K := K) (G := G) (P d) (bA c) := by
              simp [map_sub, hdelta]
      _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
            simpa [fixedRowPairingFunctionalNontrivialReadout, hπ_pairwise, hπ_complete,
              bA] using ha

/-- Fixed-family exact source boundary: the nontrivial fixed-row readout is equivalent to the
point-mass source congruence isolated by the Exercise `18.4` orthogonality route. -/
theorem fixedRowPairingFunctionalNontrivialReadout_iff_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    fixedRowPairingFunctionalNontrivialReadout
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
  · exact
      orthogonalityPairingSumPointMassSourceCongruence_of_fixedRowPairingFunctionalNontrivialReadout
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope
  · exact
      fixedRowPairingFunctionalNontrivialReadout_of_pointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope

/-- Local existential equivalence with the existing point-mass orthogonality source API. -/
theorem regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker :
    regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hreadout
    rcases hreadout with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hrow⟩
    refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
    exact
      (fixedRowPairingFunctionalNontrivialReadout_iff_pointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).1 hrow
  · intro hblock
    rcases hblock with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hsource⟩
    refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
    exact
      (fixedRowPairingFunctionalNontrivialReadout_iff_pointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).2 hsource

end LocalFixedRowReadoutSourceProofWorker

section FullMixedFixedRowReadoutSourceProofWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedFixedRowReadoutSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedFixedRowReadoutSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact source boundary against the existing point-mass orthogonality source API. -/
theorem fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker :
    fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hreadout A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)).1
        (hreadout (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The fixed-row readout input is also equivalent to the larger named Exercise `18.4`
orthogonality input already used elsewhere. -/
theorem fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_iff_orthogonalityInput :
    fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) := by
  exact
    (fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker
      (p := p) (k := k) (G := G)).trans
      (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_sourceProof_iff_pointMassSourceBlocker
        (p := p) (k := k) (G := G)).symm

end FullMixedFixedRowReadoutSourceProofWorker

end Representation
