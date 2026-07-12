import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FixedRowReadbackCompletionWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.SupportValueResidualRowsDirectWorker

/-!
Source proof for the fixed-row projective-envelope pairing functional readout.

The proof stays on the Exercise 18.4 readback route.  For a coordinate-normalized Brauer
family, Exercise 18.4 supplies the row congruence
`bA c d - delta_cd = centralizerPPart(d) * a`.  The projective-envelope pairing functional
has already been identified with the same `delta_cd` by
`projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta`.  Substituting that
readout gives the required field-side congruence for ordinary evaluation minus the
projective-envelope pairing functional.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalFixedRowPairingFunctionalSourceProofWorker

variable {p : Nat}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance fixedRowPairingFunctionalSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fixedRowPairingFunctionalSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family source proof of the nontrivial fixed-row pairing-functional readout.

This is the direct Exercise 18.4 plus projective-envelope-pairing readback calculation:
ordinary evaluation of the canonical DVR Brauer row at `d`, minus the `d`-th
projective-envelope pairing functional applied to that row, is the fraction-field image of a
`centralizerPPart(d)` multiple. -/
theorem fixedRowPairingFunctionalNontrivialReadout_sourceProof_of_exercise18_4PointMassRowCongruenceAPI
    (π : PRegularConjClass G p -> FDRep kA G)
    (hπ_simple : forall c, Simple (π c))
    (hπ_coord :
      forall c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : Int) : PRegularConjClass G p -> Int))
    (P : PRegularConjClass G p -> FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      forall c, exists f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hrow :
      exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
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
  have hsource :
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
    simpa [exercise18_4PointMassRowCongruenceAPI, hπ_pairwise, hπ_complete] using hrow
  change
    forall c d : PRegularConjClass G p,
      ConjClasses.centralizerPPart p d.1 ≠ 1 ->
        exists a : A,
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
          (((Pi.single c (1 : Int) : PRegularConjClass G p -> Int) d : A)) := by
    simpa [hπ_pairwise, hπ_complete, bA] using
      projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d
  have ha' :
      bA c d -
          ((Pi.single c (1 : Int) : PRegularConjClass G p -> Int) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a := by
    simpa [orthogonalityPairingSumPointMassSourceCongruence, hπ_pairwise, hπ_complete,
      bA, canonicalDVRBrauerBasis] using ha
  calc
    algebraMap A K (bA c d) -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P d) (bA c)
        = algebraMap A K (bA c d) -
            algebraMap A K
              (((Pi.single c (1 : Int) : PRegularConjClass G p -> Int) d : A)) := by
            rw [hdelta]
    _ = algebraMap A K
          (bA c d -
            ((Pi.single c (1 : Int) : PRegularConjClass G p -> Int) d : A)) := by
            simp [map_sub]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
            rw [ha']

/-- Local existential source proof from the Exercise 18.4 row theorem. -/
theorem regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_sourceProof_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := kA) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, P, hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    fixedRowPairingFunctionalNontrivialReadout_sourceProof_of_exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope (hsource π hπ_simple hπ_coord)

end LocalFixedRowPairingFunctionalSourceProofWorker

section FullMixedFixedRowPairingFunctionalSourceProofWorker

variable {p : Nat}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedFixedRowPairingFunctionalSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedFixedRowPairingFunctionalSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed source proof from the full mixed Exercise 18.4 row theorem. -/
theorem fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_sourceProof_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_sourceProof_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed source proof from the literal support/value row source package, routed through
the Exercise 18.4 row theorem and then the pairing-functional readout calculation above. -/
theorem fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_sourceProof_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_sourceProof_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G)
      (exercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)
        (hsource (A := A) (K := K) e0))

omit [IsAlgClosed k] [CharP k p] in
/-- Integration form: once the full mixed Exercise 18.4 row source theorem supplies the
fixed-row readout, the existing fixed-row adapter closes the regular-value source statement. -/
theorem fullMixedModelRegularValueSourceStatement_sourceProof_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement
      (p := p) (k := k) (G := G) := by
  apply fullMixedModelRegularValueSourceStatement_of_fixedRowPairingFunctionalNontrivialReadout
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_sourceProof_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The same integration form starting from the source-text support/value row package. -/
theorem fullMixedModelRegularValueSourceStatement_sourceProof_of_sourceTextSupportValueAPI
    (hsource :
      fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement
      (p := p) (k := k) (G := G) := by
  apply fullMixedModelRegularValueSourceStatement_of_fixedRowPairingFunctionalNontrivialReadout
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_sourceProof_of_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (K := K) (G := G)
      (exercise18_4PointMassRowCongruenceSourceTheorem_of_sourceTextSupportValueAPI
        (p := p) (A := A) (K := K) (G := G)
        (hsource (A := A) (K := K) e0))

end FullMixedFixedRowPairingFunctionalSourceProofWorker

end Representation
