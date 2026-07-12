import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FixedRowReadoutSourceProofWorker

/-!
Projective-orthogonality boundary for the point-mass source blocker.

The available source route evaluates the projective-envelope pairing functional on the
coordinate-normalized Brauer basis as the Kronecker delta.  The exact remaining input is the
fixed-row readout comparison between that pairing functional and ordinary row evaluation,
modulo the centralizer `p`-part.  This file records that this readout input is equivalent to
the requested local and full mixed point-mass source blockers.
-/

set_option linter.style.longLine false

noncomputable section

universe u

namespace Representation

section LocalProjectiveOrthogonalityPointMassCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Local exact boundary for the source route after the projective-envelope orthogonality
readout has supplied the `delta` term. -/
theorem regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_iff_projectiveOrthogonalityReadout :
    regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (A := A) (K := K) (G := G) :=
  (regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker
    (p := p) (A := A) (K := K) (G := G)).symm

/-- Local adapter: the fixed-row projective-orthogonality readout closes the named
point-mass source blocker. -/
theorem regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_sourceProof_of_projectiveOrthogonalityReadout
    (hreadout :
      regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
      (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_iff_projectiveOrthogonalityReadout
    (p := p) (A := A) (K := K) (G := G)).2 hreadout

end LocalProjectiveOrthogonalityPointMassCompletionWorker

section FullMixedProjectiveOrthogonalityPointMassCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact boundary for the source route after the projective-envelope
orthogonality readout has supplied the `delta` term. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_iff_projectiveOrthogonalityReadout :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (k := k) (G := G) :=
  by
    constructor
    · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR
        _instNoetherian _instComplete K _instField _instAlgebra _instFraction
        _instCharZero _instRoots _instAlgClosed _instCharP e0
      exact
        (regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker
          (p := p) (A := A) (K := K) (G := G)).2
          (hblock (A := A) (K := K) e0)
    · intro hreadout A _instComm _instLocal _instHenselian _instDomain _instDVR
        _instNoetherian _instComplete K _instField _instAlgebra _instFraction
        _instCharZero _instRoots _instAlgClosed _instCharP e0
      exact
        (regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker
          (p := p) (A := A) (K := K) (G := G)).1
          (hreadout (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed adapter: the fixed-row projective-orthogonality readout closes the requested
point-mass source blocker. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_sourceProof_of_projectiveOrthogonalityReadout
    (hreadout :
      fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
      (p := p) (k := k) (G := G) :=
  by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulFixedRowPairingFunctionalNontrivialReadoutInput_iff_pointMassSourceBlocker
        (p := p) (A := A) (K := K) (G := G)).1
        (hreadout (A := A) (K := K) e0)

end FullMixedProjectiveOrthogonalityPointMassCompletionWorker

end Representation
