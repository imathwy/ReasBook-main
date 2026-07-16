import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassProjectiveRowsProviderFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackInputCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectCompletionWorker

/-!
Alternative source boundary for point-mass projective rows.

This file stays on the Serre `18.5(a)` source side.  It records that the
projective-envelope residual source input is exactly the same remaining datum as the
nontrivial Brauer-character row congruence, and then transports that boundary to the
point-mass projective-row input and the explicit projective-restriction witness.

No Cartan cokernel/product/Smith endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRowAlternativeSourceWorker

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

local instance pointMassProjectiveRowAlternativeSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRowAlternativeSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The projective-envelope residual source input is exactly the existential nontrivial
Brauer-character row congruence for the same coordinate-normalized family. -/
theorem regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput :
    regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G) := by
  constructor
  · rintro ⟨π, hπ_simple, hπ_coord, hresidual⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    have hpoint :
        coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialBrauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hresidual
    simpa [fixedCoordinateBrauerCharacterNontrivialReadbackCongruence,
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence] using hpoint
  · rintro ⟨π, hπ_simple, hπ_coord, hchar⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    have hpoint :
        coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π := by
      simpa [fixedCoordinateBrauerCharacterNontrivialReadbackCongruence,
        coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence] using hchar
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialBrauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint

/-- The projective-envelope residual source input supplies the point-mass projective-row input
without using any downstream Cartan endpoint. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidualSourceInput
    (hsource :
      regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidual
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
      (p := p) (A := A) (K := K) (G := G) hsource)

/-- Exact local boundary: point-mass projective rows are equivalent to the A-side
projective-envelope residual source input. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput :
    regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hrows
    have hread :
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
          (p := p) (A := A) (G := G) :=
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassProjectiveRows
        (p := p) (A := A) (K := K) (G := G) hrows
    have hchar :
        regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
          (p := p) (A := A) (G := G) :=
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G) hread
    exact
      (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)).2 hchar
  · exact
      regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (K := K) (G := G)

/-- Local nontrivial Brauer-row form of the point-mass projective-row input. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_iff_brauerCharacterNontrivialReadbackInput :
    regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G) :=
  (regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
    (p := p) (A := A) (K := K) (G := G)).trans
    (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G))

/-- The explicit projective-restriction witness is equivalent to the same residual source
input. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_projectiveEnvelopeResidualSourceInput :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G) :=
  (regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)).symm.trans
    (regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
      (p := p) (A := A) (K := K) (G := G))

/-- The existential projective-envelope residual blocker has the same source boundary. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_projectiveEnvelopeResidualSourceInput :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hresidual
    have hbasis :
        regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
          (p := p) (A := A) (G := G) :=
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)).1 hresidual
    have hread :
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
          (p := p) (A := A) (G := G) :=
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_basisResidual
        (p := p) (A := A) (G := G)).2 hbasis
    have hchar :
        regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
          (p := p) (A := A) (G := G) :=
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G) hread
    exact
      (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)).2 hchar
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
        (p := p) (A := A) (K := K) (G := G)

/-- Projective-envelope residuals and point-mass projective rows are equivalent after opening
the same source-side residual datum. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualDivisibility :
    regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) :=
  (regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
    (p := p) (A := A) (K := K) (G := G)).trans
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_projectiveEnvelopeResidualSourceInput
      (p := p) (A := A) (K := K) (G := G)).symm

end LocalPointMassProjectiveRowAlternativeSourceWorker

section FullMixedPointMassProjectiveRowAlternativeSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveRowAlternativeSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveRowAlternativeSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed version of the equivalence between the projective-envelope residual source input
and the nontrivial Brauer-character row congruence. -/
theorem fullMixedModelProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput :
    fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hsource A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)).1
        (hsource (A := A) (K := K) e0)
  · intro hchar A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)).2
        (hchar (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed point-mass projective rows are equivalent to the projective-envelope residual
source input. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hrows A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (K := K) (G := G)).1
        (hrows (A := A) (K := K) e0)
  · intro hsource A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (K := K) (G := G)).2
        (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed nontrivial Brauer-row form of the point-mass projective-row input. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_brauerCharacterNontrivialReadbackInput :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelProjectiveEnvelopeResidualSourceInput_iff_brauerCharacterNontrivialReadbackInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed explicit projective-restriction witnesses are equivalent to the same
projective-envelope residual source input. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_iff_projectiveEnvelopeResidualSourceInput :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveRestrictionWitnessBlocker
    (p := p) (k := k) (G := G)).symm.trans
    (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed projective-envelope residual blockers are equivalent to the source residual
input. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_projectiveEnvelopeResidualSourceInput :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hresidual A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_projectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (K := K) (G := G)).1
        (hresidual (A := A) (K := K) e0)
  · exact
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_of_pairingResidualSourceInput
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed projective-envelope residual blockers and point-mass projective rows have the
same source-side content. -/
theorem fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualBlocker :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveEnvelopeResidualSourceInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_projectiveEnvelopeResidualSourceInput
      (p := p) (k := k) (G := G)).symm

end FullMixedPointMassProjectiveRowAlternativeSourceWorker

end Representation
