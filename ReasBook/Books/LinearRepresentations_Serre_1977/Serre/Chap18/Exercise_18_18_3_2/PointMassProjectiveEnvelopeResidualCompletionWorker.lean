import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualMatrixClosureFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualSourceWorker

/-!
Projective-envelope residual completion worker.

This file keeps the route at the Serre `18.4` / `18.5(a)` source boundary.  It does not use
Cartan range, cokernel, determinant, or product endpoints: the projective-envelope residual
target is compressed to the fixed-coordinate Brauer readback source input.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveEnvelopeResidualCompletionWorker

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

local instance pointMassProjectiveEnvelopeResidualCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveEnvelopeResidualCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Existential visible-readback source input for the projective-envelope residual route. -/
def regularValueCongruenceSourceFaithfulExistsVisibleReadbackDivisibility : Prop :=
  exists pi : PRegularConjClass G p -> FDRep kA G,
    exists hpi_simple : forall c, Simple (pi c),
      exists hpi_coord :
        forall c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([pi c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : Int) : PRegularConjClass G p -> Int),
        coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
          (p := p) (A := A) (G := G) pi hpi_simple hpi_coord

/-- Visible readback closes the requested projective-envelope residual by first producing the
Serre `18.4` A-side pairing residual, then applying the projective-envelope residual source
bridge. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_visibleReadback_worker
    (hvisible :
      regularValueCongruenceSourceFaithfulExistsVisibleReadbackDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hvisible with ⟨pi, hpi_simple, hpi_coord, hvisible⟩
  refine
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
      (p := p) (A := A) (K := K) (G := G) ?_
  refine ⟨pi, hpi_simple, hpi_coord, ?_⟩
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_of_visibleReadback
      (p := p) (A := A) (G := G) pi hpi_simple hpi_coord hvisible

/-- Exact local boundary with the visible-readback source input. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_visibleReadback_worker :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) <->
      regularValueCongruenceSourceFaithfulExistsVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hresidual
    rcases
        (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
          (p := p) (A := A) (K := K) (G := G)).1 hresidual with
      ⟨pi, hpi_simple, hpi_coord, hbasis⟩
    refine ⟨pi, hpi_simple, hpi_coord, ?_⟩
    have hpair :
        coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) pi hpi_simple hpi_coord :=
      coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) pi hpi_simple hpi_coord hbasis
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback
        (p := p) (A := A) (G := G) pi hpi_simple hpi_coord).1 hpair
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_visibleReadback_worker
        (p := p) (A := A) (K := K) (G := G)

/-- The existing fixed-coordinate Brauer-basis readback input closes the projective-envelope
residual target without passing through any Cartan/product endpoint. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_brauerBasisReadbackInput_worker
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  have hpair :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) :=
    (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPairingResidualProof
      (p := p) (A := A) (G := G)).1 hread
  refine
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
      (p := p) (A := A) (K := K) (G := G) ?_
  rcases hpair with ⟨pi, hpi_simple, hpi_coord, hpair⟩
  exact ⟨pi, hpi_simple, hpi_coord, hpair⟩

/-- Exact local boundary: the requested projective-envelope residual provider is equivalent to
the fixed-coordinate Brauer-basis readback source input. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_brauerBasisReadbackInput_worker :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) <->
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hresidual
    have hbasis :
        regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
          (p := p) (A := A) (G := G) :=
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)).1 hresidual
    exact
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_basisResidual
        (p := p) (A := A) (G := G)).2 hbasis
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_brauerBasisReadbackInput_worker
        (p := p) (A := A) (K := K) (G := G)

end LocalPointMassProjectiveEnvelopeResidualCompletionWorker

section FullMixedPointMassProjectiveEnvelopeResidualCompletionWorker

variable {p : Nat}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveEnvelopeResidualCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveEnvelopeResidualCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed version of the visible-readback source blocker. -/
def fullMixedModelPointMassProjectiveEnvelopeResidualVisibleReadbackBlocker : Prop :=
  forall {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k ->
      regularValueCongruenceSourceFaithfulExistsVisibleReadbackDivisibility
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed visible-readback source input closes the requested full mixed
projective-envelope residual blocker. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_of_visibleReadback_worker
    (hvisible :
      fullMixedModelPointMassProjectiveEnvelopeResidualVisibleReadbackBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_visibleReadback_worker
      (p := p) (A := A) (K := K) (G := G)
      (hvisible (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Exact full mixed boundary with the visible-readback source input. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_visibleReadback_worker :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) <->
      fullMixedModelPointMassProjectiveEnvelopeResidualVisibleReadbackBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hresidual A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_visibleReadback_worker
        (p := p) (A := A) (K := K) (G := G)).1
        (hresidual (A := A) (K := K) e0)
  · exact
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_of_visibleReadback_worker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed Brauer-basis readback input closes the requested full mixed
projective-envelope residual blocker. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_of_brauerBasisReadbackInput_worker
    (hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_brauerBasisReadbackInput_worker
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Exact full mixed boundary: the projective-envelope residual blocker is the same remaining
source obligation as the fixed-coordinate Brauer-basis readback input. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_brauerBasisReadbackInput_worker :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) <->
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · intro hresidual A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_brauerBasisReadbackInput_worker
        (p := p) (A := A) (K := K) (G := G)).1
        (hresidual (A := A) (K := K) e0)
  · exact
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_of_brauerBasisReadbackInput_worker
        (p := p) (k := k) (G := G)

end FullMixedPointMassProjectiveEnvelopeResidualCompletionWorker

end Representation
