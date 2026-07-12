import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveEnvelopeOrthogonalityWorker

variable {p : Nat}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance projectiveEnvelopeOrthogonalityWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveEnvelopeOrthogonalityWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- A fixed-family pairing residual is exactly enough to construct the existential
projective-envelope residual provider.  This file records the non-Cartan route: choose projective
envelopes for the same coordinate-normalized family, then use the existing orthogonality descent
from the pure `A`-side residual to the fraction-field projective-envelope residual. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_fixedFamilyPairingResidual_worker
    (pi : PRegularConjClass G p -> FDRep k G)
    (hpi_simple : forall c, Simple (pi c))
    (hpi_coord :
      forall c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([pi c]₀ : R₀[k](G)) =
          (Pi.single c (1 : Int) : PRegularConjClass G p -> Int))
    (hpair :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) pi hpi_simple hpi_coord) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  have hbasis :
      brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) pi hpi_simple hpi_coord :=
    brauerPointMassBasisResidualDivisibility_of_coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) pi hpi_simple hpi_coord hpair
  have hP_exists :
      forall c : PRegularConjClass G p,
        exists P : FiniteProjectiveGroupAlgebraModule k G,
          exists f : P.V →ₗ[k[G]] asModule (pi c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (pi c) := hpi_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := pi c)
  choose P hP_envelope using hP_exists
  refine ⟨pi, hpi_simple, hpi_coord, P, hP_envelope, ?_⟩
  exact
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      pi hpi_simple hpi_coord P hP_envelope hbasis

/-- The projective-envelope residual provider and the existential pairing residual are the same
local missing datum.  The equivalence uses only the existing Exercise `18.4`/orthogonality
alignment with the pure basis residual. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_existsPairingResidualProof_worker :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) <->
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hresidual
    exact
      (regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_basisResidual
        (p := p) (A := A) (G := G)).2
        ((regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
          (p := p) (A := A) (K := K) (G := G)).1 hresidual)
  · intro hpair
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)).2
        ((regularValueCongruenceSourceFaithfulExistsPairingResidualProof_iff_basisResidual
          (p := p) (A := A) (G := G)).1 hpair)

include K

/-- If the missing existential pairing residual is supplied, the projective-envelope provider route
bridges it to the fixed-coordinate Brauer-basis readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_existsPairingResidualProof_via_projectiveEnvelope_worker
    (hpair :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  have hprovider :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) :=
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_existsPairingResidualProof_worker
      (p := p) (A := A) (K := K) (G := G)).2 hpair
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_existsPairingResidualProof
      (p := p) (A := A) (G := G)
      ((regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_existsPairingResidualProof_worker
        (p := p) (A := A) (K := K) (G := G)).1 hprovider)

/-- Fixed-family version of the same bridge, useful once the pointwise residual lemma is proved for
one coordinate-normalized complete family. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyPairingResidual_via_projectiveEnvelope_worker
    (pi : PRegularConjClass G p -> FDRep k G)
    (hpi_simple : forall c, Simple (pi c))
    (hpi_coord :
      forall c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([pi c]₀ : R₀[k](G)) =
          (Pi.single c (1 : Int) : PRegularConjClass G p -> Int))
    (hpair :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) pi hpi_simple hpi_coord) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  have hprovider :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) :=
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_fixedFamilyPairingResidual_worker
      (p := p) (A := A) (K := K) (G := G)
      pi hpi_simple hpi_coord hpair
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_existsPairingResidualProof
      (p := p) (A := A) (G := G)
      ((regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_existsPairingResidualProof_worker
        (p := p) (A := A) (K := K) (G := G)).1 hprovider)

end LocalProjectiveEnvelopeOrthogonalityWorker

section FullMixedProjectiveEnvelopeOrthogonalityWorker

variable {p : Nat}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveEnvelopeOrthogonalityWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveEnvelopeOrthogonalityWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model form: the projective-envelope residual blocker is equivalent to the
existential pairing-residual blocker. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_existsPairingResidualBlocker_worker :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) <->
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_basisResidualDivisibilityBlocker
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisExistsPairingResidualBlocker_iff_basisResidualDivisibilityBlocker
      (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model readback bridge from a projective-envelope residual blocker, routed through the
same pairing residual equivalence. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_projectiveEnvelopeResidualBlocker_via_pairing_worker
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hpair :
      regularValueCongruenceSourceFaithfulExistsPairingResidualProof
        (p := p) (A := A) (G := G) :=
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_existsPairingResidualProof_worker
      (p := p) (A := A) (K := K) (G := G)).1
      (hresidual (A := A) (K := K) e0)
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_existsPairingResidualProof
      (p := p) (A := A) (G := G) hpair

end FullMixedProjectiveEnvelopeOrthogonalityWorker

end Representation
