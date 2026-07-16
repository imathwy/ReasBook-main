import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ForwardDiagonalWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanReadbackCoordinateProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateDivisibilityProducer
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ForwardCastMembershipWorkerLocal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance forwardCastMembershipWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance forwardCastMembershipWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The faithful local bridge for the forward/cast branch.

It does not assert the generally too-strong exact equality between the projective regular
restriction and the cast Cartan-coordinate row.  The exact statement needed by the worker is
equivalent to their congruence modulo Serre's regular-value divisibility lattice. -/
theorem forwardCastMembershipWorker_localMembership_iff_regularRestriction_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope) :
    forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation
        (p := p) (A := A) (K := K) (G := G) P ↔
      coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P := by
  simpa [forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation] using
    (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope)

/-- Local cast membership from the weaker regular-value congruence bridge. -/
theorem forwardCastMembershipWorker_localMembership_of_regularRestriction_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hcong :
      coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P) :
    forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation
        (p := p) (A := A) (K := K) (G := G) P :=
  (forwardCastMembershipWorker_localMembership_iff_regularRestriction_congruence
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord P hP_envelope).2 hcong

/-- Source-faithful regular-value congruence supplies the local cast-membership rows directly. -/
theorem forwardCastMembershipWorker_localMembership_of_regularValueCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation
        (p := p) (A := A) (K := K) (G := G) P := by
  simpa [forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation] using
    (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_sourceFaithfulRegularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hregular)

/-- Local Brauer-basis readback input supplies the forward/cast membership rows through the
source-faithful congruence API. -/
theorem forwardCastMembershipWorker_localMembership_of_brauerBasisReadbackInput
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation
        (p := p) (A := A) (K := K) (G := G) P :=
  forwardCastMembershipWorker_localMembership_of_regularValueCongruence
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord P hP_envelope
    (regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hread)

end ForwardCastMembershipWorkerLocal

section ForwardCastMembershipWorkerFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedForwardCastMembershipWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedForwardCastMembershipWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model provider from the source-faithful regular-value congruence to the worker's
projective-envelope cast/readback preservation statement. -/
theorem forwardCastMembershipWorker_fullStatement_of_regularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    forwardCastMembershipWorker_localMembership_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model provider from the Brauer-basis readback input to the worker's
projective-envelope cast/readback preservation statement. -/
theorem forwardCastMembershipWorker_fullStatement_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    forwardCastMembershipWorker_localMembership_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (hread (A := A) (K := K) e0)

end ForwardCastMembershipWorkerFullMixed

end Representation
