import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFromPairing
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProducer

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveEnvelopeResidualSourceInput

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance projectiveEnvelopeResidualSourceInputFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveEnvelopeResidualSourceInputDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The A-side source input for the projective-envelope residual route.

This is the point-mass residual left after Exercise `18.4` and the projective-envelope
orthogonality row have isolated the visible projective-envelope contribution. -/
def regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord

end ProjectiveEnvelopeResidualSourceInput

section LocalProjectiveEnvelopeResidualSourceWorker

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

local instance projectiveEnvelopeResidualSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveEnvelopeResidualSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family source bridge for Serre `18.5(a)`: the A-side pairing residual, together with
the Exercise `18.4`/orthogonality formula for the projective-envelope row, gives the requested
fraction-field projective-envelope residual. -/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
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
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c d
  rcases hsource c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  calc
    (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
        =
      algebraMap A K
        ((let hπ_pairwise :=
            pairwiseNonisomorphic_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_coord
          let hπ_complete :=
            complete_irreducible_family_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_simple hπ_coord
          let bA :=
            canonicalDVRBrauerBasis
              (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
          bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            (ConjClasses.centralizerPPart p d.1 : A) *
              (bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G)
                  (inversePRegularConjClass (p := p) d)) c))) := by
          simpa using
            canonicalDVRBrauerBasis_projectiveEnvelope_residual_algebraMap_eq
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord P hP_envelope c d
    _ =
      algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
        exact congrArg (algebraMap A K) ha

/-- Existential source input closes the point-mass projective-envelope residual provider after
choosing projective envelopes for the same coordinate-normalized simple family. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
    (hsource :
      regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases hsource with ⟨π, hπ_simple, hπ_coord, hsource⟩
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hsource

end LocalProjectiveEnvelopeResidualSourceWorker

section FullMixedProjectiveEnvelopeResidualSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveEnvelopeResidualSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveEnvelopeResidualSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic form of the A-side source input for the
projective-envelope residual route. -/
def fullMixedModelProjectiveEnvelopeResidualSourceInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsProjectiveEnvelopeResidualSourceInput
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic source bridge from the A-side residual input to the
projective-envelope residual blocker. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_of_pairingResidualSourceInput
    (hsource :
      fullMixedModelProjectiveEnvelopeResidualSourceInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_pairingResidualSourceInput
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

end FullMixedProjectiveEnvelopeResidualSourceWorker

end Representation
