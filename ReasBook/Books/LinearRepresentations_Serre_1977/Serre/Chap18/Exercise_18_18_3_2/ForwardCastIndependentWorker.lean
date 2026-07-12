import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ForwardDiagonalWorker

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ForwardCastIndependentWorkerLocal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance forwardCastIndependentWorkerLocalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance forwardCastIndependentWorkerLocalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact readback equality that would independently close the forward cast input.

For each projective-envelope row, the value-side regular restriction is literally the cast of
the fixed Cartan-coordinate row. -/
def coordinate_normalized_projective_envelope_regularRestriction_eq_cartanCoordinateCastReadback
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G) : Prop :=
  ∀ c : PRegularConjClass G p,
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) =
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀)

/-- Exact readback equality is stronger than the cast-membership row input: the value-side
projective-envelope row is already known to lie in Serre's regular-value divisibility lattice. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_regularRestriction_eq_cartanCoordinateCastReadback
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
    (hreadback_eq :
      coordinate_normalized_projective_envelope_regularRestriction_eq_cartanCoordinateCastReadback
        (p := p) (A := A) (K := K) (G := G) P) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro c
  have hrow :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    coordinate_normalized_projective_envelope_regularRestriction_mem_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c
  simpa [hreadback_eq c] using hrow

end ForwardCastIndependentWorkerLocal

section ForwardCastIndependentWorkerFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance forwardCastIndependentWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance forwardCastIndependentWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model form of the exact equality missing from the independent forward-cast route. -/
def fullMixedModelForwardCastProjectiveEnvelopeRegularRestrictionEqCartanCoordinateCastReadbackStatement :
    Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ _hπ_simple : ∀ c, Simple (π c),
          ∃ _hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            ∃ _ : PairwiseNonisomorphic π,
              ∃ _ : IsCompleteIrreducibleFamily π,
                ∃ P : PRegularConjClass G p →
                    FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
                  ∃ _ :
                    ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
                      asModule (π c).ρ, f.IsProjectiveEnvelope,
                    coordinate_normalized_projective_envelope_regularRestriction_eq_cartanCoordinateCastReadback
                      (p := p) (A := A) (K := K) (G := G) P

omit [IsAlgClosed k] [CharP k p] in
/-- The endpoint-facing cast statement is the same row data as the worker's explicit forward
cast/readback preservation statement. -/
theorem
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_projectiveEnvelope_castRegularValue
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hcast (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  simpa [forwardDiagonalWorkerLocalProjectiveEnvelopeCastReadbackPreservation] using hrows

omit [IsAlgClosed k] [CharP k p] in
/-- Source-faithful regular-value congruence is an independent source for the worker's forward
cast/readback input.  The proof uses only the local projective-envelope regular-value bridge,
not a final Cartan range, cokernel, or product endpoint. -/
theorem
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_sourceFaithfulRegularValueCongruence
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
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_sourceFaithfulRegularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The existing Brauer-basis readback input also supplies the worker's forward cast/readback
input through the same source-faithful regular-value bridge. -/
theorem
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_brauerBasisReadbackInput
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
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Exact regular-restriction/readback equality gives the stronger endpoint-facing cast
regular-value statement. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_regularRestriction_eq_cartanCoordinateCastReadback
    (hreadback_eq :
      fullMixedModelForwardCastProjectiveEnvelopeRegularRestrictionEqCartanCoordinateCastReadbackStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hreadback_eq (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hrow_eq⟩
  refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_regularRestriction_eq_cartanCoordinateCastReadback
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hrow_eq

omit [IsAlgClosed k] [CharP k p] in
/-- Exact regular-restriction/readback equality also gives the worker-facing forward cast input. -/
theorem
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_regularRestriction_eq_cartanCoordinateCastReadback
    (hreadback_eq :
      fullMixedModelForwardCastProjectiveEnvelopeRegularRestrictionEqCartanCoordinateCastReadbackStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
      (p := p) (k := k) (G := G) :=
  fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_projectiveEnvelope_castRegularValue
    (p := p) (k := k) (G := G)
    (fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_regularRestriction_eq_cartanCoordinateCastReadback
      (p := p) (k := k) (G := G) hreadback_eq)

end ForwardCastIndependentWorkerFullMixed

end Representation
