import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateDivisibilityProducer

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanReadbackPreservationEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance readbackPreservationEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance readbackPreservationEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pointwise form of the local projective-envelope readback-preservation gap.

This is the minimal non-formal coordinate assertion left after the existing value-side
projective-envelope divisibility theorem: apply the Brauer-coordinate readback to a
projective-envelope regular-restriction row, then each read-back coordinate is still divisible by
the corresponding centralizer `p`-part. -/
def coordinate_normalized_projective_envelope_brauerReadbackCoordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
          (regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
set_option linter.style.longLine false in
/-- The pointwise readback-coordinate divisibility is exactly enough to close the local
`readbackPreserves` statement, without routing through the global forward-stability adapter. -/
theorem
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility_of_brauerReadbackCoordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hreadback_coord :
      coordinate_normalized_projective_envelope_brauerReadbackCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c
  exact
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G) _).2
      (hreadback_coord c)

set_option linter.style.longLine false in
/-- Pointwise Brauer-readback coordinate divisibility gives the cast Cartan-coordinate
regular-value membership needed by the B-side reduction. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_brauerReadbackCoordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hreadback_coord :
      coordinate_normalized_projective_envelope_brauerReadbackCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_readbackPreserves
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P
      (coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility_of_brauerReadbackCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hreadback_coord)

end ProjectiveCartanReadbackPreservationEndpoint

section FullMixedModelProjectiveCartanReadbackPreservationEndpoint

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelReadbackPreservationEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelReadbackPreservationEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
set_option linter.style.longLine false in
/-- Full mixed-model adapter from the local projective-envelope readback-preservation theorem to
the endpoint-facing cast regular-value statement. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_readbackPreserves
    (hreadback :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
            (hπ_simple : ∀ c, Simple (π c))
            (hπ_coord :
              ∀ c,
                regularClassCoordinateAddEquiv
                    (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
                  (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
            (P : PRegularConjClass G p →
              FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G),
            (∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
              asModule (π c).ρ, f.IsProjectiveEnvelope) →
              coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
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
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_readbackPreserves
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P
      (hreadback (A := A) (K := K) e0 π hπ_simple hπ_coord P hP_envelope)

omit [IsAlgClosed k] [CharP k p] in
set_option linter.style.longLine false in
/-- Full mixed-model adapter from the pointwise Brauer-readback coordinate divisibility frontier
to the endpoint-facing cast regular-value statement. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_brauerReadbackCoordinateDivisibility
    (hreadback_coord :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
            ∃ hπ_simple : ∀ c, Simple (π c),
              ∃ hπ_coord :
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
                        coordinate_normalized_projective_envelope_brauerReadbackCoordinateDivisibility
                          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hreadback_coord (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope,
      hreadback_coord⟩
  refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_brauerReadbackCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hreadback_coord

end FullMixedModelProjectiveCartanReadbackPreservationEndpoint

end Representation
