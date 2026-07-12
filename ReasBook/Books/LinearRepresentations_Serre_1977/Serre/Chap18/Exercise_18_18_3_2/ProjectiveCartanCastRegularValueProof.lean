import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanReadbackCoordinateProof

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanCastRegularValueProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanCastRegularValueProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanCastRegularValueProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local cast-row regular-value theorem from the current non-circular readback input.

For a coordinate-normalized complete family with projective envelopes, the fixed Cartan row
`regularIntegerFunctionCast (cartanCoordinateAddHom [P c]ₚ₀)` lies in Serre's regular-value
divisibility lattice once the Brauer-basis readback congruence has been supplied. -/
theorem coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_brauerBasisReadbackInput
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
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_sourceFaithfulRegularValueCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope
      (regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G) hread)

end ProjectiveCartanCastRegularValueProof

section FullMixedModelProjectiveCartanCastRegularValueProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelProjectiveCartanCastRegularValueProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelProjectiveCartanCastRegularValueProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model bridge from the source-faithful regular-value congruence to the cast
regular-value input used by the maximum split.  This does not use any final Cartan range,
cokernel, or product endpoint. -/
theorem fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_sourceFaithfulRegularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
      (p := p) (k := k) (G := G) := by
  exact
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_regularValueCongruence
      (p := p) (k := k) (G := G) hregular

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model bridge from the Brauer-basis readback input to the cast regular-value input
used by the maximum split.  The remaining non-formal obligation is the readback input itself. -/
theorem fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_fullMixedBrauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
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
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope
      (hread (A := A) (K := K) e0)

end FullMixedModelProjectiveCartanCastRegularValueProof

end Representation
