import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFixedFamilyCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerOrthogonalityReadbackClosureFinal

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

local instance brauerOrthogonalityReadbackClosureFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerOrthogonalityReadbackClosureFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact source-side input still needed after the current Exercise `18.4` orthogonality
API has identified the visible projective-envelope row.

It asks for the remaining point-mass row difference, after subtracting the chosen
projective-envelope regular-restriction row, to satisfy Serre's centralizer-`p`-part
divisibility.  This is the non-Cartan residual formula consumed by
`BrauerBasisReadbackFixedFamilyCompletion`. -/
abbrev regularValueCongruenceSourceFaithfulOrthogonalityAPIInput : Prop :=
  regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
    (p := p) (A := A) (K := K) (G := G)

/-- The current Exercise `18.4`/orthogonality residual input closes the local Brauer-basis
readback input.

The proof chooses the residual family supplied by the input, descends its fraction-field
formula through the existing orthogonality API, and then packages the fixed-family readback
divisibility.  No Cartan range, cokernel, or product endpoint is used. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_orthogonalityAPI
    (horth :
      regularValueCongruenceSourceFaithfulOrthogonalityAPIInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases horth with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hresidual⟩
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveEnvelopeResidualFormula
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope
        (fun c d => hresidual c d))

/-- Conversely, an existing fixed-coordinate readback input supplies the same orthogonality
residual input after choosing projective envelopes for the normalized simple family.

This direction records that the residual input is precisely the remaining source-side datum,
not a consequence of any final Cartan endpoint. -/
theorem regularValueCongruenceSourceFaithfulOrthogonalityAPIInput_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulOrthogonalityAPIInput
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases hread with ⟨π, hπ_simple, hπ_coord, hread⟩
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  have hbasis :
      brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
    brauerPointMassBasisResidualDivisibility_of_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hread
  exact
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hbasis

/-- The orthogonality residual input is equivalent to the requested local readback input.

Thus the minimal missing source lemma can be stated as a proof of
`regularValueCongruenceSourceFaithfulOrthogonalityAPIInput`; the theorem
`regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_orthogonalityAPI`
then closes the endpoint directly. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_orthogonalityAPI :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulOrthogonalityAPIInput
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulOrthogonalityAPIInput_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_orthogonalityAPI
        (p := p) (A := A) (K := K) (G := G)

end BrauerOrthogonalityReadbackClosureFinal

end Representation
