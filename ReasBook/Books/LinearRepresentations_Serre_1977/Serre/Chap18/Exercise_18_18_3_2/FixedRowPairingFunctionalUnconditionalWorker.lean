import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FixedRowReadoutSourceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeProviderFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceClosureWorker

/-!
Fixed-row projective-envelope pairing functional readout route.

The projective-envelope pairing readback already identifies the visible functional with the
point-mass coordinate.  The one-way adapters below keep that route explicit: a projective
character lattice source input, or the equivalent projective-envelope residual blocker, closes
the fixed-row pairing-functional input and then the regular-value source statement.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section FixedRowPairingFunctionalUnconditionalWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-character lattice source theorem closes the fixed-row
projective-envelope pairing-functional readout. -/
theorem fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
      (p := p) (k := k) (G := G) := by
  exact
    (fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_iff_orthogonalityInput
      (p := p) (k := k) (G := G)).2
      ((fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_orthogonalityInput_sourceClosure
        (p := p) (k := k) (G := G)).1 hlattice)

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-envelope residuals close the fixed-row pairing-functional readout through the
projective-character lattice provider. -/
theorem fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_of_projectiveEnvelopeResidualBlocker
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput
      (p := p) (k := k) (G := G) :=
  fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_of_projectiveCharacter_lattice
    (p := p) (k := k) (G := G)
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveEnvelopeResidualBlocker
      (p := p) (k := k) (G := G) hresidual)

omit [IsAlgClosed k] [CharP k p] in
/-- The same projective-character lattice source theorem also reaches the regular-value source
statement via the fixed-row pairing-functional readout adapter. -/
theorem fullMixedModelRegularValueSourceStatement_of_projectiveCharacter_lattice_via_fixedRowPairingFunctional
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement
      (p := p) (k := k) (G := G) :=
  fullMixedModelRegularValueSourceStatement_of_fixedRowPairingFunctionalNontrivialReadout
    (p := p) (k := k) (G := G)
    (fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G) hlattice)

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-envelope residuals reach the regular-value source statement through the same
fixed-row pairing-functional readout route. -/
theorem fullMixedModelRegularValueSourceStatement_of_projectiveEnvelopeResidualBlocker_via_fixedRowPairingFunctional
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement
      (p := p) (k := k) (G := G) :=
  fullMixedModelRegularValueSourceStatement_of_fixedRowPairingFunctionalNontrivialReadout
    (p := p) (k := k) (G := G)
    (fullMixedModelFixedRowPairingFunctionalNontrivialReadoutInput_of_projectiveEnvelopeResidualBlocker
      (p := p) (k := k) (G := G) hresidual)

end FixedRowPairingFunctionalUnconditionalWorker

end Representation
