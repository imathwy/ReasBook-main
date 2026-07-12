import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassResidualProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassRegularValueSourceProof
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ExplicitResidualRegularValueRowsWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceClosureWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceProjectiveCharacter

/-!
Existing-API closure audit for the full mixed point-mass coordinate blocker.

The declarations below are a closure map, not an unconditional source proof.  They record that
the current non-Cartan APIs identify the point-mass coordinate blocker with the explicit residual
row, readback, projective-envelope residual, and projective-character lattice formulations.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section FullMixedPointMassCoordinateExistingAPIClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassCoordinateExistingAPIClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassCoordinateExistingAPIClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The existing projective-envelope residual blocker is exactly the point-mass coordinate
blocker.  This is an equivalence, so it does not provide a new source proof. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_projectiveEnvelopeResidual_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_coordinateDivisibilityBlocker
    (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- The pure basis-residual blocker is another equivalent spelling of the same obligation. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_basisResidual_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_projectiveEnvelopeResidual_existingAPIClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_basisResidualDivisibilityBlocker
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Direct point-mass rows are equivalent to the coordinate blocker through the existing
regular-value witness/readback API. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_pointMassRows_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_coordinateDivisibility
        (p := p) (k := k) (G := G)
  · intro hrows
    exact
      fullMixedModelPointMassCoordinateBlocker_of_regularValueWitnessBlocker
        (p := p) (k := k) (G := G)
        ((fullMixedModelPointMassRegularValueWitnessBlocker_iff_pointMassRowsInRegularValueSubmoduleInput
          (p := p) (k := k) (G := G)).2 hrows)

omit [IsAlgClosed k] [CharP k p] in
/-- The literal explicit residual-row blocker is equivalent to the coordinate blocker. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_explicitResidualRows_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelExplicitResidualRowsBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_pointMassRows_existingAPIClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_explicitResidualRows
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Conditional non-Cartan provider: explicit residual rows close the coordinate blocker, but
the previous theorem shows that this hypothesis is equivalent to the blocker itself. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_of_explicitResidualRows_existingAPIClosure
    (hrows :
      fullMixedModelExplicitResidualRowsBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
      (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_explicitResidualRows_existingAPIClosure
    (p := p) (k := k) (G := G)).2 hrows

omit [IsAlgClosed k] [CharP k p] in
/-- The point-mass regular-value witness blocker is equivalent to the coordinate blocker. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_regularValueWitness_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_pointMassRows_existingAPIClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRegularValueWitnessBlocker_iff_pointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- Brauer-basis readback is equivalent to the coordinate blocker through the regular-value
witness bridge. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_brauerBasisReadback_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_regularValueWitness_existingAPIClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRegularValueWitnessBlocker_iff_readbackInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-character lattice congruence is equivalent to the coordinate blocker in the
current source-side API. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_projectiveCharacterLattice_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacter_lattice_iff_pointMassCoordinateDivisibilityBlocker
    (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-restriction witnesses are also equivalent to the coordinate blocker through the
projective-character lattice closure. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_projectiveRestrictionWitness_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_projectiveCharacterLattice_existingAPIClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_projectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- The existential pairing-residual source input is equivalent to the coordinate blocker, so it
is a renamed remaining source obligation rather than an unconditional provider. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_existsPairingResidual_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_projectiveCharacterLattice_existingAPIClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_existsPairingResidualBlocker_sourceClosure
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- The explicit Exercise `18.4` / orthogonality input is likewise equivalent to the coordinate
blocker in the existing non-Cartan closure graph. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_orthogonalityInput_existingAPIClosure :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassCoordinateDivisibilityBlocker_iff_projectiveCharacterLattice_existingAPIClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_orthogonalityInput_sourceClosure
      (p := p) (k := k) (G := G))

end FullMixedPointMassCoordinateExistingAPIClosureWorker

end Representation
