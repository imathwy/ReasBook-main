import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerInversePointMassSourceClosureWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceClosureWorker

/-!
Source-side adapters for `fullMixedModelRegularValueSourceStatement`.

This file keeps the remaining Exercise `18.5(a)` input explicit.  It records that the regular
value source statement is the same non-Cartan source obligation as the direct point-mass row
divisibility input, the explicit Exercise `18.4`/orthogonality input, and the
projective-character lattice source package.  It also provides the local fixed-coordinate
readback adapter without importing the final Cartan range, cokernel, or product endpoints.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section FullMixedRegularValueSourceStatementSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedRegularValueSourceStatementSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedRegularValueSourceStatementSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The target regular-value source statement is equivalent to the direct point-mass
regular-value row input. -/
theorem fullMixedModelRegularValueSourceStatement_iff_pointMassRows_sourceProof :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_brauerInversePointMassSourceInput
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerInversePointMassSourceInput_iff_pointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Direct point-mass regular-value rows close the target source statement. -/
theorem fullMixedModelRegularValueSourceStatement_sourceProof_of_pointMassRows
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_pointMassRows_sourceProof
    (p := p) (k := k) (G := G)).2 hrows

omit [IsAlgClosed k] [CharP k p] in
/-- The target regular-value source statement is equivalent to the explicit Exercise `18.4`/
projective-envelope orthogonality input. -/
theorem fullMixedModelRegularValueSourceStatement_iff_orthogonalityInput_sourceProof :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_pointMassRows_sourceProof
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_orthogonalityInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- The explicit Exercise `18.4`/orthogonality input closes the target source statement. -/
theorem fullMixedModelRegularValueSourceStatement_sourceProof_of_orthogonalityInput
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_orthogonalityInput_sourceProof
    (p := p) (k := k) (G := G)).2 horth

omit [IsAlgClosed k] [CharP k p] in
/-- The target regular-value source statement is equivalent to the full mixed
projective-character lattice source package. -/
theorem fullMixedModelRegularValueSourceStatement_iff_projectiveCharacter_lattice_sourceProof :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_orthogonalityInput_sourceProof
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_orthogonalityInput_sourceClosure
      (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice representatives close the target source statement. -/
theorem fullMixedModelRegularValueSourceStatement_sourceProof_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_projectiveCharacter_lattice_sourceProof
    (p := p) (k := k) (G := G)).2 hlattice

omit [IsAlgClosed k] [CharP k p] in
/-- Fixed-coordinate Brauer-basis readback closes the target source statement directly. -/
theorem fullMixedModelRegularValueSourceStatement_sourceProof_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Fixed-coordinate Brauer-basis readback is equivalent to the target source statement in the
current source-side API. -/
theorem fullMixedModelRegularValueSourceStatement_iff_brauerBasisReadbackInput_sourceProof :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    have hrowsFull :
        fullMixedModelPointMassRowsInRegularValueSubmoduleInput
          (p := p) (k := k) (G := G) :=
      (fullMixedModelRegularValueSourceStatement_iff_pointMassRows_sourceProof
        (p := p) (k := k) (G := G)).1 hregular
    rcases hrowsFull (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hrow⟩
    exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrow
  · exact
      fullMixedModelRegularValueSourceStatement_sourceProof_of_brauerBasisReadbackInput
        (p := p) (k := k) (G := G)

end FullMixedRegularValueSourceStatementSourceWorker

end Representation
