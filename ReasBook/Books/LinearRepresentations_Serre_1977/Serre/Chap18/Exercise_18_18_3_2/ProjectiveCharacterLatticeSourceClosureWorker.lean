import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerOrthogonalitySourceGap
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassRegularValueWitnessSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterCongruenceSourceWorker

/-!
Source closure for the full mixed projective-character lattice provider.

No unconditional proof of the source row has appeared in the current dependency graph.  This file
therefore records the strongest non-Cartan closure available here: the full mixed
projective-character lattice congruence is Lean-equivalent to the existential pairing residual,
to the explicit Exercise `18.4` / projective-envelope orthogonality input, and to the direct
point-mass regular-value row divisibility input.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section FullMixedProjectiveCharacterLatticeSourceClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCharacterLatticeSourceClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCharacterLatticeSourceClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed projective-character lattice target is exactly the current existential
pairing-residual source input.

The forward direction specializes the lattice congruence to coordinate-normalized rows and then
uses the Exercise `18.4`/orthogonality residual bridge.  The reverse direction is the existing
row provider through the projective-character restriction lattice, not a Cartan range/cokernel
endpoint. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_existsPairingResidualBlocker_sourceClosure :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisExistsPairingResidualBlocker_of_projectiveCharacter_lattice
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_existsPairingResidualBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Equivalent source form in the explicit Exercise `18.4` / projective-envelope orthogonality
notation. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_orthogonalityInput_sourceClosure :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_existsPairingResidualBlocker_sourceClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisExistsPairingResidualBlocker_iff_orthogonalityInput
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Provider form: the explicit Exercise `18.4` / orthogonality input closes the full mixed
projective-character lattice congruence. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_orthogonalityInput_sourceClosure
    (horth :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_orthogonalityInput_sourceClosure
    (p := p) (k := k) (G := G)).2 horth

omit [IsAlgClosed k] [CharP k p] in
/-- The same equivalence in the direct point-mass regular-value row formulation of Serre
`18.5(a)`: each coordinate-normalized row difference lies in the `p^{z(s)}` divisibility
lattice. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassRowsInRegularValueSubmoduleInput_sourceClosure :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_existsPairingResidualBlocker_sourceClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_existsPairingResidualBlocker
      (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- Provider form from the direct `p^{z(s)}` point-mass row divisibility input. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassRowsInRegularValueSubmoduleInput_sourceClosure
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassRowsInRegularValueSubmoduleInput_sourceClosure
    (p := p) (k := k) (G := G)).2 hrows

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-row source input, regular-value row divisibility, and the full mixed lattice
target are the same current non-Cartan source obligation. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassRegularValueWitnessBlocker_sourceClosure :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassRowsInRegularValueSubmoduleInput_sourceClosure
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassRegularValueWitnessBlocker_iff_pointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G)).symm

end FullMixedProjectiveCharacterLatticeSourceClosureWorker

end Representation
