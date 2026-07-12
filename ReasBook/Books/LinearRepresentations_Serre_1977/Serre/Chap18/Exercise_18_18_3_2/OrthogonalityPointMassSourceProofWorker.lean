import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.OrthogonalityInputSourceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceClosureWorker

/-!
Point-mass source proof boundary for the orthogonality route.

This file follows the source direction indicated in Serre 18.5(a): Exercise 18.4 and the
orthogonality relation `<Phi_E, phi_E'> = delta_EE'` reduce the desired full mixed
point-mass congruence to the existing projective-character lattice source API.  No Cartan
cokernel, product, range, determinant, or endpoint readback is used here.

The remaining missing unconditional input is the source theorem
`fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence`, equivalently its
local form `projectiveCharacterLatticeIntegerRepresentativeCongruence`.  Once that API is
available, the requested point-mass blocker closes by the adapter below.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalOrthogonalityPointMassSourceProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance orthogonalityPointMassSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance orthogonalityPointMassSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local adapter: the projective-character lattice source API closes the pure point-mass row
congruence isolated by the orthogonality input worker. -/
theorem regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
      (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_iff_pointMassSourceBlocker
    (p := p) (A := A) (K := K) (G := G)).1
    (regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)

end LocalOrthogonalityPointMassSourceProofWorker

section FullMixedOrthogonalityPointMassSourceProofWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedOrthogonalityPointMassSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedOrthogonalityPointMassSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed adapter: the current projective-character lattice source theorem is sufficient
for the requested point-mass orthogonality blocker. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_sourceProof_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Exact full mixed boundary: the requested point-mass source blocker is equivalent to the
current projective-character lattice source API. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_sourceProof_iff_projectiveCharacter_lattice :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_sourceProof_iff_pointMassSourceBlocker
    (p := p) (k := k) (G := G)).symm.trans
    (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_orthogonalityInput_sourceClosure
      (p := p) (k := k) (G := G)).symm

end FullMixedOrthogonalityPointMassSourceProofWorker

end Representation
