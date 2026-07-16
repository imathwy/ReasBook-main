import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceProjectiveCharacter

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveCharacterLatticeCompletion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCharacterLatticeCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The Brauer-basis readback input also closes the projective-character lattice representative
statement, by the already-proved Serre `18.5(a)` lattice/regular-value equivalence. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
    (p := p) (A := A) (K := K) (G := G)).2
    (regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hread)

end LocalProjectiveCharacterLatticeCompletion

section FullMixedProjectiveCharacterLatticeCompletion

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCharacterLatticeCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCharacterLatticeCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic form of
`projectiveCharacterLatticeIntegerRepresentativeCongruence_of_brauerBasisReadbackInput`. -/
theorem fullMixedModelProjectiveCharacterLatticeCongruence_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-character lattice and regular-value source-faithful full mixed inputs have
the same Brauer-basis readback sufficient condition. -/
theorem fullMixedModel_projectiveCharacter_lattice_and_regularValue_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ∧
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) := by
  constructor
  · intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      projectiveCharacterLatticeIntegerRepresentativeCongruence_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)
  · intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)

end FullMixedProjectiveCharacterLatticeCompletion

end Representation
