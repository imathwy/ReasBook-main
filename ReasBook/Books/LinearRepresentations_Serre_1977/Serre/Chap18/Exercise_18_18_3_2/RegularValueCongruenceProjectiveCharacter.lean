import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeCokernelDescent
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section FullMixedModelRegularValueCongruenceProjectiveCharacter

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelRegularValueCongruenceProjectiveCharacterFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelRegularValueCongruenceProjectiveCharacterDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic form of the projective-character lattice representative
congruence. This is the source-side input before Serre 18.5(a) is rewritten as regular-value
divisibility. -/
def fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic projective-character lattice congruence is exactly the
source-faithful regular-value congruence. The local equivalence is just
`projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule`. -/
theorem fullMixedModelProjectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hlattice A _instComm _instLocal _instHenselian _instDomain _instDVR
      _instNoetherian _instComplete K _instField _instAlgebra _instFraction _instCharZero
      _instRoots _instAlgClosed _instCharP e0
    exact
      (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)).1
        (hlattice (A := A) (K := K) e0)
  · intro hregular A _instComm _instLocal _instHenselian _instDomain _instDVR
      _instNoetherian _instComplete K _instField _instAlgebra _instFraction _instCharZero
      _instRoots _instAlgClosed _instCharP e0
    exact
      (projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)).2
        (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Direction used by the non-circular source-faithful route. -/
theorem fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
      (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
    (p := p) (k := k) (G := G)).1 hlattice

omit [IsAlgClosed k] [CharP k p] in
/-- The same route, expressed in the fixed-coordinate point-mass divisibility formulation. -/
theorem fullMixedModelPointMassCoordinateDivisibilityBlocker_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
      (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueCongruence_iff_pointMassCoordinateDivisibilityBlocker
    (p := p) (k := k) (G := G)).1
    (fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G) hlattice)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic equivalence between the projective-character lattice route and the
fixed-coordinate point-mass divisibility blocker. -/
theorem fullMixedModelProjectiveCharacter_lattice_iff_pointMassCoordinateDivisibilityBlocker :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelRegularValueCongruence_iff_pointMassCoordinateDivisibilityBlocker
      (p := p) (k := k) (G := G))

set_option linter.style.longLine false in
omit [IsAlgClosed k] [CharP k p] in
/-- The projective-character lattice route also closes the equivalent projective-envelope
residual blocker. -/
theorem
    fullMixedModelPointMassProjectiveEnvelopeResidualBlocker_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) :=
  (fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_coordinateDivisibilityBlocker
    (p := p) (k := k) (G := G)).2
    (fullMixedModelPointMassCoordinateDivisibilityBlocker_of_projectiveCharacter_lattice
      (p := p) (k := k) (G := G) hlattice)

set_option linter.style.longLine false in
omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic equivalence between the projective-character lattice route and the
projective-envelope residual blocker. -/
theorem
    fullMixedModelProjectiveCharacter_lattice_iff_projectiveEnvelopeResidualBlocker :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacter_lattice_iff_pointMassCoordinateDivisibilityBlocker
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_coordinateDivisibilityBlocker
      (p := p) (k := k) (G := G)).symm

end FullMixedModelRegularValueCongruenceProjectiveCharacter

end Representation
