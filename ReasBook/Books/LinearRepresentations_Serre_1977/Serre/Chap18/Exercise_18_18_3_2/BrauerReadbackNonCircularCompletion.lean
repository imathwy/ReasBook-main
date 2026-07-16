import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualCompletion

/-!
This file records the non-circular readback bridge that uses Serre 18.5(a) only through the
projective-character lattice equality and then descends by the Exercise 18.4 projective-envelope
readback API.  It does not use `CartanFormalRange` or a final cokernel/product endpoint as an
input.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerReadbackNonCircularCompletion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerReadbackNonCircularCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReadbackNonCircularCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Non-circular local readback bridge from the projective-character lattice input.

The proof route is:
1. use the projective-character lattice representative congruence to put each point-mass row
   residual in the projective-character restriction lattice;
2. rewrite that lattice with Serre 18.5(a);
3. use the Exercise 18.4 projective-envelope readback formula for `canonicalDVRBrauerBasis`.

No Cartan range/cokernel/product endpoint is used as an input. -/
theorem
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveCharacter_lattice_nonCircular
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveCharacter_lattice_via_projectiveEnvelopeResidual
    (p := p) (A := A) (K := K) (G := G) hlattice

end LocalBrauerReadbackNonCircularCompletion

section FullMixedBrauerReadbackNonCircularCompletion

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerReadbackNonCircularCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerReadbackNonCircularCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model version of the non-circular readback bridge from the projective-character
lattice input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_projectiveCharacter_lattice_nonCircular
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveCharacter_lattice_nonCircular
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

end FullMixedBrauerReadbackNonCircularCompletion

end Representation
