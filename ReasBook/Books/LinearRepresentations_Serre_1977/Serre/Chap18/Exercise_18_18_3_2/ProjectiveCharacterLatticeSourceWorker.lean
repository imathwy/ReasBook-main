import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointwiseResidualWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeCompletion

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveCharacterLatticeSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCharacterLatticeSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-worker compression of the local projective-character lattice target.

It is enough to prove the pointwise source-side divisibility for the coordinate-normalized
Brauer rows.  The adapter then uses the existing Exercise `18.4`/orthogonality readback and
Serre `18.5(a)` regular-restriction equality; it does not invoke Cartan range, cokernel, or
product endpoints. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointwiseSourceDivisibility
    (hsource :
      regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_brauerBasisReadbackInput
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
      (p := p) (A := A) (G := G)
      (regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_pointwiseSourceDivisibility
        (p := p) (A := A) (K := K) (G := G) hsource))

/-- The local projective-character lattice target is equivalent to the pointwise source-side
divisibility of the normalized Brauer rows.

The forward direction is just specialization of the lattice congruence and Serre `18.5(a)`;
the reverse direction is the non-Cartan source readback route through Exercise `18.4` and
orthogonality. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointwiseSourceDivisibility :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      pointwiseSourceDivisibility_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G)
  · exact
      projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointwiseSourceDivisibility
        (p := p) (A := A) (K := K) (G := G)

end LocalProjectiveCharacterLatticeSourceWorker

section FullMixedProjectiveCharacterLatticeSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCharacterLatticeSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCharacterLatticeSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic version of the pointwise source-side divisibility input. -/
def fullMixedModelPointwiseSourceDivisibilityInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic compression of the projective-character lattice target to the
pointwise source-side divisibility input. -/
theorem fullMixedModelProjectiveCharacterLattice_of_pointwiseSourceDivisibility
    (hsource :
      fullMixedModelPointwiseSourceDivisibilityInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointwiseSourceDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic equivalence between the projective-character lattice target and
pointwise source-side divisibility. -/
theorem fullMixedModelProjectiveCharacterLattice_iff_pointwiseSourceDivisibility :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointwiseSourceDivisibilityInput
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hlattice A _instComm _instLocal _instHenselian _instDomain _instDVR
      _instNoetherian _instComplete K _instField _instAlgebra _instFraction _instCharZero
      _instRoots _instAlgClosed _instCharP e0
    exact
      pointwiseSourceDivisibility_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G)
        (hlattice (A := A) (K := K) e0)
  · exact
      fullMixedModelProjectiveCharacterLattice_of_pointwiseSourceDivisibility
        (p := p) (k := k) (G := G)

end FullMixedProjectiveCharacterLatticeSourceWorker

end Representation
