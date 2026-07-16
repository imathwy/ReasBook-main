import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerBasisReadbackProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

set_option linter.style.longLine false in
/-- Local A-side readback is equivalent to constructing the source-faithful Serre `18.5(a)`
projective-restriction witness for the point-mass row differences.

This packages the existing non-Cartan reductions in one place.  The forward direction only
unpacks the readback congruence into coordinate divisibility and applies the formalized
`18.5(a)` equivalence; the reverse direction is the intended source route from projective
restrictions to regular-value divisibility and then to the DVR Brauer-basis readback. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_projectiveRestrictionWitness :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hread
    have hcoord :
        regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
          (p := p) (A := A) (K := K) (G := G) :=
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).1 hread
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).2 hcoord
  · intro hwitness
    exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) hwitness

end BrauerBasisReadbackProof

section FullMixedModelBrauerBasisReadbackProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerBasisReadbackProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerBasisReadbackProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic form of the same exact blocker: the requested full mixed
Brauer-basis readback input is equivalent to constructing the point-mass projective-restriction
witnesses in every mixed model. -/
theorem fullMixedModelBrauerBasisReadbackInput_iff_projectiveRestrictionWitnessBlocker :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hread A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)).1
        (hread (A := A) (K := K) e0)
  · intro hwitness A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)).2
        (hwitness (A := A) (K := K) e0)

end FullMixedModelBrauerBasisReadbackProof

end Representation
