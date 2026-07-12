import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeProviderFinal

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalProjectiveCharacterCongruenceSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCharacterCongruenceSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterCongruenceSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local source compression for the projective-character lattice congruence.

The reverse implication is the Serre-basis row provider in
`ProjectiveCharacterLatticeProviderFinal`; the forward implication is only specialization to the
coordinate-normalized Brauer rows.  No Cartan range, cokernel, or product endpoint is used. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassProjectiveRows :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G)
  · exact
      projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
        (p := p) (A := A) (K := K) (G := G)

/-- Local source compression in the explicit projective-restriction witness formulation. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_projectiveRestrictionWitness :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) :=
  (projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassProjectiveRows
    (p := p) (A := A) (K := K) (G := G)).trans
    (regularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G))

/-- Named non-Cartan local provider from the explicit source witness. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitness_source
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  (projectiveCharacterLatticeIntegerRepresentativeCongruence_iff_projectiveRestrictionWitness
    (p := p) (A := A) (K := K) (G := G)).2 hwitness

end LocalProjectiveCharacterCongruenceSourceWorker

section FullMixedProjectiveCharacterCongruenceSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCharacterCongruenceSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCharacterCongruenceSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed source compression for the projective-character lattice congruence.

This records the exact source-side theorem sufficient for
`fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence`: it is equivalent to
constructing the point-mass projective rows in every full mixed model. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassProjectiveRows :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveCharacter_lattice
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed source compression in the explicit projective-restriction witness formulation. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_projectiveRestrictionWitnessBlocker :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassProjectiveRows
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_iff_projectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Named non-Cartan full mixed provider from the source row package. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows_source
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_pointMassProjectiveRows
    (p := p) (k := k) (G := G)).2 hrows

omit [IsAlgClosed k] [CharP k p] in
/-- Named non-Cartan full mixed provider from explicit point-mass projective-restriction
witnesses. -/
theorem fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_of_projectiveRestrictionWitnessBlocker_source
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence_iff_projectiveRestrictionWitnessBlocker
    (p := p) (k := k) (G := G)).2 hwitness

end FullMixedProjectiveCharacterCongruenceSourceWorker

end Representation
