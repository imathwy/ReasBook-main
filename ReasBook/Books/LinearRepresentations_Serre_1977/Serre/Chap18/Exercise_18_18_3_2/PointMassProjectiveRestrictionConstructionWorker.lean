import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRestrictionConstructionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance pointMassProjectiveRestrictionConstructionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRestrictionConstructionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-family row-divisibility extraction from the source regular-value congruence.

This is the core source input before applying Serre `18.5(a)`: for a coordinate-normalized
family `π`, the row `χ_πc - Pi.single c 1` lies in the regular-value divisibility lattice. -/
theorem brauerPointMassRegularValueWitness_of_regularValueCongruenceSourceFaithfulStatement
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    brauerPointMassRegularValueDivisibilityWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  simpa [brauerPointMassRegularValueDivisibilityWitness, hπ_coord c] using
    hregular ([π c]₀ : R₀[kA](G))

/-- Fixed-family projective-restriction construction from the source regular-value congruence.

The proof uses only the regular-value divisibility/projective-character equivalence from
Serre `18.5(a)`: once the row is in the divisibility lattice, choose a projective character
mapping to that row under regular restriction. -/
theorem brauerPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    brauerPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :=
  brauerPointMassProjectiveRestrictionWitness_of_regularValueWitness
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (brauerPointMassRegularValueWitness_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular)

/-- Rowwise form: each normalized row difference is a regular restriction of a projective
character. -/
theorem pointMassRow_projectiveRestriction_of_regularValueCongruenceSourceFaithfulStatement
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G))
    (c : PRegularConjClass G p) :
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π c]₀ : R₀[kA](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) :=
  brauerPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular c

/-- Local source regular-value congruence provides the existential point-mass projective
restriction witness by choosing the standard coordinate-normalized complete family. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := kA) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular

/-- The local source regular-value congruence is equivalent to the explicit point-mass
projective-restriction witness, without passing through the coordinate-divisibility endpoint. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_existsPointMassProjectiveRestrictionWitness :
    regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)
  · rintro ⟨π, hπ_simple, hπ_coord, hwitness⟩
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness

end LocalPointMassProjectiveRestrictionConstructionWorker

section FullMixedPointMassProjectiveRestrictionConstructionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassProjectiveRestrictionConstructionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassProjectiveRestrictionConstructionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model source regular-value congruence gives the requested point-mass
projective-restriction blocker. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_regularValueCongruenceSourceFaithfulStatement
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model exact form of the construction route: the regular-value source input and
the point-mass projective-restriction blocker are equivalent. -/
theorem fullMixedModelRegularValueCongruenceSourceFaithfulStatement_iff_pointMassProjectiveRestrictionWitnessBlocker :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_regularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR
      _instNoetherian _instComplete K _instField _instAlgebra _instFraction _instCharZero
      _instRoots _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_existsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

end FullMixedPointMassProjectiveRestrictionConstructionWorker

end Representation
