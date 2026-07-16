import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionEquiv

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassCoordinateProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerPointMassCoordinateProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassCoordinateProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Submodule-valued form of the point-mass row divisibility problem.  This is the direct
regular-value witness requested by Serre `18.5(a)`, before unpacking it into coordinates. -/
def brauerPointMassRegularValueDivisibilityWitness
    (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- Direct Serre `18.5(a)` producer from the row-difference divisibility witness to the
projective-restriction witness.  This keeps the row
`χ_c - δ_c` visible and does not route through the point-mass coordinate endpoint. -/
theorem brauerPointMassProjectiveRestrictionWitness_of_regularValueWitness
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassRegularValueDivisibilityWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  let row : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  have hrowD :
      row ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [row] using hwitness c
  have hrowMap :
      row ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hrowD
  rcases Submodule.mem_map.1 hrowMap with ⟨Φ, hΦ, hΦres⟩
  refine ⟨Φ, hΦ, ?_⟩
  simpa [row, regularRestrictionLinearMap] using hΦres

/-- A projective-restriction realization of every point-mass row difference gives the
regular-value divisibility witness by Serre `18.5(a)`. -/
theorem brauerPointMassRegularValueWitness_of_projectiveRestrictionWitness
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassRegularValueDivisibilityWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
  have hmap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    exact ⟨Φ, hΦ, rfl⟩
  have hdiv :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  simpa [brauerPointMassProjectiveRestrictionWitness, hΦres] using hdiv

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The regular-value witness is exactly enough to unpack the coordinatewise divisibility
statement. -/
theorem brauerPointMassCoordinateDivisibility_of_regularValueWitness
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassRegularValueDivisibilityWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) _).1
        (hwitness c) d with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [virtualModularCharacterOnPRegularConjClass_class] using ha

/-- Non-circular local producer: a projective-restriction witness for the point-mass row
difference closes coordinate divisibility through Serre `18.5(a)`. -/
theorem brauerPointMassCoordinateDivisibility_of_projectiveRestrictionWitness'
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :=
  brauerPointMassCoordinateDivisibility_of_regularValueWitness
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (brauerPointMassRegularValueWitness_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness)

/-- Existential form of the regular-value witness. -/
def regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness : Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G)
              ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        brauerPointMassRegularValueDivisibilityWitness
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Existential row-difference divisibility witnesses directly give existential
projective-restriction witnesses by Serre `18.5(a)`. -/
theorem existsPointMassProjectiveRestrictionWitness_of_regularValueWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassProjectiveRestrictionWitness_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness

/-- Existential projective-restriction witnesses give existential regular-value witnesses. -/
theorem existsPointMassRegularValueWitness_of_projectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassRegularValueWitness_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Existential regular-value witnesses give the existing point-mass coordinate blocker. -/
theorem existsPointMassCoordinateDivisibility_of_regularValueWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassCoordinateDivisibility_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness

/-- Existential projective-restriction witnesses give the existing point-mass coordinate
divisibility statement. -/
theorem existsPointMassCoordinateDivisibility_of_projectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) :=
  existsPointMassCoordinateDivisibility_of_regularValueWitness
    (p := p) (A := A) (K := K) (G := G)
    (existsPointMassRegularValueWitness_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) hwitness)

end BrauerPointMassCoordinateProof

section FullMixedModelBrauerPointMassCoordinateProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassCoordinateProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassCoordinateProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model version of the regular-value witness. -/
def fullMixedModelPointMassRegularValueWitnessBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model row-difference divisibility witnesses directly produce the full mixed-model
point-mass projective-restriction witness blocker. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_regularValueWitnessBlocker
    (hwitness :
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassProjectiveRestrictionWitness_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G)
      (hwitness (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model regular-value witnesses close the point-mass coordinate blocker. -/
theorem fullMixedModelPointMassCoordinateBlocker_of_regularValueWitnessBlocker
    (hwitness :
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassCoordinateDivisibility_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G)
      (hwitness (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model projective-restriction witnesses produce full mixed-model regular-value
witnesses. -/
theorem fullMixedModelPointMassRegularValueWitnessBlocker_of_projectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRegularValueWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassRegularValueWitness_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G)
      (hwitness (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Non-circular full mixed-model producer: it remains only to construct the
projective-restriction witnesses for the point-mass row differences. -/
theorem fullMixedModelPointMassCoordinateBlocker_of_projectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
      (p := p) (k := k) (G := G) :=
  fullMixedModelPointMassCoordinateBlocker_of_regularValueWitnessBlocker
    (p := p) (k := k) (G := G)
    (fullMixedModelPointMassRegularValueWitnessBlocker_of_projectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) hwitness)

/-!
Minimal remaining non-circular source lemma:

```
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_proof :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G)
```

Equivalently, for one coordinate-normalized complete Brauer family `π`, construct for every
regular class `c` a projective character `Φ` whose regular restriction is the row difference

```
virtualModularCharacterOnPRegularConjClass ... ([π c]₀)
  - regularIntegerFunctionCast ... (Pi.single c 1)
```

This file proves all formal producers from that witness to
`regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility` and to the full
mixed-model `fullMixedModelPointMassCoordinateDivisibilityBlocker`; it does not assume the
coordinate divisibility statement itself.
-/

end FullMixedModelBrauerPointMassCoordinateProof

end Representation
