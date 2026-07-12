import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassExplicitRowsSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassProjectiveRestrictionConstructionWorker

/-!
Full representative worker for the coordinate-normalized point-mass residual rows.

This file stays on the source side of Serre `18.5(a)`: a residual row is promoted from a
regular-class function to a full projective class-function representative.  The support and
centralizer-`p`-part divisibility properties are then read from the projective-character
submodule, not from a Cartan range, cokernel, or product endpoint.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassResidualFullRepresentativeWorker

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

local instance pointMassResidualFullRepresentativeWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassResidualFullRepresentativeWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal fixed-family full representative API for the coordinate-normalized residual rows.

This is the same mathematical datum as the point-mass projective-restriction witness, rewritten
with `coordinateNormalizedPointMassExplicitResidualRow` as the visible row. -/
def coordinateNormalizedPointMassResidualFullRepresentativeWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          coordinateNormalizedPointMassExplicitResidualRow
            (p := p) (A := A) (K := K) (G := G) π c

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The existing point-mass projective-restriction witness is exactly the full representative
witness for `coordinateNormalizedPointMassExplicitResidualRow`. -/
theorem coordinateNormalizedPointMassResidualFullRepresentativeWitness_of_projectiveRestrictionWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedPointMassResidualFullRepresentativeWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
  refine ⟨Φ, hΦ, ?_⟩
  simpa [coordinateNormalizedPointMassExplicitResidualRow,
    virtualModularCharacterOnPRegularConjClass_class] using hΦres

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Conversely, the visible full representative witness is the existing point-mass
projective-restriction witness. -/
theorem brauerPointMassProjectiveRestrictionWitness_of_coordinateNormalizedPointMassResidualFullRepresentativeWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      coordinateNormalizedPointMassResidualFullRepresentativeWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
  refine ⟨Φ, hΦ, ?_⟩
  simpa [coordinateNormalizedPointMassExplicitResidualRow,
    virtualModularCharacterOnPRegularConjClass_class] using hΦres

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-family equivalence between the visible full-representative API and the existing
projective-restriction witness. -/
theorem coordinateNormalizedPointMassResidualFullRepresentativeWitness_iff_projectiveRestrictionWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedPointMassResidualFullRepresentativeWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      brauerPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      brauerPointMassProjectiveRestrictionWitness_of_coordinateNormalizedPointMassResidualFullRepresentativeWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · exact
      coordinateNormalizedPointMassResidualFullRepresentativeWitness_of_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- A regular-value divisibility witness constructs a full projective representative of one
coordinate-normalized residual row, with Serre `18.5(a)` support and value properties. -/
theorem coordinateNormalizedPointMassExplicitResidualRow_fullRepresentative_of_regularValueWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassRegularValueDivisibilityWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
    (c : PRegularConjClass G p) :
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        (∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g =
            algebraMap A K ((centralizerPPart p g : A) * a)) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          coordinateNormalizedPointMassExplicitResidualRow
            (p := p) (A := A) (K := K) (G := G) π c := by
  rcases
      (brauerPointMassProjectiveRestrictionWitness_of_regularValueWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness c) with
    ⟨Φ, hΦ, hΦres⟩
  have hzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0 :=
    projectiveCharacterSubmodule_zero_on_pSingular
      (p := p) (A := A) (K := K) (G := G) hΦ
  have hreg :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    have hmap :
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
          Submodule.map
            (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
            (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
      ⟨Φ, hΦ, rfl⟩
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  have hvalue :
      ∀ g : G, IsPRegular p g →
        ∃ a : A, (Φ : G → K) g =
          algebraMap A K ((centralizerPPart p g : A) * a) := by
    intro g hg
    rcases
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G)
          (regularRestriction (p := p) (A := A) (K := K) (G := G) Φ)).1 hreg
          (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩) with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [regularRestriction_ofSubtype, ConjClasses.centralizerPPart_mk] using ha
  refine ⟨Φ, hΦ, hzero, hvalue, ?_⟩
  simpa [coordinateNormalizedPointMassExplicitResidualRow,
    virtualModularCharacterOnPRegularConjClass_class] using hΦres

/-- A regular-value witness gives the full Serre support/value source package for all
coordinate-normalized residual rows in the fixed family. -/
theorem coordinateNormalizedPointMassResidualSerreSupportValueSource_of_regularValueWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassRegularValueDivisibilityWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedPointMassResidualSerreSupportValueSource
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  rcases
      coordinateNormalizedPointMassExplicitResidualRow_fullRepresentative_of_regularValueWitness
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord hwitness c with
    ⟨Φ, _hΦ, hzero, hvalue, hres⟩
  exact ⟨Φ, hzero, hvalue, hres⟩

/-- A full representative witness gives the Serre support/value source package. -/
theorem coordinateNormalizedPointMassResidualSerreSupportValueSource_of_fullRepresentativeWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      coordinateNormalizedPointMassResidualFullRepresentativeWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedPointMassResidualSerreSupportValueSource
      (p := p) (A := A) (K := K) (G := G) π := by
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      ((coordinateNormalizedPointMassResidualFullRepresentativeWitness_iff_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hwitness)

/-- Source regular-value congruence constructs the full representative package for a fixed
coordinate-normalized family. -/
theorem coordinateNormalizedPointMassResidualSerreSupportValueSource_of_regularValueCongruenceSourceFaithfulStatement
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
    coordinateNormalizedPointMassResidualSerreSupportValueSource
      (p := p) (A := A) (K := K) (G := G) π := by
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (brauerPointMassRegularValueWitness_of_regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular)

/-- Existential regular-value witnesses produce the explicit Serre support/value row package. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_regularValueWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness

/-- Source regular-value congruence produces the explicit Serre support/value row package by
choosing the standard coordinate-normalized Brauer family. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_regularValueCongruenceSourceFaithfulStatement
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := kA) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular

end LocalPointMassResidualFullRepresentativeWorker

section FullMixedPointMassResidualFullRepresentativeWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassResidualFullRepresentativeWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassResidualFullRepresentativeWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model version of the visible full representative API. -/
def fullMixedModelPointMassResidualFullRepresentativeBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ hπ_simple : ∀ c, Simple (π c),
          ∃ hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            coordinateNormalizedPointMassResidualFullRepresentativeWitness
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

omit [IsAlgClosed k] [CharP k p] in
/-- The visible full-representative blocker is equivalent to the existing projective-restriction
blocker. -/
theorem fullMixedModelPointMassResidualFullRepresentativeBlocker_iff_projectiveRestrictionWitnessBlocker :
    fullMixedModelPointMassResidualFullRepresentativeBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hblock (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hwitness⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      ((coordinateNormalizedPointMassResidualFullRepresentativeWitness_iff_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hwitness)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hblock (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hwitness⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      ((coordinateNormalizedPointMassResidualFullRepresentativeWitness_iff_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hwitness)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed regular-value witnesses supply the full Serre support/value source blocker. -/
theorem fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_regularValueWitnessBlocker
    (hwitness :
      fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G)
      (hwitness (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed visible full representatives supply the full Serre support/value source blocker. -/
theorem fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_fullRepresentativeBlocker
    (hblock :
      fullMixedModelPointMassResidualFullRepresentativeBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G) := by
  exact
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_projectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G)
      ((fullMixedModelPointMassResidualFullRepresentativeBlocker_iff_projectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)).1 hblock)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed source regular-value congruence supplies the full Serre support/value source
blocker by constructing the full representatives row by row. -/
theorem fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_regularValueCongruenceSourceFaithfulStatement
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

/-!
Remaining unconditional input isolated by this worker:

```
theorem fullMixedModelPointMassResidualFullRepresentativeBlocker_proof :
    fullMixedModelPointMassResidualFullRepresentativeBlocker
      (p := p) (k := k) (G := G)
```

The equivalence above shows that this is exactly the existing point-mass projective-restriction
witness blocker, but with the residual row written as
`coordinateNormalizedPointMassExplicitResidualRow`.  A proof must construct the full projective
class-function representatives themselves; the support condition cannot be recovered from the
restricted row alone.
-/

end FullMixedPointMassResidualFullRepresentativeWorker

end Representation
