import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ExplicitResidualRegularValueRowsWorker

/-!
Source-side support/value bridge for the explicit point-mass residual rows.

This file keeps the route at the level of Serre `18.5(a)`: a full class-function row is zero
off the `p`-regular locus and its regular values are divisible by the centralizer `p`-part.
The current row blocker only sees the regular restriction, so the remaining source lemma is the
existence of such full class-function representatives for the point-mass residual rows.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassExplicitRowsSourceWorker

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

local instance pointMassExplicitRowsSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassExplicitRowsSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The coordinate-normalized residual row on regular classes. -/
noncomputable def coordinateNormalizedPointMassExplicitResidualRow
    (π : PRegularConjClass G p → FDRep kA G)
    (c : PRegularConjClass G p) : PRegularConjClass G p → K :=
  FDRep.modularCharacterOnPRegularConjClass
      (p := p) (G := G) (A := K) (π c)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
      (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)

/-- Literal Serre `18.5(a)` support/value source input for the point-mass residual rows.

For every row `c`, it asks for a full class function `Φ : A ⊗R[K](G)` whose regular restriction
is the residual row, which is zero on `p`-singular elements, and whose values on `p`-regular
elements are divisible by the corresponding centralizer `p`-part. -/
def coordinateNormalizedPointMassResidualSerreSupportValueSource
    (π : PRegularConjClass G p → FDRep kA G) : Prop :=
  ∀ c : PRegularConjClass G p,
    ∃ Φ : A ⊗R[K](G),
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        (∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g =
            algebraMap A K ((centralizerPPart p g : A) * a)) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          coordinateNormalizedPointMassExplicitResidualRow
            (p := p) (A := A) (K := K) (G := G) π c

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The support/value source input immediately gives the explicit regular-value row
divisibility condition seen by the restricted row blocker. -/
theorem coordinateNormalizedPointMassResidualRegularValueRows_of_serreSupportValueSource
    (π : PRegularConjClass G p → FDRep kA G)
    (hsource :
      coordinateNormalizedPointMassResidualSerreSupportValueSource
        (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedPointMassResidualRegularValueRows
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c d
  rcases hsource c with ⟨Φ, _hzero, hvalue, hres⟩
  let s := PRegularConjClass.representative (G := G) (p := p) d
  have hs : PRegularConjClass.ofSubtype (G := G) p s = d := by
    apply Subtype.ext
    simp [s]
  rcases hvalue s.1 s.2 with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change coordinateNormalizedPointMassExplicitResidualRow
      (p := p) (A := A) (K := K) (G := G) π c d =
    algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)
  calc
    coordinateNormalizedPointMassExplicitResidualRow
        (p := p) (A := A) (K := K) (G := G) π c d =
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ d := by
          exact (congrFun hres d).symm
    _ = regularRestriction (p := p) (A := A) (K := K) (G := G) Φ
        (PRegularConjClass.ofSubtype (G := G) p s) := by
          rw [hs]
    _ = (Φ : G → K) s.1 := by
          simpa using
            (regularRestriction_ofSubtype
              (p := p) (A := A) (K := K) (G := G) Φ s.1 s.2)
    _ = algebraMap A K ((centralizerPPart p s.1 : A) * a) := ha
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
          have hmk : ConjClasses.mk s.1 = d.1 := by
            simp [s]
          rw [← hmk, ConjClasses.centralizerPPart_mk]

/-- Existential Serre support/value source input for the explicit residual row route. -/
def regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows : Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ _hπ_simple : ∀ c, Simple (π c),
      ∃ _hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        coordinateNormalizedPointMassResidualSerreSupportValueSource
          (p := p) (A := A) (K := K) (G := G) π

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The support/value source lemma closes the local explicit residual row blocker. -/
theorem regularValueCongruenceSourceFaithfulExistsExplicitResidualRows_of_serreSupportValueRows
    (hsource :
      regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsExplicitResidualRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hsource with ⟨π, hπ_simple, hπ_coord, hsource⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedPointMassResidualRegularValueRows_of_serreSupportValueSource
      (p := p) (A := A) (K := K) (G := G) π hsource

/-- A projective-restriction witness supplies the support/value source input by Serre `18.5(a)`.
This is an adapter only; the missing source theorem is still the construction of such rows. -/
theorem coordinateNormalizedPointMassResidualSerreSupportValueSource_of_projectiveRestrictionWitness
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
    coordinateNormalizedPointMassResidualSerreSupportValueSource
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  rcases hwitness c with ⟨Φ, hΦ, hΦres⟩
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
  refine ⟨Φ, hzero, hvalue, ?_⟩
  simpa [coordinateNormalizedPointMassExplicitResidualRow,
    virtualModularCharacterOnPRegularConjClass_class] using hΦres

/-- Existing projective-restriction witnesses imply the explicit support/value source input. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_projectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness

/-- Existing projective-restriction witnesses imply the local explicit residual row blocker. -/
theorem regularValueCongruenceSourceFaithfulExistsExplicitResidualRows_of_projectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsExplicitResidualRows
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulExistsExplicitResidualRows_of_serreSupportValueRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) hwitness)

end LocalPointMassExplicitRowsSourceWorker

section FullMixedPointMassExplicitRowsSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassExplicitRowsSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassExplicitRowsSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model support/value source lemma for the explicit residual rows. -/
def fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed support/value source lemma closes `fullMixedModelExplicitResidualRowsBlocker`.
-/
theorem fullMixedModelExplicitResidualRowsBlocker_of_serreSupportValueSourceBlocker
    (hsource :
      fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsExplicitResidualRows_of_serreSupportValueRows
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Existing full mixed projective-restriction witnesses imply the full mixed support/value
source lemma. -/
theorem
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_projectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_projectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G)
      (hwitness (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Existing full mixed projective-restriction witnesses imply the explicit residual row blocker.
-/
theorem fullMixedModelExplicitResidualRowsBlocker_of_projectiveRestrictionWitnessBlocker
    (hwitness :
      fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsBlocker
      (p := p) (k := k) (G := G) :=
  fullMixedModelExplicitResidualRowsBlocker_of_serreSupportValueSourceBlocker
    (p := p) (k := k) (G := G)
    (fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_projectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) hwitness)

/-!
Minimal missing source lemma isolated by this worker:

```
theorem fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_proof :
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G)
```

Locally, this means constructing one coordinate-normalized Brauer family `π` such that every
residual row `χ_c - δ_c` has a full class-function representative `Φ : A ⊗R[K](G)` satisfying
Serre `18.5(a)`'s two right-hand-side conditions:

* `Φ(g) = 0` for `p`-singular `g`;
* `Φ(g) ∈ |C_G(g)|_p A` for `p`-regular `g`.

The support half cannot be recovered from the current restricted row type
`PRegularConjClass G p → K`; it must come from such a full class-function representative.
-/

end FullMixedPointMassExplicitRowsSourceWorker

end Representation
