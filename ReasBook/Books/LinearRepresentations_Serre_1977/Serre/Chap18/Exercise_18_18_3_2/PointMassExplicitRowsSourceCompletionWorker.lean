import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassResidualFullRepresentativeWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueSourceCompletion
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.Serre18_5ASupportValueCriterionWorker

/-!
Completion helpers for the source-side support/value route of Serre `18.5(a)`.

The declarations here keep the full class function visible.  Given a point-mass row in the
regular restriction of the projective-character submodule, we choose an actual
`Φ : A ⊗R[K](G)`, prove its vanishing on the `p`-singular locus, prove the centralizer
`p`-part divisibility of its regular values, and identify its regular restriction with the
coordinate-normalized residual row.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassExplicitRowsSourceCompletionWorker

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

local instance pointMassExplicitRowsSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassExplicitRowsSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family completion from projective row preimages to Serre's full support/value row
package.

For each row `c`, the hypothesis gives that the residual regular row lies in the image of
regular restriction from projective class functions.  This proof chooses the preimage `Φ`,
then obtains the two pointwise Serre `18.5(a)` conditions from the projective-character
submodule itself. -/
theorem coordinateNormalizedPointMassResidualSerreSupportValueSource_of_fixedFamilyProjectiveRowInput
    (π : PRegularConjClass G p → FDRep kA G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[kA](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
            Submodule.map
              (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
              (projectiveCharacterSubmodule (A := A) (K := K) (G := G))) :
    coordinateNormalizedPointMassResidualSerreSupportValueSource
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  rcases Submodule.mem_map.1 (hrows c) with ⟨Φ, hΦ, hΦres⟩
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
          algebraMap A K ((centralizerPPart p g : A) * a) :=
    (regularRestriction_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value_serre18_5a
      (p := p) (A := A) (K := K) (G := G) Φ).1 hreg
  refine ⟨Φ, hzero, hvalue, ?_⟩
  simpa [coordinateNormalizedPointMassExplicitResidualRow,
    virtualModularCharacterOnPRegularConjClass_class, regularRestrictionLinearMap] using hΦres

/-- Local existential completion from the point-mass projective-row input to the explicit
Serre support/value source package. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_pointMassProjectiveRowInput
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedPointMassResidualSerreSupportValueSource_of_fixedFamilyProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hrows

/-- Local source-faithful congruence completion in the requested full support/value form. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_sourceFaithfulStatement_via_projectiveRows
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
      (p := p) (A := A) (K := K) (G := G) := by
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) hregular

end LocalPointMassExplicitRowsSourceCompletionWorker

section FullMixedPointMassExplicitRowsSourceCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedPointMassExplicitRowsSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassExplicitRowsSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed completion from point-mass projective rows to Serre's support/value blocker. -/
theorem fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_pointMassProjectiveRowInput
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_pointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed source-faithful regular-value congruence supplies the requested support/value
blocker.  The actual full class functions are constructed locally by the preceding theorem. -/
theorem fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_sourceFaithfulStatement_via_projectiveRows
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker
      (p := p) (k := k) (G := G) := by
  exact
    fullMixedModelExplicitResidualRowsSerreSupportValueSourceBlocker_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (k := k) (G := G) hregular

end FullMixedPointMassExplicitRowsSourceCompletionWorker

end Representation
