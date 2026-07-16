import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalBrauerRowTransportWorker

/-!
Worker B: source-side completion boundary for the direct Brauer-row route.

This file does not use the Cartan range/cokernel/product/determinant endpoints and does not
invoke the projective-character lattice route.  It identifies the direct A-valued Brauer row
API with the remaining K-valued source row membership in Serre's regular-value divisibility
submodule.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerCharacterPointwiseSourceCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerCharacterPointwiseSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerCharacterPointwiseSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact K-side source row membership left by the direct Brauer-character route.

For each coordinate-normalized Brauer family and each row `c`, the K-valued Brauer character
row minus the corresponding point-mass row lies in Serre's regular-value divisibility
submodule.  Unpacking this submodule gives precisely divisibility by
`ConjClasses.centralizerPPart p d.1` at every regular class `d`.
-/
def coordinateNormalizedBrauerCharacterFieldRowSource : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p),
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- K-side source row membership gives the requested A-side direct Brauer-character
pointwise readback congruence.

The proof uses only the canonical Brauer-row transport and the fraction-field/A-valued
readback equivalence `fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility`.
-/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_of_fieldRowSource
    (hrow :
      coordinateNormalizedBrauerCharacterFieldRowSource
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hfixed :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
    refine
      (fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete).1 ?_
    intro c
    simpa [hπ_coord c, coordinateNormalizedBrauerCharacterFieldRowSource] using
      hrow π hπ_simple hπ_coord c
  exact
    brauerCharacterPointwiseReadbackCongruence_of_fixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (by simpa [hπ_pairwise, hπ_complete] using hfixed)

/-- Conversely, the requested A-side direct Brauer-character API supplies the same K-side
source row membership after transporting through the fixed-coordinate readback equivalence.

This proves that the remaining source-side row goal is not an artifact of the canonical basis
or lift choices: it is exactly the requested pointwise congruence, viewed after scalar
extension to the fraction field.
-/
theorem fieldRowSource_of_coordinateNormalizedBrauerCharacterPointwiseSourceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G)) :
    coordinateNormalizedBrauerCharacterFieldRowSource
      (p := p) (A := A) (K := K) (G := G) := by
  intro π hπ_simple hπ_coord c
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hfixed :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
    exact
      fixedCoordinateReadbackDivisibility_of_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
        (hapi π hπ_simple hπ_coord)
  have hfield :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G))) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    (fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete).2 hfixed
  simpa [hπ_coord c] using hfield c

/-- Exact local boundary for Worker B: proving the direct A-valued
`coordinateNormalizedBrauerCharacterPointwiseSourceAPI` is equivalent to proving the K-valued
source row membership above. -/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_fieldRowSource :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
      coordinateNormalizedBrauerCharacterFieldRowSource
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      fieldRowSource_of_coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (K := K) (G := G)
  · exact
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI_of_fieldRowSource
        (p := p) (A := A) (K := K) (G := G)

/-- Pointwise unpacking of the remaining K-side source membership.  This is the precise
remaining source goal in coordinates. -/
theorem coordinateNormalizedBrauerCharacterFieldRowSource_iff_pointwise :
    coordinateNormalizedBrauerCharacterFieldRowSource
        (p := p) (A := A) (K := K) (G := G) ↔
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (_hπ_simple : ∀ c, Simple (π c))
        (_hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
        (c d : PRegularConjClass G p),
        ∃ a : A,
          (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π c]₀ : R₀[k](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) d =
            algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
  constructor
  · intro hrow π hπ_simple hπ_coord c d
    exact
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))).1
        (hrow π hπ_simple hπ_coord c) d
  · intro hpoint π hπ_simple hπ_coord c
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))).2 ?_
    intro d
    exact hpoint π hπ_simple hπ_coord c d

/-- Combined exact boundary: the requested A-side Brauer-character API is equivalent to the
literal K-side pointwise centralizer-`p`-part divisibility of every coordinate-normalized row.
-/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_fieldRowPointwise :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (_hπ_simple : ∀ c, Simple (π c))
        (_hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
        (c d : PRegularConjClass G p),
        ∃ a : A,
          (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π c]₀ : R₀[k](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) d =
            algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) :=
  (coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_fieldRowSource
    (p := p) (A := A) (K := K) (G := G)).trans
    (coordinateNormalizedBrauerCharacterFieldRowSource_iff_pointwise
      (p := p) (A := A) (K := K) (G := G))

end LocalBrauerCharacterPointwiseSourceCompletionWorker

end Representation
