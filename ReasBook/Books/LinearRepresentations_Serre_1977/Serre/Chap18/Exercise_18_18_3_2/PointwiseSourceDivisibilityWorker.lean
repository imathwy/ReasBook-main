import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointwiseResidualWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeProviderFinal

/-!
Worker F bridge file for the source-side pointwise divisibility input used by
`BrauerPointwiseResidualWorker`.

The unconditional source-row divisibility is not constructed here.  The lemmas below isolate the
small local inputs that are enough to obtain
`regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof` without using Cartan
range/cokernel/product endpoints as a reverse implication.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PointwiseSourceDivisibilityWorker

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

local instance pointwiseSourceDivisibilityWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointwiseSourceDivisibilityWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A minimal bridge: if every coordinate-normalized Brauer row difference is already a member
of Serre's regular-value divisibility submodule, then the pointwise source-row divisibility
definition follows by evaluating the submodule membership at each regular class. -/
theorem
    pointwiseSourceDivisibility_of_pointwiseRegularValueRowMem
    (hrow :
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
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) := by
  intro π hπ_simple hπ_coord c d _hd
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))).1
        (hrow π hπ_simple hπ_coord c) d with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [virtualModularCharacterOnPRegularConjClass_class] using ha

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Brauer-basis readback, if available for every coordinate-normalized family, supplies the
row-membership hypothesis of the preceding bridge. -/
theorem
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof_of_allBrauerBasisReadback
    (hread :
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    pointwiseSourceDivisibility_of_pointwiseRegularValueRowMem
      (p := p) (A := A) (K := K) (G := G) ?_
  intro π hπ_simple hπ_coord c
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hcoordRow :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    ((fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete).2
      (hread π hπ_simple hπ_coord)) c
  simpa [hπ_coord c] using hcoordRow

/-- Existing point-mass projective-row input is enough for the pointwise source divisibility:
first extend those rows to the projective-character lattice congruence, then specialize the
already available pointwise bridge from `BrauerPointwiseResidualWorker`. -/
theorem
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof_of_pointMassProjectiveRows
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) :=
  pointwiseSourceDivisibility_of_projectiveCharacter_lattice
    (p := p) (A := A) (K := K) (G := G)
    (projectiveCharacterLatticeIntegerRepresentativeCongruence_of_pointMassProjectiveRows
      (p := p) (A := A) (K := K) (G := G) hrows)

/-- Existing Brauer-basis readback input is also enough, via the local projective-character
lattice completion. -/
theorem
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) :=
  pointwiseSourceDivisibility_of_projectiveCharacter_lattice
    (p := p) (A := A) (K := K) (G := G)
    (projectiveCharacterLatticeIntegerRepresentativeCongruence_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hread)

end PointwiseSourceDivisibilityWorker

end Representation
