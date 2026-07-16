import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerVisibleReadbackSourceProofWorker

/-!
Direct source-side boundary for the fixed-family visible Brauer readback congruence.

This file deliberately stays upstream of Cartan range, cokernel, product, Smith, and determinant
endpoints.  The result below identifies the requested visible readback divisibility with the
remaining point-mass regular-value row input for the same coordinate-normalized Brauer family.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section VisibleReadbackDirectSourceCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance visibleReadbackDirectSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance visibleReadbackDirectSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The requested visible readback congruence gives the point-mass regular-value row input for
the same coordinate-normalized Brauer family.  This is only the coefficient readback of the
canonical DVR Brauer basis through the fraction-field embedding. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_visibleReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π := by
  classical
  intro c
  let row : PRegularConjClass G p → K :=
    FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := K) (π c)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  refine
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G) row).2 ?_
  intro d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  rcases hread c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hbasis :=
    congrFun
      (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete c) d
  have hclass :=
    congrFun
      (virtualModularCharacterOnPRegularConjClass_class
        (p := p)
        (lift := PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        (E := π c)) d
  have hchar :
      algebraMap A K (bA c d) =
        FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d :=
    hbasis.trans hclass
  calc
    row d =
        FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d := by
          rfl
    _ = algebraMap A K
          (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
          rw [← hchar]
          simp [regularIntegerFunctionCast, map_sub]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
          rw [ha]

/-- Fixed-family source equivalence: the visible readback congruence is exactly the point-mass
regular-value row input, after applying Exercise `18.4` readback and coefficientwise descent
through the fraction-field embedding. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_iff_pointMassRows
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · exact
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_visibleReadback
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · exact
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_sourceProof_of_pointMassRows
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

end VisibleReadbackDirectSourceCompletionWorker

end Representation
