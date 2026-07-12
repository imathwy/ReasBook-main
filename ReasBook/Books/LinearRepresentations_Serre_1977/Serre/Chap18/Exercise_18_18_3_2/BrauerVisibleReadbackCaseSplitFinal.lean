import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualMatrixClosureFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerVisibleReadbackCaseSplitFinal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerVisibleReadbackCaseSplitFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerVisibleReadbackCaseSplitFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Case-split glue for the fixed-coordinate visible readback target.

This file deliberately contains only the formal assembly: the mathematical source inputs are the
diagonal and off-diagonal pointwise divisibility statements isolated for parallel workers. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_diagonal_offDiagonal
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hdiag :
      ∀ c : PRegularConjClass G p,
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        let bA :=
          canonicalDVRBrauerBasis
            (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
        ∃ a : A,
          bA c c - (1 : A) =
            (ConjClasses.centralizerPPart p c.1 : A) * a)
    (hoffDiagonal :
      ∀ c d : PRegularConjClass G p,
        c ≠ d →
          let hπ_pairwise :=
            pairwiseNonisomorphic_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_coord
          let hπ_complete :=
            complete_irreducible_family_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_simple hπ_coord
          let bA :=
            canonicalDVRBrauerBasis
              (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
          ∃ a : A,
            bA c d =
              (ConjClasses.centralizerPPart p d.1 : A) * a) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  intro c d
  by_cases hcd : c = d
  · subst d
    simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibility, Pi.single_apply]
      using hdiag c
  · rcases hoffDiagonal c d hcd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibility, Pi.single_apply, hcd]
      using ha

end BrauerVisibleReadbackCaseSplitFinal

end Representation
