import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalDVRBrauerBasisPointwiseSourceCompletionWorker

/-!
Source-level case split for the final visible point-mass row congruence.

This file keeps the last Exercise `18.4` / orthogonality blocker split into the two
pointwise obligations that can be worked on independently:

* the diagonal congruence `bA c c - 1` is divisible by the centralizer `p`-part of `c`;
* the off-diagonal entry `bA c d` is divisible by the centralizer `p`-part of `d`.

No Cartan range, cokernel, product, Smith, determinant, or downstream endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section VisibleReadbackCaseSplitSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance visibleReadbackCaseSplitSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance visibleReadbackCaseSplitSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Diagonal half of the final visible point-mass row congruence. -/
def exercise18_4PointMassRowVisibleReadbackDiagonalSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p),
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c c - (1 : A) = (ConjClasses.centralizerPPart p c.1 : A) * a

/-- Off-diagonal half of the final visible point-mass row congruence. -/
def exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p),
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
      ∃ a : A, bA c d = (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The final visible source lemma is exactly the conjunction of its diagonal and off-diagonal
parts.  This is the current maximal safe parallel split of the remaining source-side blocker. -/
theorem exercise18_4PointMassRowVisibleReadbackSourceLemma_iff_diagonal_and_offDiagonal :
    exercise18_4PointMassRowVisibleReadbackSourceLemma
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowVisibleReadbackDiagonalSourceLemma
          (p := p) (A := A) (G := G) ∧
        exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma
          (p := p) (A := A) (G := G) := by
  constructor
  · intro hvisible
    constructor
    · intro π hπ_simple hπ_coord c
      rcases hvisible π hπ_simple hπ_coord c c with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra]
        using ha
    · intro π hπ_simple hπ_coord c d hcd
      rcases hvisible π hπ_simple hπ_coord c d with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have hdc : d ≠ c := fun h => hcd h.symm
      simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
        Pi.single_apply, hdc] using ha
  · rintro ⟨hdiag, hoffDiagonal⟩ π hπ_simple hπ_coord c d
    by_cases hcd : c = d
    · subst d
      rcases hdiag π hπ_simple hπ_coord c with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra]
        using ha
    · rcases hoffDiagonal π hπ_simple hπ_coord c d hcd with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have hdc : d ≠ c := fun h => hcd h.symm
      simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
        Pi.single_apply, hdc] using ha

end VisibleReadbackCaseSplitSourceWorker

end Representation
