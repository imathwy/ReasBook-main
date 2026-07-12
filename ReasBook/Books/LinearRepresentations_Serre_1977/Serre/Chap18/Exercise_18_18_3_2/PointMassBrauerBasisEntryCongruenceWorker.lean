import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ExplicitResidualBasisAlgebraWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ExplicitResidualPairingSumWorker

/-!
Brauer basis-entry congruence frontier for the point-mass residual route.

Both current residual workers reduce the remaining Serre `18.5(a)` source input to the same
entrywise congruence

```
  bA c d = delta c d  mod centralizerPPart(d).
```

This file keeps that frontier in a single place.  The first lemma records that the
`canonicalDVRBrauerBasis` and the explicit Exercise `18.18.2.9` basis used by the orthogonality
worker are definitionally the same basis.  The following lemmas show that the two named residual
frontiers are exactly the same proposition, and then identify them with the older fixed-coordinate
Brauer-basis readback congruence.

No Cartan range, cokernel, determinant, or product endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PointMassBrauerBasisEntryCongruenceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance pointMassBrauerBasisEntryCongruenceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassBrauerBasisEntryCongruenceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The canonical DVR Brauer basis is the Exercise `18.18.2.9` Brauer basis with the canonical
Hensel lift of prime-to-`p` roots. -/
theorem canonicalDVRBrauerBasis_eq_exercise_18_18_2_9_basis
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete =
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A)
        (primeToPRoot_canonicalLift (p := p) (A := A))
        (primeToPRoot_unitsLift_injective (p := p) (A := A))
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete := by
  rfl

/-- The point-mass source congruence isolated by the orthogonality worker is exactly the same
entrywise Brauer-basis congruence as the visible readback divisibility isolated by the pure
basis-algebra worker. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_iff_visibleReadbackBasisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  rfl

/-- Forward alias for the definitional bridge from the orthogonality-worker source congruence
to the basis-algebra visible readback form. -/
theorem visibleReadbackBasisAlgebra_of_orthogonalityPairingSumPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_visibleReadbackBasisAlgebra
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource

/-- Reverse alias for the definitional bridge from basis-algebra visible readback to the
orthogonality-worker point-mass source congruence. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_visibleReadbackBasisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_visibleReadbackBasisAlgebra
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread

/-- The basis-algebra visible readback frontier is the coordinate-normalized specialization of
the fixed-coordinate Brauer-basis readback congruence. -/
theorem visibleReadbackBasisAlgebra_iff_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  constructor
  · intro hread c d
    rcases hread c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hcoord_d :
        ((regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
      rw [hπ_coord c]
    simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
      brauerBasisFixedCoordinateReadbackDivisibility, hπ_pairwise, hπ_complete,
      hcoord_d] using ha
  · intro hread c d
    rcases hread c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hcoord_d :
        ((regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
      rw [hπ_coord c]
    simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
      brauerBasisFixedCoordinateReadbackDivisibility, hπ_pairwise, hπ_complete,
      hcoord_d] using ha

/-- Combined reduction: after the canonical/Exercise-basis identification, the point-mass source
congruence is precisely the fixed-coordinate Brauer-basis entry congruence for the same
coordinate-normalized family. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  exact
    (orthogonalityPairingSumPointMassSourceCongruence_iff_visibleReadbackBasisAlgebra
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
      (visibleReadbackBasisAlgebra_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

end PointMassBrauerBasisEntryCongruenceWorker

end Representation
