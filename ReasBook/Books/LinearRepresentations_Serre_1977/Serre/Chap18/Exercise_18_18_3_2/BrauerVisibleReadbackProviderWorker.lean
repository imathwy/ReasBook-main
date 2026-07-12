import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualMatrixClosureFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackResidualProof
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectProof

/-!
This worker keeps the visible readback provider upstream of the Cartan range/cokernel/product
endpoints.  The unconditional fixed-family provider is not available from the imported local
matrix/readback files alone: the remaining source input is still the pointwise divisibility
recorded in `BrauerBasisResidualDirectProof` and `BrauerBasisReadbackResidualProof`.

The bridge below is harmless but useful: for a coordinate-normalized family, the visible
readback statement and the older fixed-coordinate readback statement are the same pointwise
divisibility condition.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerVisibleReadbackProviderWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerVisibleReadbackProviderWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerVisibleReadbackProviderWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- A fixed-coordinate readback proof immediately gives the visible readback form for the same
coordinate-normalized family.  The only step is rewriting the fixed regular-class coordinate
row by `hπ_coord`. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord)) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
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
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  simpa [hπ_pairwise, hπ_complete, bA, hcoord_d] using ha

/-- Conversely, the visible readback form gives the fixed-coordinate readback statement for the
same coordinate-normalized family. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_visibleReadback
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
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  intro c d
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
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  simpa [hπ_pairwise, hπ_complete, bA, hcoord_d] using ha

/-- For a coordinate-normalized family, visible readback and fixed-coordinate readback are
equivalent.  This is a source-side bridge only; it does not use downstream Cartan range,
cokernel, or product endpoints. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_iff_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  constructor
  · exact
      brauerBasisFixedCoordinateReadbackDivisibility_of_visibleReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  · exact
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

end BrauerVisibleReadbackProviderWorker

end Representation
