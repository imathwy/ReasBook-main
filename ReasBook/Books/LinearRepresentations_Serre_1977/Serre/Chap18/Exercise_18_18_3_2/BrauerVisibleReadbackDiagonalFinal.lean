import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerResidualMatrixClosureFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerVisibleReadbackDiagonalFinal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerVisibleReadbackDiagonalFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerVisibleReadbackDiagonalFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The diagonal readback is automatic at classes with trivial centralizer `p`-part.

This is the unconditional part already supplied by the existing A-side readback API; no Cartan
range, cokernel, or product endpoint is used. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDiagonalDivisibility_of_centralizerPPart_eq_one
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p)
    (hc : ConjClasses.centralizerPPart p c.1 = 1) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c c - (1 : A) = (ConjClasses.centralizerPPart p c.1 : A) * a := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  rcases
      brauerBasisFixedCoordinateReadbackDivisibility_pointwise_of_centralizerPPart_eq_one
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete c c hc with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hcoord :
      ((regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G))) c : A) =
        (1 : A) := by
    rw [hπ_coord c]
    simp
  simpa [hπ_pairwise, hπ_complete, bA, hcoord] using ha

/-- Diagonal extraction from the fixed visible readback residual.

This is the exact pointwise diagonal consequence of the current non-Cartan readback blocker:
after substituting `d = c`, the fixed coordinate row is `Pi.single c 1`, hence its diagonal
entry is `1`. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDiagonalDivisibility_of_visibleReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hreadback :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c c - (1 : A) = (ConjClasses.centralizerPPart p c.1 : A) * a := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  rcases hreadback c c with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [Pi.single_eq_same, hπ_pairwise, hπ_complete, bA] using ha

/-- The same diagonal extraction from the older fixed-coordinate readback API.

The only extra step compared with the visible form is rewriting the fixed regular-class
coordinate by `hπ_coord`. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDiagonalDivisibility_of_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hreadback :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord))
    (c : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c c - (1 : A) = (ConjClasses.centralizerPPart p c.1 : A) * a := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  rcases hreadback c c with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hcoord :
      ((regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G))) c : A) =
        (1 : A) := by
    rw [hπ_coord c]
    simp
  simpa [hπ_pairwise, hπ_complete, bA, hcoord] using ha

end BrauerVisibleReadbackDiagonalFinal

end Representation
