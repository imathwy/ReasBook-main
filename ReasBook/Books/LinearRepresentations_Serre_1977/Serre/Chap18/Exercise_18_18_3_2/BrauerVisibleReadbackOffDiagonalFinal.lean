import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualMatrixClosureFinal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerResidualValuationFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerVisibleReadbackOffDiagonalFinal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerVisibleReadbackOffDiagonalFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerVisibleReadbackOffDiagonalFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Visible readback divisibility is the exact DVR valuation input for the same residual. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_visibleReadbackDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hreadback :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases hreadback c d with ⟨a, ha⟩
  have hdiv :
      (ConjClasses.centralizerPPart p d.1 : A) ∣
        coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
    refine ⟨a, ?_⟩
    simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibility,
      coordinateNormalizedBrauerBasis_visibleReadbackResidual] using ha
  exact
    (IsDiscreteValuationRing.addVal_le_iff_dvd
      (R := A)
      (a := (ConjClasses.centralizerPPart p d.1 : A))
      (b := coordinateNormalizedBrauerBasis_visibleReadbackResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)).2 hdiv

/-- Diagonal and off-diagonal visible readback divisibility hypotheses give the exact
visible-readback DVR valuation input. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_diagonal_offDiagonal
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
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  refine
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_visibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord ?_
  intro c d
  by_cases hcd : c = d
  · subst d
    simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibility, Pi.single_apply]
      using hdiag c
  · rcases hoffDiagonal c d hcd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibility, Pi.single_apply, hcd]
      using ha

/-- Off-diagonal extraction from the current A-side pairing residual.

For `c ≠ d`, the fixed coordinate point mass is zero, so the visible
projective-envelope multiple can be added back without changing the target divisibility
lattice.  This is a purely local A-side step and does not use any Cartan range/cokernel/product
endpoint. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackOffDiagonalDivisibility_of_pairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p) (hcd : c ≠ d) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c d = (ConjClasses.centralizerPPart p d.1 : A) * a := by
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
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases hresidual c d with ⟨a, ha⟩
  refine ⟨a + coeff, ?_⟩
  have hdc : d ≠ c := fun h => hcd h.symm
  have hsingle :
      ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) = 0 := by
    simp [hdc]
  calc
    bA c d =
        (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          z * coeff) +
          z * coeff := by
          rw [hsingle]
          ring
    _ = z * a + z * coeff := by
          rw [ha]
    _ = z * (a + coeff) := by
          rw [mul_add]

/-- Off-diagonal extraction from the visible readback statement.

This is the exact off-diagonal pointwise target once the visible readback congruence is known:
the `Pi.single` coordinate vanishes away from the diagonal. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackOffDiagonalDivisibility_of_visibleReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hreadback :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p) (hcd : c ≠ d) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c d = (ConjClasses.centralizerPPart p d.1 : A) * a := by
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
  let z : A := ConjClasses.centralizerPPart p d.1
  rcases hreadback c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdc : d ≠ c := fun h => hcd h.symm
  have hsingle :
      ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) = 0 := by
    simp [hdc]
  calc
    bA c d =
        bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
          rw [hsingle]
          ring
    _ = z * a := ha

/-- Off-diagonal extraction from the original fixed-coordinate readback congruence.

This version keeps the source-side `regularClassCoordinateAddEquiv` visible.  Under the
coordinate normalization hypothesis, its off-diagonal value is the zero `Pi.single` coordinate. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackOffDiagonalDivisibility_of_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hreadback :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord))
    (c d : PRegularConjClass G p) (hcd : c ≠ d) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c d = (ConjClasses.centralizerPPart p d.1 : A) * a := by
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
  let coord : PRegularConjClass G p → ℤ :=
    regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G))
  let z : A := ConjClasses.centralizerPPart p d.1
  rcases hreadback c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdc : d ≠ c := fun h => hcd h.symm
  have hcoord_zero : (coord d : A) = 0 := by
    rw [show coord = (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) by
      exact hπ_coord c]
    simp [hdc]
  calc
    bA c d = bA c d - (coord d : A) := by
        rw [hcoord_zero]
        ring
    _ = z * a := ha

end BrauerVisibleReadbackOffDiagonalFinal

end Representation
