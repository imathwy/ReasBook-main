import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PrimeToPIndicatorBasisCoefficientWorker

/-!
Direct completion boundary for the inverse prime-to-`p` indicator coefficient route.

The unconditional Exercise `18.4` computation available here is the weighted inverse-indicator
column expansion.  This file records the strongest direct source-side reduction obtained from
that route: the inverse-indicator coefficient residual is exactly the fixed-coordinate Brauer row
readback congruence, and the only columns that need proof are those with nontrivial
centralizer `p`-part.

No Cartan cokernel/product/Smith/endpoint argument is used in this file.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section InverseIndicatorCoefficientDirectCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance inverseIndicatorCoefficientDirectCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance inverseIndicatorCoefficientDirectCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Direct coefficient boundary: after removing the visibly divisible inverse-indicator
coefficient column, the residual is exactly the visible Brauer-row readback congruence. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_visibleReadback_direct
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    inversePrimeToPIndicatorCoefficientResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pairingResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback_basisAlgebra
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

/-- The same boundary in the source-faithful fixed-coordinate readback language.  This is the
minimal direct row congruence left by the inverse-indicator route. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_fixedCoordinateReadback_direct
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
    inversePrimeToPIndicatorCoefficientResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
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
    (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_visibleReadback_direct
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
      (visibleReadbackBasisAlgebra_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

/-- Supplying the fixed-coordinate Brauer row congruence closes the inverse-indicator
coefficient residual, hence the point-mass source congruence. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_of_fixedCoordinateReadback_direct
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord)) :
    inversePrimeToPIndicatorCoefficientResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_fixedCoordinateReadback_direct
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread

/-- Fixed-coordinate Brauer row readback is sufficient for the desired point-mass source
congruence through the inverse-indicator coefficient residual. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_fixedCoordinateReadback_via_inverseIndicator
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pointMassSourceCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
    (inversePrimeToPIndicatorCoefficientResidualDivisibility_of_fixedCoordinateReadback_direct
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hread)

/-- Nontrivial-column form of the fixed-coordinate blocker.  The columns with
`centralizerPPart = 1` are automatic, so this is the smallest columnwise source input left by
the direct coefficient route. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_nontrivialFixedCoordinateReadback
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
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    inversePrimeToPIndicatorCoefficientResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      ∀ c d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 ≠ 1 →
          ∃ a : A,
            bA c d -
              ((regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
                (ConjClasses.centralizerPPart p d.1 : A) * a := by
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
  exact
    (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_fixedCoordinateReadback_direct
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
      (brauerBasisFixedCoordinateReadbackDivisibility_iff_nontrivial_centralizerPPart
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete)

/-- The coordinate-normalized point-mass version of the previous nontrivial-column blocker. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_nontrivialPointMassReadback
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
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    inversePrimeToPIndicatorCoefficientResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      ∀ c d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 ≠ 1 →
          ∃ a : A,
            bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
                (ConjClasses.centralizerPPart p d.1 : A) * a := by
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
  constructor
  · intro hres c d hd
    have hfixed :
        ∀ c d : PRegularConjClass G p,
          ConjClasses.centralizerPPart p d.1 ≠ 1 →
            ∃ a : A,
              bA c d -
                ((regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
                  (ConjClasses.centralizerPPart p d.1 : A) * a :=
      (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_nontrivialFixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hres
    simpa [hπ_coord c, hπ_pairwise, hπ_complete, bA] using hfixed c d hd
  · intro hpoint
    have hfixed :
        ∀ c d : PRegularConjClass G p,
          ConjClasses.centralizerPPart p d.1 ≠ 1 →
            ∃ a : A,
              bA c d -
                ((regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
                  (ConjClasses.centralizerPPart p d.1 : A) * a := by
      intro c d hd
      simpa [hπ_coord c, hπ_pairwise, hπ_complete, bA] using hpoint c d hd
    exact
      (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_nontrivialFixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hfixed

/-- If all regular centralizer `p`-parts are trivial, the inverse-indicator coefficient
residual is closed unconditionally. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_of_forall_centralizerPPart_eq_one
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcentral :
      ∀ d : PRegularConjClass G p, ConjClasses.centralizerPPart p d.1 = 1) :
    inversePrimeToPIndicatorCoefficientResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  apply
    (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_visibleReadback_direct
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
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
  refine
    ⟨bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A), ?_⟩
  have hz : (ConjClasses.centralizerPPart p d.1 : A) = 1 := by
    simp [hcentral d]
  simp [bA, hz]

/-- The same degenerate centralizer case closes the point-mass source congruence. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_forall_centralizerPPart_eq_one
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcentral :
      ∀ d : PRegularConjClass G p, ConjClasses.centralizerPPart p d.1 = 1) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pointMassSourceCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
    (inversePrimeToPIndicatorCoefficientResidualDivisibility_of_forall_centralizerPPart_eq_one
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hcentral)

end InverseIndicatorCoefficientDirectCompletionWorker

end Representation
