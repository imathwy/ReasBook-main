import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.VisibleReadbackCaseSplitSourceWorker

/-!
Off-diagonal source-side completion boundary for visible point-mass readback.

The unconditional off-diagonal theorem is exactly the remaining source readback step.  This file
keeps only the off-diagonal, nontrivial-centralizer residue that is left after Exercise `18.4`
expands the inverse prime-to-`p` indicator in the canonical DVR Brauer basis.  The trivial
centralizer columns are formal, and the displayed residue closes the off-diagonal target by
pure `A`-algebra.

No Cartan cokernel, product, Smith, determinant, or final range endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section VisibleReadbackOffDiagonalSourceCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance visibleReadbackOffDiagonalSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance visibleReadbackOffDiagonalSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact off-diagonal source residue still needed after the visible
`centralizerPPart * repr` column has been split off by the Exercise `18.4` basis expansion.

It is restricted to `c ≠ d` and to columns whose centralizer `p`-part is nontrivial; the
remaining columns are automatic because divisibility by `1` is formal. -/
def exercise18_4PointMassRowVisibleReadbackOffDiagonalNontrivialResidualSourceLemma :
    Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p),
    c ≠ d →
      ConjClasses.centralizerPPart p d.1 ≠ 1 →
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
          bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            (ConjClasses.centralizerPPart p d.1 : A) *
              (bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G)
                  (inversePRegularConjClass (p := p) d)) c) =
            (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The nontrivial off-diagonal residual closes the off-diagonal half of visible readback.

For `c ≠ d`, the fixed coordinate row is zero.  The residue differs from the desired entry only
by the already visible multiple
`centralizerPPart(d) * bA.repr (primeToP_regular_indicator d⁻¹) c`, so adding that multiple back
gives the required quotient. -/
theorem exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma_of_nontrivialResidual
    (hresidual :
      exercise18_4PointMassRowVisibleReadbackOffDiagonalNontrivialResidualSourceLemma
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma
      (p := p) (A := A) (G := G) := by
  classical
  intro π hπ_simple hπ_coord c d hcd
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
  by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
  · refine ⟨bA c d, ?_⟩
    have hz : z = 1 := by
      simp [z, hd]
    change bA c d = z * bA c d
    simp [hz]
  · let coeff : A :=
      (bA.repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G)
          (inversePRegularConjClass (p := p) d)) c)
    rcases hresidual π hπ_simple hπ_coord c d hcd hd with ⟨a, ha⟩
    refine ⟨a + coeff, ?_⟩
    have hdc : d ≠ c := fun h => hcd h.symm
    have hsingle :
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) = 0 := by
      simp [hdc]
    have ha' :
        bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            z * coeff =
          z * a := by
      simpa [hπ_pairwise, hπ_complete, bA, z, coeff] using ha
    calc
      bA c d =
          (bA c d -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
              z * coeff) +
            z * coeff := by
            rw [hsingle]
            ring
      _ = z * a + z * coeff := by
            rw [ha']
      _ = z * (a + coeff) := by
            rw [mul_add]

/-- Direct Brauer-row form of the off-diagonal source boundary.

After unfolding `canonicalDVRBrauerBasis`, this is exactly the nontrivial-column part of the
off-diagonal target: away from the diagonal, the coordinate point mass contributes zero, so the
only remaining input is divisibility of the actual Brauer-character row value. -/
def exercise18_4PointMassRowVisibleReadbackOffDiagonalBrauerCharacterSourceLemma :
    Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p),
    c ≠ d →
      ConjClasses.centralizerPPart p d.1 ≠ 1 →
        ∃ a : A,
          FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := A) (π c)
              (primeToPRoot_canonicalLift (p := p) (A := A)) d =
            (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The direct Brauer-row off-diagonal source boundary is equivalent to the canonical-basis
off-diagonal source theorem.  The `centralizerPPart = 1` columns are formal, and on the
nontrivial columns `canonicalDVRBrauerBasis` unfolds to the Brauer-character row. -/
theorem exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma_iff_brauerCharacterSource :
    exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowVisibleReadbackOffDiagonalBrauerCharacterSourceLemma
        (p := p) (A := A) (G := G) := by
  classical
  constructor
  · intro hoff π hπ_simple hπ_coord c d hcd hd
    rcases hoff π hπ_simple hπ_coord c d hcd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    have hbasis :
        bA c d =
          FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := A) (π c)
              (primeToPRoot_canonicalLift (p := p) (A := A)) d := by
      simp [bA, canonicalDVRBrauerBasis]
    rw [← hbasis]
    exact ha
  · intro hchar π hπ_simple hπ_coord c d hcd
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
    · refine ⟨bA c d, ?_⟩
      have hz : (ConjClasses.centralizerPPart p d.1 : A) = 1 := by
        simp [hd]
      change bA c d = (ConjClasses.centralizerPPart p d.1 : A) * bA c d
      simp [hz]
    · rcases hchar π hπ_simple hπ_coord c d hcd hd with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have hbasis :
          bA c d =
            FDRep.modularCharacterOnPRegularConjClass
                (p := p) (G := G) (A := A) (π c)
                (primeToPRoot_canonicalLift (p := p) (A := A)) d := by
        simp [bA, canonicalDVRBrauerBasis]
      rw [hbasis]
      exact ha

/-- The off-diagonal source theorem also implies the nontrivial residual isolated above.

Thus the residual is not a weaker side condition: for off-diagonal columns it is exactly the
same missing divisibility after subtracting the already visible
`centralizerPPart * repr` term. -/
theorem exercise18_4PointMassRowVisibleReadbackOffDiagonalNontrivialResidualSourceLemma_of_offDiagonal
    (hoffDiagonal :
      exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackOffDiagonalNontrivialResidualSourceLemma
      (p := p) (A := A) (G := G) := by
  classical
  intro π hπ_simple hπ_coord c d hcd hd
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
  rcases hoffDiagonal π hπ_simple hπ_coord c d hcd with ⟨a, ha⟩
  refine ⟨a - coeff, ?_⟩
  have hdc : d ≠ c := fun h => hcd h.symm
  have hsingle :
      ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) = 0 := by
    simp [hdc]
  calc
    bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        z * coeff =
        bA c d - z * coeff := by
        rw [hsingle]
        ring
    _ = z * a - z * coeff := by
        rw [ha]
    _ = z * (a - coeff) := by
        rw [mul_sub]

/-- The nontrivial residual and the off-diagonal source theorem are equivalent on the
off-diagonal part. -/
theorem exercise18_4PointMassRowVisibleReadbackOffDiagonalNontrivialResidualSourceLemma_iff_offDiagonal :
    exercise18_4PointMassRowVisibleReadbackOffDiagonalNontrivialResidualSourceLemma
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      exercise18_4PointMassRowVisibleReadbackOffDiagonalSourceLemma_of_nontrivialResidual
        (p := p) (A := A) (G := G)
  · exact
      exercise18_4PointMassRowVisibleReadbackOffDiagonalNontrivialResidualSourceLemma_of_offDiagonal
        (p := p) (A := A) (G := G)

end VisibleReadbackOffDiagonalSourceCompletionWorker

end Representation
