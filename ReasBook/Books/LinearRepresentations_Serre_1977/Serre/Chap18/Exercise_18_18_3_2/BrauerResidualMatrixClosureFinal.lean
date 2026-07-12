import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerResidualMatrixClosureFinal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerResidualMatrixClosureFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerResidualMatrixClosureFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The fixed-coordinate readback statement left after the matrix identity has identified the
visible projective-envelope column.  This is the exact missing pointwise lemma type for closing
`coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof` by the local matrix route. -/
def coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a

/-- Re-export of the direct Exercise `18.4` matrix identity in the closure file.

This is the strongest matrix statement currently available from the point-mass expansion alone:
the projective-envelope coefficient column is dual to the inverse regular point masses after
multiplication by the centralizer `p`-part. -/
theorem coordinateNormalizedBrauerBasis_projectiveColumn_matrix_identity_final
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∑ i : PRegularConjClass G p,
        bA i (inversePRegularConjClass (p := p) c) *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) i)) =
      if c = d then (ConjClasses.centralizerCard d.1 : A) else 0 :=
  coordinateNormalizedBrauerBasis_inverse_pointMass_matrix_identity
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d

/-- The explicit projective-envelope column entries are already centralizer-`p`-part multiples.
Thus the pairing residual is equivalent to the fixed-coordinate readback divisibility of the
Brauer rows themselves. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hresidual c d
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
    calc
      bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
          =
            (bA c d -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
              z * coeff) +
            z * coeff := by
              ring
      _ = z * a + z * coeff := by
            rw [ha]
      _ = z * (a + coeff) := by
            rw [mul_add]
  · intro hreadback c d
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
    rcases hreadback c d with ⟨a, ha⟩
    refine ⟨a - coeff, ?_⟩
    calc
      bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          z * coeff
          = z * a - z * coeff := by
              rw [ha]
      _ = z * (a - coeff) := by
            rw [mul_sub]

/-- Conditional final closure: the precise missing readback lemma above is sufficient to prove
the requested pairing residual using only the local A-side residual arithmetic. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_of_visibleReadback
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
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hreadback

end BrauerResidualMatrixClosureFinal

end Representation
