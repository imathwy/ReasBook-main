import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFromPairing

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackResidualProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisReadbackResidualProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackResidualProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The fixed-coordinate DVR Brauer-basis readback congruence implies the pairing residual.

This is only the visible subtraction of the projective-envelope row supplied by the
Exercise `18.4` basis plus Serre's orthogonality computation; the remaining mathematical input is
the fixed-coordinate readback congruence itself. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_fixedCoordinateReadback
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
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
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
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases hread c d with ⟨a, ha⟩
  refine ⟨a - coeff, ?_⟩
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  calc
    bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        z * coeff =
      bA c d -
          ((regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) -
        z * coeff := by
          rw [hcoord_d]
    _ = z * a - z * coeff := by
          rw [ha]
    _ = z * (a - coeff) := by
          rw [mul_sub]

/-- The pairing residual is equivalent to the fixed-coordinate DVR Brauer-basis readback
congruence. Both directions are pure `A`-linear arithmetic after the pairing row has been
identified by Exercise `18.4` and orthogonality. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
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
      brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  · exact
      coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Nontrivial-coordinate bridge from fixed readback to the pairing residual.

This avoids using the full residual/readback equivalence: the `centralizerPPart = 1` coordinates
are supplied by the pointwise trivial lemma, and the displayed proof only subtracts the
projective-envelope row multiple on the remaining coordinates. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      ∀ c d : PRegularConjClass G p,
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
                ((regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
                (ConjClasses.centralizerPPart p d.1 : A) * a) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  refine
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord ?_
  intro c d hd
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
  rcases hread c d hd with ⟨a, ha⟩
  refine ⟨a - coeff, ?_⟩
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  calc
    bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        z * coeff =
      bA c d -
          ((regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) -
        z * coeff := by
          rw [hcoord_d]
    _ = z * a - z * coeff := by
          rw [ha]
    _ = z * (a - coeff) := by
          rw [mul_sub]

/-- Nontrivial-coordinate bridge from the pairing residual to fixed readback.

This is the reverse A-side arithmetic step restricted to `centralizerPPart ≠ 1`; the trivial
coordinates are filled by the existing pointwise `centralizerPPart = 1` readback lemma. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivial_pairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      ∀ c d : PRegularConjClass G p,
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
                (ConjClasses.centralizerPPart p d.1 : A) * a) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  refine
    brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivial_centralizerPPart
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) ?_
  intro c d hd
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
  rcases hresidual c d hd with ⟨a, ha⟩
  refine ⟨a + coeff, ?_⟩
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  calc
    bA c d -
        ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A)
        =
          (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            z * coeff) + z * coeff := by
            rw [hcoord_d]
            ring
    _ = z * a + z * coeff := by
          rw [ha]
    _ = z * (a + coeff) := by
          rw [mul_add]

/-- Endpoint wrapper for the remaining non-circular A-side pointwise residual.

This is the smallest fixed-coordinate readback input still needed by the current A-side API:
for every nontrivial centralizer-`p`-part coordinate, the canonical DVR Brauer row minus the
coordinate point mass and the visible projective-envelope multiple is already a
centralizer-`p`-part multiple.  The `centralizerPPart = 1` coordinates are closed by
`brauerBasisFixedCoordinateReadbackDivisibility_pointwise_of_centralizerPPart_eq_one`, via
`brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivial_pairingResidual`.

This theorem does not use the readback iff, coordinate iff, projective-restriction iff, or any
Cartan/cokernel endpoint. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_proof_of_pointwiseResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      ∀ c d : PRegularConjClass G p,
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
                (ConjClasses.centralizerPPart p d.1 : A) * a) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
  brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivial_pairingResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual

/-!
Remaining non-circular local goal:

```
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof
    {p : ℕ}
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    {G : Type u} [Group G] [Finite G]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord : ∀ c,
      regularClassCoordinateAddEquiv (p := p) (G := G)
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
```

By the equivalence above, the remaining proof obligation is exactly the fixed-coordinate
readback congruence:

```
brauerBasisFixedCoordinateReadbackDivisibility
  (p := p) (A := A) (G := G)
  π
  (pairwiseNonisomorphic_of_regularClassCoordinate_single
    (p := p) (G := G) (π := π) hπ_coord)
  (complete_irreducible_family_of_regularClassCoordinate_single
    (p := p) (G := G) (π := π) hπ_simple hπ_coord)
```
-/

end BrauerBasisReadbackResidualProof

end Representation
