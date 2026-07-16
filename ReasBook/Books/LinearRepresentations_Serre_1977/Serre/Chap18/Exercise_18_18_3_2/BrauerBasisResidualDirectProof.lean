import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFromPairing

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisResidualDirectProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisResidualDirectProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisResidualDirectProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Direct `A`-side Exercise `18.4` expansion of a prime-to-`p` point mass after multiplying
by the target centralizer `p`-part.

This is the non-circular matrix identity supplied by the canonical DVR Brauer basis: expand the
prime-to-`p` point mass in the Brauer basis, then multiply the resulting pointwise identity by the
centralizer `p`-part. -/
theorem coordinateNormalizedBrauerBasis_primeToPIndicator_centralizerPPart_sum
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
        bA i c *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator (p := p) (A := A) (G := G) d) i)) =
      (ConjClasses.centralizerPPart p d.1 : A) *
        (primeToP_regular_indicator (p := p) (A := A) (G := G) d c) := by
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
  let f : PRegularConjClass G p → A :=
    primeToP_regular_indicator (p := p) (A := A) (G := G) d
  let z : A := ConjClasses.centralizerPPart p d.1
  have hsum :
      ∑ i : PRegularConjClass G p, (bA.repr f i) * bA i c = f c := by
    simpa [bA, f, Pi.smul_apply] using congrFun (bA.sum_repr f) c
  calc
    ∑ i : PRegularConjClass G p, bA i c * (z * (bA.repr f i))
        = z * ∑ i : PRegularConjClass G p, (bA.repr f i) * bA i c := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
    _ = z * f c := by
          rw [hsum]

omit [IsLocalRing A] [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed k] [CharP k p] in
/-- Evaluation of the inverse prime-to-`p` point mass after multiplying by the target
centralizer `p`-part.  This is the point-mass side of the previous matrix identity, with no
Cartan/product/cokernel input. -/
theorem centralizerPPart_mul_primeToP_regular_indicator_inverse_apply
    (c d : PRegularConjClass G p) :
    (ConjClasses.centralizerPPart p d.1 : A) *
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G)
          (inversePRegularConjClass (p := p) d))
          (inversePRegularConjClass (p := p) c) =
      if c = d then (ConjClasses.centralizerCard d.1 : A) else 0 := by
  classical
  by_cases hcd : c = d
  · subst c
    have hcard :
        ConjClasses.centralizerCard d.1 =
          ConjClasses.centralizerPPart p d.1 *
            ordCompl[p] (ConjClasses.centralizerCard d.1) :=
      ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
        (p := p) (G := G) d.1
    calc
      (ConjClasses.centralizerPPart p d.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G)
            (inversePRegularConjClass (p := p) d))
            (inversePRegularConjClass (p := p) d)
          =
        (ConjClasses.centralizerPPart p d.1 : A) *
          (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) := by
            simp [primeToP_regular_indicator, ConjClasses.centralizerCard_inv]
      _ = (ConjClasses.centralizerCard d.1 : A) := by
            simpa [Nat.cast_mul] using congrArg (fun n : ℕ => (n : A)) hcard.symm
      _ = (if d = d then (ConjClasses.centralizerCard d.1 : A) else 0) := by
            simp
  · have hinv_ne :
        inversePRegularConjClass (p := p) c ≠ inversePRegularConjClass (p := p) d := by
      intro h
      exact hcd (by
        simpa using congrArg (inversePRegularConjClass (p := p)) h)
    simp [primeToP_regular_indicator, hcd, hinv_ne]

/-- In inverse coordinates, the direct `A`-side point-mass expansion recovers the full
centralizer point mass.  This is the finite-matrix content of Exercise `18.4` plus the
prime-to-`p`/`p`-part factorization of centralizer orders. -/
theorem coordinateNormalizedBrauerBasis_inverse_pointMass_matrix_identity
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
      if c = d then (ConjClasses.centralizerCard d.1 : A) else 0 := by
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
  calc
    ∑ i : PRegularConjClass G p,
        bA i (inversePRegularConjClass (p := p) c) *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) i))
        =
      (ConjClasses.centralizerPPart p d.1 : A) *
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G)
          (inversePRegularConjClass (p := p) d))
          (inversePRegularConjClass (p := p) c) := by
          simpa [bA] using
            (coordinateNormalizedBrauerBasis_primeToPIndicator_centralizerPPart_sum
              (p := p) (A := A) (G := G)
              π hπ_simple hπ_coord
              (inversePRegularConjClass (p := p) c)
              (inversePRegularConjClass (p := p) d))
    _ = if c = d then (ConjClasses.centralizerCard d.1 : A) else 0 :=
          centralizerPPart_mul_primeToP_regular_indicator_inverse_apply
            (p := p) (A := A) (G := G) c d

/-- If the source-side row congruence is supplied pointwise, then the pairing residual follows
pointwise by subtracting the explicit Exercise `18.4` coefficient multiple.

This is deliberately only the forward, local arithmetic bridge.  The missing source statement is
the row congruence itself; it cannot be obtained by reading
`regularClassCoordinateAddEquiv [π c]₀ = Pi.single c 1` as a value formula for the Brauer
character row. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_pointwise_of_sourceRowCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (hrow :
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
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a) :
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
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases hrow with ⟨a, ha⟩
  refine ⟨a - coeff, ?_⟩
  calc
    bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) * coeff
        =
          (ConjClasses.centralizerPPart p d.1 : A) * a -
            (ConjClasses.centralizerPPart p d.1 : A) * coeff := by
            rw [ha]
    _ = (ConjClasses.centralizerPPart p d.1 : A) * (a - coeff) := by
          rw [mul_sub]

/-- A fixed-family source-side row congruence closes the pairing residual directly.

This is the formal shape of the remaining source-faithful input: a value congruence for the
canonical DVR Brauer-character rows modulo the target centralizer `p`-part. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_sourceRowCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrow :
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
            (ConjClasses.centralizerPPart p d.1 : A) * a) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  exact
    coordinateNormalizedBrauerBasis_pairingResidual_pointwise_of_sourceRowCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d (hrow c d)

/-!
The direct matrix identity above is the part of the A-side residual supplied by the current
Exercise `18.4` basis and point-mass API.

The remaining non-circular local target is still:

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
      regularClassCoordinateAddEquiv
          (p := p) (G := G)
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
```

Pointwise, with `bA` the canonical DVR Brauer basis attached to the coordinate-normalized `π`,
this asks for:

```
∀ c d : PRegularConjClass G p,
  ∃ a : A,
    bA c d -
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
      (ConjClasses.centralizerPPart p d.1 : A) *
        (bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G)
            (inversePRegularConjClass (p := p) d)) c) =
        (ConjClasses.centralizerPPart p d.1 : A) * a
```
-/

end BrauerBasisResidualDirectProof

end Representation
