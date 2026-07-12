import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopePairing
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackFromPairing

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisReadbackFromPairingFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackFromPairingDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pairing-route source formula specialized to the coordinate-normalized Brauer family.

This is the exact contribution supplied by Exercise `18.4` plus Serre's projective-envelope
orthogonality relation: the regular restriction of the projective envelope of the `c`-th simple
has `d`-coordinate equal to the centralizer `p`-part times the Exercise `18.4` coordinate of the
prime-to-`p` point mass at the inverse class. -/
theorem coordinateNormalized_projectiveEnvelope_regularRestriction_value_from_pairing
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
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
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
      algebraMap A K
        ((ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c)) := by
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
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  change
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
      algebraMap A K
        ((ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c))
  have hsrc :=
    projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
      (p := p) (A := A) (K := K) (G := G)
      (hω := hω)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) c
      (inversePRegularConjClass (p := p) d)
  change
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)
        (inversePRegularConjClass (p := p) (inversePRegularConjClass (p := p) d)) =
      algebraMap A K
        ((ConjClasses.centralizerPPart p (inversePRegularConjClass (p := p) d).1 : A) *
          ((canonicalDVRBrauerBasis
            (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete).repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c)) at hsrc
  rw [inversePRegularConjClass_involutive] at hsrc
  rw [inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] at hsrc
  simpa [bA] using hsrc

/-- The pure `A`-valued residual left after subtracting the projective-envelope row supplied by
the pairing formula.

This is the smallest remaining fixed-coordinate readback input isolated by the pairing route:
the previous theorem supplies the subtracted centralizer-`p`-part multiple, so proving this
residual condition is equivalent to the desired fixed-coordinate congruence for the same
coordinate-normalized family. -/
def coordinateNormalizedBrauerBasisPairingResidualDivisibility
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
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a

/-- If one regular class has trivial centralizer `p`-part, then the pairing residual at that
class is automatically divisible.  This is the direct A-side residual calculation, not a rewrite
through the fixed-coordinate readback equivalence. -/
theorem coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_centralizerPPart_eq_one
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (hd : ConjClasses.centralizerPPart p d.1 = 1) :
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
  let a : A :=
    bA c d -
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
      (ConjClasses.centralizerPPart p d.1 : A) * coeff
  refine ⟨a, ?_⟩
  have hz : (ConjClasses.centralizerPPart p d.1 : A) = 1 := by
    simp [hd]
  simp [a, coeff, bA, hz]

/-- Degenerate residual case: if all regular centralizer `p`-parts are trivial, the
coordinate-normalized pairing residual divisibility follows directly from the pointwise
`centralizerPPart = 1` calculation. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_forall_centralizerPPart_eq_one
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcentral :
      ∀ d : PRegularConjClass G p, ConjClasses.centralizerPPart p d.1 = 1) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  exact
    coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_centralizerPPart_eq_one
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d (hcentral d)

/-- The pairing residual is reduced to regular classes with nontrivial centralizer `p`-part. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
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
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
  · exact
      coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_centralizerPPart_eq_one
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d hd
  · exact hresidual c d hd

/-- Equivalent nontrivial-coordinate form of the pairing residual. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivial_centralizerPPart
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
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
                (ConjClasses.centralizerPPart p d.1 : A) * a := by
  constructor
  · intro hresidual c d _hd
    exact hresidual c d
  · exact
      coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The residual isolated above closes the canonical DVR Brauer-basis fixed-coordinate readback
congruence. This final step is only `A`-linear arithmetic and the coordinate normalization
`regularClassCoordinateAddEquiv [π c] = Pi.single c 1`. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
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
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases hresidual c d with ⟨a, ha⟩
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

/-!
Minimal missing Lean statement after the pairing computation above:

```
coordinateNormalizedBrauerBasisPairingResidualDivisibility
  (p := p) (A := A) (G := G) π hπ_simple hπ_coord
```

Equivalently, pointwise:

```
∀ c d : PRegularConjClass G p,
  ∃ a : A,
    bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
      - (ConjClasses.centralizerPPart p d.1 : A)
          * (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c)
      =
    (ConjClasses.centralizerPPart p d.1 : A) * a
```

Here `bA` is the canonical DVR Brauer basis attached to the coordinate-normalized `π`.  The
pairing theorem proves the subtracted projective-envelope term is exactly a projective row; the
remaining displayed residual is the part not closed by the current pairing/indicator API.
-/

end BrauerBasisReadbackFromPairing

end Representation
