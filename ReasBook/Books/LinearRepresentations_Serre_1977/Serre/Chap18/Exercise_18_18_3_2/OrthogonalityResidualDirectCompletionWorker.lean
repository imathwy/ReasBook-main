import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFromPairing
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ExplicitResidualPairingSumWorker

/-!
Direct orthogonality residual completion frontier.

This file keeps the Serre `18.5(a)` source route at the class-sum level.  Exercise `18.4`
supplies the `A`-valued Brauer basis, and projective-envelope orthogonality supplies the
visible `<Phi_E, phi_E'> = delta` replacements upstream.  The remaining missing source API is
that the residual class-sum coefficient obtained by pairing

```
  b_c - 1_c
```

with the inverse prime-to-`p` class indicator is again `A`-valued.  The class-sum denominator
calculation below shows this coefficient is exactly
`(centralizerPPart d)^{-1} * (b_c(d) - delta_cd)`, so this `A`-valuedness closes the requested
point-mass source congruence without using Cartan cokernel/product/Smith/determinant endpoints.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section OrthogonalityResidualDirectCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance orthogonalityResidualDirectCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance orthogonalityResidualDirectCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre's class-sum pairing of two `A`-valued regular class functions.

This is the same finite sum as the projective-envelope pairing, with the first factor replaced by
an arbitrary `A`-valued regular class function. -/
noncomputable def regularClassFunctionPairingSum
    (φ ψ : PRegularConjClass G p → A) : K :=
  (Fintype.card G : K)⁻¹ *
    ∑ s : G,
      (if hs : IsPRegular p (s⁻¹) then
        algebraMap A K (φ (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩))
      else 0) *
        (if hs : IsPRegular p s then
          algebraMap A K (ψ (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
        else 0)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Class-sum denominator calculation for the inverse prime-to-`p` indicator.

Pairing an arbitrary `A`-valued regular class function with Serre's prime-to-`p` indicator at
`c` reads the inverse-class value divided by the centralizer `p`-part. -/
theorem regularClassFunctionPairingSum_primeToPIndicator_eq_inverse_value
    (φ : PRegularConjClass G p → A) (c : PRegularConjClass G p) :
    regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
        φ (primeToP_regular_indicator (p := p) (A := A) (G := G) c) =
      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
        algebraMap A K (φ (inversePRegularConjClass (p := p) c)) := by
  classical
  let a : ConjClasses G → K := fun d ↦
    if h : d = c.1 then
      algebraMap A K (φ (inversePRegularConjClass (p := p) c)) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
    else 0
  have hsum :
      ∑ s : G,
        (if hs : IsPRegular p (s⁻¹) then
          algebraMap A K (φ (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩))
        else 0) *
          (if hs : IsPRegular p s then
            algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
          else 0) =
        ∑ s : G, a (ConjClasses.mk s) := by
    refine Finset.sum_congr rfl ?_
    intro s _hs
    by_cases hmk : ConjClasses.mk s = c.1
    · have hs_reg : IsPRegular p s := by
        exact c.2 s (by simpa [ConjClasses.mem_carrier_iff_mk_eq] using hmk)
      have hs_inv : IsPRegular p (s⁻¹) := by
        simpa [IsPRegular, orderOf_inv] using hs_reg
      have hInvClass :
          PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs_inv⟩ =
            inversePRegularConjClass (p := p) c := by
        apply Subtype.ext
        simpa [ConjClasses.inv_mk] using congrArg Inv.inv hmk
      rw [dif_pos hs_inv, dif_pos hs_reg,
        primeToP_regular_indicator_ofSubtype_eq_ordCompl
          (p := p) (A := A) (G := G) c hs_reg hmk]
      simp [a, hmk, hInvClass]
    · by_cases hs_reg : IsPRegular p s
      · rw [dif_pos hs_reg,
          primeToP_regular_indicator_ofSubtype_eq_zero_of_mk_ne
            (p := p) (A := A) (G := G) c hs_reg hmk]
        simp [a, hmk]
      · simp [a, hmk, hs_reg]
  rw [regularClassFunctionPairingSum, hsum,
    sum_over_group_eq_sum_over_conjClasses (G := G) (K := K) a]
  rw [Finset.sum_eq_single c.1]
  · rw [show a c.1 =
        algebraMap A K (φ (inversePRegularConjClass (p := p) c)) *
          algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) from
        dif_pos rfl]
    calc
      (Fintype.card G : K)⁻¹ *
          ((Nat.card c.1.carrier : K) *
            (algebraMap A K (φ (inversePRegularConjClass (p := p) c)) *
              algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)))
          =
        (Fintype.card G : K)⁻¹ *
          (((Nat.card c.1.carrier : K) *
              algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)) *
            algebraMap A K (φ (inversePRegularConjClass (p := p) c))) := by
            ring
      _ =
        (Fintype.card G : K)⁻¹ *
          (((Fintype.card G : K) *
              (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
            algebraMap A K (φ (inversePRegularConjClass (p := p) c))) := by
            rw [class_card_mul_ordCompl_eq_card_mul_centralizerPPart_inv
              (p := p) (A := A) (K := K) (G := G) c]
      _ =
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
          algebraMap A K (φ (inversePRegularConjClass (p := p) c)) := by
          have hcardG_ne : (Fintype.card G : K) ≠ 0 :=
            Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          calc
            (Fintype.card G : K)⁻¹ *
                (((Fintype.card G : K) *
                    (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
                  algebraMap A K (φ (inversePRegularConjClass (p := p) c)))
                =
              (((Fintype.card G : K)⁻¹ * (Fintype.card G : K)) *
                  (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
                algebraMap A K (φ (inversePRegularConjClass (p := p) c)) := by
                  ring
            _ =
              (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
                algebraMap A K (φ (inversePRegularConjClass (p := p) c)) := by
                simp [hcardG_ne]
  · intro d _hd hdc
    simp [a, hdc]
  · intro hc
    simp at hc

/-- The precise source-side missing API for the direct residual route.

For every row `c` and target class `d`, the class-sum coefficient of
`b_c - 1_c` against the inverse prime-to-`p` indicator of `d` is required to be in the image of
`A` inside `K`.  The theorem below shows this is enough to close the point-mass congruence. -/
def coordinateNormalizedBrauerBasisResidualClassSumAValued
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
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          (fun e =>
            bA c e -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
        algebraMap A K a

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The residual class-sum `A`-valuedness closes the pure point-mass source congruence.

This is the direct denominator-clearing step: the class-sum computation identifies the assumed
`A`-valued coefficient with `(centralizerPPart d)^{-1} * (b_c(d) - delta_cd)`. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_residualClassSumAValued
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcoeff :
      coordinateNormalizedBrauerBasisResidualClassSumAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
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
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a
  intro c d
  let diff : PRegularConjClass G p → A := fun e =>
    bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A)
  let invd := inversePRegularConjClass (p := p) d
  rcases hcoeff c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  let z : A := ConjClasses.centralizerPPart p d.1
  have hz : algebraMap A K z ≠ 0 :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) d
  have hpair :
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          diff
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) invd) =
        (algebraMap A K z)⁻¹ * algebraMap A K (diff d) := by
    simpa [diff, invd, z, inversePRegularConjClass_involutive,
      inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] using
      (regularClassFunctionPairingSum_primeToPIndicator_eq_inverse_value
        (p := p) (A := A) (K := K) (G := G) diff invd)
  have hcoeff' :
      (algebraMap A K z)⁻¹ * algebraMap A K (diff d) = algebraMap A K a := by
    rw [← hpair]
    simpa [coordinateNormalizedBrauerBasisResidualClassSumAValued, bA, hπ_pairwise,
      hπ_complete, diff, invd] using ha
  calc
    algebraMap A K
        (bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
        = algebraMap A K (diff d) := by
            simp [diff]
    _ = algebraMap A K z * ((algebraMap A K z)⁻¹ * algebraMap A K (diff d)) := by
            field_simp [hz]
    _ = algebraMap A K z * algebraMap A K a := by
            rw [hcoeff']
    _ = algebraMap A K (z * a) := by
            rw [map_mul]

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Conversely, the point-mass source congruence gives exactly the residual class-sum
`A`-valuedness above.  Together with the previous theorem, this identifies the remaining Lean
API as the `A`-valuedness of this class-sum coefficient. -/
theorem residualClassSumAValued_of_orthogonalityPairingSumPointMassSourceCongruence
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
    coordinateNormalizedBrauerBasisResidualClassSumAValued
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
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
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
            (fun e =>
              bA c e -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
          algebraMap A K a
  intro c d
  let diff : PRegularConjClass G p → A := fun e =>
    bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A)
  let invd := inversePRegularConjClass (p := p) d
  rcases hsource c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  let z : A := ConjClasses.centralizerPPart p d.1
  have hz : algebraMap A K z ≠ 0 :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) d
  have hpair :
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          diff
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) invd) =
        (algebraMap A K z)⁻¹ * algebraMap A K (diff d) := by
    simpa [diff, invd, z, inversePRegularConjClass_involutive,
      inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] using
      (regularClassFunctionPairingSum_primeToPIndicator_eq_inverse_value
        (p := p) (A := A) (K := K) (G := G) diff invd)
  have hdiff : diff d = z * a := by
    simpa [diff, z, bA, canonicalDVRBrauerBasis] using ha
  calc
    regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
        (fun e =>
          bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))
        =
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
        diff
        (primeToP_regular_indicator (p := p) (A := A) (G := G) invd) := by
          rfl
    _ = (algebraMap A K z)⁻¹ * algebraMap A K (diff d) := hpair
    _ = (algebraMap A K z)⁻¹ * algebraMap A K (z * a) := by
          rw [hdiff]
    _ = algebraMap A K a := by
          rw [map_mul]
          field_simp [hz]

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Exact fixed-family boundary for the direct residual route. -/
theorem coordinateNormalizedBrauerBasisResidualClassSumAValued_iff_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisResidualClassSumAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      (let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) := by
  constructor
  · exact
      orthogonalityPairingSumPointMassSourceCongruence_of_residualClassSumAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · exact
      residualClassSumAValued_of_orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The same residual class-sum `A`-valuedness also closes the original fixed-family pairing
residual divisibility. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residualClassSumAValued
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcoeff :
      coordinateNormalizedBrauerBasisResidualClassSumAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
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
  have hsource :
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
    orthogonalityPairingSumPointMassSourceCongruence_of_residualClassSumAValued
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hcoeff
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a
  intro c d
  rcases hsource c d with ⟨a, ha⟩
  let z : A := ConjClasses.centralizerPPart p d.1
  have ha_bA :
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        z * a := by
    simpa [bA, canonicalDVRBrauerBasis, z] using ha
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
  refine ⟨a - coeff, ?_⟩
  calc
    bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        z * coeff
        = z * a - z * coeff := by
            rw [ha_bA]
    _ = z * (a - coeff) := by
          rw [mul_sub]

end OrthogonalityResidualDirectCompletionWorker

end Representation
