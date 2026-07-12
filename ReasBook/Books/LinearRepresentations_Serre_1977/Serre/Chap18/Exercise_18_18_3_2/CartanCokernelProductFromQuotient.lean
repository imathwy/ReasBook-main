import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductFiniteImageAdapter
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanCokernelProductImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelProductFromQuotient

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanCokernelProductFromQuotientFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelProductFromQuotientDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Non-fixed source-quotient/product image input.

This is the precise extra finite-image statement still needed by the quotient route: for some
Cartan-coordinate `A`-span product equivalence, the actual integral Cartan image inside the
displayed product agrees additively with the coordinatewise integer image. -/
def projectiveCartanSourceQuotientProductImageMatchesIntegerImage : Prop :=
  ∃ e :
    ((PRegularConjClass G p → K) ⧸
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K))) ≃ₗ[A]
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K),
    Nonempty
      ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e).range ≃+
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range)

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- One-sided finite-image criterion for the projective Cartan product range.

Because the integral Cartan-coordinate quotient embeds in the displayed product, it is enough to
show that its image lies in the coordinatewise integer image and that the Cartan cokernel has the
same finite cardinality as that integer image. This is the product-range analogue of the canonical
source-product finite image adapter. -/
theorem projectiveCartanProductImageMatchesIntegerImage_of_range_le_of_cokernel_natCard_eq
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
    (hrange :
      (cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e).range ≤
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range)
    (hcard :
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range) :
    Nonempty
      ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e).range ≃+
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range) := by
  let φ :=
    cartanCoordinateRangeQuotientToProjectiveCartanProduct
      (p := p) (A := A) (K := K) (G := G) e
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  refine
    addMonoidHom_range_nonempty_addEquiv_of_le_of_injective_of_domain_natCard_eq
      φ ψ ?_ ?_ ?_ ?_
  · simpa [ψ] using
      regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_ne_zero
        (p := p) (A := A) (K := K) (G := G)
  · simpa [φ] using
      cartanCoordinateRangeQuotientToProjectiveCartanProduct_injective
        (p := p) (A := A) (K := K) (G := G) e
  · simpa [φ, ψ] using hrange
  · calc
      Nat.card
          (((PRegularConjClass G p → ℤ) ⧸
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range)) =
          Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) := by
            exact
              (Nat.card_congr
                (cartanCokernel_addEquiv_cartanCoordinateRangeQuotient
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).toEquiv).symm
      _ = Nat.card ψ.range := by
            simpa [ψ] using hcard

/-- Forward-inclusion plus cardinality form of the remaining projective source-quotient image
input. The inclusion and determinant/cardinality halves can be attacked independently. -/
def projectiveCartanSourceQuotientProductFiniteImageCriterion : Prop :=
  ∃ e :
    ((PRegularConjClass G p → K) ⧸
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K))) ≃ₗ[A]
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K),
    (cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G) e).range ≤
      (regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)).range ∧
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The finite-image criterion gives the source quotient/product image match. -/
theorem projectiveCartanSourceQuotientProductImageMatchesIntegerImage_of_finiteImageCriterion
    (hfinite :
      projectiveCartanSourceQuotientProductFiniteImageCriterion
        (p := p) (A := A) (K := K) (G := G)) :
    projectiveCartanSourceQuotientProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hfinite with ⟨e, hrange, hcard⟩
  exact
    ⟨e,
      projectiveCartanProductImageMatchesIntegerImage_of_range_le_of_cokernel_natCard_eq
        (p := p) (A := A) (K := K) (G := G) e hrange hcard⟩

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Product-range form of the non-fixed source quotient adapter. -/
theorem projectiveCartanProductRange_nonempty_addEquiv_pi_of_sourceQuotientProduct
    (himage :
      projectiveCartanSourceQuotientProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    ∃ e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K),
      Nonempty
        ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
            (p := p) (A := A) (K := K) (G := G) e).range ≃+
          ∀ c : PRegularConjClass G p,
            ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases himage with ⟨e, hmatch⟩
  exact
    ⟨e,
      projectiveCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
        (p := p) (A := A) (K := K) (G := G) e hmatch⟩

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Residue-field Cartan cokernel product obtained from the non-fixed source quotient/product
image input.

The quotient/product decomposition alone supplies an ambient `K / dA` product and an injected
finite Cartan image. The additional hypothesis above is exactly the remaining identification of
that finite image with the coordinatewise integer image. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_sourceQuotientProduct
    (himage :
      projectiveCartanSourceQuotientProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases
      projectiveCartanProductRange_nonempty_addEquiv_pi_of_sourceQuotientProduct
        (p := p) (A := A) (K := K) (G := G) himage with
    ⟨e, hproduct⟩
  exact
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_projectiveCartanProductRange
      (p := p) (A := A) (K := K) (G := G) e hproduct

end CartanCokernelProductFromQuotient

end Representation
