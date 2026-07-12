import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegralQuotient
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelSmith

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegralProductBridge

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local instance projectiveCartanIntegralProductBridgeFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegralProductBridgeDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The existing integer-quotient injection identifies the Cartan cokernel with its image inside
the source-product quotient. This is the strongest unconditional conclusion supplied by the
current integral quotient route: the target is the actual range subgroup of the displayed
`K / dA` product, not the whole product. -/
noncomputable def cartanCokernel_addEquiv_projectiveCartanProductRange
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      (cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G) e).range :=
  (cartanCokernel_addEquiv_cartanCoordinateRangeQuotient
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).trans
    (AddMonoidHom.ofInjective
      (cartanCoordinateRangeQuotientToProjectiveCartanProduct_injective
        (p := p) (A := A) (K := K) (G := G) e))

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- The product-range subgroup obtained from the integral quotient route is finite. -/
theorem projectiveCartanProductRange_finite
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) :
    Finite
      (cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G) e).range := by
  letI : Finite (cartanCokernel (IsLocalRing.ResidueField A) G) :=
    cartanCokernel_finite (p := p) (k := IsLocalRing.ResidueField A) (G := G)
  exact
    Finite.of_equiv (cartanCokernel (IsLocalRing.ResidueField A) G)
      (cartanCokernel_addEquiv_projectiveCartanProductRange
        (p := p) (A := A) (K := K) (G := G) e).toEquiv

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- The product-range subgroup obtained from the integral quotient route is a `p`-group. -/
theorem projectiveCartanProductRange_isPGroup
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) :
    IsPGroup p
      (Multiplicative
        (cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e).range) := by
  exact
    (cartanCokernel_isPGroup (p := p) (k := IsLocalRing.ResidueField A) (G := G)).of_equiv
      (AddEquiv.toMultiplicative
        (cartanCokernel_addEquiv_projectiveCartanProductRange
          (p := p) (A := A) (K := K) (G := G) e))

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- If the finite image subgroup from the integral quotient route is identified with the expected
centralizer-`p`-part cyclic product, then the existing Smith adapter gives the desired coordinate
description of the Cartan range. -/
theorem existsCartanRangeCoordinateEquiv_of_projectiveCartanProductRange_equiv_pi
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
    (himage :
      Nonempty
        ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G) e).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    ∃ coord : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map coord.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rcases himage with ⟨himage⟩
  have hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
    ⟨(cartanCokernel_addEquiv_projectiveCartanProductRange
        (p := p) (A := A) (K := K) (G := G) e).trans himage⟩
  exact
    existsCartanRangeCoordinateEquiv_of_cokernelProduct_and_invariantFactorUniqueness
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) hCokernel
      (cartanCokernelCentralizerPPartProductUniqueness_holds (p := p) (G := G))

omit [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A] [IsDiscreteValuationRing A]
  [CharZero K] in
/-- Full surjectivity onto the displayed `K / dA` product would force that whole product to be
finite, since the source integer Cartan-coordinate quotient is finite. This isolates why the
unconditional injection should be viewed as an embedding into a finite image subgroup, rather than
as evidence for surjectivity onto the full fraction-field quotient product. -/
theorem projectiveCartanProduct_finite_of_surjective
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
    (hsurj :
      Function.Surjective
        (cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e)) :
    Finite
      (∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) := by
  letI :
      Finite
        ((PRegularConjClass G p → ℤ) ⧸
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :=
    cartanCoordinateAddHom_range_quotient_finite
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
  exact
    Finite.of_surjective
      (cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G) e)
      hsurj

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- A full-surjectivity version of the previous bridge.

This statement records the exact extra hypotheses needed for the stronger, currently unavailable
route: surjectivity onto the entire `K / dA` product is not enough by itself; one must also identify
that whole product additively with the expected finite `ZMod` product. -/
theorem existsCartanRangeCoordinateEquiv_of_projectiveCartanProduct_surjective
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
    (hsurj :
      Function.Surjective
        (cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e))
    (hproduct :
      Nonempty
        ((∀ c : PRegularConjClass G p,
            K ⧸ Submodule.span A
              ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    ∃ coord : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map coord.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rcases hproduct with ⟨hproduct⟩
  let φ :=
    cartanCoordinateRangeQuotientToProjectiveCartanProduct
      (p := p) (A := A) (K := K) (G := G) e
  let hφ : Function.Bijective φ :=
    ⟨cartanCoordinateRangeQuotientToProjectiveCartanProduct_injective
      (p := p) (A := A) (K := K) (G := G) e, hsurj⟩
  let φequiv :
      ((PRegularConjClass G p → ℤ) ⧸
          (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) ≃+
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) :=
    AddEquiv.ofBijective φ hφ
  have hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
    ⟨((cartanCokernel_addEquiv_cartanCoordinateRangeQuotient
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).trans φequiv).trans hproduct⟩
  exact
    existsCartanRangeCoordinateEquiv_of_cokernelProduct_and_invariantFactorUniqueness
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) hCokernel
      (cartanCokernelCentralizerPPartProductUniqueness_holds (p := p) (G := G))

end ProjectiveCartanIntegralProductBridge

end Representation
