import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageCardinalityEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelProductSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanFormalRangeSourceProductTransport

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CanonicalSourceProductImageSourceFaithful

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance canonicalSourceProductImageSourceFaithfulFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductImageSourceFaithfulDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pure cardinality endpoint for the canonical source-product image.

The forward hypothesis supplies the inclusion of the canonical source-product image in the
coordinatewise integer image. The second hypothesis is exactly the finite-cardinality equality
needed to upgrade that inclusion to equality of images. No fixed Cartan column or fixed point-mass
witness is chosen. -/
theorem canonicalProductImage_of_regularValue_congruence_and_natCard_eq
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hcard :
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_le_of_domain_natCard_eq
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProductRange_le_integerImage_of_regularValue_congruence
      (p := p) (A := A) (K := K) (G := G) hforward)
    hcard

/-- Coordinate-range endpoint from the cardinality route. -/
theorem existsCartanRangeCoordinateEquiv_of_regularValue_congruence_and_domain_natCard_eq
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hcard :
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_canonicalVirtualModularCartanProductImage
    (p := p) (A := A) (K := K) (G := G)
    (canonicalProductImage_of_regularValue_congruence_and_natCard_eq
      (p := p) (A := A) (K := K) (G := G) hforward hcard)

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Source-faithful diagonal product supplies the cardinality equality used by the image route. -/
theorem cartanCokernel_natCard_eq_regularIntegerImageRange_of_sourceFaithfulDiagonalProduct
    (hdiag :
      cartanCokernelSourceFaithfulDiagonalProduct
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)) :
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range :=
  cartanCokernel_natCard_eq_regularIntegerImageRange_of_cokernelProduct
    (p := p) (A := A) (K := K) (G := G)
    (cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_sourceFaithful
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) hdiag)

/-- Source-faithful diagonal version of the canonical source-product cardinality endpoint. -/
theorem canonicalProductImage_of_regularValue_congruence_and_sourceFaithful
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hdiag :
      cartanCokernelSourceFaithfulDiagonalProduct
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalProductImage_of_regularValue_congruence_and_natCard_eq
    (p := p) (A := A) (K := K) (G := G)
    hforward
    (cartanCokernel_natCard_eq_regularIntegerImageRange_of_sourceFaithfulDiagonalProduct
      (p := p) (A := A) (K := K) (G := G) hdiag)

/-- Final range endpoint from the source-faithful diagonal/cardinality route. -/
theorem existsCartanRangeCoordinateEquiv_of_regularValue_congruence_and_sourceFaithful
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hdiag :
      cartanCokernelSourceFaithfulDiagonalProduct
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_regularValue_congruence_and_domain_natCard_eq
    (p := p) (A := A) (K := K) (G := G)
    hforward
    (cartanCokernel_natCard_eq_regularIntegerImageRange_of_sourceFaithfulDiagonalProduct
      (p := p) (A := A) (K := K) (G := G) hdiag)

end CanonicalSourceProductImageSourceFaithful

section CanonicalSourceProductImageSourceFaithfulTransport

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance canonicalSourceProductImageSourceFaithfulTransportFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductImageSourceFaithfulTransportDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Full mixed-characteristic transport endpoint for the bare cardinality route.

For each full mixed model, it is enough to prove the forward regular-value congruence and the
cardinality equality between the Cartan cokernel and the coordinatewise integer image. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cardinalityRoute
    (hforward :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∀ x : R₀[IsLocalRing.ResidueField A](G),
            virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
                regularValueDivisibilitySubmodule
                  (p := p) (A := A) (K := K) (G := G))
    (hcard :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
            Nat.card
              (regularIntegerDiagonalQuotientToIntegerImageProduct
                (p := p) (A := A) (K := K) (G := G)).range) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    canonicalProductImage_of_regularValue_congruence_and_natCard_eq
      (p := p) (A := A) (K := K) (G := G)
      (hforward (A := A) (K := K) e0)
      (hcard (A := A) (K := K) e0)

include p in
/-- Full mixed-characteristic transport endpoint for the source-faithful diagonal/cardinality
route. The source-faithful diagonal product is used only to provide the cardinality equality;
the image inclusion still comes from the canonical regular-value congruence. -/
theorem
    existsCartanRangeCoordinateEquiv_via_fullMixedModel_regularValueAndSourceFaithful
    (hforward :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∀ x : R₀[IsLocalRing.ResidueField A](G),
            virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
                regularValueDivisibilitySubmodule
                  (p := p) (A := A) (K := K) (G := G))
    (hdiag :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          cartanCokernelSourceFaithfulDiagonalProduct
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    canonicalProductImage_of_regularValue_congruence_and_sourceFaithful
      (p := p) (A := A) (K := K) (G := G)
      (hforward (A := A) (K := K) e0)
      (hdiag (A := A) (K := K) e0)

end CanonicalSourceProductImageSourceFaithfulTransport

end Representation
