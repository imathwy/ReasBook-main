import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductFiniteImageAdapter
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProductForward

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CanonicalSourceProductImageCardinalityEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance canonicalSourceProductImageCardinalityEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductImageCardinalityEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- A representative-level inclusion adapter for ranges of additive homomorphisms. -/
theorem addMonoidHom_range_le_range_of_representatives
    {D E M : Type*} [AddGroup D] [AddGroup E] [AddGroup M]
    (φ : D →+ M) (ψ : E →+ M)
    (hrep : ∀ x : D, ∃ y : E, φ x = ψ y) :
    φ.range ≤ ψ.range := by
  rintro z ⟨x, rfl⟩
  rcases hrep x with ⟨y, hy⟩
  exact ⟨y, hy.symm⟩

/-- Forward representatives give the inclusion of the canonical source-product image in the
coordinatewise integer image. -/
theorem canonicalVirtualModularCartanProductRange_le_integerImage_of_forwardRepresentatives
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (cartanHom (IsLocalRing.ResidueField A) G).range x) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g)) :
    (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range ≤
      (regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)).range := by
  let φ :=
    cartanCokernelToCanonicalVirtualModularCartanProduct
      (p := p) (A := A) (K := K) (G := G)
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  refine addMonoidHom_range_le_range_of_representatives φ ψ ?_
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro x
  rcases hforward x with ⟨g, hg⟩
  refine
    ⟨QuotientAddGroup.mk'
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g, ?_⟩
  simpa [φ, ψ] using hg

/-- The regular-value congruence supplies the forward image inclusion needed by the finite
cardinality route. -/
theorem canonicalVirtualModularCartanProductRange_le_integerImage_of_regularValue_congruence
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range ≤
      (regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)).range :=
  canonicalVirtualModularCartanProductRange_le_integerImage_of_forwardRepresentatives
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProduct_forwardRepresentative_of_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hforward)

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A Cartan-cokernel cyclic-product equivalence gives the exact cardinality equality needed by
the finite image adapter. -/
theorem cartanCokernel_natCard_eq_regularIntegerImageRange_of_cokernelProduct
    (hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range := by
  rcases hCokernel with ⟨hCokernel⟩
  calc
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
      Nat.card_congr hCokernel.toEquiv
    _ =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range :=
      (Nat.card_congr
        (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
          (p := p) (A := A) (K := K) (G := G)).toEquiv).symm

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The span-equality quotient endpoint gives the same cardinality equality, without choosing
fixed Cartan columns as the image witness. -/
theorem cartanCokernel_natCard_eq_regularIntegerImageRange_of_projectiveCartanCoordinate_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range :=
  cartanCokernel_natCard_eq_regularIntegerImageRange_of_cokernelProduct
    (p := p) (A := A) (K := K) (G := G)
    (cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The coordinatewise integer image has nonzero `Nat.card`, in the form needed by the local
cardinality endpoint. -/
theorem regularIntegerImageProductRange_natCard_ne_zero :
    Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range ≠ 0 := by
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  have hcard :
      Nat.card ψ.range =
        Nat.card
          (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
    exact
      Nat.card_congr
        (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
          (p := p) (A := A) (K := K) (G := G)).toEquiv
  rw [hcard, Nat.card_pi]
  exact
    Finset.prod_ne_zero_iff.mpr (by
      intro c _
      rw [Nat.card_zmod]
      rcases ConjClasses.centralizerPPart_eq_prime_pow (p := p) (G := G) c.1 with ⟨e, he⟩
      rw [he]
      exact pow_ne_zero e (Fact.out : Nat.Prime p).ne_zero)

/-- Image/cardinality endpoint: forward image inclusion plus an abstract Cartan-cokernel product
decomposition identify the canonical source-product image with the coordinatewise integer image.
-/
theorem canonicalSourceProductImage_of_regularValue_and_cokernelProduct
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
    (hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  let φ :=
    cartanCokernelToCanonicalVirtualModularCartanProduct
      (p := p) (A := A) (K := K) (G := G)
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  exact
    addMonoidHom_range_nonempty_addEquiv_of_le_of_injective_of_domain_natCard_eq
      φ ψ
      (by
        simpa [ψ] using
          regularIntegerImageProductRange_natCard_ne_zero
            (p := p) (A := A) (K := K) (G := G))
      (by
        simpa [φ] using
          cartanCokernelToCanonicalVirtualModularCartanProduct_injective
            (p := p) (A := A) (K := K) (G := G))
      (by
        simpa [φ, ψ] using
          canonicalVirtualModularCartanProductRange_le_integerImage_of_regularValue_congruence
            (p := p) (A := A) (K := K) (G := G) hforward)
      (by
        simpa [ψ] using
          cartanCokernel_natCard_eq_regularIntegerImageRange_of_cokernelProduct
            (p := p) (A := A) (K := K) (G := G) hCokernel)

/-- Span-equality version of the image/cardinality endpoint. -/
theorem canonicalSourceProductImage_of_regularValue_and_span_eq
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
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalSourceProductImage_of_regularValue_and_cokernelProduct
    (p := p) (A := A) (K := K) (G := G) hforward
    (cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)

/-- Final range endpoint obtained through the image/cardinality route from the abstract
cokernel-product input. -/
theorem existsCartanRangeCoordinateEquiv_of_regularValue_congruence_and_cokernelProduct
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
    (hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_canonicalVirtualModularCartanProductImage
    (p := p) (A := A) (K := K) (G := G)
    (canonicalSourceProductImage_of_regularValue_and_cokernelProduct
      (p := p) (A := A) (K := K) (G := G) hforward hCokernel)

/-- Final range endpoint obtained through the image/cardinality route from the fixed-coordinate
span equality. -/
theorem existsCartanRangeCoordinateEquiv_of_regularValue_and_span_eq
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
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_canonicalVirtualModularCartanProductImage
    (p := p) (A := A) (K := K) (G := G)
    (canonicalSourceProductImage_of_regularValue_and_span_eq
      (p := p) (A := A) (K := K) (G := G) hforward hspan)

end CanonicalSourceProductImageCardinalityEndpoint

end Representation
