import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageFromQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section FiniteImageCardinalityAdapter

variable {M D E : Type*} [AddGroup M] [AddGroup D] [AddGroup E]

/-- A finite-subgroup cardinality adapter: inside a common ambient additive group, an inclusion
between additive subgroups and equality of cardinalities identify the subgroups. -/
theorem addSubgroup_eq_of_le_of_natCard_eq
    (H K : AddSubgroup M) (hKcard : Nat.card K ≠ 0) (hHK : H ≤ K)
    (hcard : Nat.card H = Nat.card K) :
    H = K := by
  letI : Finite K := Nat.finite_of_card_ne_zero hKcard
  apply SetLike.coe_injective
  exact
    Set.Finite.eq_of_subset_of_card_le (Set.toFinite (K : Set M)) (by
      intro x hx
      exact hHK hx) (by
      rw [SetLike.coe_sort_coe, SetLike.coe_sort_coe]
      exact hcard.ge)

/-- Nonempty additive-equivalence packaging of `addSubgroup_eq_of_le_of_natCard_eq`. -/
theorem addSubgroup_nonempty_addEquiv_of_le_of_natCard_eq
    (H K : AddSubgroup M) (hKcard : Nat.card K ≠ 0) (hHK : H ≤ K)
    (hcard : Nat.card H = Nat.card K) :
    Nonempty (H ≃+ K) := by
  have hEq : H = K := addSubgroup_eq_of_le_of_natCard_eq H K hKcard hHK hcard
  cases hEq
  exact ⟨AddEquiv.refl H⟩

/-- If an injective hom has image contained in a known finite image and its domain has the same
cardinality as that image, then the two images are additively equivalent. -/
theorem addMonoidHom_range_nonempty_addEquiv_of_le_of_injective_of_domain_natCard_eq
    (φ : D →+ M) (ψ : E →+ M) (hψcard : Nat.card ψ.range ≠ 0)
    (hφ : Function.Injective φ) (hrange : φ.range ≤ ψ.range)
    (hcard : Nat.card D = Nat.card ψ.range) :
    Nonempty (φ.range ≃+ ψ.range) := by
  refine addSubgroup_nonempty_addEquiv_of_le_of_natCard_eq φ.range ψ.range hψcard hrange ?_
  calc
    Nat.card φ.range = Nat.card D := (Nat.card_congr (AddMonoidHom.ofInjective hφ).toEquiv).symm
    _ = Nat.card ψ.range := hcard

end FiniteImageCardinalityAdapter

section CanonicalSourceProductFiniteImageAdapter

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance canonicalSourceProductFiniteImageAdapterFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductFiniteImageAdapterDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The coordinatewise integer image has nonzero `Nat.card`, hence is finite in the `Nat.card`
sense used by the finite-image adapter. -/
theorem regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_ne_zero :
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

/-- Cardinality adapter for the canonical source-product image.

If the canonical source-product image is contained in the coordinatewise integer image and the
Cartan cokernel has the same cardinality as that coordinatewise image, then the two finite images
are additively equivalent. The injectivity input is the existing canonical product-map theorem. -/
theorem canonicalVirtualModularCartanProductRange_nonempty_addEquiv_integerImage_of_le_of_domain_natCard_eq
    (hrange :
      (cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≤
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range)
    (hcard :
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range) :
    Nonempty
      ((cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≃+
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range) := by
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  exact
    addMonoidHom_range_nonempty_addEquiv_of_le_of_injective_of_domain_natCard_eq
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G))
      ψ
      (by
        simpa [ψ] using
          regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_ne_zero
            (p := p) (A := A) (K := K) (G := G))
      (cartanCokernelToCanonicalVirtualModularCartanProduct_injective
        (p := p) (A := A) (K := K) (G := G))
      (by simpa [ψ] using hrange)
      (by simpa [ψ] using hcard)

/-- Image-match form of the finite cardinality adapter. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_le_of_domain_natCard_eq
    (hrange :
      (cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≤
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range)
    (hcard :
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductRange_nonempty_addEquiv_integerImage_of_le_of_domain_natCard_eq
    (p := p) (A := A) (K := K) (G := G) hrange hcard

/-- Cyclic-product range form of the finite cardinality adapter. -/
theorem canonicalVirtualModularCartanProductRange_nonempty_addEquiv_pi_of_le_of_domain_natCard_eq
    (hrange :
      (cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≤
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range)
    (hcard :
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range) :
    Nonempty
      ((cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases
      canonicalVirtualModularCartanProductRange_nonempty_addEquiv_integerImage_of_le_of_domain_natCard_eq
        (p := p) (A := A) (K := K) (G := G) hrange hcard with
    ⟨himage⟩
  exact
    ⟨himage.trans
      (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
        (p := p) (A := A) (K := K) (G := G))⟩

end CanonicalSourceProductFiniteImageAdapter

end Representation
