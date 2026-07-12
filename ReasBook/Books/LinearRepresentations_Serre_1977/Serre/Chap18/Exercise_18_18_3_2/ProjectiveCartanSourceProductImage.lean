import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceCokernelBridge
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanProductImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSourceProductImage

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanSourceProductImageFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSourceProductImageDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- If the canonical source-product image matches the coordinatewise integer image, then it is the
expected product of cyclic groups. -/
theorem canonicalVirtualModularCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
    (himage :
      canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      ((cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases himage with ⟨himage⟩
  exact
    ⟨himage.trans
      (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
        (p := p) (A := A) (K := K) (G := G))⟩

/-- Direct cyclic-product form of
`canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_integerRepresentatives`. -/
theorem canonicalVirtualModularCartanProductRange_nonempty_addEquiv_pi_of_integerRepresentatives
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
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
            cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (cartanHom (IsLocalRing.ResidueField A) G).range x)) :
    Nonempty
      ((cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  exact
    canonicalVirtualModularCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
      (p := p) (A := A) (K := K) (G := G)
      (canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_integerRepresentatives
        (p := p) (A := A) (K := K) (G := G) hforward hreverse)

/-- Coordinatewise version of the representative criterion.

This spelling avoids mentioning the regular diagonal quotient map in the hypotheses: each integer
representative is compared directly with the coordinatewise classes
`integerQuotientImageHom (ConjClasses.centralizerPPart p c.1) (g c)`. -/
theorem canonicalVirtualModularCartanProductRange_nonempty_addEquiv_pi_of_coordinateRepresentatives
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (cartanHom (IsLocalRing.ResidueField A) G).range x) =
            fun c : PRegularConjClass G p =>
              integerQuotientImageHom
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          (fun c : PRegularConjClass G p =>
              integerQuotientImageHom
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c)) =
            cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (cartanHom (IsLocalRing.ResidueField A) G).range x)) :
    Nonempty
      ((cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  refine
    canonicalVirtualModularCartanProductRange_nonempty_addEquiv_pi_of_integerRepresentatives
      (p := p) (A := A) (K := K) (G := G) ?_ ?_
  · intro x
    rcases hforward x with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    simpa [regularIntegerDiagonalQuotientToIntegerImageProduct_mk] using hg
  · intro g
    rcases hreverse g with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [regularIntegerDiagonalQuotientToIntegerImageProduct_mk] using hx

end ProjectiveCartanSourceProductImage

end Representation
