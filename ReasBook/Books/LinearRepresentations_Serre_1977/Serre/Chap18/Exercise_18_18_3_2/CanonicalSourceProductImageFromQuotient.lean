import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CanonicalSourceProductImageFromQuotient

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance canonicalSourceProductImageFromQuotientFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductImageFromQuotientDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- If the canonical source-product range itself is known to have Serre's cyclic product
structure, then it matches the coordinatewise integer image as an abstract finite image.

This is deliberately only an image-level statement: it uses no fixed Cartan-column witness and no
fixed point-mass congruence. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_productRange
    (hproduct :
      Nonempty
        ((cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hproduct with ⟨hproduct⟩
  exact
    ⟨hproduct.trans
      (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
        (p := p) (A := A) (K := K) (G := G)).symm⟩

/-- Cokernel-product form of the previous endpoint.

This is the formal shape of the non-fixed-witness route from Serre 18.5(b): an abstract
decomposition of the Cartan cokernel as the centralizer-`p`-part cyclic product is enough to
identify the canonical source-product image with the coordinatewise integer image, because both
maps are injective into their ranges. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_cokernelProduct
    (hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hCokernel with ⟨hCokernel⟩
  refine
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_productRange
      (p := p) (A := A) (K := K) (G := G) ?_
  exact
    ⟨(cartanCokernel_addEquiv_canonicalVirtualModularCartanProductRange
        (p := p) (A := A) (K := K) (G := G)).symm.trans hCokernel⟩

/-- The canonical image-match endpoint is equivalent to Serre's abstract cokernel-product
decomposition. The forward implication is the existing adapter; the reverse implication is the
non-fixed-witness quotient/product route above. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_iff_cokernelProduct :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G) ↔
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  constructor
  · exact
      cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
        (p := p) (A := A) (K := K) (G := G)
  · exact
      canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_cokernelProduct
        (p := p) (A := A) (K := K) (G := G)

end CanonicalSourceProductImageFromQuotient

end Representation
