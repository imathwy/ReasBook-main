import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeTransport
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageFromQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeSourceProductTransport

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeSourceProductTransportFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeSourceProductTransportDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Final transport adapter specialized to the canonical source-product image endpoint.

This keeps the mixed-characteristic transport separate from the remaining Serre 18.5(b) input:
for each full mixed-characteristic model, it is enough to prove that the canonical source-product
image matches the coordinatewise integer image. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
    (himage :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          canonicalVirtualModularCartanProductImageMatchesIntegerImage
            (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModel_residueEndpoint
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    existsCartanRangeCoordinateEquiv_of_canonicalVirtualModularCartanProductImage
      (p := p) (A := A) (K := K) (G := G)
      (himage (A := A) (K := K) e0)

include p in
/-- Final transport adapter specialized to Serre's cokernel-product endpoint.

This is the most direct non-fixed-column form of the remaining Exercise 18.5(b) input: for each
full mixed-characteristic model, prove only the abstract product decomposition of the Cartan
cokernel. The canonical source-product and Smith adapters then supply the coordinate range. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cokernelProduct
    (hproduct :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          Nonempty
            (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
              ∀ c : PRegularConjClass G p,
                ZMod (ConjClasses.centralizerPPart p c.1))) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_cokernelProduct
      (p := p) (A := A) (K := K) (G := G)
      (hproduct (A := A) (K := K) e0)

end CartanFormalRangeSourceProductTransport

end Representation
