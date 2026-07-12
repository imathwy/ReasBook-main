import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelProductSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanFormalRangeSourceProductTransport

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeCokernelProductEndpoint

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeCokernelProductEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeCokernelProductEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Cokernel-product endpoint for the formal Cartan range theorem over the given residue field.

This is the direct source-faithful form of Serre 18.5(b): once the Cartan cokernel is identified
with the product of the cyclic groups indexed by the `p`-regular classes, the Smith adapter in
`CartanCokernelSmith.lean` turns that product decomposition back into the diagonal Cartan image.
-/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_cokernelProduct_endpoint
    (hproduct :
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p,
            ZMod (ConjClasses.centralizerPPart p c.1))) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    cartanCokernelSourceFaithfulDiagonalProduct_of_cokernelProduct
      (p := p) (k := k) (G := G) hproduct

/-- Product-endpoint version of the theorem, stated through the source-faithful diagonal-product
proposition used by `CartanCokernelProductSourceFaithful.lean`. -/
theorem cartanCokernelSourceFaithfulDiagonalProduct_of_cokernelProduct_endpoint
    (hproduct :
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p,
            ZMod (ConjClasses.centralizerPPart p c.1))) :
    cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G) :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_cokernelProduct_endpoint
    (p := p) (k := k) (G := G) hproduct

include p in
/-- Full mixed-characteristic cokernel-product endpoint for the final theorem in
`CartanFormalRange.lean`.

After applying this helper to the theorem at `CartanFormalRange.lean:43`, the exact remaining
source-faithful input is the displayed `hproduct`: for each full mixed-characteristic model, prove
Serre's cokernel product decomposition over its residue field. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cokernelProduct_endpoint
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
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cokernelProduct
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact hproduct (A := A) (K := K) e0

end CartanFormalRangeCokernelProductEndpoint

end Representation
