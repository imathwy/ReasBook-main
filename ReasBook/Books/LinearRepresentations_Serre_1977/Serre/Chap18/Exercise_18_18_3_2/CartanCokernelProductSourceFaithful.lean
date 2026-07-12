import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelSmith
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularIntegerDiagonalQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelProductSourceFaithful

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelProductSourceFaithfulFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelProductSourceFaithfulDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-faithful diagonal Cartan-image endpoint.

This is the abstract quotient step in Serre 18.5(b): after choosing some regular-class coordinate
equivalence, the image of the Cartan homomorphism is exactly the integer lattice whose `c`-th
coordinate is divisible by `|C_G(c)|_p`. The coordinate equivalence is not fixed to the canonical
`regularClassCoordinateAddEquiv`, so the statement stays independent of any chosen Cartan-column
witness. -/
def cartanCokernelSourceFaithfulDiagonalProduct : Prop :=
  ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
    (cartanHom k G).range.map e.toAddMonoidHom =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup

/-- Quotient form of the source-faithful diagonal endpoint. -/
noncomputable def cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_sourceFaithful
    (hdiag : cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G)) :
    cartanCokernel k G ≃+
      ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) := by
  let e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ) := Classical.choose hdiag
  have he :
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    Classical.choose_spec hdiag
  simpa [cartanCokernel] using
    QuotientAddGroup.congr
      ((cartanHom k G).range)
      ((regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
      e
      he

/-- Source-faithful cokernel-product endpoint.

This is the formal part of Serre 18.5(b): quotienting the diagonal lattice gives the product of
the cyclic groups `ZMod |C_G(c)|_p`. -/
noncomputable def cartanCokernel_addEquiv_pi_centralizerPPart_of_sourceFaithful
    (hdiag : cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G)) :
    cartanCokernel k G ≃+
      ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1) :=
  (cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_sourceFaithful
      (p := p) (k := k) (G := G) hdiag).trans
    (regularIntegerDiagonalQuotient_addEquiv_pi_centralizerPPart
      (p := p) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Nonempty wrapper for the source-faithful cokernel-product endpoint. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_sourceFaithful
    (hdiag : cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G)) :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  ⟨cartanCokernel_addEquiv_pi_centralizerPPart_of_sourceFaithful
    (p := p) (k := k) (G := G) hdiag⟩

/-- The Smith adapter turns Serre's abstract cokernel product back into the source-faithful
diagonal Cartan-image endpoint. -/
theorem cartanCokernelSourceFaithfulDiagonalProduct_of_cokernelProduct
    (hCokernel :
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G) :=
  existsCartanRangeCoordinateEquiv_of_cokernelProduct
    (p := p) (k := k) (G := G) hCokernel

/-- Equivalence between the abstract source-faithful diagonal endpoint and the cokernel-product
endpoint accepted by `CartanCokernelSmith.lean`. -/
theorem cartanCokernelSourceFaithfulDiagonalProduct_iff_cokernelProduct :
    cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G) ↔
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  constructor
  · exact
      cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_sourceFaithful
        (p := p) (k := k) (G := G)
  · exact
      cartanCokernelSourceFaithfulDiagonalProduct_of_cokernelProduct
        (p := p) (k := k) (G := G)

end CartanCokernelProductSourceFaithful

end Representation
