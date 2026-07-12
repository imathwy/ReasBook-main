import Mathlib

/-!
# Characteristic polynomial of the reduction of an endomorphism modulo an ideal

Let `A` be a commutative ring, `I : Ideal A`, and `L` a finite free `A`-module.  The quotient
`L ⧸ (I • ⊤ : Submodule A L)` is naturally a module over `A ⧸ I`, and an endomorphism
`u : L →ₗ[A] L` induces an `A ⧸ I`-linear endomorphism of the quotient.  We show that the
characteristic polynomial (over `A ⧸ I`) of the induced endomorphism is the image of the
characteristic polynomial of `u` under `Ideal.Quotient.mk I`.

This applies in particular to a discrete valuation ring `A` with maximal ideal `I` and residue
field `A ⧸ I`.
-/

noncomputable section

open TensorProduct

universe u v

namespace Representation

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {L : Type v} [AddCommGroup L] [Module A L]

instance : IsScalarTower A (A ⧸ I) (L ⧸ (I • ⊤ : Submodule A L)) :=
  (Module.isTorsionBySet_quotient_ideal_smul L I).isScalarTower

/-- The `A ⧸ I`-linear equivalence `(A ⧸ I) ⊗[A] L ≃ L ⧸ I • ⊤`, refining Mathlib's `A`-linear
`TensorProduct.quotTensorEquivQuotSMul`. -/
def quotSMulTopEquiv : ((A ⧸ I) ⊗[A] L) ≃ₗ[A ⧸ I] L ⧸ (I • ⊤ : Submodule A L) :=
  (TensorProduct.quotTensorEquivQuotSMul L I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

@[simp]
theorem quotSMulTopEquiv_symm_mk (x : L) :
    (quotSMulTopEquiv (L := L) I).symm (Submodule.Quotient.mk x) = 1 ⊗ₜ[A] x :=
  TensorProduct.quotTensorEquivQuotSMul_symm_mk I x

/-- The `A ⧸ I`-linear endomorphism of `L ⧸ (I • ⊤)` induced by `u : L →ₗ[A] L`, obtained by
conjugating the base change `u.baseChange (A ⧸ I)` by `quotSMulTopEquiv`. -/
def quotientSmulTopEndo (u : L →ₗ[A] L) :
    (L ⧸ (I • ⊤ : Submodule A L)) →ₗ[A ⧸ I] (L ⧸ (I • ⊤ : Submodule A L)) :=
  (quotSMulTopEquiv I).conj (u.baseChange (A ⧸ I))

@[simp]
theorem quotientSmulTopEndo_mk (u : L →ₗ[A] L) (x : L) :
    quotientSmulTopEndo I u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u x) := by
  simp only [quotientSmulTopEndo, LinearEquiv.conj_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, quotSMulTopEquiv_symm_mk,
    LinearMap.baseChange_tmul]
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I (u x)

variable [Module.Free A L] [Module.Finite A L]

instance : Module.Free (A ⧸ I) (L ⧸ (I • ⊤ : Submodule A L)) :=
  Module.Free.of_equiv (quotSMulTopEquiv (L := L) I)

instance : Module.Finite (A ⧸ I) (L ⧸ (I • ⊤ : Submodule A L)) :=
  Module.Finite.equiv (quotSMulTopEquiv (L := L) I)

/-- For a finite free module `L` over a commutative ring `A` and an ideal `I`, the characteristic
polynomial (over `A ⧸ I`) of the endomorphism induced on `L ⧸ I • ⊤` by `u : L →ₗ[A] L` is the
image of the characteristic polynomial of `u` under `Ideal.Quotient.mk I`. -/
theorem charpoly_quotientSmulTopEndo (u : L →ₗ[A] L) :
    (quotientSmulTopEndo I u).charpoly = u.charpoly.map (Ideal.Quotient.mk I) := by
  rw [quotientSmulTopEndo, LinearEquiv.charpoly_conj, LinearMap.charpoly_baseChange,
    Ideal.Quotient.algebraMap_eq]

end Representation
