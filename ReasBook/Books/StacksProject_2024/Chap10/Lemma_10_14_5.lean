import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule
open CategoryTheory ModuleCat

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {M : Type u} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable {N : Type u} [AddCommGroup N] [Module S N]
variable {P : Type u} [AddCommGroup P] [Module R P]

/- Lemma 10.14.5 is a `bridge/view` item. Its owner abstractions are the change-of-rings
adjunction `ModuleCat.restrictCoextendScalarsAdj` from Lemma 10.14.4 and the heterobasic
tensor-Hom equivalence `TensorProduct.AlgebraTensorModule.lift.equiv` from Lemma 10.12.8. The
source-facing tensor-Hom bijection is their composite. -/
/-- The restricted `S`-tensor object is canonically the expected `R`-module on `M ⊗[S] N`. -/
private noncomputable def restrictTensorIso :
    (restrictScalars (algebraMap R S)).obj (of S (M ⊗[S] N)) ≅ of R (M ⊗[S] N) :=
  ({ toFun := fun x ↦ x
     invFun := fun x ↦ x
     left_inv := fun x ↦ rfl
     right_inv := fun x ↦ rfl
     map_add' := fun x y ↦ rfl
     map_smul' := fun r x ↦ by simp } :
      ↑((restrictScalars (algebraMap R S)).obj (of S (M ⊗[S] N))) ≃ₗ[R] (M ⊗[S] N)).toModuleIso

/-- Lemma 10.14.5: for a ring map `R → S`, the textbook bijection
`Hom_R(M ⊗[S] N, P) ≃ Hom_S(M, Hom_R(N, P))` is the canonical composite of the
restriction-coextension adjunction with the heterobasic tensor-Hom adjunction. Mathlib expresses
`Hom_R(N, P)` by the coextension model `N →ₗ[S] coextend_R^S(P)`. -/
noncomputable def changeOfRings_tensor_homEquiv :
    (M ⊗[S] N →ₗ[R] P) ≃
      (M →ₗ[S] N →ₗ[S] ((coextendScalars (algebraMap R S)).obj (of R P))) :=
  let f := algebraMap R S
  let tensorObj := of S (M ⊗[S] N)
  let Pobj := of R P
  let coextendP := (coextendScalars f).obj Pobj
  let sourceEquiv :
      (M ⊗[S] N →ₗ[R] P) ≃ (((restrictScalars f).obj tensorObj) ⟶ Pobj) :=
    ((homEquiv : (of R (M ⊗[S] N) ⟶ Pobj) ≃ (M ⊗[S] N →ₗ[R] P))).symm.trans
      (restrictTensorIso.symm.homCongr (Iso.refl Pobj))
  let targetEquiv : (tensorObj ⟶ coextendP) ≃ (M →ₗ[S] N →ₗ[S] coextendP) :=
    ((homEquiv : (tensorObj ⟶ coextendP) ≃ (M ⊗[S] N →ₗ[S] coextendP))).trans
      (lift.equiv S S S M N coextendP).symm.toEquiv
  sourceEquiv.trans (((restrictCoextendScalarsAdj f).homEquiv tensorObj Pobj).trans targetEquiv)

/-- The change-of-rings tensor-Hom comparison is a genuine bijection. -/
theorem changeOfRings_tensor_homEquiv_bijective :
    Function.Bijective
      (changeOfRings_tensor_homEquiv :
        (M ⊗[S] N →ₗ[R] P) →
          (M →ₗ[S] N →ₗ[S] ((coextendScalars (algebraMap R S)).obj (of R P)))) :=
  changeOfRings_tensor_homEquiv.bijective

end
