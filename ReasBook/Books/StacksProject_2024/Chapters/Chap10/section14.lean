import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_14_1 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {R' : Type w} [CommRing R'] [Algebra R R']
local notation "S'" => S ⊗[R] R'
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Definition 10.14.1: for a ring map `R → S` and a ring map `R → R'`, the base change of
`R → S` by `R → R'` is the canonical `R`-algebra map `R' → S'`. -/
#check (includeRight : R' →ₐ[R] S')

/- The defining tensor-product square for the base-changed ring is the canonical pushout square
`R → S`, `R → R'`, `R' → S'`. -/
#check (TensorProduct.isPushout : Algebra.IsPushout R S R' S')

variable {M : Type x} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
local notation "M'" => S' ⊗[S] M

/- Definition 10.14.1 at the `core/canonical` owner layer: the base change of the `S`-module
`M` along `R → R'` is extension of scalars along `S → S'`, namely the canonical `S'`-module
`M'`. -/
#check M'

/- The owner tensor product carries its natural module structure over the base-changed ring
`S'`. -/
#check (inferInstance : Module S' M')

/- The same base-changed tensor module carries the canonical restricted-scalar `R'`-module
structure, and hence the scalar tower `R' → S' → M'`. -/
instance : Module R' M' :=
  Module.compHom _ (algebraMap R' S')

instance : IsScalarTower R' S' M' :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

#check (inferInstance : Module R' M')
#check (inferInstance : IsScalarTower R' S' M')

/-- The canonical tensor-base-change map `M → S' ⊗[S] M`, `m ↦ 1 ⊗ m`. -/
abbrev tensorBaseChangeModuleMap (M : Type x) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] : M →ₗ[S] S' ⊗[S] M :=
  TensorProduct.AlgebraTensorModule.mk S S' S' M (1 : S')

/-- The canonical tensor-base-change map, viewed as an `R`-linear map by restriction of scalars. -/
abbrev tensorBaseChangeModuleMapRestrictScalars (M : Type x) [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M] : M →ₗ[R] S' ⊗[S] M :=
  (tensorBaseChangeModuleMap M).restrictScalars R

/- At the `bridge/view` layer, the pushout owner abstraction identifies `M'` with the simpler
tensor model `R' ⊗[R] M`. -/
#check (Algebra.IsPushout.cancelBaseChange R R' S S' M : M' ≃ₗ[R'] R' ⊗[R] M)

/- The source-facing textbook presentation `M ⊗[R] R'` is the further tensor-symmetry view of
that canonical model. -/
#check (TensorProduct.comm R R' M : R' ⊗[R] M ≃ₗ[R] M ⊗[R] R')

end

/-! ### Lemma_10_14_2 (from Chap10) -/
universe u

/-
Domain-style sampling:
- primary domain: finiteness conditions for modules and algebras under tensor-product base change;
- sampled owner declarations:
  `Module.Finite.base_change`,
  the tensor-product base-change instance for `Module.FinitePresentation`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.FinitePresentation.baseChange`;
- best owner abstraction: the canonical finiteness owners `Module.Finite`,
  `Module.FinitePresentation`, `Algebra.FiniteType`, and `Algebra.FinitePresentation`;
- primitive data: the ring maps `R → S`, `R → R'`, and the original finiteness hypotheses on `M`
  or `S`;
- derived API: the four textbook finiteness statements after base change.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 10.14.2;
- `core/canonical`: the owner declarations listed above;
- `bridge/view`: the tensor-product models `S' = S ⊗[R] R'` and `M' = S' ⊗[S] M`, together with
  the tensor-symmetry identification relating the textbook order of factors to the owner
  orientation used by mathlib.
-/

section ModuleBaseChange

variable {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R'] [AddCommGroup M] [Module S M]
local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- Lemma 10.14.2 (1): if `M` is a finite `S`-module, then after base change along `R → R'`,
`M'` is finite over `S'`. This is the canonical theorem `Module.Finite.base_change`, applied to
the `S`-algebra `S'`. -/
recall Module.Finite.base_change

/- Lemma 10.14.2 (2): if `M` is a finitely presented `S`-module, then after base change along
`R → R'`, `M'` is finitely presented over `S'`. Mathlib exposes this as the canonical
tensor-product base-change instance for finitely presented modules. -/
variable [Module.FinitePresentation S M]

#check (inferInstance : Module.FinitePresentation S' M')

end ModuleBaseChange

section AlgebraBaseChange

variable {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R']
local notation "S'" => S ⊗[R] R'

/- Lemma 10.14.2 (3): if `R → S` is of finite type, then the standard base change
`R' → R' ⊗[R] S` is of finite type; via `Algebra.TensorProduct.comm R' S`, this is the textbook
base change `R' → S'`. This is the canonical theorem `Algebra.FiniteType.baseChange`. -/
recall Algebra.FiniteType.baseChange

/- Lemma 10.14.2 (4): if `R → S` is of finite presentation, then the standard base change
`R' → R' ⊗[R] S` is of finite presentation; via `Algebra.TensorProduct.comm R' S`, this is the
textbook base change `R' → S'`. This is the canonical theorem
`Algebra.FinitePresentation.baseChange`. -/
recall Algebra.FinitePresentation.baseChange

end AlgebraBaseChange

/-! ### Lemma_10_14_3 (from Chap10) -/
universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

/- Lemma 10.14.3: for a ring map `f : R →+* S`, extension of scalars
`ModuleCat.extendScalars f : ModuleCat R ⥤ ModuleCat S` is left adjoint to restriction of scalars
`ModuleCat.restrictScalars f : ModuleCat S ⥤ ModuleCat R`. This is the canonical tensor-Hom
adjunction for modules. -/
recall ModuleCat.extendRestrictScalarsAdj

/- Companion recall: the owner-object form of the tensor-Hom adjunction is the canonical
equivalence
`Hom_S(S ⊗[R] M, N) ≃ Hom_R(M, N|_R)`,
implemented by `(ModuleCat.extendRestrictScalarsAdj f).homEquiv`. The textbook orientation
`Hom_S(M ⊗[R] S, N) ≃ Hom_R(M, N|_R)` is obtained by tensor symmetry. -/
#check (ModuleCat.extendRestrictScalarsAdj f).homEquiv

/-! ### Lemma_10_14_4 (from Chap10) -/
universe u v

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

/- Lemma 10.14.4 is a `core/canonical` recall item in the change-of-rings domain. Its owner
abstraction is the mathlib adjunction `ModuleCat.restrictCoextendScalarsAdj`; the textbook
statement that `ModuleCat.restrictScalars f` is left adjoint to `ModuleCat.coextendScalars f` is
exactly this canonical declaration. -/
recall ModuleCat.restrictCoextendScalarsAdj

/- Companion check: for an `S`-module `N` and an `R`-module `M`, the textbook bijection
`Hom_R(N, M) ≃ Hom_S(N, Hom_R(S, M))` is the canonical equivalence
`(ModuleCat.restrictCoextendScalarsAdj f).homEquiv N M`. -/
#check (ModuleCat.restrictCoextendScalarsAdj f).homEquiv

/-! ### Lemma_10_14_5 (from Chap10) -/
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
