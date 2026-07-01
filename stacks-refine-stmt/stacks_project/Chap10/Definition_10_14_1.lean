import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
