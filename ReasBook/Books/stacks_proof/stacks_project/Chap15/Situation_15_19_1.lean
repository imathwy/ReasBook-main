import stacks_proof.stacks_project.Chap10.Definition_10_14_1
import stacks_proof.stacks_project.Chap15.«15_19_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra.TensorProduct
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable (J : Ideal S)

/- Situation 15.19.1 fixes an ideal `J ⊂ S` together with an `S`-module `M`; its underlying
`R`-module structure is the canonical restriction of scalars. -/
#check (Module.restrictScalars R S M : Module R M)

section

variable {R' : Type x} [CommRing R'] [Algebra R R']
variable [Module R M] [IsScalarTower R S M]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- For a base change `R → R'`, the canonical owner ring is `S ⊗[R] R'`, the canonical owner
module is `((S ⊗[R] R') ⊗[S] M)`, and the source condition `(15.19.1.1)` is recalled separately
in `15_19_1_1`. The base-change owner layer itself is already Chapter `10`, Definition `10.14.1`,
so Situation `15.19.1` reuses those canonical declarations under the restricted-scalar
`R`-module structure and scalar tower on `M`; the textbook tensor model `M ⊗[R] R'` remains only
the bridge view of that owner. -/
#check (includeRight : R' →ₐ[R] S')
#check (TensorProduct.isPushout : Algebra.IsPushout R S R' S')
#check M'
#check (tensorBaseChangeModuleMap M : M →ₗ[S] M')
#check (tensorBaseChangeModuleMapRestrictScalars M : M →ₗ[R] M')
#check (Algebra.IsPushout.cancelBaseChange R R' S S' M : M' ≃ₗ[R'] R' ⊗[R] M)
#check (TensorProduct.comm R R' M : R' ⊗[R] M ≃ₗ[R] M ⊗[R] R')

end

end
