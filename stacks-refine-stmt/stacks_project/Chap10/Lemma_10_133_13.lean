import Mathlib
import stacks_project.Chap10.Definition_10_133_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open LinearMap

universe uR uA uB uM uM' uN

section

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {M' : Type uM'} {N : Type uN}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B]
variable [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
variable [Module A M] [Module A M'] [Module B N]
variable [Module R M] [Module R M'] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N]

/- Domain-style sampling for Lemma 10.133.13:
- primary domain: differential operators under tensor extension/base change on the right;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LinearMap.isDifferentialOperatorOfOrder_succ_iff`,
  `LinearMap.scalarCommutator`,
  `LinearMap.rTensor`,
  `TensorProduct.Algebra.module`,
  `TensorProduct.Algebra.smul_def`;
- best owner abstraction: the recursive owner predicate
  `LinearMap.IsDifferentialOperatorOfOrder`; the tensor map itself is only a bridge/view reusing
  the canonical right-tensor map `D.rTensor N`, equipped with the canonical
  `(A ⊗[R] B)`-action on tensors;
- primitive data: an `R`-linear map `D : M →ₗ[R] M'` and its standard tensor extension
  `D.rTensor N`;
- derived API: the source-facing theorem below, stated directly for `D.rTensor N`; the only
  auxiliary layer is a private transported right-factor `B`-action used to install the canonical
  tensor-product owner action.

Source/core/bridge triage:
- `source-facing`: Lemma 10.133.13, the differential-operator statement after tensoring on the
  right;
- `core/canonical`: `LinearMap.IsDifferentialOperatorOfOrder`;
- `bridge/view`: no public bridge remains; the right-factor `B`-action and induced
  `(A ⊗[R] B)`-action are private implementation scaffolding for the canonical theorem statement.
-/

private abbrev tensorRightModule :
    Module B (M ⊗[R] N) :=
  (TensorProduct.comm R M N).toAddEquiv.module B

private abbrev tensorRightModule' :
    Module B (M' ⊗[R] N) :=
  (TensorProduct.comm R M' N).toAddEquiv.module B

private theorem tensorRightIsScalarTower :
    letI : Module B (M ⊗[R] N) := tensorRightModule
    IsScalarTower R B (M ⊗[R] N) := by
  letI : Module B (M ⊗[R] N) := tensorRightModule
  refine ⟨?_⟩
  intro r b x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul m n =>
      show m ⊗ₜ[R] ((r • b) • n) = r • (m ⊗ₜ[R] (b • n) : M ⊗[R] N)
      rw [← TensorProduct.tmul_smul, smul_assoc]
  | add x y hx hy =>
      simp [hx, hy]

private theorem tensorRightIsScalarTower' :
    letI : Module B (M' ⊗[R] N) := tensorRightModule'
    IsScalarTower R B (M' ⊗[R] N) := by
  letI : Module B (M' ⊗[R] N) := tensorRightModule'
  refine ⟨?_⟩
  intro r b x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul m n =>
      show m ⊗ₜ[R] ((r • b) • n) = r • (m ⊗ₜ[R] (b • n) : M' ⊗[R] N)
      rw [← TensorProduct.tmul_smul, smul_assoc]
  | add x y hx hy =>
      simp [hx, hy]

private theorem tensorSmulCommClass :
    letI : Module B (M ⊗[R] N) := tensorRightModule
    SMulCommClass A B (M ⊗[R] N) := by
  letI : Module B (M ⊗[R] N) := tensorRightModule
  refine ⟨?_⟩
  intro a b x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul m n =>
      show (a • m) ⊗ₜ[R] (b • n) = b • (a • m ⊗ₜ[R] n : M ⊗[R] N)
      rfl
  | add x y hx hy =>
      simp [hx, hy]

private theorem tensorSmulCommClass' :
    letI : Module B (M' ⊗[R] N) := tensorRightModule'
    SMulCommClass A B (M' ⊗[R] N) := by
  letI : Module B (M' ⊗[R] N) := tensorRightModule'
  refine ⟨?_⟩
  intro a b x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul m n =>
      show (a • m) ⊗ₜ[R] (b • n) = b • (a • m ⊗ₜ[R] n : M' ⊗[R] N)
      rfl
  | add x y hx hy =>
      simp [hx, hy]

local instance tensorAlgebraModule :
    Module (A ⊗[R] B) (M ⊗[R] N) := by
  letI : Module A (M ⊗[R] N) := TensorProduct.leftModule
  letI : IsScalarTower R A (M ⊗[R] N) := TensorProduct.isScalarTower_left
  letI : Module B (M ⊗[R] N) := tensorRightModule
  letI : IsScalarTower R B (M ⊗[R] N) :=
    tensorRightIsScalarTower
  letI : SMulCommClass A B (M ⊗[R] N) :=
    tensorSmulCommClass
  exact TensorProduct.Algebra.module

local instance tensorAlgebraModule' :
    Module (A ⊗[R] B) (M' ⊗[R] N) := by
  letI : Module A (M' ⊗[R] N) := TensorProduct.leftModule
  letI : IsScalarTower R A (M' ⊗[R] N) := TensorProduct.isScalarTower_left
  letI : Module B (M' ⊗[R] N) := tensorRightModule'
  letI : IsScalarTower R B (M' ⊗[R] N) :=
    tensorRightIsScalarTower'
  letI : SMulCommClass A B (M' ⊗[R] N) :=
    tensorSmulCommClass'
  exact TensorProduct.Algebra.module

private theorem tensorAlgebra_smulCommClass :
    SMulCommClass (A ⊗[R] B) R (M ⊗[R] N) := by
  sorry

attribute [local instance] tensorAlgebra_smulCommClass

private theorem tensorAlgebra_smulCommClass' :
    SMulCommClass (A ⊗[R] B) R (M' ⊗[R] N) := by
  sorry

attribute [local instance] tensorAlgebra_smulCommClass'

-- Proof sketch: induct on `k`. For order `0`, the scalar commutator of `D.rTensor N` with an
-- element of `A ⊗[R] B` is checked on pure tensors and reduces to the order-zero commutator
-- relation for `D` over `A`. For the inductive step, the commutator with a generator `a ⊗ₜ b`
-- is `(D.scalarCommutator a).rTensor N`, and Lemma 10.133.11 upgrades the generator computation to
-- all of `A ⊗[R] B`.
/-- Lemma 10.133.13: tensoring a differential operator `D : M → M'` of order `k` over `R → A`
with the identity on a `B`-module `N` yields a differential operator of the same order on
`M ⊗[R] N → M' ⊗[R] N` with respect to `R → A ⊗[R] B`, for the canonical tensor-product action.
-/
theorem isDifferentialOperatorOfOrder_rTensor
    {D : M →ₗ[R] M'} {k : ℕ} (hD : D.IsDifferentialOperatorOfOrder A k) :
    (D.rTensor N).IsDifferentialOperatorOfOrder (A ⊗[R] B) k := by
  sorry

end
