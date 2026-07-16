import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_133_1
import stacks_proof.stacks_project.Chap10.Lemma_10_133_11

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
  -- The tensor-product algebra action is given by an `R`-linear endomorphism, so it commutes
  -- with the ambient `R`-scalar action by linearity.
  letI : Module B (M ⊗[R] N) := tensorRightModule
  letI : IsScalarTower R B (M ⊗[R] N) := tensorRightIsScalarTower
  letI : SMulCommClass A B (M ⊗[R] N) := tensorSmulCommClass
  refine ⟨?_⟩
  intro x r m
  change TensorProduct.Algebra.moduleAux x (r • m) = r • TensorProduct.Algebra.moduleAux x m
  simpa using
    (TensorProduct.Algebra.moduleAux (R := R) (A := A) (B := B) (M := M ⊗[R] N) x).map_smul r m

attribute [local instance] tensorAlgebra_smulCommClass

private theorem tensorAlgebra_smulCommClass' :
    SMulCommClass (A ⊗[R] B) R (M' ⊗[R] N) := by
  -- The same linearity argument installs the commuting scalar-action bridge on the codomain.
  letI : Module B (M' ⊗[R] N) := tensorRightModule'
  letI : IsScalarTower R B (M' ⊗[R] N) := tensorRightIsScalarTower'
  letI : SMulCommClass A B (M' ⊗[R] N) := tensorSmulCommClass'
  refine ⟨?_⟩
  intro x r m
  change TensorProduct.Algebra.moduleAux x (r • m) = r • TensorProduct.Algebra.moduleAux x m
  simpa using
    (TensorProduct.Algebra.moduleAux (R := R) (A := A) (B := B) (M := M' ⊗[R] N) x).map_smul r m

attribute [local instance] tensorAlgebra_smulCommClass'

/-- Helper for Lemma 10.133.13: the transported right `B`-action on `P ⊗[R] N` acts on pure
tensors by scaling the right factor. -/
private theorem tensor_right_smul_tmul
    {P : Type*} [AddCommGroup P] [Module R P]
    (b : B) (p : P) (n : N) :
    letI : Module B (P ⊗[R] N) := (TensorProduct.comm R P N).toAddEquiv.module B
    b • (p ⊗ₜ[R] n : P ⊗[R] N) = p ⊗ₜ[R] (b • n) := by
  -- The transported action is definitionally the usual action on the right tensor factor.
  rfl

/-- Helper for Lemma 10.133.13: a pure tensor scalar in `A ⊗[R] B` acts on `M ⊗[R] N` by acting
on the left factor through `A` and on the right factor through `B`. -/
private theorem tensorAlgebra_tmul_smul
    (a : A) (b : B) (m : M) (n : N) :
    (a ⊗ₜ[R] b : A ⊗[R] B) • (m ⊗ₜ[R] n : M ⊗[R] N) = (a • m) ⊗ₜ[R] (b • n) := by
  -- Expand the tensor-product algebra action into the successive `A`- and `B`-actions.
  letI : Module B (M ⊗[R] N) := tensorRightModule
  letI : IsScalarTower R B (M ⊗[R] N) := tensorRightIsScalarTower
  letI : SMulCommClass A B (M ⊗[R] N) := tensorSmulCommClass
  rw [TensorProduct.Algebra.smul_def]
  rw [tensor_right_smul_tmul (R := R) (B := B) (P := M) b m n]
  simpa using
    (TensorProduct.smul_tmul' a m (b • n) :
      a • (m ⊗ₜ[R] (b • n : N)) = (a • m) ⊗ₜ[R] (b • n))

/-- Helper for Lemma 10.133.13: the same pure-tensor scalar formula holds on the tensor-product
codomain `M' ⊗[R] N`. -/
private theorem tensorAlgebra_tmul_smul'
    (a : A) (b : B) (m : M') (n : N) :
    (a ⊗ₜ[R] b : A ⊗[R] B) • (m ⊗ₜ[R] n : M' ⊗[R] N) = (a • m) ⊗ₜ[R] (b • n) := by
  -- The codomain action is built from the same left/right tensor factors, so the computation
  -- is identical.
  letI : Module B (M' ⊗[R] N) := tensorRightModule'
  letI : IsScalarTower R B (M' ⊗[R] N) := tensorRightIsScalarTower'
  letI : SMulCommClass A B (M' ⊗[R] N) := tensorSmulCommClass'
  rw [TensorProduct.Algebra.smul_def]
  rw [tensor_right_smul_tmul (R := R) (B := B) (P := M') b m n]
  simpa using
    (TensorProduct.smul_tmul' a m (b • n) :
      a • (m ⊗ₜ[R] (b • n : N)) = (a • m) ⊗ₜ[R] (b • n))

/-- Helper for Lemma 10.133.13: the canonical `A ⊗[R] B`-module structure on `M ⊗[R] N` extends
the ambient `R`-module structure through the algebra map `R → A ⊗[R] B`. -/
private theorem tensorAlgebra_isScalarTower :
    IsScalarTower R (A ⊗[R] B) (M ⊗[R] N) := by
  refine IsScalarTower.of_algebraMap_smul (R := R) (A := A ⊗[R] B) ?_
  intro r x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul m n =>
      -- Convert the algebra-map scalar to a pure tensor and compute its action on a pure tensor.
      simpa [algebraMap_apply, IsScalarTower.algebraMap_smul (A := A), TensorProduct.smul_tmul']
        using tensorAlgebra_tmul_smul (R := R) (A := A) (B := B)
          (algebraMap R A r) (1 : B) m n
  | add x y hx hy =>
      -- The scalar action is additive in the tensor argument, so the induction hypothesis applies
      -- termwise.
      have hx' : ((algebraMap R A r) ⊗ₜ[R] (1 : B)) • x = r • x := by
        simpa [algebraMap_apply] using hx
      have hy' : ((algebraMap R A r) ⊗ₜ[R] (1 : B)) • y = r • y := by
        simpa [algebraMap_apply] using hy
      simpa [algebraMap_apply, smul_add, hx', hy']

attribute [local instance] tensorAlgebra_isScalarTower

/-- Helper for Lemma 10.133.13: the same scalar-tower compatibility holds on the tensor-product
codomain `M' ⊗[R] N`. -/
private theorem tensorAlgebra_isScalarTower' :
    IsScalarTower R (A ⊗[R] B) (M' ⊗[R] N) := by
  refine IsScalarTower.of_algebraMap_smul (R := R) (A := A ⊗[R] B) ?_
  intro r x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul m n =>
      -- The codomain tensor module has the same scalar-tower computation on pure tensors.
      simpa [algebraMap_apply, IsScalarTower.algebraMap_smul (A := A), TensorProduct.smul_tmul']
        using tensorAlgebra_tmul_smul' (R := R) (A := A) (B := B)
          (algebraMap R A r) (1 : B) m n
  | add x y hx hy =>
      have hx' : ((algebraMap R A r) ⊗ₜ[R] (1 : B)) • x = r • x := by
        simpa [algebraMap_apply] using hx
      have hy' : ((algebraMap R A r) ⊗ₜ[R] (1 : B)) • y = r • y := by
        simpa [algebraMap_apply] using hy
      simpa [algebraMap_apply, smul_add, hx', hy']

attribute [local instance] tensorAlgebra_isScalarTower'

/-- Helper for Lemma 10.133.13: the scalar commutator of `D.rTensor N` with a pure tensor scalar
factors through the scalar commutator of `D` and a right-factor scalar. -/
private theorem rTensor_scalarCommutator_tmul
    {D : M →ₗ[R] M'} (a : A) (b : B) :
    (D.rTensor N).scalarCommutator (a ⊗ₜ[R] b) =
      ((Algebra.lsmul R (A ⊗[R] B) (M' ⊗[R] N) ((1 : A) ⊗ₜ[R] b) :
          Module.End R (M' ⊗[R] N))).comp ((D.scalarCommutator a).rTensor N) := by
  -- Compare both sides on pure tensors, where the source proof’s commutator identity is visible.
  ext m n
  simp [LinearMap.scalarCommutator_apply, tensorAlgebra_tmul_smul, tensorAlgebra_tmul_smul',
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 10.133.13: multiplication by a tensor-product scalar is an order-zero
differential operator on the tensor-product codomain. -/
private theorem tensorAlgebra_lsmul_isDifferentialOperatorOfOrder_zero
    (x : A ⊗[R] B) :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := R) (M := M' ⊗[R] N) (N := M' ⊗[R] N)
      (Algebra.lsmul R (A ⊗[R] B) (M' ⊗[R] N) x : Module.End R (M' ⊗[R] N))
      (A ⊗[R] B) 0 := by
  -- Left multiplication commutes with every scalar multiplication because `A ⊗[R] B` is
  -- commutative.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro y z
  simp [smul_smul, mul_comm]

/-- Helper for Lemma 10.133.13: order-zero differential operators remain order zero after
tensoring on the right. -/
private theorem isDifferentialOperatorOfOrder_zero_rTensor
    {D : M →ₗ[R] M'} (hD0 : D.IsDifferentialOperatorOfOrder A 0) :
    (D.rTensor N).IsDifferentialOperatorOfOrder (A ⊗[R] B) 0 := by
  -- Unfold order zero and check the tensor-product scalar commutator by induction on the scalar.
  change ∀ a : A, D.scalarCommutator a = 0 at hD0
  change ∀ x : A ⊗[R] B, (D.rTensor N).scalarCommutator x = 0
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- The zero scalar has zero commutator by direct expansion.
    ext z
    simp [LinearMap.scalarCommutator_apply]
  · intro a b
    -- For pure tensors, the commutator formula reduces to the tensor of the vanishing source
    -- commutator.
    have hcomm :
        ((D.scalarCommutator a).rTensor N : M ⊗[R] N →ₗ[R] M' ⊗[R] N) = 0 := by
      simpa using congrArg (fun φ : M →ₗ[R] M' => φ.rTensor N) (hD0 a)
    rw [rTensor_scalarCommutator_tmul (D := D) a b]
    simp [hcomm]
  · intro x y hx hy
    -- Additivity of the scalar variable makes the commutator with `x + y` split into the sum of
    -- the already-vanishing commutators with `x` and `y`.
    ext m n
    have hxz := LinearMap.congr_fun hx (m ⊗ₜ[R] n)
    have hyz := LinearMap.congr_fun hy (m ⊗ₜ[R] n)
    calc
      (D.rTensor N).scalarCommutator (x + y) (m ⊗ₜ[R] n) =
          (D.rTensor N).scalarCommutator x (m ⊗ₜ[R] n) +
            (D.rTensor N).scalarCommutator y (m ⊗ₜ[R] n) := by
              simp [LinearMap.scalarCommutator_apply, add_smul, map_add, sub_eq_add_neg,
                add_assoc, add_left_comm, add_comm]
      _ = 0 + 0 := by simp [hxz, hyz]
      _ = 0 := by simp

-- Proof sketch: induct on `k`. For order `0`, the scalar commutator of `D.rTensor N` with an
-- element of `A ⊗[R] B` is checked on pure tensors and reduces to the order-zero commutator
-- relation for `D` over `A`. For the inductive step, the commutator with a generator `a ⊗ₜ b`
-- is given by postcomposing `((D.scalarCommutator a).rTensor N)` with multiplication by
-- `((1 : A) ⊗ₜ b)`, and additivity in the tensor-product scalar upgrades the pure-tensor
-- computation to all of `A ⊗[R] B`.
/-- Lemma 10.133.13: tensoring a differential operator `D : M → M'` of order `k` over `R → A`
with the identity on a `B`-module `N` yields a differential operator of the same order on
`M ⊗[R] N → M' ⊗[R] N` with respect to `R → A ⊗[R] B`, for the canonical tensor-product action.
-/
@[stacks 0G37]
theorem isDifferentialOperatorOfOrder_rTensor
    {D : M →ₗ[R] M'} {k : ℕ} (hD : D.IsDifferentialOperatorOfOrder A k) :
    (D.rTensor N).IsDifferentialOperatorOfOrder (A ⊗[R] B) k := by
  induction k generalizing D with
  | zero =>
      -- The base case is the tensor-product linearity statement proved above.
      simpa using isDifferentialOperatorOfOrder_zero_rTensor (N := N) hD
  | succ k ih =>
      -- The recursive criterion reduces order `k + 1` to scalar commutators of order `k`.
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · -- The zero scalar commutator is the zero map, which has every order bound.
        have hzero :
            (D.rTensor N).scalarCommutator (0 : A ⊗[R] B) = 0 := by
          ext z
          simp [LinearMap.scalarCommutator_apply]
        rw [hzero]
        exact (differential_operators_order_le_submodule
          R (A ⊗[R] B) (M ⊗[R] N) k (M' ⊗[R] N)).zero_mem
      · intro a b
        -- For a pure tensor scalar, postcompose the tensor of the source commutator with the
        -- order-zero multiplication map by `1 ⊗ b`.
        rw [rTensor_scalarCommutator_tmul (D := D) a b]
        have hrtensor :
            ((D.scalarCommutator a).rTensor N).IsDifferentialOperatorOfOrder (A ⊗[R] B) k :=
          ih (hD a)
        have hlsmul :
            LinearMap.IsDifferentialOperatorOfOrder
              (R := R) (M := M' ⊗[R] N) (N := M' ⊗[R] N)
              (Algebra.lsmul R (A ⊗[R] B) (M' ⊗[R] N) ((1 : A) ⊗ₜ[R] b) :
                Module.End R (M' ⊗[R] N))
              (A ⊗[R] B) 0 :=
          tensorAlgebra_lsmul_isDifferentialOperatorOfOrder_zero
            (M' := M') (N := N) ((1 : A) ⊗ₜ[R] b)
        have hcomp :
            (((Algebra.lsmul R (A ⊗[R] B) (M' ⊗[R] N) ((1 : A) ⊗ₜ[R] b) :
                Module.End R (M' ⊗[R] N))).comp
              ((D.scalarCommutator a).rTensor N)).IsDifferentialOperatorOfOrder
                (A ⊗[R] B) (k + 0) :=
          LinearMap.isDifferentialOperatorOfOrder_comp
            (R := R) (S := A ⊗[R] B)
            (L := M ⊗[R] N) (M := M' ⊗[R] N) (N := M' ⊗[R] N)
            hrtensor hlsmul
        simpa using hcomp
      · intro x y hx hy
        -- The scalar commutator is additive in the tensor-product scalar, and order `k`
        -- differential operators are closed under addition.
        have hxy :
            (D.rTensor N).scalarCommutator (x + y) =
              (D.rTensor N).scalarCommutator x + (D.rTensor N).scalarCommutator y := by
          ext z
          simp [LinearMap.scalarCommutator_apply, add_smul, map_add, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]
        rw [hxy]
        exact LinearMap.isDifferentialOperatorOfOrder_add hx hy

end
