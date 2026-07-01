import Mathlib
import stacks_project.Chap10.Definition_10_14_1
import stacks_project.Chap10.Lemma_10_133_13
import stacks_project.Chap10.Remark_10_133_7

open scoped PrincipalParts TensorProduct
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

variable {A B A' : Type u}
variable [CommRing A] [CommRing B] [CommRing A']
variable [Algebra A B] [Algebra A A']

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Algebra.TensorProduct.right_isScalarTower

variable {M : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

local notation "B'" => B ⊗[A] A'
local notation "M'" => B' ⊗[B] M

/-- The tensor-base-changed module carries the canonical restricted `A`-module structure. -/
local instance tensorBaseChangeModuleA : Module A M' :=
  inferInstance

/-- The tensor-base-changed module carries the canonical `B`-module structure coming from the left
factor of `B ⊗[A] A'`. -/
local instance tensorBaseChangeModuleB : Module B M' :=
  inferInstance

/-- The tensor-base-changed module carries the canonical restricted `A'`-module structure. -/
local instance tensorBaseChangeModuleA' : Module A' M' :=
  inferInstance

/-- The tensor-base-changed module carries the canonical `B'`-module structure. -/
local instance tensorBaseChangeModuleB' : Module B' M' :=
  inferInstance

/-- The canonical scalar tower `A → A' → M'` on the tensor-base-changed module. -/
local instance tensorBaseChangeIsScalarTowerAA' : IsScalarTower A A' M' :=
  inferInstance

/-- Helper for Lemma 10.133.8: use a fixed name for the scalar tower `A → A' → M'`. -/
local instance tensorBaseChangeModuleIsScalarTowerAA' : IsScalarTower A A' M' :=
  tensorBaseChangeIsScalarTowerAA'

/-- The canonical scalar tower `B → B' → M'` on the tensor-base-changed module. -/
local instance tensorBaseChangeIsScalarTowerBB' : IsScalarTower B B' M' :=
  inferInstance

/-- The canonical scalar tower `A' → B' → M'` on the tensor-base-changed module. -/
local instance tensorBaseChangeIsScalarTowerA' : IsScalarTower A' B' M' :=
  inferInstance

/-- The `A'`- and `B'`-actions commute on the tensor-base-changed module. -/
local instance tensorBaseChangeSmulCommClass : SMulCommClass B' A' M' where
  smul_comm b a x := by
    -- Both actions come from multiplication in the commutative ring `B'`.
    change b • ((algebraMap A' B' a) • x) = (algebraMap A' B' a) • (b • x)
    rw [← smul_assoc, ← smul_assoc]
    congr 1
    exact mul_comm _ _

/-- Helper for Lemma 10.133.8: use a fixed name for the commuting `B'`- and `A'`-actions on
`M'`. -/
local instance tensorBaseChangeModuleSmulCommClass : SMulCommClass B' A' M' :=
  tensorBaseChangeSmulCommClass

/-- The `A'`-action commutes with itself on the tensor-base-changed module. -/
local instance tensorBaseChangeSmulCommClass_self : SMulCommClass A' A' M' where
  smul_comm a a' x := by
    -- Both actions factor through multiplication by `algebraMap A' B'`.
    change (algebraMap A' B' a) • ((algebraMap A' B' a') • x) =
      (algebraMap A' B' a') • ((algebraMap A' B' a) • x)
    rw [← smul_assoc, ← smul_assoc]
    congr 1
    exact mul_comm _ _

/-- The `A'`- and `B'`-actions commute in both orders on the tensor-base-changed module. -/
local instance tensorBaseChangeSmulCommClass_symm : SMulCommClass A' B' M' where
  smul_comm a b x := by
    -- Both actions again come from multiplication in the commutative ring `B'`.
    change (algebraMap A' B' a) • (b • x) = b • ((algebraMap A' B' a) • x)
    rw [← smul_assoc, ← smul_assoc]
    congr 1
    exact mul_comm _ _

/-- Any tensor-base-changed `B`-module carries the canonical restricted `A'`-module structure. -/
local instance tensorBaseChangeCodomainA' {X : Type u} [AddCommGroup X] [Module B X] [Module A X]
    [IsScalarTower A B X] : Module A' (B' ⊗[B] X) :=
  inferInstance

/-- Helper for Lemma 10.133.8: any tensor-base-changed `B`-module carries the canonical
restricted `A`-module structure. -/
local instance tensorBaseChangeCodomainA {X : Type u} [AddCommGroup X] [Module B X] [Module A X]
    [IsScalarTower A B X] : Module A (B' ⊗[B] X) :=
  inferInstance

/-- Any tensor-base-changed `B`-module carries the canonical scalar tower `A' → B' → B' ⊗[B] X`.
-/
local instance tensorBaseChangeCodomainIsScalarTowerA' {X : Type u} [AddCommGroup X] [Module B X]
    [Module A X] [IsScalarTower A B X] : IsScalarTower A' B' (B' ⊗[B] X) :=
  inferInstance

/-- Helper for Lemma 10.133.8: any tensor-base-changed `B`-module carries the canonical scalar
tower `A → A' → B' ⊗[B] X`. -/
local instance tensorBaseChangeCodomainIsScalarTowerAA' {X : Type u} [AddCommGroup X]
    [Module B X] [Module A X] [IsScalarTower A B X] : IsScalarTower A A' (B' ⊗[B] X) :=
  inferInstance

/-- Any tensor-base-changed `B`-module has commuting `A'`- and `B'`-actions. -/
local instance tensorBaseChangeCodomainSmulCommClass {X : Type u} [AddCommGroup X] [Module B X]
    [Module A X] [IsScalarTower A B X] : SMulCommClass B' A' (B' ⊗[B] X) :=
  inferInstance

/-- Helper for Lemma 10.133.8: the generic tensor-base-change generator map with the ambient
rings fixed to `A`, `B`, and `A'`. -/
private abbrev tensorBaseChangeModuleMapFixed
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    X →ₗ[B] B' ⊗[B] X :=
  tensorBaseChangeModuleMap (R := A) (S := B) (R' := A') X

/-- Helper for Lemma 10.133.8: transporting `1 ⊗ x` back through `cancelBaseChange` recovers the
canonical base-change generator. -/
private theorem tensorBaseChangeModuleMapFixed_eq_cancelBaseChange_symm_one_tmul
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (x : X) :
    (Algebra.IsPushout.cancelBaseChange A A' B B' X).symm ((1 : A') ⊗ₜ[A] x) =
      (tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x := by
  -- Proof comment: this is the pushout generator formula specialized to `1 ⊗ x`.
  simpa [tensorBaseChangeModuleMapFixed, tensorBaseChangeModuleMap] using
    (Algebra.IsPushout.cancelBaseChange_symm_tmul (R := A) (S := A') (A := B) (B := B')
      (M := X) (1 : A') x)

/-- Helper for Lemma 10.133.8: an `A'`-linear map on the base-changed module is determined by its
values on the canonical image `x ↦ 1 ⊗ x`. -/
theorem linearMap_eq_of_apply_tensorBaseChange_eq
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    {Q : Type u} [AddCommMonoid Q] [Module A' Q] [Module A Q] [IsScalarTower A A' Q]
    {F G : (B' ⊗[B] X) →ₗ[A'] Q}
    (hcomp : ∀ x : X,
      F ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x) =
        G ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x)) :
    F = G := by
  let e := Algebra.IsPushout.cancelBaseChange A A' B B' X
  let F' : A' ⊗[A] X →ₗ[A'] Q := F.comp e.symm.toLinearMap
  let G' : A' ⊗[A] X →ₗ[A'] Q := G.comp e.symm.toLinearMap
  have hgen : ∀ x : X, F' ((1 : A') ⊗ₜ[A] x) = G' ((1 : A') ⊗ₜ[A] x) := by
    intro x
    -- Proof comment: after transporting to `A' ⊗[A] X`, the canonical generators are still the
    -- elements `1 ⊗ x`.
    change
      F ((Algebra.IsPushout.cancelBaseChange A A' B B' X).symm ((1 : A') ⊗ₜ[A] x)) =
        G ((Algebra.IsPushout.cancelBaseChange A A' B B' X).symm ((1 : A') ⊗ₜ[A] x))
    rw [tensorBaseChangeModuleMapFixed_eq_cancelBaseChange_symm_one_tmul
      (A := A) (B := B) (A' := A') (X := X) x]
    exact hcomp x
  have hFG' : F' = G' := by
    -- Proof comment: `TensorProduct.ext` reduces equality on the tensor product to the pure
    -- generators `a • (1 ⊗ x)`.
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    calc
      F' (a ⊗ₜ[A] x) = F' (a • ((1 : A') ⊗ₜ[A] x)) := by
        rw [TensorProduct.tmul_eq_smul_one_tmul]
      _ = a • F' ((1 : A') ⊗ₜ[A] x) := by rw [map_smul]
      _ = a • G' ((1 : A') ⊗ₜ[A] x) := by rw [hgen x]
      _ = G' (a • ((1 : A') ⊗ₜ[A] x)) := by rw [map_smul]
      _ = G' (a ⊗ₜ[A] x) := by rw [← TensorProduct.tmul_eq_smul_one_tmul]
  apply LinearMap.ext
  intro z
  -- Proof comment: evaluate the transported equality at `cancelBaseChange z` and simplify.
  have hz : F (e.symm (e z)) = G (e.symm (e z)) := by
    simpa only [F', G', LinearMap.comp_apply] using DFunLike.congr_fun hFG' (e z)
  rw [LinearEquiv.symm_apply_apply] at hz
  exact hz

/-- Helper for Lemma 10.133.8: transport an `A`-linear map to the tensor-base-changed model using
the canonical `cancelBaseChange` comparison. -/
private noncomputable abbrev tensoredLinearMap
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (D : M →ₗ[A] N) :
    M' →ₗ[A'] B' ⊗[B] N :=
  (((Algebra.IsPushout.cancelBaseChange A A' B B' N).symm.toLinearMap).comp
    (D.baseChange A')).comp
      ((Algebra.IsPushout.cancelBaseChange A A' B B' M).toLinearMap)

/-- Helper for Lemma 10.133.8: the source universal differential transported to the tensor
base-change model by the canonical `cancelBaseChange` equivalences. -/
noncomputable abbrev tensoredUniversalDifferential (k : ℕ) :
    M' →ₗ[A'] B' ⊗[B] P^{k}_{B⁄A}(M) :=
  tensoredLinearMap (A := A) (B := B) (A' := A') (M := M)
    (principal_parts_universal_differential (R := A) (S := B) (M := M) k)

/-- Helper for Lemma 10.133.8: transporting any `A`-linear map to the base-changed model sends the
generator `1 ⊗ m` to `1 ⊗ D m`. -/
private theorem tensoredLinearMap_apply_tensorBaseChange
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (D : M →ₗ[A] N) (m : M) :
    tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D
      ((tensorBaseChangeModuleMap M) m) =
    (1 : B') ⊗ₜ[B] D m := by
  -- Proof comment: rewrite the source generator through `cancelBaseChange`, apply the
  -- base-changed linear map on the pure tensor `1 ⊗ m`, and transport the result back.
  calc
    tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D
        ((tensorBaseChangeModuleMap M) m) =
      (Algebra.IsPushout.cancelBaseChange A A' B B' N).symm
        ((D.baseChange A') ((1 : A') ⊗ₜ[A] m)) := by
          change
            (Algebra.IsPushout.cancelBaseChange A A' B B' N).symm
              ((D.baseChange A')
                ((Algebra.IsPushout.cancelBaseChange A A' B B' M)
                  ((tensorBaseChangeModuleMap M) m))) =
              (Algebra.IsPushout.cancelBaseChange A A' B B' N).symm
                ((D.baseChange A') ((1 : A') ⊗ₜ[A] m))
          rw [show (Algebra.IsPushout.cancelBaseChange A A' B B' M)
              ((tensorBaseChangeModuleMap M) m) = ((1 : A') ⊗ₜ[A] m) by
                simpa [tensorBaseChangeModuleMap] using
                  (Algebra.IsPushout.cancelBaseChange_tmul
                    (R := A) (S := A') (A := B) (B := B') (M := M) m)]
    _ =
      (Algebra.IsPushout.cancelBaseChange A A' B B' N).symm
        ((1 : A') ⊗ₜ[A] D m) := by
          rw [LinearMap.baseChange_tmul]
    _ = (1 : B') ⊗ₜ[B] D m := by
          simpa [tensorBaseChangeModuleMapFixed, tensorBaseChangeModuleMap] using
            (Algebra.IsPushout.cancelBaseChange_symm_tmul
              (R := A) (S := A') (A := B) (B := B') (M := N) (1 : A') (D m))

/-- Helper for Lemma 10.133.8: the transported universal differential sends `1 ⊗ m` to
`1 ⊗ [m]`. -/
theorem tensoredUniversalDifferential_apply_tensorBaseChange
    (k : ℕ) (m : M) :
    tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
      ((tensorBaseChangeModuleMap M) m) =
    (1 : B') ⊗ₜ[B]
      principal_parts_universal_differential (R := A) (S := B) (M := M) k m := by
  -- Proof comment: this is the generic tensor-transport formula specialized to `D_univ`.
  simpa [tensoredUniversalDifferential] using
    tensoredLinearMap_apply_tensorBaseChange
      (A := A) (B := B) (A' := A') (M := M)
      (D := principal_parts_universal_differential (R := A) (S := B) (M := M) k) m

/-- Helper for Lemma 10.133.8: the source universal differential into `P^k_{B/A}(M)` has order
at most `k`. -/
private theorem principal_parts_universal_differential_isDifferentialOperatorOfOrder
    (k : ℕ) :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := M) (N := P^{k}_{B⁄A}(M))
      (principal_parts_universal_differential (R := A) (S := B) (M := M) k)
      B k := by
  let e := principal_parts_linear_map_equiv_differential_operators A B M k (P^{k}_{B⁄A}(M))
  -- Proof comment: the representing equivalence sends the identity map on principal parts to the
  -- universal differential operator.
  have hId :
      (((e (LinearMap.id : P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B⁄A}(M))) :
          differential_operators_order_le A B M k (P^{k}_{B⁄A}(M))).1).IsDifferentialOperatorOfOrder
        B k := by
    change
      (((e (LinearMap.id : P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B⁄A}(M))) :
          differential_operators_order_le A B M k (P^{k}_{B⁄A}(M))).1) ∈
        differential_operators_order_le_submodule A B M k (P^{k}_{B⁄A}(M))
    exact
      ((e (LinearMap.id : P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B⁄A}(M))) :
        differential_operators_order_le A B M k (P^{k}_{B⁄A}(M))).2
  simpa [e] using hId

/-- Helper for Lemma 10.133.8: scaling a tensor-base-changed codomain by a fixed `A'`-scalar,
packaged as an `A'`-linear endomorphism. -/
private abbrev tensorBaseChangeCodomainSmulLinearMap
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (a' : A') :
    Module.End A' (B' ⊗[B] N) where
  toFun := fun z ↦ a' • z
  map_add' := by
    intro x y
    simp [smul_add]
  map_smul' := by
    intro c z
    calc
      a' • c • z = (a' * c) • z := by rw [smul_smul]
      _ = (c * a') • z := by rw [mul_comm]
      _ = c • a' • z := by rw [smul_smul]

/-- Helper for Lemma 10.133.8: the explicit scalar-multiplication endomorphism acts by pointwise
`A'`-scalar multiplication. -/
private theorem tensorBaseChangeCodomainSmulLinearMap_apply
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (a' : A') (z : B' ⊗[B] N) :
    tensorBaseChangeCodomainSmulLinearMap (A := A) (B := B) (A' := A') (N := N) a' z = a' • z :=
  rfl

/-- Helper for Lemma 10.133.8: in `B ⊗[A] A'`, the pure tensor `b ⊗ a'` is the product of
`b ⊗ 1` with the image of `a'`. -/
private theorem tensorProduct_tmul_eq_mul_algebraMap
    (b : B) (a' : A') :
    (b ⊗ₜ[A] a' : B') = (b ⊗ₜ[A] (1 : A')) * algebraMap A' B' a' := by
  change (b ⊗ₜ[A] a' : B') = ((b ⊗ₜ[A] (1 : A')) * ((1 : B) ⊗ₜ[A] a'))
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- Helper for Lemma 10.133.8: the pure tensor `b ⊗ 1` is the image of `b` in `B ⊗[A] A'`. -/
private theorem tensorProduct_tmul_one_eq_algebraMap (b : B) :
    (b ⊗ₜ[A] (1 : A') : B') = algebraMap B B' b := by
  rfl

/-- Helper for Lemma 10.133.8: fix the explicit scalar commutator of a transported tensor-base
changed map, so later proofs do not depend on instance search. -/
private abbrev tensoredLinearMapScalarCommutator
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (D : M →ₗ[A] N) (c : B') :
    M' →ₗ[A'] B' ⊗[B] N :=
  @LinearMap.scalarCommutator A' B' M' (B' ⊗[B] N)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance
    tensorBaseChangeModuleSmulCommClass
    (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A') (X := N))
    (tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D) c

/-- Helper for Lemma 10.133.8: a pure tensor scalar in `B ⊗[A] A'` acts on the generator
`1 ⊗ x` by moving the `B`-scalar to the module factor and the `A'`-scalar to the tensor factor.
-/
private theorem tensor_base_change_pure_scalar_smul_generator_eq
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (b : B) (a' : A') (x : X) :
    ((b ⊗ₜ[A] a' : B') • ((1 : B') ⊗ₜ[B] x)) =
      (((algebraMap A' B' a') : B') ⊗ₜ[B] (b • x)) := by
  calc
    ((b ⊗ₜ[A] a' : B') • ((1 : B') ⊗ₜ[B] x)) =
        ((b • (algebraMap A' B' a') : B') ⊗ₜ[B] x) := by
          change (((b ⊗ₜ[A] a' : B') * (1 : B')) ⊗ₜ[B] x) =
            ((b • (algebraMap A' B' a') : B') ⊗ₜ[B] x)
          rw [mul_one, Algebra.smul_def,
            tensorProduct_tmul_eq_mul_algebraMap (A := A) (B := B) (A' := A') b a',
            tensorProduct_tmul_one_eq_algebraMap (A := A) (B := B) (A' := A') b]
    _ = b • ((((algebraMap A' B' a') : B') ⊗ₜ[B] x)) := by
          simpa using
            (TensorProduct.smul_tmul' (R := B) (M := B') (N := X)
              b ((algebraMap A' B' a') : B') x).symm
    _ = (((algebraMap A' B' a') : B') ⊗ₜ[B] (b • x)) := by
          simpa using
            (TensorProduct.tmul_smul (R := B) (M := B') (N := X)
              b ((algebraMap A' B' a') : B') x).symm

/-- Helper for Lemma 10.133.8: a pure tensor scalar in `B ⊗[A] A'` acts on the generator
`1 ⊗ x` by the corresponding `A'`-scalar times `1 ⊗ (b • x)`. -/
private theorem tensor_base_change_pure_scalar_smul_generator
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (b : B) (a' : A') (x : X) :
    ((b ⊗ₜ[A] a' : B') • ((1 : B') ⊗ₜ[B] x)) =
      a' • ((1 : B') ⊗ₜ[B] (b • x)) := by
  rw [tensor_base_change_pure_scalar_smul_generator_eq (A := A) (B := B) (A' := A') b a' x]
  simpa using
    (TensorProduct.smul_tmul' (R := B) (M := B') (N := X)
      (algebraMap A' B' a') (1 : B') (b • x)).symm

/-- Helper for Lemma 10.133.8: the same pure-tensor scalar formula written with the canonical
generator map `x ↦ 1 ⊗ x`. -/
private theorem tensor_base_change_pure_scalar_smul_tensorBaseChangeModuleMap
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (b : B) (a' : A') (x : X) :
    ((b ⊗ₜ[A] a' : B') • ((tensorBaseChangeModuleMap X) x)) =
      a' • ((tensorBaseChangeModuleMap X) (b • x)) := by
  simpa [tensorBaseChangeModuleMap] using
    tensor_base_change_pure_scalar_smul_generator (A := A) (B := B) (A' := A') b a' x

/-- Helper for Lemma 10.133.8: on a pure tensor scalar, the scalar commutator of the transported
map is the transported source scalar commutator followed by multiplication by the `A'`-factor. -/
private theorem tensoredLinearMap_scalarCommutator_tmul
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (D : M →ₗ[A] N) (b : B) (a' : A') :
    tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D
        (b ⊗ₜ[A] a') =
      (tensorBaseChangeCodomainSmulLinearMap (A := A) (B := B) (A' := A') (N := N) a').comp
        (tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) (D.scalarCommutator b)) := by
  letI : Module A (B' ⊗[B] N) := tensorBaseChangeCodomainA (A := A) (B := B) (A' := A') (X := N)
  letI : IsScalarTower A A' (B' ⊗[B] N) :=
    tensorBaseChangeCodomainIsScalarTowerAA' (A := A) (B := B) (A' := A') (X := N)
  apply linearMap_eq_of_apply_tensorBaseChange_eq (A := A) (B := B) (A' := A')
  intro m
  -- Proof comment: evaluate both sides on the generators `1 ⊗ m` and rewrite the pure tensor
  -- scalar action into the source scalar commutator.
  calc
    tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D
        (b ⊗ₜ[A] a') ((tensorBaseChangeModuleMap M) m) =
      tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D
          (((b ⊗ₜ[A] a' : B') • ((tensorBaseChangeModuleMap M) m))) -
        (b ⊗ₜ[A] a' : B') •
          tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D
            ((tensorBaseChangeModuleMap M) m) := by
            simp [tensoredLinearMapScalarCommutator, LinearMap.scalarCommutator_apply]
    _ =
      tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D
          (a' • ((tensorBaseChangeModuleMap M) (b • m))) -
        (b ⊗ₜ[A] a' : B') •
          tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D
            ((tensorBaseChangeModuleMap M) m) := by
            rw [tensor_base_change_pure_scalar_smul_tensorBaseChangeModuleMap
              (A := A) (B := B) (A' := A') b a' m]
    _ =
      a' • ((tensorBaseChangeModuleMap N) (D (b • m))) -
        (b ⊗ₜ[A] a' : B') •
          tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D
            ((tensorBaseChangeModuleMap M) m) := by
            rw [map_smul, tensoredLinearMap_apply_tensorBaseChange
              (A := A) (B := B) (A' := A') (M := M) (D := D) (b • m)]
    _ =
      a' • ((tensorBaseChangeModuleMap N) (D (b • m))) -
        a' • ((tensorBaseChangeModuleMap N) (b • D m)) := by
            rw [tensoredLinearMap_apply_tensorBaseChange
              (A := A) (B := B) (A' := A') (M := M) (D := D) m]
            rw [tensor_base_change_pure_scalar_smul_tensorBaseChangeModuleMap
              (A := A) (B := B) (A' := A') b a' (D m)]
    _ = a' • (((tensorBaseChangeModuleMap N) (D (b • m))) -
        ((tensorBaseChangeModuleMap N) (b • D m))) := by
            rw [smul_sub]
    _ = a' • ((tensorBaseChangeModuleMap N) (D (b • m) - b • D m)) := by
            simp [tensorBaseChangeModuleMap]
    _ = a' • ((tensorBaseChangeModuleMap N) (D.scalarCommutator b m)) := by
            simp [LinearMap.scalarCommutator_apply]
    _ =
      tensorBaseChangeCodomainSmulLinearMap (A := A) (B := B) (A' := A') (N := N) a'
        (tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) (D.scalarCommutator b)
          ((tensorBaseChangeModuleMap M) m)) := by
            rw [tensoredLinearMap_apply_tensorBaseChange
              (A := A) (B := B) (A' := A') (M := M) (D := D.scalarCommutator b) m,
              tensorBaseChangeCodomainSmulLinearMap_apply]

/-- Helper for Lemma 10.133.8: transporting an order-`k` differential operator along the
canonical tensor-base-change model preserves the order bound. -/
private theorem tensoredLinearMap_isDifferentialOperatorOfOrder
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {D : M →ₗ[A] N} {k : ℕ}
    (hD : LinearMap.IsDifferentialOperatorOfOrder (R := A) (M := M) (N := N) D B k) :
    @LinearMap.IsDifferentialOperatorOfOrder A' M' (B' ⊗[B] N)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) D) B'
      inferInstance inferInstance tensorBaseChangeModuleSmulCommClass
      (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A') (X := N)) k := by
  induction k generalizing D with
  | zero =>
      change ∀ c : B',
        tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D c = 0
      intro c
      refine TensorProduct.induction_on c ?_ ?_ ?_
      · ext z
        simp [LinearMap.scalarCommutator_apply]
      · intro b a'
        rw [tensoredLinearMap_scalarCommutator_tmul (A := A) (B := B) (A' := A')
          (M := M) (N := N) D b a']
        have hcomm : D.scalarCommutator b = 0 := hD b
        have hten :
            tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) (D.scalarCommutator b) = 0 := by
          apply linearMap_eq_of_apply_tensorBaseChange_eq (A := A) (B := B) (A' := A')
          intro m
          rw [tensoredLinearMap_apply_tensorBaseChange
            (A := A) (B := B) (A' := A') (M := M) (D := D.scalarCommutator b) m]
          simp [hcomm]
        simp [hten]
      · intro x y hx hy
        have hxy :
            tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D
                (x + y) =
              tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D
                  x +
                tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N)
                  D y := by
          ext z
          simp [LinearMap.scalarCommutator_apply, add_smul, map_add, sub_eq_add_neg, add_assoc,
            add_left_comm, add_comm]
        rw [hxy]
        exact LinearMap.isDifferentialOperatorOfOrder_add hx hy
  | succ k ih =>
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro c
      refine TensorProduct.induction_on c ?_ ?_ ?_
      · have hzero :
            tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D
              (0 : B') = 0 := by
          ext z
          simp [LinearMap.scalarCommutator_apply]
        rw [hzero]
        exact (differential_operators_order_le_submodule
          A B' (B' ⊗[B] M) k (B' ⊗[B] N)).zero_mem
      · intro b a'
        rw [tensoredLinearMap_scalarCommutator_tmul (A := A) (B := B) (A' := A')
          (M := M) (N := N) D b a']
        have hten :
            @LinearMap.IsDifferentialOperatorOfOrder A' M' (B' ⊗[B] N)
              inferInstance inferInstance inferInstance inferInstance inferInstance
              (tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) (D.scalarCommutator b)) B'
              inferInstance inferInstance tensorBaseChangeModuleSmulCommClass
              (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A') (X := N)) k :=
          ih (hD b)
        have hsmul :
            @LinearMap.IsDifferentialOperatorOfOrder A' (B' ⊗[B] N) (B' ⊗[B] N)
              inferInstance inferInstance inferInstance inferInstance inferInstance
              (tensorBaseChangeCodomainSmulLinearMap (A := A) (B := B) (A' := A') (N := N) a') B'
              inferInstance inferInstance
              (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A') (X := N))
              (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A') (X := N)) 0 := by
          rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
          intro c z
          simp [tensorBaseChangeCodomainSmulLinearMap_apply, smul_smul, mul_comm]
        have hcomp :
            @LinearMap.IsDifferentialOperatorOfOrder A' M' (B' ⊗[B] N)
              inferInstance inferInstance inferInstance inferInstance inferInstance
              ((tensorBaseChangeCodomainSmulLinearMap (A := A) (B := B) (A' := A') (N := N) a').comp
                (tensoredLinearMap (A := A) (B := B) (A' := A') (M := M) (D.scalarCommutator b))) B'
              inferInstance inferInstance tensorBaseChangeModuleSmulCommClass
              (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A') (X := N))
              (k + 0) :=
          LinearMap.isDifferentialOperatorOfOrder_comp
            (R := A') (S := B') (L := M') (M := B' ⊗[B] N) (N := B' ⊗[B] N) hten hsmul
        simpa using hcomp
      · intro x y hx hy
        have hxy :
            tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D
                (x + y) =
              tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N) D
                  x +
                tensoredLinearMapScalarCommutator (A := A) (B := B) (A' := A') (M := M) (N := N)
                  D y := by
          ext z
          simp [LinearMap.scalarCommutator_apply, add_smul, map_add, sub_eq_add_neg, add_assoc,
            add_left_comm, add_comm]
        rw [hxy]
        exact LinearMap.isDifferentialOperatorOfOrder_add hx hy

/-- Helper for Lemma 10.133.8: the transported universal differential still has order at most
`k` after tensor base change. -/
theorem tensoredUniversalDifferential_isDifferentialOperatorOfOrder
    (k : ℕ) :
    @LinearMap.IsDifferentialOperatorOfOrder A' M' (B' ⊗[B] P^{k}_{B⁄A}(M))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k) B'
      inferInstance inferInstance tensorBaseChangeModuleSmulCommClass
      (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A')
        (X := P^{k}_{B⁄A}(M))) k := by
  -- Proof comment: this is the general transported-order theorem applied to the source universal
  -- differential operator.
  simpa [tensoredUniversalDifferential] using
    tensoredLinearMap_isDifferentialOperatorOfOrder
      (A := A) (B := B) (A' := A') (M := M)
      (N := P^{k}_{B⁄A}(M))
      (D := principal_parts_universal_differential (R := A) (S := B) (M := M) k)
      (k := k)
      (principal_parts_universal_differential_isDifferentialOperatorOfOrder
        (A := A) (B := B) (M := M) k)
