import Mathlib
import StacksProject_2024.Chap10.Definition_10_14_1
import StacksProject_2024.Chap10.Lemma_10_133_2
import StacksProject_2024.Chap10.Remark_10_133_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PrincipalParts TensorProduct
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

/-
Domain triage:
* primary domain: principal parts and their behavior under base change;
* sampled owner API:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `tensorBaseChangeModuleMap`,
  `IsBaseChange`,
  `TensorProduct.isBaseChange`,
  `IsBaseChange.equiv`;
* source-facing layer here: principal parts commute with base change along the pushout square
  `A → B`, `A → A'`, `B → B ⊗[A] A'`;
* core/canonical owner: `IsBaseChange B' (principalPartsBaseChangeMap k
  (tensorBaseChangeModuleMap M))`;
* bridge/view: the later textbook model `M ⊗[A] A'`, obtained from the owner tensor by
  `Algebra.IsPushout.cancelBaseChange` and tensor symmetry; the lifted tensor map and its
  bijectivity are derived API from the owner abstraction.

Primitive data are the canonical base-change map `M → (B ⊗[A] A') ⊗[B] M` and the upstream owner
`principalPartsBaseChangeMap`; the comparison on principal parts is controlled canonically by the
owner predicate `IsBaseChange`, while the lifted tensor map and its bijectivity are derived API.
-/

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

/-- Any tensor-base-changed `B`-module carries the canonical restricted `A'`-module structure. -/
local instance tensorBaseChangeCodomainA'
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    Module A' (B' ⊗[B] X) :=
  inferInstance

/-- Any tensor-base-changed `B`-module carries the canonical scalar tower `A' → B' → B' ⊗[B] X`.
-/
local instance tensorBaseChangeCodomainIsScalarTowerA'
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    IsScalarTower A' B' (B' ⊗[B] X) :=
  inferInstance

/-- Any tensor-base-changed `B`-module has commuting `A'`- and `B'`-actions. -/
local instance tensorBaseChangeCodomainSmulCommClass
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    SMulCommClass B' A' (B' ⊗[B] X) :=
  inferInstance

/-- The target free module on `M'` inherits the scalar tower `B → B'`. -/
local instance tensorBaseChangeFinsuppIsScalarTowerBB' : IsScalarTower B B' (M' →₀ B') :=
  inferInstance

/-- Any tensor-base-changed `B`-module carries the canonical restricted `A`-module structure. -/
local instance tensorBaseChangeCodomainA {X : Type u} [AddCommGroup X] [Module B X] [Module A X]
    [IsScalarTower A B X] : Module A (B' ⊗[B] X) :=
  inferInstance

/-- Any tensor-base-changed `B`-module carries the canonical scalar tower `A → A' → B' ⊗[B] X`.
-/
local instance tensorBaseChangeCodomainIsScalarTowerAA' {X : Type u} [AddCommGroup X]
    [Module B X] [Module A X] [IsScalarTower A B X] : IsScalarTower A A' (B' ⊗[B] X) :=
  inferInstance

/-- Helper for Lemma 10.133.8: the generic tensor-base-change generator map with the ambient rings
fixed to `A`, `B`, and `A'`. -/
private abbrev tensorBaseChangeModuleMapFixed
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    X →ₗ[B] B' ⊗[B] X :=
  tensorBaseChangeModuleMap (R := A) (S := B) (R' := A') X

/-- Helper for Lemma 10.133.8: the canonical tensor-base-change generator is the pure tensor
`1 ⊗ x`. -/
private theorem tensor_base_change_generator_eq_one_tmul
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (x : X) :
    tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X x = ((1 : B') ⊗ₜ[B] x) := by
  rfl

/-- Helper for Lemma 10.133.8: the principal-parts universal class maps to the pure tensor
generator `1 ⊗ [m]` under tensor base change. -/
private theorem principal_parts_tensor_base_change_generator_eq_one_tmul
    (k : ℕ) (m : M) :
    (tensorBaseChangeModuleMap (P^{k}_{B⁄A}(M)))
      (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
        ((1 : B') ⊗ₜ[B]
          principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
  -- Proof comment: this is the general tensor-base-change generator formula specialized to the
  -- source principal-parts module.
  exact tensor_base_change_generator_eq_one_tmul
    (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M))
    (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)

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
private theorem linearMap_eq_of_apply_tensorBaseChange_eq
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
private noncomputable abbrev tensoredUniversalDifferential (k : ℕ) :
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
private theorem tensoredUniversalDifferential_apply_tensorBaseChange
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

/-
Route correction: the theorem-local support file owns the canonical tensor-base-change API for
`D_univ ⊗ 1`. This item now consumes that owner theorem instead of shadowing it locally.
-/

/-- Helper for Lemma 10.133.8: scaling a tensor-base-changed codomain by a fixed `A'`-scalar,
packaged as an `A'`-linear endomorphism. -/
private abbrev tensorBaseChangeCodomainSmulLinearMap
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (a' : A') :
    Module.End A' (B' ⊗[B] N) where
  toFun := fun z ↦ a' • z
  map_add' := by simp [smul_add]
  map_smul' := by
    intro c z
    calc
      a' • c • z = (a' * c) • z := by rw [smul_smul]
      _ = (c * a') • z := by rw [mul_comm]
      _ = (RingHom.id A') c • a' • z := by
            simpa using (smul_assoc c a' z)

/-- Helper for Lemma 10.133.8: the explicit scalar-multiplication endomorphism acts by pointwise
`A'`-scalar multiplication. -/
private theorem tensorBaseChangeCodomainSmulLinearMap_apply
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (a' : A') (z : B' ⊗[B] N) :
    tensorBaseChangeCodomainSmulLinearMap (A := A) (B := B) (A' := A') (N := N) a' z = a' • z :=
  rfl

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

/-- Helper for Lemma 10.133.8: any `B'`-linear map becomes an order-`0` differential operator
after restricting scalars to any smaller base ring. -/
private theorem restrictScalars_isDifferentialOperatorOfOrder_zero_of_linear
    {R S X Y : Type u} [Semiring R] [Semiring S] [SMul R S]
    [AddCommGroup X] [AddCommGroup Y]
    [Module S X] [Module R X] [IsScalarTower R S X]
    [SMulCommClass S R X]
    [Module S Y] [Module R Y] [IsScalarTower R S Y]
    [SMulCommClass S R Y]
    (f : X →ₗ[S] Y) :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := R) (M := X) (N := Y) (f.restrictScalars R) S 0 := by
  -- Proof comment: order `0` means `S`-linearity, which is exactly the hypothesis on `f`.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro s x
  simpa using f.map_smul s x

/-- Helper for Lemma 10.133.8: an order bound proved after restricting scalars from `A'` to `A`
upgrades back to the original `A'`-linear map. -/
private theorem isDifferentialOperatorOfOrder_of_restrictScalars
    {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module B' X] [Module A' X] [Module A X]
    [IsScalarTower A A' X] [IsScalarTower A' B' X]
    [SMulCommClass B' A X] [SMulCommClass B' A' X]
    [Module B' Y] [Module A' Y] [Module A Y]
    [IsScalarTower A A' Y] [IsScalarTower A' B' Y]
    [SMulCommClass B' A Y] [SMulCommClass B' A' Y]
    {f : X →ₗ[A'] Y} {k : ℕ}
    (h :
      LinearMap.IsDifferentialOperatorOfOrder
        (R := A) (M := X) (N := Y) (f.restrictScalars A) B' k) :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A') (M := X) (N := Y) f B' k := by
  induction k generalizing X Y f with
  | zero =>
      -- Proof comment: for order `0`, the restricted and unreduced statements are literally the
      -- same commuting-with-`B'` condition.
      rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at h ⊢
      exact h
  | succ k ih =>
      -- Proof comment: at the successor step, the scalar commutators agree after restricting
      -- scalars, so the induction hypothesis upgrades each restricted commutator certificate.
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at h ⊢
      intro b
      have hb :
          LinearMap.IsDifferentialOperatorOfOrder
            (R := A) (M := X) (N := Y)
            ((f.scalarCommutator b).restrictScalars A) B' k := by
        simpa [LinearMap.scalarCommutator] using h b
      exact ih (f := f.scalarCommutator b) hb

/-- Helper for Lemma 10.133.8: transport the `A'`-action on `X ⊗[A] A'` to the right tensor
factor. -/
private abbrev rtensor_right_module
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    Module A' (X ⊗[A] A') :=
  (TensorProduct.comm A X A').toAddEquiv.module A'

/-- Helper for Lemma 10.133.8: the transported right `A'`-action on `X ⊗[A] A'` is compatible
with the ambient `A`-module structure. -/
private theorem rtensor_right_isScalarTower
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
    IsScalarTower A A' (X ⊗[A] A') := by
  letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
  refine ⟨?_⟩
  intro a a' z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x c =>
      -- Proof comment: on pure tensors the transported right action is literally the action on
      -- the second factor.
      change x ⊗ₜ[A] ((a • a') • c) = a • (x ⊗ₜ[A] (a' • c) : X ⊗[A] A')
      rw [← TensorProduct.tmul_smul, smul_assoc]
  | add z w hz hw =>
      simp [hz, hw]

/-- Helper for Lemma 10.133.8: the left `B`-action and transported right `A'`-action commute on
`X ⊗[A] A'`. -/
private theorem rtensor_smulCommClass
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
    SMulCommClass B A' (X ⊗[A] A') := by
  letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
  refine ⟨?_⟩
  intro b a' z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x c =>
      -- Proof comment: on pure tensors the `B`-action is on the left factor and the transported
      -- `A'`-action is on the right factor.
      change (b • x) ⊗ₜ[A] (a' • c) = a' • (b • x ⊗ₜ[A] c : X ⊗[A] A')
      rfl
  | add z w hz hw =>
      simp [hz, hw]

local instance rtensor_module
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    Module B' (X ⊗[A] A') := by
  letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A A' (X ⊗[A] A') :=
    rtensor_right_isScalarTower (A := A) (B := B) (A' := A') X
  letI : SMulCommClass B A' (X ⊗[A] A') :=
    rtensor_smulCommClass (A := A) (B := B) (A' := A') X
  exact TensorProduct.Algebra.module

/-- Helper for Lemma 10.133.8: the canonical `B'`-action on the right tensor model commutes with
the ambient `A`-action. -/
private theorem rtensor_tensorAlgebra_smulCommClass
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    SMulCommClass B' A (X ⊗[A] A') := by
  letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A A' (X ⊗[A] A') :=
    rtensor_right_isScalarTower (A := A) (B := B) (A' := A') X
  letI : SMulCommClass B A' (X ⊗[A] A') :=
    rtensor_smulCommClass (A := A) (B := B) (A' := A') X
  letI : Module B' (X ⊗[A] A') := rtensor_module (A := A) (B := B) (A' := A') X
  -- Proof comment: the tensor-product algebra action is given by an `A`-linear endomorphism, so
  -- it commutes with the ambient `A`-scalar action by linearity.
  refine ⟨?_⟩
  intro x a z
  change TensorProduct.Algebra.moduleAux x (a • z) = a • TensorProduct.Algebra.moduleAux x z
  simpa using
    (TensorProduct.Algebra.moduleAux (R := A) (A := B) (B := A')
      (M := X ⊗[A] A') x).map_smul a z

attribute [local instance] rtensor_tensorAlgebra_smulCommClass

/-- Helper for Lemma 10.133.8: the commuting scalar-action relation on the right tensor model is
available with the scalar order reversed. -/
local instance rtensor_tensorAlgebra_smulCommClass_symm
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    SMulCommClass A B' (X ⊗[A] A') where
  smul_comm a x z := by
    -- Proof comment: symmetry of the established commuting scalar-action law gives the reverse
    -- order relation.
    simpa using (smul_comm x a z : x • (a • z) = a • (x • z)).symm

/-- Helper for Lemma 10.133.8: the right tensor model carries the expected scalar tower
`A → B' → X ⊗[A] A'`. -/
local instance rtensor_tensorAlgebra_isScalarTower
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    IsScalarTower A B' (X ⊗[A] A') := by
  letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A A' (X ⊗[A] A') :=
    rtensor_right_isScalarTower (A := A) (B := B) (A' := A') X
  letI : SMulCommClass B A' (X ⊗[A] A') :=
    rtensor_smulCommClass (A := A) (B := B) (A' := A') X
  letI : Module B' (X ⊗[A] A') := rtensor_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A' B' (X ⊗[A] A') := by
    apply IsScalarTower.of_algebraMap_smul
    intro a' z
    -- Proof comment: on pure tensors, the `A'`-scalar from `B'` is the pure tensor
    -- `(1 : B) ⊗ a'`, and both actions become the right-factor action.
    induction z using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul x c =>
        change ((1 : B) ⊗ₜ[A] a' : B') • (x ⊗ₜ[A] c : X ⊗[A] A') =
          a' • (x ⊗ₜ[A] c : X ⊗[A] A')
        rw [TensorProduct.Algebra.smul_def, one_smul]
    | add z w hz hw =>
        simp [hz, hw]
  -- Proof comment: with the intermediate tower `A → A' → B'` made explicit on the right tensor
  -- model, the desired scalar tower is the standard tower-composition instance.
  apply IsScalarTower.of_algebraMap_smul
  intro a z
  rw [IsScalarTower.algebraMap_apply A A' B']
  simpa using (IsScalarTower.algebraMap_smul (R := A) (A := A') a z)

/-- Helper for Lemma 10.133.8: the transported right `A'`-action scales the right tensor factor
on pure tensors. -/
private theorem rtensor_right_smul_tmul
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (a' : A') (x : X) (c : A') :
    letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
    a' • (x ⊗ₜ[A] c : X ⊗[A] A') = x ⊗ₜ[A] (a' • c) := by
  -- Proof comment: this transported action is definitionally the usual action on the second
  -- tensor factor.
  rfl

/-- Helper for Lemma 10.133.8: a pure tensor scalar in `B ⊗[A] A'` acts on `X ⊗[A] A'` by acting
separately on the two tensor factors. -/
private theorem rtensor_tmul_smul
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (b : B) (a' : A') (x : X) (c : A') :
    (b ⊗ₜ[A] a' : B') • (x ⊗ₜ[A] c : X ⊗[A] A') = (b • x) ⊗ₜ[A] (a' • c) := by
  letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A A' (X ⊗[A] A') :=
    rtensor_right_isScalarTower (A := A) (B := B) (A' := A') X
  letI : SMulCommClass B A' (X ⊗[A] A') :=
    rtensor_smulCommClass (A := A) (B := B) (A' := A') X
  letI : Module B' (X ⊗[A] A') := rtensor_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A B' (X ⊗[A] A') :=
    rtensor_tensorAlgebra_isScalarTower (A := A) (B := B) (A' := A') X
  -- Proof comment: expand the tensor-product algebra action into the successive `B`- and
  -- `A'`-actions on the two tensor factors.
  rw [TensorProduct.Algebra.smul_def]
  change b • (a' • (x ⊗ₜ[A] c : X ⊗[A] A')) = (b • x) ⊗ₜ[A] (a' • c)
  rw [rtensor_right_smul_tmul (A := A) (B := B) (A' := A') a' x c]
  simpa using
    (TensorProduct.smul_tmul' b x (a' • c) :
      b • (x ⊗ₜ[A] (a' • c : A')) = (b • x) ⊗ₜ[A] (a' • c))

/-- Helper for Lemma 10.133.8: the canonical map `x ↦ x ⊗ 1` into the right tensor model is
`B`-linear. -/
private theorem rightTensorBaseChangeGenerator_map_add
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (x y : X) :
    (x + y : X) ⊗ₜ[A] (1 : A') =
      (x ⊗ₜ[A] (1 : A')) + (y ⊗ₜ[A] (1 : A')) := by
  -- Proof comment: tensoring with the fixed scalar `1` is additive in the module argument.
  simpa using (TensorProduct.add_tmul x y (1 : A'))

/-- Helper for Lemma 10.133.8: the canonical map `x ↦ x ⊗ 1` into the right tensor model is
`B`-linear. -/
private theorem rightTensorBaseChangeGenerator_map_smul
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (b : B) (x : X) :
    (b • x : X) ⊗ₜ[A] (1 : A') = b • (x ⊗ₜ[A] (1 : A') : X ⊗[A] A') := by
  letI : Module A' (X ⊗[A] A') := rtensor_right_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A A' (X ⊗[A] A') :=
    rtensor_right_isScalarTower (A := A) (B := B) (A' := A') X
  letI : SMulCommClass B A' (X ⊗[A] A') :=
    rtensor_smulCommClass (A := A) (B := B) (A' := A') X
  letI : Module B' (X ⊗[A] A') := rtensor_module (A := A) (B := B) (A' := A') X
  letI : IsScalarTower A B' (X ⊗[A] A') :=
    rtensor_tensorAlgebra_isScalarTower (A := A) (B := B) (A' := A') X
  -- Proof comment: the restricted `B`-action is exactly the left-factor action on the right tensor
  -- model, so `b • (x ⊗ 1)` is `(b • x) ⊗ 1`.
  simpa using
    (TensorProduct.smul_tmul' b x (1 : A') :
      b • (x ⊗ₜ[A] (1 : A')) = (b • x) ⊗ₜ[A] (1 : A'))

/-- Helper for Lemma 10.133.8: the canonical map `x ↦ x ⊗ 1` into the right tensor model. -/
private abbrev rightTensorBaseChangeGenerator
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    X →ₗ[B] X ⊗[A] A' :=
  { toFun := fun x ↦ x ⊗ₜ[A] (1 : A')
    map_add' := rightTensorBaseChangeGenerator_map_add (A := A) (B := B) (A' := A') (X := X)
    map_smul' := rightTensorBaseChangeGenerator_map_smul (A := A) (B := B) (A' := A')
      (X := X) }

/-- Helper for Lemma 10.133.8: the scalar commutator of a right-tensored map with a pure tensor
scalar is postcomposition by multiplication with the right tensor factor, applied to the
right-tensored source commutator. -/
private theorem rtensor_scalarCommutator_tmul
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {D : M →ₗ[A] N} (b : B) (a' : A') :
    (D.rTensor A').scalarCommutator (b ⊗ₜ[A] a') =
      ((Algebra.lsmul A B' (N ⊗[A] A') ((1 : B) ⊗ₜ[A] a') :
          Module.End A (N ⊗[A] A'))).comp ((D.scalarCommutator b).rTensor A') := by
  -- Proof comment: compare both maps on pure tensors, where the scalar commutator visibly factors
  -- through the right-factor multiplication map.
  ext m c
  simp [rtensor_tmul_smul, sub_eq_add_neg]

/-- Helper for Lemma 10.133.8: multiplication by a `B'`-scalar on the right tensor model is an
order-`0` differential operator. -/
private theorem rtensor_lsmul_isDifferentialOperatorOfOrder_zero
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (x : B') :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := N ⊗[A] A') (N := N ⊗[A] A')
      (Algebra.lsmul A B' (N ⊗[A] A') x : Module.End A (N ⊗[A] A'))
      B' 0 := by
  -- Proof comment: left multiplication by a fixed scalar commutes with every scalar action
  -- because the tensor-product algebra `B'` is commutative.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro y z
  simp [smul_smul, mul_comm]

/-- Helper for Lemma 10.133.8: order-`0` differential operators remain order `0` after tensoring
on the right with `A'`. -/
private theorem isDifferentialOperatorOfOrder_zero_rTensor
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {D : M →ₗ[A] N}
    (hD0 : LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := M) (N := N) D B 0) :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := M ⊗[A] A') (N := N ⊗[A] A')
      (D.rTensor A') B' 0 := by
  -- Proof comment: unfold order zero and reduce the `B'`-scalar commutator to pure tensors.
  change ∀ b : B, D.scalarCommutator b = 0 at hD0
  change ∀ x : B', (D.rTensor A').scalarCommutator x = 0
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Proof comment: the zero scalar has zero commutator by direct expansion.
    ext z
    simp
  · intro b a'
    -- Proof comment: for pure tensors, the commutator formula reduces to the tensor of the
    -- vanishing source commutator.
    have hcomm :
        ((D.scalarCommutator b).rTensor A' : M ⊗[A] A' →ₗ[A] N ⊗[A] A') = 0 := by
      simpa using congrArg (fun φ : M →ₗ[A] N ↦ φ.rTensor A') (hD0 b)
    rw [rtensor_scalarCommutator_tmul (A := A) (B := B) (A' := A') (M := M) (D := D) b a']
    simp [hcomm]
  · intro x y hx hy
    -- Proof comment: the scalar commutator is additive in the scalar variable, so the induction
    -- hypotheses combine immediately.
    ext m c
    have hxz := LinearMap.congr_fun hx (m ⊗ₜ[A] c)
    have hyz := LinearMap.congr_fun hy (m ⊗ₜ[A] c)
    calc
      (D.rTensor A').scalarCommutator (x + y) (m ⊗ₜ[A] c) =
          (D.rTensor A').scalarCommutator x (m ⊗ₜ[A] c) +
            (D.rTensor A').scalarCommutator y (m ⊗ₜ[A] c) := by
              simp [add_smul, map_add, sub_eq_add_neg, add_assoc,
                add_left_comm, add_comm]
      _ = 0 + 0 := by simp [hxz, hyz]
      _ = 0 := by simp

/-- Helper for Lemma 10.133.8: tensoring an order-`k` differential operator on `M` with the
identity on `A'` preserves the order bound over `B ⊗[A] A'`. -/
private theorem linearMap_rTensor_isDifferentialOperatorOfOrder
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {D : M →ₗ[A] N} {k : ℕ}
    (hD : LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := M) (N := N) D B k) :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := M ⊗[A] A') (N := N ⊗[A] A')
      (D.rTensor A') B' k := by
  induction k generalizing D with
  | zero =>
      -- Proof comment: the order-zero case is exactly the already separated tensor-linearity
      -- argument.
        simpa using isDifferentialOperatorOfOrder_zero_rTensor
          (A := A) (B := B) (A' := A') (M := M) (N := N) hD
  | succ k ih =>
      -- Proof comment: the recursive criterion reduces the claim to order bounds for the scalar
      -- commutators with elements of `B'`; prove those by tensor induction on the scalar.
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · -- Proof comment: the commutator with the zero scalar is the zero map.
        have hzero :
            (D.rTensor A').scalarCommutator (0 : B') = 0 := by
          ext z
          simp
        rw [hzero]
        exact (differential_operators_order_le_submodule
          A B' (M ⊗[A] A') k (N ⊗[A] A')).zero_mem
      · intro b a'
        -- Proof comment: for a pure tensor scalar, the commutator factors through the tensor of
        -- the source commutator followed by multiplication by the right-factor scalar.
        rw [rtensor_scalarCommutator_tmul (A := A) (B := B) (A' := A') (M := M) (D := D) b a']
        have hrtensor :
            LinearMap.IsDifferentialOperatorOfOrder
              (R := A) (M := M ⊗[A] A') (N := N ⊗[A] A')
              ((D.scalarCommutator b).rTensor A') B' k :=
          ih (hD b)
        have hlsmul :
            LinearMap.IsDifferentialOperatorOfOrder
              (R := A) (M := N ⊗[A] A') (N := N ⊗[A] A')
              (Algebra.lsmul A B' (N ⊗[A] A') ((1 : B) ⊗ₜ[A] a') :
                Module.End A (N ⊗[A] A')) B' 0 :=
          rtensor_lsmul_isDifferentialOperatorOfOrder_zero
            (A := A) (B := B) (A' := A') (N := N) ((1 : B) ⊗ₜ[A] a')
        have hcomp :
            LinearMap.IsDifferentialOperatorOfOrder
              (R := A) (M := M ⊗[A] A') (N := N ⊗[A] A')
              (((Algebra.lsmul A B' (N ⊗[A] A') ((1 : B) ⊗ₜ[A] a') :
                  Module.End A (N ⊗[A] A'))).comp
                ((D.scalarCommutator b).rTensor A')) B' (k + 0) :=
          LinearMap.isDifferentialOperatorOfOrder_comp
            (R := A) (S := B')
            (L := M ⊗[A] A') (M := N ⊗[A] A') (N := N ⊗[A] A')
            hrtensor hlsmul
        simpa using hcomp
      · intro x y hx hy
        -- Proof comment: the scalar commutator is additive in the tensor-product scalar, and
        -- differential operators of bounded order are closed under addition.
        have hxy :
            (D.rTensor A').scalarCommutator (x + y) =
              (D.rTensor A').scalarCommutator x + (D.rTensor A').scalarCommutator y := by
          ext z
          simp [add_smul, map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [hxy]
        exact LinearMap.isDifferentialOperatorOfOrder_add hx hy

/-- Helper for Lemma 10.133.8: the universal differential operator remains order `k` on the
canonical right tensor model `M ⊗[A] A'`. -/
private theorem principal_parts_universal_differential_rTensor_isDifferentialOperatorOfOrder
    (k : ℕ) :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := M ⊗[A] A') (N := P^{k}_{B⁄A}(M) ⊗[A] A')
      ((principal_parts_universal_differential (R := A) (S := B) (M := M) k).rTensor A')
      B' k := by
  -- Proof comment: this is the generic right-tensor order theorem applied to the universal
  -- differential operator.
  exact linearMap_rTensor_isDifferentialOperatorOfOrder
    (A := A) (B := B) (A' := A') (M := M)
    (N := P^{k}_{B⁄A}(M))
    (D := principal_parts_universal_differential (R := A) (S := B) (M := M) k)
    (k := k)
    (principal_parts_universal_differential_isDifferentialOperatorOfOrder
      (A := A) (B := B) (M := M) k)

/-- Helper for Lemma 10.133.8: `baseChange` is the `TensorProduct.comm` conjugate of `rTensor`.
-/
private theorem linearMap_baseChange_eq_comm_conjugate
    {N : Type u} [AddCommGroup N] [Module A N]
    (D : M →ₗ[A] N) :
    D.baseChange A' =
      (((TensorProduct.comm A A' N).symm.toLinearMap).comp
        ((D.rTensor A').comp (TensorProduct.comm A A' M).toLinearMap)) := by
  -- Proof comment: on a pure tensor `a' ⊗ m`, both sides are `a' ⊗ D m`.
  ext a' m
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

/-- Any left-base-changed `A`-module carries the canonical restricted `A`-module structure. -/
local instance leftBaseChangeModuleA {X : Type u} [AddCommGroup X] [Module A X] :
    Module A (A' ⊗[A] X) :=
  inferInstance

/-- Any left-base-changed `A`-module carries the canonical restricted `A'`-module structure. -/
local instance leftBaseChangeModuleA' {X : Type u} [AddCommGroup X] [Module A X] :
    Module A' (A' ⊗[A] X) :=
  inferInstance

/-- Any left-base-changed `A`-module sits in the scalar tower `A → A' → A' ⊗[A] X`. -/
local instance leftBaseChangeIsScalarTowerAA' {X : Type u} [AddCommGroup X] [Module A X] :
    IsScalarTower A A' (A' ⊗[A] X) :=
  inferInstance

/-- Helper for Lemma 10.133.8: the left tensor generator `1 ⊗ x` swaps to the right tensor
generator `x ⊗ 1`. -/
private theorem tensorProduct_comm_apply_one_tmul
    {X : Type u} [AddCommGroup X] [Module A X] (x : X) :
    (TensorProduct.comm A A' X) ((1 : A') ⊗ₜ[A] x) = x ⊗ₜ[A] (1 : A') := by
  -- Proof comment: tensor symmetry literally swaps the factors of the pure generator.
  simp [TensorProduct.comm_tmul]

/-- Helper for Lemma 10.133.8: the inverse tensor symmetry sends the right tensor generator
`x ⊗ 1` back to `1 ⊗ x`. -/
private theorem tensorProduct_comm_symm_apply_tmul_one
    {X : Type u} [AddCommGroup X] [Module A X] (x : X) :
    (TensorProduct.comm A A' X).symm (x ⊗ₜ[A] (1 : A')) = ((1 : A') ⊗ₜ[A] x) := by
  -- Proof comment: this is the inverse pure-generator formula for the tensor symmetry.
  simpa using (TensorProduct.comm_symm_tmul (R := A) (M := A') (N := X) (1 : A') x)

/-- Helper for Lemma 10.133.8: transport the canonical tensor-base-changed module to the right
tensor model `X ⊗[A] A'` by `cancelBaseChange` followed by tensor symmetry. -/
private noncomputable abbrev tensorBaseChangeToRightTensor
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    B' ⊗[B] X →ₗ[A] X ⊗[A] A' :=
  ((TensorProduct.comm A A' X).toLinearMap).comp
    ((Algebra.IsPushout.cancelBaseChange A A' B B' X).toLinearMap.restrictScalars A)

/-- Helper for Lemma 10.133.8: transport the right tensor model `X ⊗[A] A'` back to the
canonical tensor-base-changed module by tensor symmetry followed by `cancelBaseChange.symm`. -/
private noncomputable abbrev rightTensorToTensorBaseChange
    (X : Type u) [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    X ⊗[A] A' →ₗ[A] B' ⊗[B] X :=
  ((Algebra.IsPushout.cancelBaseChange A A' B B' X).symm.toLinearMap.restrictScalars A).comp
    ((TensorProduct.comm A A' X).symm.toLinearMap)

/-- Helper for Lemma 10.133.8: the comparison from `B' ⊗[B] X` to `X ⊗[A] A'` sends the
canonical generator `1 ⊗ x` to the right-tensor generator `x ⊗ 1`. -/
private theorem tensorBaseChangeToRightTensor_apply_tensorBaseChange
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (x : X) :
    tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') X
      ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x) =
        x ⊗ₜ[A] (1 : A') := by
  -- Proof comment: `cancelBaseChange` sends the source generator to `1 ⊗ x`, and tensor
  -- symmetry then swaps that pure tensor to `x ⊗ 1`.
  calc
    tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') X
        ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x) =
      (TensorProduct.comm A A' X)
        ((Algebra.IsPushout.cancelBaseChange A A' B B' X)
          ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x)) := by
            rfl
    _ = (TensorProduct.comm A A' X) (((1 : A') ⊗ₜ[A] x)) := by
          rw [show (Algebra.IsPushout.cancelBaseChange A A' B B' X)
              ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x) =
                ((1 : A') ⊗ₜ[A] x) by
                  simpa [tensorBaseChangeModuleMapFixed, tensorBaseChangeModuleMap] using
                    (Algebra.IsPushout.cancelBaseChange_tmul
                      (R := A) (S := A') (A := B) (B := B') (M := X) x)]
    _ = x ⊗ₜ[A] (1 : A') := by
          exact tensorProduct_comm_apply_one_tmul (A := A) (A' := A') x

/-- Helper for Lemma 10.133.8: the comparison from `B' ⊗[B] X` to `X ⊗[A] A'` sends the pure
left tensor `(algebraMap A' B' a') ⊗ x` to the right pure tensor `x ⊗ a'`. -/
private theorem tensorBaseChangeToRightTensor_apply_pure_left_tensor
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (x : X) (a' : A') :
    tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') X
      (((algebraMap A' B' a') : B') ⊗ₜ[B] x) =
        x ⊗ₜ[A] a' := by
  -- Proof comment: rewrite the source pure tensor as the `A'`-multiple of `1 ⊗ x`, transport it
  -- through `cancelBaseChange`, and then swap the tensor factors.
  calc
    tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') X
        (((algebraMap A' B' a') : B') ⊗ₜ[B] x) =
      (TensorProduct.comm A A' X)
        ((Algebra.IsPushout.cancelBaseChange A A' B B' X)
          ((((algebraMap A' B' a') : B') ⊗ₜ[B] x))) := by
            rfl
    _ = (TensorProduct.comm A A' X) (a' • ((1 : A') ⊗ₜ[A] x)) := by
          congr 1
          have hsource : (((algebraMap A' B' a') : B') ⊗ₜ[B] x) = a' • ((1 : B') ⊗ₜ[B] x) := by
            change (((algebraMap A' B' a') : B') ⊗ₜ[B] x) =
              (((algebraMap A' B' a') * (1 : B')) ⊗ₜ[B] x)
            simp
          calc
            (Algebra.IsPushout.cancelBaseChange A A' B B' X)
                ((((algebraMap A' B' a') : B') ⊗ₜ[B] x)) =
              (Algebra.IsPushout.cancelBaseChange A A' B B' X)
                (a' • ((1 : B') ⊗ₜ[B] x)) := by
                  rw [hsource]
            _ = a' •
                (Algebra.IsPushout.cancelBaseChange A A' B B' X)
                  ((1 : B') ⊗ₜ[B] x) := by
                    rw [LinearEquiv.map_smul]
            _ = a' • ((1 : A') ⊗ₜ[A] x) := by
                  simp
    _ = (TensorProduct.comm A A' X) (a' ⊗ₜ[A] x) := by
          congr 1
          simpa using (TensorProduct.smul_tmul' a' (1 : A') x)
    _ = x ⊗ₜ[A] a' := by
          simp [TensorProduct.comm_tmul]

/-- Helper for Lemma 10.133.8: transporting the right-tensor generator `x ⊗ 1` back to
`B' ⊗[B] X` recovers the canonical base-change generator `1 ⊗ x`. -/
private theorem rightTensorToTensorBaseChange_apply_tmul_one
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (x : X) :
    rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') X (x ⊗ₜ[A] (1 : A')) =
      (tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x := by
  -- Proof comment: tensor symmetry first turns `x ⊗ 1` into `1 ⊗ x`, and then
  -- `cancelBaseChange.symm` turns that tensor back into the canonical base-change generator.
  calc
    rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') X (x ⊗ₜ[A] (1 : A')) =
      (Algebra.IsPushout.cancelBaseChange A A' B B' X).symm
        ((TensorProduct.comm A A' X).symm (x ⊗ₜ[A] (1 : A'))) := by
          rfl
    _ = (Algebra.IsPushout.cancelBaseChange A A' B B' X).symm (((1 : A') ⊗ₜ[A] x)) := by
          rw [tensorProduct_comm_symm_apply_tmul_one (A := A) (A' := A') x]
    _ = (tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') X) x := by
          exact tensorBaseChangeModuleMapFixed_eq_cancelBaseChange_symm_one_tmul
            (A := A) (B := B) (A' := A') (X := X) x

/-- Helper for Lemma 10.133.8: transporting a general right pure tensor `x ⊗ a'` back to the
canonical tensor-base-change model gives the pure tensor `a' ⊗ x`. -/
private theorem rightTensorToTensorBaseChange_apply_tmul
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    (x : X) (a' : A') :
    rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') X (x ⊗ₜ[A] a') =
      ((algebraMap A' B' a') ⊗ₜ[B] x) := by
  -- Proof comment: tensor symmetry swaps `x ⊗ a'` to `a' ⊗ x`, and `cancelBaseChange.symm`
  -- then identifies that left tensor with the canonical base-change pure tensor.
  calc
    rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') X (x ⊗ₜ[A] a') =
      (Algebra.IsPushout.cancelBaseChange A A' B B' X).symm
        ((TensorProduct.comm A A' X).symm (x ⊗ₜ[A] a')) := by
          rfl
    _ = (Algebra.IsPushout.cancelBaseChange A A' B B' X).symm (a' ⊗ₜ[A] x) := by
          simpa using (TensorProduct.comm_symm_tmul (R := A) (M := A') (N := X) a' x)
    _ = ((algebraMap A' B' a') ⊗ₜ[B] x) := by
          simpa using
            (Algebra.IsPushout.cancelBaseChange_symm_tmul
              (R := A) (S := A') (A := B) (B := B') (M := X) a' x)

/-- Helper for Lemma 10.133.8: the principal-parts module inherits the restricted `A`-module
structure from its ambient `B`-module structure. -/
local instance principalPartsModuleA (k : ℕ) : Module A (P^{k}_{B⁄A}(M)) :=
  inferInstance

/-- Helper for Lemma 10.133.8: the principal-parts module sits in the scalar tower `A → B →
P^k_{B/A}(M)`. -/
local instance principalPartsModuleIsScalarTower (k : ℕ) :
    IsScalarTower A B (P^{k}_{B⁄A}(M)) :=
  inferInstance

/-- Helper for Lemma 10.133.8: the base-changed principal-parts tensor module carries the
canonical scalar tower `A → A' → B' ⊗[B] P^k_{B/A}(M)`. -/
local instance principalPartsTensorBaseChangeIsScalarTowerAA' (k : ℕ) :
    IsScalarTower A A' (B' ⊗[B] P^{k}_{B⁄A}(M)) :=
  inferInstance

/-- Helper for Lemma 10.133.8: the base-changed principal-parts tensor module carries the
canonical scalar tower `A' → B' → B' ⊗[B] P^k_{B/A}(M)`. -/
local instance principalPartsTensorBaseChangeIsScalarTowerA' (k : ℕ) :
    IsScalarTower A' B' (B' ⊗[B] P^{k}_{B⁄A}(M)) :=
  tensorBaseChangeCodomainIsScalarTowerA' (A := A) (B := B) (A' := A')
    (X := P^{k}_{B⁄A}(M))

/-- Helper for Lemma 10.133.8: the `B'`- and restricted `A'`-actions commute on the base-changed
principal-parts tensor module. -/
local instance principalPartsTensorBaseChangeSmulCommClass (k : ℕ) :
    SMulCommClass B' A' (B' ⊗[B] P^{k}_{B⁄A}(M)) :=
  tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A')
    (X := P^{k}_{B⁄A}(M))

/-- Helper for Lemma 10.133.8: linear maps from `M'` to the base-changed principal-parts tensor
module admit restricted `A`-scalars along `A → A'`. -/
local instance principalPartsTensorBaseChangeCompatibleSmul (k : ℕ) :
    LinearMap.CompatibleSMul M' (B' ⊗[B] P^{k}_{B⁄A}(M)) A A' :=
  ⟨fun f c x ↦ by
    rw [← smul_one_smul A' c x, ← smul_one_smul A' c (f x), map_smul]⟩

/-- Helper for Lemma 10.133.8: linear maps out of a tensor-base-changed `B`-module admit
restricted `A'`-scalars along `A' → B'`. -/
local instance tensorBaseChangeCompatibleSmulA'
    {X Q : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X]
    [AddCommMonoid Q] [Module B' Q] [Module A' Q] [IsScalarTower A' B' Q] :
    LinearMap.CompatibleSMul (B' ⊗[B] X) Q A' B' :=
  ⟨fun f a' x ↦ by
    rw [← smul_one_smul B' a' x, ← smul_one_smul B' a' (f x), map_smul]⟩

/-- Helper for Lemma 10.133.8: after restricting scalars to `A`, the transported universal
differential is literally the comparison to the right tensor model, followed by `D_univ.rTensor`,
followed by the inverse comparison. -/
private abbrev tensoredUniversalDifferentialRestrictScalars (k : ℕ) :
    M' →ₗ[A] (B' ⊗[B] P^{k}_{B⁄A}(M)) :=
  (tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k).restrictScalars A

/-- Helper for Lemma 10.133.8: after restricting scalars to `A`, the transported universal
differential is literally the comparison to the right tensor model, followed by `D_univ.rTensor`,
followed by the inverse comparison. -/
private theorem tensoredUniversalDifferential_restrictScalars_eq_transport_comp_rTensor
    (k : ℕ) :
    tensoredUniversalDifferentialRestrictScalars
      (A := A) (B := B) (A' := A') (M := M) k =
      LinearMap.comp
        (rightTensorToTensorBaseChange (A := A) (B := B) (A' := A')
          (P^{k}_{B⁄A}(M)))
        (LinearMap.comp
          ((principal_parts_universal_differential (R := A) (S := B) (M := M) k).rTensor A')
          (tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') M)) := by
  -- Proof comment: rewrite `baseChange` as the tensor-symmetry conjugate of `rTensor`, then
  -- refold the left and right transport composites into the named comparison maps.
  ext x
  change
    (Algebra.IsPushout.cancelBaseChange A A' B B' (P^{k}_{B⁄A}(M))).symm
        (((principal_parts_universal_differential (R := A) (S := B) (M := M) k).baseChange A')
          ((Algebra.IsPushout.cancelBaseChange A A' B B' M) x)) =
      (rightTensorToTensorBaseChange (A := A) (B := B) (A' := A')
          (P^{k}_{B⁄A}(M)) ∘ₗ
        (principal_parts_universal_differential (R := A) (S := B) (M := M) k).rTensor A' ∘ₗ
          tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') M) x
  have hbc :
      (((principal_parts_universal_differential (R := A) (S := B) (M := M) k).baseChange A') :
          A' ⊗[A] M →ₗ[A] A' ⊗[A] P^{k}_{B⁄A}(M)) =
        LinearMap.comp
          ((TensorProduct.comm A A' P^{k}_{B⁄A}(M)).symm.toLinearMap)
          (LinearMap.comp
            ((principal_parts_universal_differential (R := A) (S := B) (M := M) k).rTensor A')
            (TensorProduct.comm A A' M).toLinearMap) := by
    simpa using
      (linearMap_baseChange_eq_comm_conjugate
        (A := A) (A' := A') (M := M)
        (D := principal_parts_universal_differential (R := A) (S := B) (M := M) k))
  have happly := congrArg
    (fun F : A' ⊗[A] M →ₗ[A] A' ⊗[A] P^{k}_{B⁄A}(M) ↦
      (Algebra.IsPushout.cancelBaseChange A A' B B' (P^{k}_{B⁄A}(M))).symm
        (F ((Algebra.IsPushout.cancelBaseChange A A' B B' M) x)))
    hbc
  simpa [tensorBaseChangeToRightTensor, rightTensorToTensorBaseChange, LinearMap.comp_assoc]
    using happly

/-- Helper for Lemma 10.133.8: the comparison from `B' ⊗[B] X` to the right tensor model
`X ⊗[A] A'` is an order-`0` differential operator over `A → B'`. -/
private theorem tensorBaseChangeToRightTensor_isDifferentialOperatorOfOrder_zero
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := B' ⊗[B] X) (N := X ⊗[A] A')
      (tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') X)
      B' 0 := by
  -- Proof comment: order `0` means `B'`-linearity. Reduce to the generators `1 ⊗ x`, prove the
  -- scalar action formula there by tensor induction on the scalar, and then extend to all pure
  -- tensors `r ⊗ x = r • (1 ⊗ x)` and hence to all tensors.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro c z
  induction z using TensorProduct.induction_on with
  | zero =>
      -- Proof comment: both sides send `0` to `0`.
      simp
  | add z w hz hw =>
      -- Proof comment: the statement is additive in the tensor variable.
      simp [smul_add, map_add, hz, hw]
  | tmul r x =>
      let T := tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') X
      have hgen :
          ∀ s : B',
            T (s • ((1 : B') ⊗ₜ[B] x)) = s • (x ⊗ₜ[A] (1 : A')) := by
        intro s
        induction s using TensorProduct.induction_on with
        | zero =>
            -- Proof comment: the zero scalar kills the generator on both sides.
            simp
        | add s t hs ht =>
            -- Proof comment: additivity in the scalar variable reduces to the induction
            -- hypotheses.
            calc
              T ((s + t) • ((1 : B') ⊗ₜ[B] x)) =
                  T (s • ((1 : B') ⊗ₜ[B] x) + t • ((1 : B') ⊗ₜ[B] x)) := by
                    rw [add_smul]
              _ = T (s • ((1 : B') ⊗ₜ[B] x)) + T (t • ((1 : B') ⊗ₜ[B] x)) := by
                    rw [map_add]
              _ = s • (x ⊗ₜ[A] (1 : A')) + t • (x ⊗ₜ[A] (1 : A')) := by
                    rw [hs, ht]
              _ = (s + t) • (x ⊗ₜ[A] (1 : A')) := by
                    rw [add_smul]
        | tmul b a' =>
            have hsource :
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
            calc
              T (((b ⊗ₜ[A] a' : B') • ((1 : B') ⊗ₜ[B] x))) =
                  T ((((algebraMap A' B' a') : B') ⊗ₜ[B] (b • x))) := by rw [hsource]
              _ = (b • x) ⊗ₜ[A] a' := by
                    rw [tensorBaseChangeToRightTensor_apply_pure_left_tensor
                      (A := A) (B := B) (A' := A') (X := X) (x := b • x) (a' := a')]
              _ = (b ⊗ₜ[A] a' : B') • (x ⊗ₜ[A] (1 : A')) := by
                    simpa using
                      (rtensor_tmul_smul (A := A) (B := B) (A' := A') (X := X) b a' x
                        (1 : A')).symm
      have hr : (r ⊗ₜ[B] x : B' ⊗[B] X) = r • ((1 : B') ⊗ₜ[B] x) := by
        change (r ⊗ₜ[B] x : B' ⊗[B] X) = ((r * (1 : B')) ⊗ₜ[B] x)
        simp
      calc
        T (c • (r ⊗ₜ[B] x)) = T (c • (r • ((1 : B') ⊗ₜ[B] x))) := by rw [hr]
        _ = T ((c * r) • ((1 : B') ⊗ₜ[B] x)) := by rw [smul_smul]
        _ = (c * r) • (x ⊗ₜ[A] (1 : A')) := hgen (c * r)
        _ = c • (r • (x ⊗ₜ[A] (1 : A'))) := by rw [smul_smul]
        _ = c • T (r • ((1 : B') ⊗ₜ[B] x)) := by rw [hgen r]
        _ = c • T (r ⊗ₜ[B] x) := by rw [hr]

/-- Helper for Lemma 10.133.8: the comparison from the right tensor model `X ⊗[A] A'` back to
`B' ⊗[B] X` is an order-`0` differential operator over `A → B'`. -/
private theorem rightTensorToTensorBaseChange_isDifferentialOperatorOfOrder_zero
    {X : Type u} [AddCommGroup X] [Module B X] [Module A X] [IsScalarTower A B X] :
    LinearMap.IsDifferentialOperatorOfOrder
      (R := A) (M := X ⊗[A] A') (N := B' ⊗[B] X)
      (rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') X)
      B' 0 := by
  -- Proof comment: again order `0` is `B'`-linearity. Reduce to the generators `x ⊗ 1`, prove
  -- the scalar action formula there by tensor induction on the scalar, and extend to all pure
  -- tensors `x ⊗ a' = (algebraMap A' B' a') • (x ⊗ 1)`.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro c z
  induction z using TensorProduct.induction_on with
  | zero =>
      -- Proof comment: both sides send `0` to `0`.
      simp
  | add z w hz hw =>
      -- Proof comment: the statement is additive in the tensor variable.
      simp [smul_add, map_add, hz, hw]
  | tmul x a' =>
      let Rmap := rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') X
      have hgen :
          ∀ s : B',
            Rmap (s • (x ⊗ₜ[A] (1 : A'))) =
              s • Rmap (x ⊗ₜ[A] (1 : A')) := by
        intro s
        induction s using TensorProduct.induction_on with
        | zero =>
            -- Proof comment: the zero scalar kills the generator on both sides.
            simp
        | add s t hs ht =>
            -- Proof comment: additivity in the scalar variable reduces to the induction
            -- hypotheses.
            calc
              Rmap ((s + t) • (x ⊗ₜ[A] (1 : A'))) =
                  Rmap (s • (x ⊗ₜ[A] (1 : A')) + t • (x ⊗ₜ[A] (1 : A'))) := by
                    rw [add_smul]
              _ = Rmap (s • (x ⊗ₜ[A] (1 : A'))) + Rmap (t • (x ⊗ₜ[A] (1 : A'))) := by
                    rw [map_add]
              _ = s • Rmap (x ⊗ₜ[A] (1 : A')) + t • Rmap (x ⊗ₜ[A] (1 : A')) := by
                    rw [hs, ht]
              _ = (s + t) • Rmap (x ⊗ₜ[A] (1 : A')) := by
                    rw [add_smul]
        | tmul b a'' =>
            have htarget :
                (((algebraMap A' B' a'') : B') ⊗ₜ[B] (b • x)) =
                  ((b ⊗ₜ[A] a'' : B') • ((1 : B') ⊗ₜ[B] x)) := by
              calc
                (((algebraMap A' B' a'') : B') ⊗ₜ[B] (b • x)) =
                    b • ((((algebraMap A' B' a'') : B') ⊗ₜ[B] x)) := by
                      simpa using
                        (TensorProduct.tmul_smul (R := B) (M := B') (N := X)
                          b ((algebraMap A' B' a'') : B') x)
                _ = ((b • (algebraMap A' B' a'') : B') ⊗ₜ[B] x) := by
                      simpa using
                        (TensorProduct.smul_tmul' (R := B) (M := B') (N := X)
                          b ((algebraMap A' B' a'') : B') x)
                _ = ((b ⊗ₜ[A] a'' : B') ⊗ₜ[B] x) := by
                      rw [Algebra.smul_def,
                        tensorProduct_tmul_eq_mul_algebraMap (A := A) (B := B) (A' := A') b a'',
                        tensorProduct_tmul_one_eq_algebraMap (A := A) (B := B) (A' := A') b]
                _ = ((b ⊗ₜ[A] a'' : B') • ((1 : B') ⊗ₜ[B] x)) := by
                      change ((b ⊗ₜ[A] a'' : B') ⊗ₜ[B] x) =
                        (((b ⊗ₜ[A] a'' : B') * (1 : B')) ⊗ₜ[B] x)
                      simp
            calc
              Rmap (((b ⊗ₜ[A] a'' : B') • (x ⊗ₜ[A] (1 : A')))) =
                  Rmap ((b • x) ⊗ₜ[A] a'') := by
                    exact congrArg Rmap <| by
                      simpa using
                        (rtensor_tmul_smul (A := A) (B := B) (A' := A') (X := X) b a'' x
                          (1 : A'))
              _ = (((algebraMap A' B' a'') : B') ⊗ₜ[B] (b • x)) := by
                    rw [rightTensorToTensorBaseChange_apply_tmul
                      (A := A) (B := B) (A' := A') (X := X) (x := b • x) (a' := a'')]
              _ = ((b ⊗ₜ[A] a'' : B') • ((1 : B') ⊗ₜ[B] x)) := htarget
              _ = (b ⊗ₜ[A] a'' : B') • Rmap (x ⊗ₜ[A] (1 : A')) := by
                    rw [rightTensorToTensorBaseChange_apply_tmul_one
                      (A := A) (B := B) (A' := A') (X := X) (x := x),
                      tensor_base_change_generator_eq_one_tmul
                        (A := A) (B := B) (A' := A') (X := X) x]
      have htmul :
          (x ⊗ₜ[A] a' : X ⊗[A] A') =
            (algebraMap A' B' a') • (x ⊗ₜ[A] (1 : A')) := by
        simpa [Algebra.TensorProduct.one_def] using
          (rtensor_tmul_smul (A := A) (B := B) (A' := A') (X := X) (1 : B) a' x
            (1 : A')).symm
      calc
        Rmap (c • (x ⊗ₜ[A] a')) =
            Rmap (c • ((algebraMap A' B' a') • (x ⊗ₜ[A] (1 : A')))) := by rw [htmul]
        _ = Rmap ((c * algebraMap A' B' a') • (x ⊗ₜ[A] (1 : A'))) := by rw [smul_smul]
        _ = (c * algebraMap A' B' a') • Rmap (x ⊗ₜ[A] (1 : A')) := hgen _
        _ = c • ((algebraMap A' B' a') • Rmap (x ⊗ₜ[A] (1 : A'))) := by rw [smul_smul]
        _ = c • Rmap ((algebraMap A' B' a') • (x ⊗ₜ[A] (1 : A'))) := by rw [hgen _]
        _ = c • Rmap (x ⊗ₜ[A] a') := by rw [htmul]

-- Route correction: the remaining hard step is the target-side order certificate for
-- `tensoredUniversalDifferential`. The downstream universal-property construction is organized to
-- consume this exact source-faithful transport theorem once the instance-stable statement is
-- restored.

/-- Helper for Lemma 10.133.8: the target-side transported universal differential has order at
most `k`, proved by restricting scalars to `A`, transporting to the right tensor model, applying
the right-tensor order theorem there, and transporting back. -/
private theorem tensoredUniversalDifferential_isDifferentialOperatorOfOrder_local
    (k : ℕ) :
    @LinearMap.IsDifferentialOperatorOfOrder A' M' (B' ⊗[B] P^{k}_{B⁄A}(M))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k) B'
      inferInstance inferInstance tensorBaseChangeModuleSmulCommClass
      (tensorBaseChangeCodomainSmulCommClass (A := A) (B := B) (A' := A')
        (X := P^{k}_{B⁄A}(M))) k := by
  let D :=
    principal_parts_universal_differential (R := A) (S := B) (M := M) k
  have hsrc :
      LinearMap.IsDifferentialOperatorOfOrder
        (R := A) (M := B' ⊗[B] M) (N := M ⊗[A] A')
        (tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') M)
        B' 0 :=
    tensorBaseChangeToRightTensor_isDifferentialOperatorOfOrder_zero
      (A := A) (B := B) (A' := A') (X := M)
  have hmid :
      LinearMap.IsDifferentialOperatorOfOrder
        (R := A) (M := M ⊗[A] A') (N := P^{k}_{B⁄A}(M) ⊗[A] A')
        (D.rTensor A') B' k := by
    simpa [D] using
      principal_parts_universal_differential_rTensor_isDifferentialOperatorOfOrder
        (A := A) (B := B) (A' := A') (M := M) k
  have htgt :
      LinearMap.IsDifferentialOperatorOfOrder
        (R := A) (M := P^{k}_{B⁄A}(M) ⊗[A] A') (N := B' ⊗[B] P^{k}_{B⁄A}(M))
        (rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') (P^{k}_{B⁄A}(M)))
        B' 0 :=
    rightTensorToTensorBaseChange_isDifferentialOperatorOfOrder_zero
      (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M))
  have hcomp₁ :
      LinearMap.IsDifferentialOperatorOfOrder
        (R := A) (M := B' ⊗[B] M) (N := P^{k}_{B⁄A}(M) ⊗[A] A')
        ((D.rTensor A').comp (tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') M))
        B' k := by
    simpa [Nat.zero_add] using
      LinearMap.isDifferentialOperatorOfOrder_comp
        (R := A) (S := B') (L := B' ⊗[B] M) (M := M ⊗[A] A') (N := P^{k}_{B⁄A}(M) ⊗[A] A')
        hsrc hmid
  have hrestrict :
      LinearMap.IsDifferentialOperatorOfOrder
        (R := A) (M := B' ⊗[B] M) (N := B' ⊗[B] P^{k}_{B⁄A}(M))
        (tensoredUniversalDifferentialRestrictScalars
          (A := A) (B := B) (A' := A') (M := M) k)
        B' k := by
    have hcomp₂ :
        LinearMap.IsDifferentialOperatorOfOrder
          (R := A) (M := B' ⊗[B] M) (N := B' ⊗[B] P^{k}_{B⁄A}(M))
          ((rightTensorToTensorBaseChange (A := A) (B := B) (A' := A') (P^{k}_{B⁄A}(M))).comp
            ((D.rTensor A').comp (tensorBaseChangeToRightTensor (A := A) (B := B) (A' := A') M)))
          B' k := by
      simpa [Nat.add_zero, LinearMap.comp_assoc] using
        LinearMap.isDifferentialOperatorOfOrder_comp
          (R := A) (S := B') (L := B' ⊗[B] M) (M := P^{k}_{B⁄A}(M) ⊗[A] A')
          (N := B' ⊗[B] P^{k}_{B⁄A}(M)) hcomp₁ htgt
    rw [tensoredUniversalDifferential_restrictScalars_eq_transport_comp_rTensor
      (A := A) (B := B) (A' := A') (M := M) k]
    simpa [D, LinearMap.comp_assoc] using hcomp₂
  letI : IsScalarTower A A' M' := tensorBaseChangeIsScalarTowerAA'
  letI : IsScalarTower A A' (B' ⊗[B] P^{k}_{B⁄A}(M)) :=
    principalPartsTensorBaseChangeIsScalarTowerAA' (A := A) (B := B) (A' := A') (M := M) k
  letI : SMulCommClass B' A M' := inferInstance
  letI : SMulCommClass B' A (B' ⊗[B] P^{k}_{B⁄A}(M)) := inferInstance
  exact
    @isDifferentialOperatorOfOrder_of_restrictScalars A B A'
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (M') (B' ⊗[B] P^{k}_{B⁄A}(M))
      inferInstance inferInstance
      tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeModuleA
      tensorBaseChangeIsScalarTowerAA' tensorBaseChangeIsScalarTowerA'
      inferInstance tensorBaseChangeModuleSmulCommClass
      inferInstance
      (tensorBaseChangeCodomainA' (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M)))
      (tensorBaseChangeCodomainA (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M)))
      (principalPartsTensorBaseChangeIsScalarTowerAA' (A := A) (B := B) (A' := A') (M := M) k)
      (principalPartsTensorBaseChangeIsScalarTowerA' (A := A) (B := B) (A' := A') (M := M) k)
      inferInstance
      (principalPartsTensorBaseChangeSmulCommClass (A := A) (B := B) (A' := A') (M := M) k)
      (f := tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k)
      (k := k) hrestrict

-- Route correction: the right-tensor transport instances are only needed for the source-side
-- `rTensor` argument. Turn them off before the target-side principal-parts owners so the target
-- free module uses the canonical self-module on `B'`, matching `principal_parts_module`.
attribute [-instance] rtensor_module
attribute [-instance] rtensor_tensorAlgebra_smulCommClass
attribute [-instance] rtensor_tensorAlgebra_smulCommClass_symm
attribute [-instance] rtensor_tensorAlgebra_isScalarTower

/-- Helper for Lemma 10.133.8: pin the target principal-parts relation submodule to the explicit
`A' → B' → M'` owner chain used throughout the target-side universal-property argument. -/
private abbrev targetPrincipalPartsRelationSubmodule (k : ℕ) : Submodule B' (M' →₀ B') :=
  @principal_parts_relation_submodule A' B' M'
    inferInstance inferInstance inferInstance inferInstance
    tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeIsScalarTowerA' k

/-- Helper for Lemma 10.133.8: use a single explicit quotient owner for the target principal-parts
module so `PP' k`, `mkQ`, and the target universal differential are definitionally aligned. -/
private abbrev targetPrincipalPartsModule (k : ℕ) : Type u :=
  (M' →₀ B') ⧸ targetPrincipalPartsRelationSubmodule
    (A := A) (B := B) (A' := A') (M := M) k

local notation "PP'" k =>
  targetPrincipalPartsModule (A := A) (B := B) (A' := A') (M := M) k

/-- The canonical principal-parts base-change map specialized to the tensor-base-changed module. -/
abbrev principalPartsTensorBaseChangeMap (k : ℕ) :
    P^{k}_{B⁄A}(M) →ₗ[B] PP' k :=
  @principalPartsBaseChangeMap A B A' B'
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    M M'
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance tensorBaseChangeModuleA tensorBaseChangeModuleA'
    inferInstance tensorBaseChangeIsScalarTowerA' inferInstance tensorBaseChangeIsScalarTowerAA'
    k (tensorBaseChangeModuleMap M)

/-- Helper for Lemma 10.133.8: evaluating a represented differential operator on the universal
class amounts to evaluating the underlying operator on the source element. -/
private theorem principal_parts_linear_map_equiv_symm_apply_universal_differential
    (k : ℕ) {Q : Type u} [AddCommGroup Q] [Module B Q] [Module A Q] [IsScalarTower A B Q]
    (D : differential_operators_order_le A B M k Q) (m : M) :
    (principal_parts_linear_map_equiv_differential_operators A B M k Q).symm D
      (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) = D.1 m := by
  let e := principal_parts_linear_map_equiv_differential_operators A B M k Q
  -- Proof comment: evaluate the identity `e (e.symm D) = D` at `m`.
  have h : (e (e.symm D)).1 m = D.1 m := by
    simpa using
      congrArg (fun E : differential_operators_order_le A B M k Q ↦ E.1 m)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 m = D.1 m
  exact h

/-- Helper for Lemma 10.133.8: evaluating the represented operator attached to a linear map out of
principal parts amounts to evaluating that linear map on the universal class. -/
private theorem principal_parts_linear_map_equiv_apply_universal_differential
    (k : ℕ) {Q : Type u} [AddCommGroup Q] [Module B Q] [Module A Q] [IsScalarTower A B Q]
    (L : P^{k}_{B⁄A}(M) →ₗ[B] Q) (m : M) :
    ((principal_parts_linear_map_equiv_differential_operators A B M k Q L).1 m) =
      L (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
  let e := principal_parts_linear_map_equiv_differential_operators A B M k Q
  -- Proof comment: reduce to the already established formula for `e.symm`.
  simpa [e] using
    (principal_parts_linear_map_equiv_symm_apply_universal_differential
      (k := k) (Q := Q) (D := e L) m).symm

/-- Helper for Lemma 10.133.8: the principal-parts representing equivalence evaluates on the
universal class by applying the represented linear map, uniformly over any base ring pair. -/
private theorem principal_parts_linear_map_equiv_symm_apply_universal_differential_generic
    {R S X Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (k : ℕ) (D : differential_operators_order_le R S X k Q) (x : X) :
    (principal_parts_linear_map_equiv_differential_operators R S X k Q).symm D
      (principal_parts_universal_differential (R := R) (S := S) (M := X) k x) = D.1 x := by
  let e := principal_parts_linear_map_equiv_differential_operators R S X k Q
  -- Proof comment: evaluate the identity `e (e.symm D) = D` at `x`.
  have h : (e (e.symm D)).1 x = D.1 x := by
    simpa using
      congrArg (fun E : differential_operators_order_le R S X k Q ↦ E.1 x)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 x = D.1 x
  exact h

/-- Helper for Lemma 10.133.8: the principal-parts representing equivalence evaluates on the
universal class by applying the represented linear map, uniformly over any base ring pair. -/
private theorem principal_parts_linear_map_equiv_apply_universal_differential_generic
    {R S X Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (k : ℕ) (L : P^{k}_{S⁄R}(X) →ₗ[S] Q) (x : X) :
    ((principal_parts_linear_map_equiv_differential_operators R S X k Q L).1 x) =
      L (principal_parts_universal_differential (R := R) (S := S) (M := X) k x) := by
  let e := principal_parts_linear_map_equiv_differential_operators R S X k Q
  -- Proof comment: reduce to the generic `e.symm` evaluation formula.
  simpa [e] using
    (principal_parts_linear_map_equiv_symm_apply_universal_differential_generic
      (R := R) (S := S) (X := X) (Q := Q) (k := k) (D := e L) x).symm

/-- Helper for Lemma 10.133.8: the specialized free-presentation map from Remark 10.133.7 sends
the basis vector `[m]` to the basis vector of `1 ⊗ m`. -/
private theorem principalPartsTensorBaseChangeMapOnFree_apply_basis_vector
    (m : M) :
    (((Finsupp.mapRange.linearMap (Algebra.linearMap B B')).comp
        (Finsupp.lmapDomain B B (tensorBaseChangeModuleMap M))) :
        (M →₀ B) →ₗ[B] (M' →₀ B'))
      (Finsupp.single m (1 : B)) =
        Finsupp.single ((tensorBaseChangeModuleMap M) m) (1 : B') := by
  -- Proof comment: the free map first changes the index `m` to `1 ⊗ m` and then transports the
  -- coefficient `1` along `B → B'`.
  simpa [LinearMap.comp_apply, tensorBaseChangeModuleMap, Algebra.TensorProduct.one_def]

/-- Helper for Lemma 10.133.8: the target universal differential with the explicit base-changed
module instances. -/
private abbrev targetPrincipalPartsUniversalDifferential (k : ℕ) :
    M' →ₗ[A'] PP' k :=
  @principal_parts_universal_differential A' B' M'
    inferInstance inferInstance inferInstance inferInstance
    tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeIsScalarTowerA' k

/-- Helper for Lemma 10.133.8: on the target side, the universal differential is literally the
quotient class of the basis vector `[m']`. -/
private theorem targetPrincipalPartsUniversalDifferential_eq_mkQ_basis
    (k : ℕ) (m' : M') :
    targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k m' =
      (targetPrincipalPartsRelationSubmodule (A := A) (B := B) (A' := A') (M := M) k).mkQ
        (Finsupp.single m' (1 : B')) := by
  -- Proof comment: the target universal differential is definitionally the quotient class of the
  -- basis vector with coefficient `1`.
  rfl

/-- Helper for Lemma 10.133.8: principal-parts base change sends the universal class `[m]` to the
universal class of the tensor-base-change generator `1 ⊗ m`. -/
private theorem principalPartsTensorBaseChangeMap_apply_universal_differential
    (k : ℕ) (m : M) :
    (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)
      (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
        ((@principal_parts_universal_differential A' B' M'
          inferInstance inferInstance inferInstance inferInstance
          tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeIsScalarTowerA'
          k) ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)) := by
  -- Proof comment: unfold the descended quotient map, evaluate it on the source basis class by
  -- `Submodule.mapQ_mkQ`, rewrite the free-map image of `[m]`, and then refold the target
  -- universal differential using the pinned quotient owner.
  change
    (targetPrincipalPartsRelationSubmodule (A := A) (B := B) (A' := A') (M := M) k).mkQ
        ((((Finsupp.mapRange.linearMap (Algebra.linearMap B B')).comp
            (Finsupp.lmapDomain B B (tensorBaseChangeModuleMap M))))
          (Finsupp.single m (1 : B))) =
      targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
        ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)
  rw [principalPartsTensorBaseChangeMapOnFree_apply_basis_vector]
  exact
    (targetPrincipalPartsUniversalDifferential_eq_mkQ_basis
      (A := A) (B := B) (A' := A') (M := M) k
      ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)).symm

/-- Helper for Lemma 10.133.8: a linear map out of principal parts is determined by its values on
the universal differential classes. -/
private theorem principal_parts_linear_map_eq_of_apply_universal_differential_eq
    {R S X Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (k : ℕ) {L₁ L₂ : P^{k}_{S⁄R}(X) →ₗ[S] Q}
    (h : ∀ x : X,
      L₁ (principal_parts_universal_differential (R := R) (S := S) (M := X) k x) =
        L₂ (principal_parts_universal_differential (R := R) (S := S) (M := X) k x)) :
    L₁ = L₂ := by
  let e := principal_parts_linear_map_equiv_differential_operators R S X k Q
  -- Proof comment: under the representing equivalence, pointwise equality on the universal
  -- differential classes is exactly equality of the represented differential operators.
  apply e.injective
  ext x
  simpa [principal_parts_linear_map_equiv_apply_universal_differential_generic] using h x

/-- Helper for Lemma 10.133.8: after lifting the principal-parts comparison map to the tensor
base change, the generator `1 ⊗ [m]` is sent to the target universal class of `1 ⊗ m`. -/
private theorem liftBaseChange_principalPartsTensorBaseChangeMap_apply_tensorBaseChange
    (k : ℕ) (m : M) :
    ((LinearMap.liftBaseChange B'
        (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)) :
        B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k)
      ((tensorBaseChangeModuleMap (P^{k}_{B⁄A}(M)))
        (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) =
        ((@principal_parts_universal_differential A' B' M'
          inferInstance inferInstance inferInstance inferInstance
          tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeIsScalarTowerA'
          k) ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)) := by
  -- Proof comment: rewrite the source generator as `1 ⊗ [m]`, evaluate the lifted map on a pure
  -- tensor, and then insert the restored generator formula for the descended principal-parts map.
  rw [tensor_base_change_generator_eq_one_tmul
    (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M))
    (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)]
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  exact principalPartsTensorBaseChangeMap_apply_universal_differential
    (A := A) (B := B) (A' := A') (M := M) k m

/-- Helper for Lemma 10.133.8: if `g'` lifts `g`, then evaluating `g'` on the target universal
class of `1 ⊗ m` reproduces the value of `g` on the source universal class of `m`. -/
private theorem lift_property_apply_universal_differential
    (k : ℕ) {Q : Type u} [AddCommMonoid Q] [Module B Q] [Module B' Q] [IsScalarTower B B' Q]
    (g : P^{k}_{B⁄A}(M) →ₗ[B] Q) (g' : (PP' k) →ₗ[B'] Q)
    (hLift :
      (g'.restrictScalars B).comp
          (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k) = g)
    (m : M) :
    g' (targetPrincipalPartsUniversalDifferential
      (A := A) (B := B) (A' := A') (M := M) k
      ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)) =
        g (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
  -- Proof comment: evaluate the lift identity on the source universal class and then rewrite the
  -- target side using the generator formula for `principalPartsTensorBaseChangeMap`.
  have hgen := DFunLike.congr_fun hLift
    (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)
  simpa [LinearMap.comp_apply, principalPartsTensorBaseChangeMap_apply_universal_differential]
    using hgen

/-- Helper for Lemma 10.133.8: after rewriting `tensorBaseChangeModuleMapFixed` as `1 ⊗ [m]`,
the lifted comparison map sends that pure tensor to the target universal class of `1 ⊗ m`. -/
private theorem liftBaseChange_principalPartsTensorBaseChangeMap_apply_one_tmul
    (k : ℕ) (m : M) :
    ((LinearMap.liftBaseChange B'
        (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)) :
        B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k)
      (((1 : B') ⊗ₜ[B]
        principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) =
        targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
          ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m) := by
  -- Proof comment: rewrite `1 ⊗ [m]` back to the canonical tensor-base-change generator and apply
  -- the established comparison-map generator formula.
  rw [← principal_parts_tensor_base_change_generator_eq_one_tmul
    (A := A) (B := B) (A' := A') (M := M) k m]
  exact liftBaseChange_principalPartsTensorBaseChangeMap_apply_tensorBaseChange
    (A := A) (B := B) (A' := A') (M := M) k m

/-- Helper for Lemma 10.133.8: the inverse comparison map is the `B'`-linear map represented by
the tensored universal differential `D_univ ⊗ 1`. -/
private noncomputable abbrev principalPartsTensorBaseChangeLift (k : ℕ) :
    (PP' k) →ₗ[B'] B' ⊗[B] P^{k}_{B⁄A}(M) :=
  -- Proof comment: represent the transported universal differential on the target principal-parts
  -- module via the standard principal-parts equivalence over `A' → B'`.
  (@principal_parts_linear_map_equiv_differential_operators A' B' M'
      inferInstance inferInstance inferInstance inferInstance
      tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeIsScalarTowerA'
      k (B' ⊗[B] P^{k}_{B⁄A}(M))
      inferInstance inferInstance
      (tensorBaseChangeCodomainA' (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M)))
      (tensorBaseChangeCodomainIsScalarTowerA' (A := A) (B := B) (A' := A')
        (X := P^{k}_{B⁄A}(M)))).symm
    ⟨tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k,
      tensoredUniversalDifferential_isDifferentialOperatorOfOrder_local
        (A := A) (B := B) (A' := A') (M := M) k⟩

/-- Helper for Lemma 10.133.8: the represented inverse sends the target universal class of
`1 ⊗ m` to the source tensor generator `1 ⊗ [m]`. -/
private theorem principalPartsTensorBaseChangeLift_apply_universal_differential
    (k : ℕ) (m : M) :
    principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k
      (targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
        ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)) =
        ((1 : B') ⊗ₜ[B]
          principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
  -- Proof comment: evaluate the represented target-side lift on the target universal class and
  -- then rewrite the represented operator value with the explicit generator formula for
  -- `D_univ ⊗ 1`.
  calc
    principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k
        (targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
          ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)) =
      tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
        ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m) := by
          simpa [principalPartsTensorBaseChangeLift, targetPrincipalPartsUniversalDifferential] using
            (@principal_parts_linear_map_equiv_symm_apply_universal_differential_generic
      A' B' M' (B' ⊗[B] P^{k}_{B⁄A}(M))
      inferInstance inferInstance inferInstance inferInstance
      tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeIsScalarTowerA'
      inferInstance inferInstance
      (tensorBaseChangeCodomainA' (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M)))
      (tensorBaseChangeCodomainIsScalarTowerA' (A := A) (B := B) (A' := A')
        (X := P^{k}_{B⁄A}(M)))
      k
      (D := ⟨tensoredUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k,
        tensoredUniversalDifferential_isDifferentialOperatorOfOrder_local
          (A := A) (B := B) (A' := A') (M := M) k⟩)
      ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m))
    _ = ((1 : B') ⊗ₜ[B]
        principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
          simpa [tensorBaseChangeModuleMapFixed] using
            (tensoredUniversalDifferential_apply_tensorBaseChange
              (A := A) (B := B) (A' := A') (M := M) k m)

/-- Helper for Lemma 10.133.8: on the tensor-product side, the represented inverse is a left
inverse to the lifted principal-parts comparison map. -/
private theorem principalPartsTensorBaseChangeLift_comp_liftBaseChange_eq_id
    (k : ℕ) :
    ((principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k).comp
        ((LinearMap.liftBaseChange B'
          (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)) :
          B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k)) =
      (LinearMap.id : B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] B' ⊗[B] P^{k}_{B⁄A}(M)) := by
  let G :
      B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k :=
    (LinearMap.liftBaseChange B'
      (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k))
  let F :
      B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] B' ⊗[B] P^{k}_{B⁄A}(M) :=
    (principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k).comp G
  change F = LinearMap.id
  have hsource :
      ((F.restrictScalars B).comp
          (tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A')
            (P^{k}_{B⁄A}(M)))) =
        tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A')
          (P^{k}_{B⁄A}(M)) := by
    -- Proof comment: on the source universal differential classes, the lifted comparison map
    -- sends `1 ⊗ [m]` to the target universal class of `1 ⊗ m`, and the represented inverse sends
    -- that class back to `1 ⊗ [m]`; then extensionality on source principal parts finishes.
    apply principal_parts_linear_map_eq_of_apply_universal_differential_eq
      (R := A) (S := B) (X := M) (Q := B' ⊗[B] P^{k}_{B⁄A}(M)) k
    intro m
    calc
      ((F.restrictScalars B).comp
          (tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A')
            (P^{k}_{B⁄A}(M))))
          (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
        F (((1 : B') ⊗ₜ[B]
          principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) := by
            rw [LinearMap.comp_apply,
              principal_parts_tensor_base_change_generator_eq_one_tmul
                (A := A) (B := B) (A' := A') (M := M) k m]
            rfl
      _ =
        principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k
          (targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
            ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)) := by
              change
                principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k
                  (((LinearMap.liftBaseChange B'
                    (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M)
                      k)) :
                    B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k)
                    (((1 : B') ⊗ₜ[B]
                      principal_parts_universal_differential (R := A) (S := B) (M := M) k
                        m))) = _
              rw [liftBaseChange_principalPartsTensorBaseChangeMap_apply_one_tmul
                (A := A) (B := B) (A' := A') (M := M) k m]
      _ = ((1 : B') ⊗ₜ[B]
          principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
            rw [principalPartsTensorBaseChangeLift_apply_universal_differential
              (A := A) (B := B) (A' := A') (M := M) k m]
      _ =
        (tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A')
          (P^{k}_{B⁄A}(M)))
          (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
            rw [← principal_parts_tensor_base_change_generator_eq_one_tmul
              (A := A) (B := B) (A' := A') (M := M) k m]
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r x
    have hx :
        F (((1 : B') ⊗ₜ[B] x)) = ((1 : B') ⊗ₜ[B] x) := by
      simpa [tensor_base_change_generator_eq_one_tmul
        (A := A) (B := B) (A' := A') (X := P^{k}_{B⁄A}(M)) x,
        LinearMap.comp_apply] using DFunLike.congr_fun hsource x
    have hr : (r ⊗ₜ[B] x : B' ⊗[B] P^{k}_{B⁄A}(M)) = r • ((1 : B') ⊗ₜ[B] x) := by
      change (r ⊗ₜ[B] x : B' ⊗[B] P^{k}_{B⁄A}(M)) = ((r * (1 : B')) ⊗ₜ[B] x)
      simp
    calc
      F (r ⊗ₜ[B] x) = F (r • ((1 : B') ⊗ₜ[B] x)) := by rw [hr]
      _ = r • F (((1 : B') ⊗ₜ[B] x)) := by rw [map_smul]
      _ = r • ((1 : B') ⊗ₜ[B] x) := by rw [hx]
      _ = (r ⊗ₜ[B] x : B' ⊗[B] P^{k}_{B⁄A}(M)) := by
        change ((r * (1 : B')) ⊗ₜ[B] x) = (r ⊗ₜ[B] x : B' ⊗[B] P^{k}_{B⁄A}(M))
        simp
  · intro z w hz hw
    simpa [map_add, hz, hw]

/-- Helper for Lemma 10.133.8: on the target principal-parts side, the lifted principal-parts
comparison map is a left inverse to the represented inverse. -/
private theorem liftBaseChange_principalPartsTensorBaseChangeMap_comp_principalPartsTensorBaseChangeLift_eq_id
    (k : ℕ) :
    (((LinearMap.liftBaseChange B'
        (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)) :
        B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k).comp
      (principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k)) =
      (LinearMap.id : (PP' k) →ₗ[B'] PP' k) := by
  let G :
      B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k :=
    (LinearMap.liftBaseChange B'
      (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k))
  let F : (PP' k) →ₗ[B'] PP' k :=
    G.comp (principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k)
  -- Proof comment: target principal parts are generated by the target universal differential, so
  -- it is enough to compare the two maps after precomposing with that universal operator.
  change F = LinearMap.id
  refine @principal_parts_linear_map_eq_of_apply_universal_differential_eq
    A' B' M' (PP' k)
    inferInstance inferInstance inferInstance inferInstance
    tensorBaseChangeModuleB' tensorBaseChangeModuleA' tensorBaseChangeIsScalarTowerA'
    inferInstance inferInstance inferInstance inferInstance
    k (L₁ := F) (L₂ := LinearMap.id) ?_
  intro m'
  have hpre :
      (((F.restrictScalars A').comp
          (targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k)) :
          M' →ₗ[A'] PP' k) =
        targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k := by
    -- Proof comment: reduce the equality of the two `A'`-linear maps on `M'` to the canonical
    -- base-change generators `1 ⊗ m`.
    apply linearMap_eq_of_apply_tensorBaseChange_eq
      (A := A) (B := B) (A' := A') (X := M) (Q := PP' k)
    intro m
    calc
      (((F.restrictScalars A').comp
          (targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k)) :
          M' →ₗ[A'] PP' k)
          ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m) =
        F (targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
          ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m)) := by
            rw [LinearMap.comp_apply]
            rfl
      _ =
        ((LinearMap.liftBaseChange B'
          (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)) :
          B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k)
          (((1 : B') ⊗ₜ[B]
            principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) := by
              change
                ((LinearMap.liftBaseChange B'
                  (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)) :
                  B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k)
                  (principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k
                    (targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A')
                      (M := M) k
                      ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m))) = _
              rw [principalPartsTensorBaseChangeLift_apply_universal_differential
                (A := A) (B := B) (A' := A') (M := M) k m]
      _ = targetPrincipalPartsUniversalDifferential (A := A) (B := B) (A' := A') (M := M) k
          ((tensorBaseChangeModuleMapFixed (A := A) (B := B) (A' := A') M) m) := by
            rw [liftBaseChange_principalPartsTensorBaseChangeMap_apply_one_tmul
              (A := A) (B := B) (A' := A') (M := M) k m]
  exact congrArg (fun G : M' →ₗ[A'] PP' k ↦ G m') hpre

/-- Helper for Lemma 10.133.8: the lifted principal-parts comparison map is a `B'`-linear
equivalence with inverse represented by `D_univ ⊗ 1`. -/
private noncomputable abbrev principalPartsTensorBaseChange_linearEquiv (k : ℕ) :
    B' ⊗[B] P^{k}_{B⁄A}(M) ≃ₗ[B'] (PP' k) :=
  -- Proof comment: package the canonical comparison map and the represented inverse into a
  -- two-sided linear equivalence.
  LinearEquiv.ofLinear
    ((LinearMap.liftBaseChange B'
      (principalPartsTensorBaseChangeMap (A := A) (B := B) (A' := A') (M := M) k)) :
      B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k)
    (principalPartsTensorBaseChangeLift (A := A) (B := B) (A' := A') (M := M) k)
    (liftBaseChange_principalPartsTensorBaseChangeMap_comp_principalPartsTensorBaseChangeLift_eq_id
      (A := A) (B := B) (A' := A') (M := M) k)
    (principalPartsTensorBaseChangeLift_comp_liftBaseChange_eq_id
      (A := A) (B := B) (A' := A') (M := M) k)

-- Proof sketch: identify `P^{k}_{B'⁄A'}(M')` as the base change of `P^{k}_{B⁄A}(M)` along
-- `B → B'` via the owner-level predicate `IsBaseChange` applied to the canonical comparison map
-- `principalPartsBaseChangeMap k (tensorBaseChangeModuleMap M)`.
/-- Owner-level base-change form of Lemma 10.133.8: the canonical principal-parts comparison map
realizes `P^k_{B'⁄A'}(M')` as the base change of `P^k_{B⁄A}(M)` along `B → B'`. -/
theorem principalPartsBaseChangeMap_isBaseChange (k : ℕ)
    :
    letI : IsScalarTower A A' M' := tensorBaseChangeIsScalarTowerAA'
    letI : IsScalarTower A' B' M' := tensorBaseChangeIsScalarTowerA'
    letI : SMulCommClass B' A' M' := tensorBaseChangeSmulCommClass
    letI : IsScalarTower A A' (B' ⊗[B] P^{k}_{B⁄A}(M)) := inferInstance
    letI : IsScalarTower A' B' (B' ⊗[B] P^{k}_{B⁄A}(M)) := inferInstance
    letI : SMulCommClass B' A' (B' ⊗[B] P^{k}_{B⁄A}(M)) := inferInstance
    IsBaseChange B' (principalPartsTensorBaseChangeMap k :
      P^{k}_{B⁄A}(M) →ₗ[B] PP' k) := by
  -- Proof comment: the explicit linear equivalence from the base-changed source principal parts to
  -- the target principal parts identifies the canonical tensor generator `1 ⊗ x` with the
  -- descended comparison map on `x`.
  apply IsBaseChange.of_equiv
    (principalPartsTensorBaseChange_linearEquiv (A := A) (B := B) (A' := A') (M := M) k)
  intro x
  simp [principalPartsTensorBaseChange_linearEquiv, LinearMap.liftBaseChange_tmul]

-- The source-facing tensor-product formulation is the derived bijectivity statement attached to
-- the owner-level base-change theorem above.
/-- Lemma 10.133.8: the canonical lifted principal-parts base-change map is bijective. -/
@[stacks 0H8Z]
theorem principal_parts_module_base_change_bijective (k : ℕ) :
    Function.Bijective
      ((LinearMap.liftBaseChange B' (principalPartsTensorBaseChangeMap k)) :
        B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] PP' k) := by
  let hbase := principalPartsBaseChangeMap_isBaseChange (A := A) (B := B) (A' := A') (M := M) k
  -- The source-facing tensor-product map is the linear equivalence attached to the owner-level
  -- base-change predicate.
  simpa using hbase.equiv.bijective
