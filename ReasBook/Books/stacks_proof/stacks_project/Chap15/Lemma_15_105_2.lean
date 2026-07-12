import Mathlib
import StacksProject_2024.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/- Domain triage:
- primary domain: commutative algebra of flat modules and the tensor-square criterion for weakly
  étale morphisms;
- source-facing layer: this Stacks lemma transferring flatness of a module from the base ring `A`
  to the algebra `B` under flatness of the multiplication map `B ⊗[A] B → B`;
- core/canonical owners: `Module.Flat`, `Module.Flat.baseChange`, `Module.Flat.trans`,
  `Algebra.IsWeaklyEtale`, and `(lmul' A).Flat`;
- bridge/view: the owner-level companion `Module.Flat.of_isWeaklyEtale`, obtained by feeding the
  tensor-square flatness field of `Algebra.IsWeaklyEtale A B` into the source-facing theorem.

The numbered theorem remains source-facing: there is no exact upstream owner theorem with this
interface, so the refinement is to keep the textbook statement while exposing the direct
owner-facing bridge separately.
-/

/-- Helper for Lemma 15.105.2: after restricting scalars from `B` to `A`, tensoring an exact
pair of `B`-linear maps with the `A`-flat module `N` stays exact. -/
-- This is the base-ring part of the Stacks argument: before using flatness of the multiplication
-- map `B ⊗[A] B → B`, exactness already holds after tensoring over `A`.
lemma tensorSquare_left_tensor_exact_of_flat_base
    (hflatN : Module.Flat A N)
    {L₁ L₂ L₃ : Type*}
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃]
    [Module B L₁] [Module B L₂] [Module B L₃]
    [Module A L₁] [Module A L₂] [Module A L₃]
    [IsScalarTower A B L₁] [IsScalarTower A B L₂] [IsScalarTower A B L₃]
    (f : L₁ →ₗ[B] L₂) (g : L₂ →ₗ[B] L₃)
    (hexact : Function.Exact f g) :
    Function.Exact
      (LinearMap.lTensor N (f.restrictScalars A))
      (LinearMap.lTensor N (g.restrictScalars A)) := by
  letI : Module.Flat A N := hflatN
  -- Once the coefficient ring is fixed to `A`, this is exactly `Module.Flat.lTensor_exact`.
  simpa using (Module.Flat.lTensor_exact (R := A) N hexact)

/-- Helper for Lemma 15.105.2: flatness of the multiplication map
`B ⊗[A] B → B` is equivalent to flatness of `B` as a module over the tensor square. -/
lemma tensorSquare_multiplication_algebraMap_flat
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    let _ : Algebra (B ⊗[A] B) B := (lmul' A).toRingHom.toAlgebra
    (algebraMap (B ⊗[A] B) B).Flat := by
  -- Convert ring-hom flatness of `lmul' A` into module flatness for the induced algebra map.
  letI : Algebra (B ⊗[A] B) B := (lmul' A).toRingHom.toAlgebra
  simpa [RingHom.algebraMap_toAlgebra] using
    (show (lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom.Flat from hflatMul)

/-- Helper for Lemma 15.105.2: the canonical `1 ⊗ -` map into the tensor-square base change
source used by the later comparison equivalence. -/
noncomputable def tensorSquare_right_baseChange_map
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    N ⊗[B] L →ₗ[B] (B ⊗[A] B) ⊗[B] (N ⊗[B] L) :=
  TensorProduct.mk B (B ⊗[A] B) (N ⊗[B] L) 1

/-- Helper for Lemma 15.105.2: on pure tensors, `tensorSquare_right_baseChange_map` is the
expected `1 ⊗ -` inclusion. -/
@[simp] lemma tensorSquare_right_baseChange_map_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (n : N) (l : L) :
    tensorSquare_right_baseChange_map (A := A) (B := B) (N := N) (L := L) (n ⊗ₜ[B] l) =
      (1 : B ⊗[A] B) ⊗ₜ[B] (n ⊗ₜ[B] l) :=
  rfl

/-- Helper for Lemma 15.105.2: the canonical `1 ⊗ -` map commutes with tensoring a `B`-linear map
on the right. -/
lemma tensorSquare_right_baseChange_map_naturality
    {L₁ L₂ : Type*}
    [AddCommGroup L₁] [AddCommGroup L₂]
    [Module B L₁] [Module B L₂]
    [Module A L₁] [Module A L₂]
    [IsScalarTower A B L₁] [IsScalarTower A B L₂]
    (f : L₁ →ₗ[B] L₂) :
    tensorSquare_right_baseChange_map (A := A) (B := B) (N := N) (L := L₂) ∘ₗ
        LinearMap.lTensor N f =
      LinearMap.lTensor (B ⊗[A] B) (LinearMap.lTensor N f) ∘ₗ
        tensorSquare_right_baseChange_map (A := A) (B := B) (N := N) (L := L₁) := by
  -- Both sides agree on pure tensors, so tensor-product extensionality finishes the comparison.
  ext n l
  simp [tensorSquare_right_baseChange_map]

/-- Helper for Lemma 15.105.2: canceling the right `B`-factor in
`(B ⊗[A] B) ⊗[B] N` identifies it with the ordinary base change `N ⊗[A] B`. -/
noncomputable def tensorSquare_right_factor_equiv :
    let S := B ⊗[A] B
    let _ : Algebra B S := Algebra.TensorProduct.rightAlgebra
    S ⊗[B] N ≃ₗ[B] N ⊗[A] B :=
  -- Route correction: cancel only the single right `B`-factor first.
  -- The source proof needs exactly `S ⊗[B] N ≃ N ⊗[A] B`, and this owner-level composite is
  -- stable: first swap the two `B`-tensor factors, then apply `cancelBaseChange`.
  (TensorProduct.comm B (B ⊗[A] B) N).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B N B)

/-- Helper for Lemma 15.105.2: the right-factor cancellation sends `1 ⊗ n` to the expected
pure tensor `n ⊗ 1`. -/
@[simp] lemma tensorSquare_right_factor_equiv_one_tmul (n : N) :
    let S := B ⊗[A] B
    let _ : Algebra B S := Algebra.TensorProduct.rightAlgebra
    tensorSquare_right_factor_equiv (A := A) (B := B) (N := N)
      ((1 : B ⊗[A] B) ⊗ₜ[B] n) =
        n ⊗ₜ[A] (1 : B) := by
  -- Reduce the composite to the two owner-level pure-tensor formulas: `comm_tmul` and then
  -- `cancelBaseChange_tmul` after rewriting the tensor-square unit as `1 ⊗ 1`.
  simp [tensorSquare_right_factor_equiv, Algebra.TensorProduct.one_def]

/-- Helper for Lemma 15.105.2: the right-factor cancellation keeps track of both tensor-square
coordinates on pure tensors. -/
@[simp] lemma tensorSquare_right_factor_equiv_tmul
    (b₁ b₂ : B) (n : N) :
    let S := B ⊗[A] B
    let _ : Algebra B S := Algebra.TensorProduct.rightAlgebra
    tensorSquare_right_factor_equiv (A := A) (B := B) (N := N)
      ((b₁ ⊗ₜ[A] b₂) ⊗ₜ[B] n) =
        (b₁ • n) ⊗ₜ[A] b₂ := by
  -- Expand the defining composite once; `comm_tmul` and `cancelBaseChange_tmul` then give the
  -- source-faithful normal form.
  simp [tensorSquare_right_factor_equiv]

/-- Helper for Lemma 15.105.2: the right `B`-factor acts on `N ⊗[A] L` through the `L`-slot. -/
noncomputable def tensorSquare_right_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) :
    N ⊗[A] L →ₗ[A] N ⊗[A] L :=
  LinearMap.lTensor N ((Algebra.lsmul A B L b).restrictScalars A)

/-- Helper for Lemma 15.105.2: on pure tensors, the right `B`-factor acts on the `L`-component. -/
@[simp] lemma tensorSquare_right_smul_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) (n : N) (l : L) :
    tensorSquare_right_smul (A := A) (B := B) (N := N) (L := L) b (n ⊗ₜ[A] l) =
      n ⊗ₜ[A] (b • l) := by
  -- This is exactly the `lTensor` pure-tensor formula for the right multiplication map on `L`.
  simp [tensorSquare_right_smul]

/-- Helper for Lemma 15.105.2: the left `B`-action from `N` commutes with the right `B`-action
through `L` on `N ⊗[A] L`. -/
lemma tensorSquare_left_right_smul_comm
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b₁ b₂ : B) (x : N ⊗[A] L) :
    tensorSquare_right_smul (A := A) (B := B) (N := N) (L := L) b₂ (b₁ • x) =
      b₁ • tensorSquare_right_smul (A := A) (B := B) (N := N) (L := L) b₂ x := by
  -- Compare both actions on pure tensors; the two scalar actions commute because `B` is
  -- commutative.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [tensorSquare_right_smul]
  | tmul n l =>
      simp [tensorSquare_right_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

/-- Helper for Lemma 15.105.2: the left `B`-factor acts on `N ⊗[A] L` through the `N`-slot. -/
noncomputable def tensorSquare_left_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) :
    N ⊗[A] L →ₗ[A] N ⊗[A] L :=
  LinearMap.restrictScalars A
    ((Algebra.lsmul A B (N ⊗[A] L)) b)

/-- Helper for Lemma 15.105.2: on pure tensors, the left `B`-factor acts on the `N`-component. -/
@[simp] lemma tensorSquare_left_smul_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) (n : N) (l : L) :
    tensorSquare_left_smul (A := A) (B := B) (N := N) (L := L) b (n ⊗ₜ[A] l) =
      (b • n) ⊗ₜ[A] l := by
  -- This is the standard left scalar action on the first tensor factor.
  rfl

/-- Helper for Lemma 15.105.2: the tensor-square action on `N ⊗[A] L` as an `A`-linear
endomorphism. -/
noncomputable def tensorSquare_tensor_action
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    B ⊗[A] B →ₗ[A] Module.End A (N ⊗[A] L) :=
  -- Build the tensor-square action by bilinearly combining the left action on the `N`-slot and
  -- the right action on the `L`-slot.
  TensorProduct.AlgebraTensorModule.lift <|
    { toFun := fun b₁ =>
        { toFun := fun b₂ =>
            (tensorSquare_right_smul (A := A) (B := B) (N := N) (L := L) b₂).comp
              (tensorSquare_left_smul (A := A) (B := B) (N := N) (L := L) b₁)
          map_add' := by
            intro b₂ c₂
            ext n l
            simp [tensorSquare_right_smul, LinearMap.comp_apply]
          map_smul' := by
            intro a b₂
            ext n l
            simp [tensorSquare_right_smul, LinearMap.comp_apply, TensorProduct.smul_tmul'] }
      map_add' := by
        intro b₁ c₁
        ext b₂ n l
        simp [tensorSquare_left_smul, LinearMap.comp_apply]
      map_smul' := by
        intro a b₁
        ext b₂ n l
        simp [tensorSquare_left_smul, LinearMap.comp_apply, TensorProduct.smul_tmul'] }

/-- Helper for Lemma 15.105.2: on pure tensors, the tensor-square action sends
`(b₁ ⊗ b₂, n ⊗ l)` to `(b₁ • n) ⊗ (b₂ • l)`. -/
@[simp] lemma tensorSquare_tensor_action_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b₁ b₂ : B) (n : N) (l : L) :
    tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L)
        (b₁ ⊗ₜ[A] b₂) (n ⊗ₜ[A] l) =
      (b₁ • n) ⊗ₜ[A] (b₂ • l) := by
  -- Evaluate the lifted bilinear map once and normalize the two component actions.
  simp [tensorSquare_tensor_action, LinearMap.comp_apply]

/-- Helper for Lemma 15.105.2: the tensor-square action defines an actual scalar action. -/
noncomputable instance tensorSquare_tensor_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    SMul (B ⊗[A] B) (N ⊗[A] L) where
  smul s x := tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) s x

/-- Helper for Lemma 15.105.2: on pure tensors, the induced scalar action is the expected
two-sided tensor-square action. -/
@[simp] lemma tensorSquare_tensor_smul_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b₁ b₂ : B) (n : N) (l : L) :
    (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (n ⊗ₜ[A] l : N ⊗[A] L) =
      (b₁ • n) ⊗ₜ[A] (b₂ • l) := by
  -- This is just the pure-tensor formula for `tensorSquare_tensor_action`.
  change
    tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L)
        (b₁ ⊗ₜ[A] b₂) (n ⊗ₜ[A] l) =
      (b₁ • n) ⊗ₜ[A] (b₂ • l)
  exact tensorSquare_tensor_action_tmul (A := A) (B := B) (N := N) (L := L) b₁ b₂ n l

/-- Helper for Lemma 15.105.2: the tensor-square scalar action distributes over addition in the
module variable. -/
lemma tensorSquare_tensor_smul_add
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (s : B ⊗[A] B) (x y : N ⊗[A] L) :
    s • (x + y) = s • x + s • y := by
  -- The action is evaluation of an `A`-linear endomorphism.
  change tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) s (x + y) =
      tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) s x +
        tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) s y
  exact map_add _ _ _

/-- Helper for Lemma 15.105.2: the tensor-square scalar action is additive in the scalar
variable. -/
lemma tensorSquare_tensor_add_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (s t : B ⊗[A] B) (x : N ⊗[A] L) :
    (s + t) • x = s • x + t • x := by
  -- This is the `A`-linearity of the action homomorphism in the scalar variable.
  change tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) (s + t) x =
      tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) s x +
        tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) t x
  simp [tensorSquare_tensor_action]

/-- Helper for Lemma 15.105.2: the tensor-square unit acts trivially on `N ⊗[A] L`. -/
lemma tensorSquare_tensor_one_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (x : N ⊗[A] L) :
    (1 : B ⊗[A] B) • x = x := by
  -- Reduce to pure tensors and use the pure-tensor action formula for `1 ⊗ 1`.
  induction x using TensorProduct.induction_on with
  | zero =>
      change tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) (1 : B ⊗[A] B) 0 = 0
      simp
  | tmul n l =>
      simp [Algebra.TensorProduct.one_def]
  | add x y hx hy =>
      rw [tensorSquare_tensor_smul_add, hx, hy]

/-- Helper for Lemma 15.105.2: multiplication in `B ⊗[A] B` matches iterated tensor-square
action on `N ⊗[A] L`. -/
lemma tensorSquare_tensor_mul_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (s t : B ⊗[A] B) (x : N ⊗[A] L) :
    (s * t) • x = s • (t • x) := by
  -- Reduce successively to pure tensors in all three arguments, where the claim is just
  -- associativity of the two scalar actions.
  have hsmul_zero (u : B ⊗[A] B) : u • (0 : N ⊗[A] L) = 0 := by
    change tensorSquare_tensor_action (A := A) (B := B) (N := N) (L := L) u 0 = 0
    simp
  induction s using TensorProduct.induction_on with
  | zero =>
      have hzero_x : (0 : B ⊗[A] B) • x = 0 := hsmul_zero 0
      have hzero_tx : (0 : B ⊗[A] B) • (t • x) = 0 := hsmul_zero 0
      change ((0 : B ⊗[A] B) * t) • x = (0 : B ⊗[A] B) • (t • x)
      rw [zero_mul, hzero_x, hzero_tx]
  | tmul b₁ b₂ =>
      induction t using TensorProduct.induction_on with
      | zero =>
          have hzero_x : (0 : B ⊗[A] B) • x = 0 := hsmul_zero 0
          have hs_zero : (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (0 : N ⊗[A] L) = 0 :=
            hsmul_zero (b₁ ⊗ₜ[A] b₂)
          change ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (0 : B ⊗[A] B)) • x =
              (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((0 : B ⊗[A] B) • x)
          rw [mul_zero, hzero_x, hs_zero]
      | tmul c₁ c₂ =>
          induction x using TensorProduct.induction_on with
          | zero =>
              calc
                (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) •
                    (0 : N ⊗[A] L)) = 0 := by
                      exact hsmul_zero _
                _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                      ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (0 : N ⊗[A] L)) := by
                        rw [hsmul_zero]
                        symm
                        exact hsmul_zero _
          | tmul n l =>
              -- On pure tensors, both sides normalize to the same iterated scalar action.
              calc
                (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂)) • (n ⊗ₜ[A] l : N ⊗[A] L))
                    = ((b₁ * c₁) • n) ⊗ₜ[A] ((b₂ * c₂) • l) := by
                        simp [Algebra.TensorProduct.tmul_mul_tmul]
                _ = (b₁ • (c₁ • n)) ⊗ₜ[A] (b₂ • (c₂ • l)) := by
                      rw [smul_smul, smul_smul]
                _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                      ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (n ⊗ₜ[A] l : N ⊗[A] L)) := by
                      simp
          | add x y hx hy =>
              calc
                (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂)) • (x + y))
                    = ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂)) • x +
                        ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂)) • y := by
                          rw [tensorSquare_tensor_smul_add]
                _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • x) +
                      (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • y) := by
                        rw [hx, hy]
                _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                      (((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • x) +
                        ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • y)) := by
                        rw [← tensorSquare_tensor_smul_add]
                _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                      ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (x + y)) := by
                        rw [← tensorSquare_tensor_smul_add]
      | add t₁ t₂ ht₁ ht₂ =>
          calc
            ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (t₁ + t₂)) • x
                = (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * t₁) • x) +
                    (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * t₂) • x) := by
                      rw [mul_add, tensorSquare_tensor_add_smul]
            _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (t₁ • x) +
                  (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (t₂ • x) := by
                    rw [ht₁, ht₂]
            _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (t₁ • x + t₂ • x) := by
                  rw [← tensorSquare_tensor_smul_add]
            _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((t₁ + t₂) • x) := by
                  rw [tensorSquare_tensor_add_smul]
  | add s₁ s₂ hs₁ hs₂ =>
      calc
        ((s₁ + s₂) * t) • x = (s₁ * t) • x + (s₂ * t) • x := by
          rw [add_mul, tensorSquare_tensor_add_smul]
        _ = s₁ • (t • x) + s₂ • (t • x) := by
          rw [hs₁, hs₂]
        _ = (s₁ + s₂) • (t • x) := by
          rw [tensorSquare_tensor_add_smul]

/-- Helper for Lemma 15.105.2: the tensor-square action upgrades `N ⊗[A] L` to a module over
`B ⊗[A] B`. -/
noncomputable instance tensorSquare_tensor_module
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    Module (B ⊗[A] B) (N ⊗[A] L) :=
  Module.ofMinimalAxioms
    (tensorSquare_tensor_smul_add (A := A) (B := B) (N := N) (L := L))
    (tensorSquare_tensor_add_smul (A := A) (B := B) (N := N) (L := L))
    (tensorSquare_tensor_mul_smul (A := A) (B := B) (N := N) (L := L))
    (tensorSquare_tensor_one_smul (A := A) (B := B) (N := N) (L := L))

/-- Helper for Lemma 15.105.2: tensoring a `B`-linear map over `A` is linear for the
tensor-square action. -/
noncomputable def tensorSquare_left_tensor_linear
    {L₁ L₂ : Type*}
    [AddCommGroup L₁] [AddCommGroup L₂]
    [Module B L₁] [Module B L₂]
    [Module A L₁] [Module A L₂]
    [IsScalarTower A B L₁] [IsScalarTower A B L₂]
    (f : L₁ →ₗ[B] L₂) :
    N ⊗[A] L₁ →ₗ[B ⊗[A] B] N ⊗[A] L₂ :=
  LinearMap.mk
    (LinearMap.lTensor N (f.restrictScalars A)).toAddMonoidHom
    (by
      intro s x
      -- Compare both sides first on pure tensor-square scalars and pure tensors in the module,
      -- then extend by additivity in each variable.
      induction s using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul b₁ b₂ =>
          induction x using TensorProduct.induction_on with
          | zero =>
              simp
          | tmul n l =>
              simp [tensorSquare_tensor_smul_tmul, map_smul]
          | add x y hx hy =>
              -- Here the scalar is fixed, so both sides reduce by additivity of `lTensor` and of
              -- the tensor-square action in the module variable.
              show
                (LinearMap.lTensor N (f.restrictScalars A))
                    ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (x + y)) =
                  (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                    (LinearMap.lTensor N (f.restrictScalars A) (x + y))
              rw [tensorSquare_tensor_smul_add, LinearMap.map_add, LinearMap.map_add,
                smul_add]
              have hx' :
                  (LinearMap.lTensor N (f.restrictScalars A))
                      ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • x) =
                    (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                      (LinearMap.lTensor N (f.restrictScalars A) x) := by
                simpa [RingHom.id_apply] using hx
              have hy' :
                  (LinearMap.lTensor N (f.restrictScalars A))
                      ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • y) =
                    (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                      (LinearMap.lTensor N (f.restrictScalars A) y) := by
                simpa [RingHom.id_apply] using hy
              rw [hx', hy']
      | add s t hs ht =>
          -- Here the module element is fixed, so both sides reduce by additivity in the scalar
          -- variable.
          show
            (LinearMap.lTensor N (f.restrictScalars A)) ((s + t) • x) =
              (s + t) • (LinearMap.lTensor N (f.restrictScalars A) x)
          rw [tensorSquare_tensor_add_smul, LinearMap.map_add, add_smul]
          have hs' :
              (LinearMap.lTensor N (f.restrictScalars A)) (s • x) =
                s • (LinearMap.lTensor N (f.restrictScalars A) x) := by
            simpa [RingHom.id_apply] using hs
          have ht' :
              (LinearMap.lTensor N (f.restrictScalars A)) (t • x) =
                t • (LinearMap.lTensor N (f.restrictScalars A) x) := by
            simpa [RingHom.id_apply] using ht
          rw [hs', ht'])

/-- Helper for Lemma 15.105.2: on pure tensors, the `S`-linear upgrade of `lTensor` is the
expected right-factor map. -/
@[simp] lemma tensorSquare_left_tensor_linear_tmul
    {L₁ L₂ : Type*}
    [AddCommGroup L₁] [AddCommGroup L₂]
    [Module B L₁] [Module B L₂]
    [Module A L₁] [Module A L₂]
    [IsScalarTower A B L₁] [IsScalarTower A B L₂]
    (f : L₁ →ₗ[B] L₂) (n : N) (l : L₁) :
    tensorSquare_left_tensor_linear (A := A) (B := B) (N := N) f (n ⊗ₜ[A] l) =
      n ⊗ₜ[A] f l := by
  -- The new `S`-linear map has the same underlying `A`-linear `lTensor` formula.
  rfl

/-- Helper for Lemma 15.105.2: the verified owner-level part of the source comparison isolates
the right base-change factor `L ⊗[A] B`. -/
noncomputable def tensorSquare_tensor_to_right_baseChange
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    (B ⊗[A] B) ⊗[B] (N ⊗[B] L) ≃ₗ[B] N ⊗[B] (L ⊗[A] B) :=
  -- Reassociate, cancel the right tensor-square factor, and move the resulting `L ⊗[A] B`
  -- term into the right tensor slot.
  ((TensorProduct.assoc B (B ⊗[A] B) N L).symm.trans
      (TensorProduct.congr
        (tensorSquare_right_factor_equiv (A := A) (B := B) (N := N))
        (LinearEquiv.refl B L))).trans
    ((TensorProduct.comm B (N ⊗[A] B) L).trans
      (TensorProduct.AlgebraTensorModule.leftComm A B L N B))

/-- Helper for Lemma 15.105.2: on pure tensors, the right-base-change comparison sends
`((b₁ ⊗ b₂) ⊗ (n ⊗ l))` to `(b₁ • n) ⊗ (l ⊗ b₂)`. -/
@[simp] lemma tensorSquare_tensor_to_right_baseChange_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b₁ b₂ : B) (n : N) (l : L) :
    tensorSquare_tensor_to_right_baseChange (A := A) (B := B) (N := N) (L := L)
      (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) ⊗ₜ[B] (n ⊗ₜ[B] l)) : (B ⊗[A] B) ⊗[B] (N ⊗[B] L)) =
        (b₁ • n) ⊗ₜ[B] (l ⊗ₜ[A] b₂) := by
  -- Each owner-level comparison has a pure-tensor formula, so the whole composite reduces by
  -- repeated `simp`.
  simp [tensorSquare_tensor_to_right_baseChange, tensorSquare_right_factor_equiv_tmul,
    TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.leftComm_tmul]

/-- Helper for Lemma 15.105.2: the inverse right-base-change comparison sends
`n ⊗ (l ⊗ b)` back to `((1 ⊗ b) ⊗ (n ⊗ l))`. -/
@[simp] lemma tensorSquare_tensor_to_right_baseChange_symm_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (n : N) (l : L) (b : B) :
    (tensorSquare_tensor_to_right_baseChange (A := A) (B := B) (N := N) (L := L)).symm
      (n ⊗ₜ[B] (l ⊗ₜ[A] b)) =
        (((1 : B) ⊗ₜ[A] b : B ⊗[A] B) ⊗ₜ[B] (n ⊗ₜ[B] l)) := by
  -- Apply the verified forward pure-tensor formula and cancel the surrounding equivalence.
  apply (tensorSquare_tensor_to_right_baseChange (A := A) (B := B) (N := N) (L := L)).injective
  simp [tensorSquare_tensor_to_right_baseChange_tmul]

/-- Helper for Lemma 15.105.2: the canonical source inclusion `1 ⊗ -` becomes the expected
right-base-change tensor with unit final factor under the owner-level comparison. -/
@[simp] lemma tensorSquare_tensor_to_right_baseChange_right_baseChange_map_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (n : N) (l : L) :
    tensorSquare_tensor_to_right_baseChange (A := A) (B := B) (N := N) (L := L)
      (tensorSquare_right_baseChange_map (A := A) (B := B) (N := N) (L := L)
        (n ⊗ₜ[B] l)) =
      n ⊗ₜ[B] (l ⊗ₜ[A] (1 : B)) := by
  -- Expand the canonical inclusion once and then use the pure-tensor formula for the comparison.
  simpa [tensorSquare_right_baseChange_map, Algebra.TensorProduct.one_def] using
    (tensorSquare_tensor_to_right_baseChange_tmul (A := A) (B := B) (N := N) (L := L)
      (1 : B) (1 : B) n l)

/-- Helper for Lemma 15.105.2: the inverse right-factor cancellation sends `n ⊗ b` back to the
source normal form `((1 ⊗ b) ⊗ n)`. -/
@[simp] lemma tensorSquare_right_factor_equiv_symm_tmul
    (n : N) (b : B) :
    let S := B ⊗[A] B
    let _ : Algebra B S := Algebra.TensorProduct.rightAlgebra
    (tensorSquare_right_factor_equiv (A := A) (B := B) (N := N)).symm (n ⊗ₜ[A] b) =
      (((1 : B) ⊗ₜ[A] b : B ⊗[A] B) ⊗ₜ[B] n) := by
  -- Apply the forward pure-tensor formula and cancel the surrounding equivalence.
  apply (tensorSquare_right_factor_equiv (A := A) (B := B) (N := N)).injective
  simp [tensorSquare_right_factor_equiv_tmul]

/-- Helper for Lemma 15.105.2: on `L ⊗[A] B`, the missing right tensor-square factor acts by
right multiplication on the `B`-slot. -/
noncomputable def tensorSquare_right_baseChange_right_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) :
    L ⊗[A] B →ₗ[B] L ⊗[A] B := by
  -- Route correction: the inferable `B`-action on `L ⊗[A] B` comes from the `L`-slot, but the
  -- source proof needs the extra tensor-square owner that multiplies on the right `B`-slot.
  -- Build the underlying `A`-linear operator by `lTensor`, then verify separately that it also
  -- commutes with the ambient `B`-action through the `L`-slot.
  let f : L ⊗[A] B →ₗ[A] L ⊗[A] B :=
    LinearMap.lTensor L (LinearMap.restrictScalars A ((Algebra.lsmul A B B) b))
  refine
    { toFun := f
      map_add' := f.map_add
      map_smul' := ?_ }
  intro c x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [f]
  | tmul l d =>
      simp [f, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

/-- Helper for Lemma 15.105.2: on pure tensors, the right-slot operator on `L ⊗[A] B` multiplies
the final `B`-factor. -/
@[simp] lemma tensorSquare_right_baseChange_right_smul_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b d : B) (l : L) :
    tensorSquare_right_baseChange_right_smul (A := A) (B := B) (L := L) b (l ⊗ₜ[A] d) =
      l ⊗ₜ[A] (b * d) := by
  -- The operator was defined by `lTensor` on the right factor, so the pure-tensor formula is
  -- immediate.
  simp [tensorSquare_right_baseChange_right_smul]

/-- Helper for Lemma 15.105.2: tensoring the right-slot operator with `N` gives the corresponding
right-factor action on `N ⊗[B] (L ⊗[A] B)`. -/
noncomputable def tensorSquare_right_baseChange_tensor_right_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) :
    N ⊗[B] (L ⊗[A] B) →ₗ[B] N ⊗[B] (L ⊗[A] B) :=
  -- Once the inner operator is genuinely `B`-linear, the outer tensor product can use the
  -- standard `lTensor` owner unchanged.
  LinearMap.lTensor N (tensorSquare_right_baseChange_right_smul (A := A) (B := B) (L := L) b)

/-- Helper for Lemma 15.105.2: on pure tensors, the lifted right-slot operator multiplies the
final `B`-factor inside `N ⊗[B] (L ⊗[A] B)`. -/
@[simp] lemma tensorSquare_right_baseChange_tensor_right_smul_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b d : B) (n : N) (l : L) :
    tensorSquare_right_baseChange_tensor_right_smul (A := A) (B := B) (N := N) (L := L) b
      (n ⊗ₜ[B] (l ⊗ₜ[A] d)) =
        n ⊗ₜ[B] (l ⊗ₜ[A] (b * d)) := by
  -- The outer tensor step preserves the pure-tensor formula coming from the inner right-slot
  -- operator.
  simp [tensorSquare_right_baseChange_tensor_right_smul,
    tensorSquare_right_baseChange_right_smul_tmul]

/-- Helper for Lemma 15.105.2: on the right-base-change tensor product, the left tensor-square
factor acts through the `N`-slot. -/
noncomputable def tensorSquare_right_baseChange_left_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) :
    N ⊗[B] (L ⊗[A] B) →ₗ[B] N ⊗[B] (L ⊗[A] B) :=
  (Algebra.lsmul A B N b).rTensor (L ⊗[A] B)

/-- Helper for Lemma 15.105.2: on pure tensors, the left `B`-factor acts on the `N`-component
inside `N ⊗[B] (L ⊗[A] B)`. -/
@[simp] lemma tensorSquare_right_baseChange_left_smul_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b : B) (n : N) (l : L) (d : B) :
    tensorSquare_right_baseChange_left_smul (A := A) (B := B) (N := N) (L := L) b
      (n ⊗ₜ[B] (l ⊗ₜ[A] d)) =
        (b • n) ⊗ₜ[B] (l ⊗ₜ[A] d) := by
  -- This is the standard `rTensor` pure-tensor formula for left multiplication on `N`.
  simp [tensorSquare_right_baseChange_left_smul]

/-- Helper for Lemma 15.105.2: the tensor-square action on the right-base-change form as a
`B`-linear endomorphism. -/
-- Route correction: Lean does not expose the source-side transported `S`-module structure in a
-- directly usable form, so we record the same source-faithful action formula explicitly at the
-- owner level before packaging the later `S`-linear equivalence.
noncomputable def tensorSquare_right_baseChange_tensor_action
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    B ⊗[A] B →ₗ[A] Module.End B (N ⊗[B] (L ⊗[A] B)) :=
  TensorProduct.AlgebraTensorModule.lift <|
    { toFun := fun b₁ =>
        { toFun := fun b₂ =>
            (tensorSquare_right_baseChange_tensor_right_smul (A := A) (B := B) (N := N)
              (L := L) b₂).comp
              (tensorSquare_right_baseChange_left_smul (A := A) (B := B) (N := N) (L := L) b₁)
          map_add' := by
            intro b₂ c₂
            ext n l d
            simp [LinearMap.comp_apply, add_mul, TensorProduct.tmul_add]
          map_smul' := by
            intro a b₂
            ext n l d
            simp [LinearMap.comp_apply, TensorProduct.tmul_smul] }
      map_add' := by
        intro b₁ c₁
        ext b₂ n l d
        simp [LinearMap.comp_apply, add_smul, TensorProduct.add_tmul]
      map_smul' := by
        intro a b₁
        ext b₂ n l d
        simp [LinearMap.comp_apply, smul_assoc, TensorProduct.smul_tmul'] }

/-- Helper for Lemma 15.105.2: on pure tensors, the explicit right-base-change tensor-square
action matches the source-proof formula `((b₁ ⊗ b₂), n ⊗ (l ⊗ d)) ↦ (b₁ • n) ⊗ (l ⊗ b₂ d)`. -/
@[simp] lemma tensorSquare_right_baseChange_tensor_action_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b₁ b₂ d : B) (n : N) (l : L) :
    tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L)
        (b₁ ⊗ₜ[A] b₂) (n ⊗ₜ[B] (l ⊗ₜ[A] d)) =
      (b₁ • n) ⊗ₜ[B] (l ⊗ₜ[A] (b₂ * d)) := by
  -- Evaluate the lifted bilinear map once and normalize the two component actions.
  simp [tensorSquare_right_baseChange_tensor_action, LinearMap.comp_apply]

/-- Helper for Lemma 15.105.2: the explicit right-base-change action induces the corresponding
scalar action of `B ⊗[A] B` on `N ⊗[B] (L ⊗[A] B)`. -/
noncomputable instance tensorSquare_right_baseChange_tensor_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    SMul (B ⊗[A] B) (N ⊗[B] (L ⊗[A] B)) where
  smul s x := tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) s x

/-- Helper for Lemma 15.105.2: on pure tensors, the induced scalar action is the expected
source-faithful tensor-square action on the mixed-base object. -/
@[simp] lemma tensorSquare_right_baseChange_tensor_smul_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (b₁ b₂ d : B) (n : N) (l : L) :
    (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (n ⊗ₜ[B] (l ⊗ₜ[A] d) : N ⊗[B] (L ⊗[A] B)) =
      (b₁ • n) ⊗ₜ[B] (l ⊗ₜ[A] (b₂ * d)) := by
  -- This is just the pure-tensor formula for `tensorSquare_right_baseChange_tensor_action`.
  change
    tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L)
        (b₁ ⊗ₜ[A] b₂) (n ⊗ₜ[B] (l ⊗ₜ[A] d)) =
      (b₁ • n) ⊗ₜ[B] (l ⊗ₜ[A] (b₂ * d))
  exact tensorSquare_right_baseChange_tensor_action_tmul
    (A := A) (B := B) (N := N) (L := L) b₁ b₂ d n l

/-- Helper for Lemma 15.105.2: the explicit tensor-square scalar action distributes over
addition in the mixed-base tensor variable. -/
lemma tensorSquare_right_baseChange_tensor_smul_add
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (s : B ⊗[A] B) (x y : N ⊗[B] (L ⊗[A] B)) :
    s • (x + y) = s • x + s • y := by
  -- The action is evaluation of a `B`-linear endomorphism.
  change
    tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) s (x + y) =
      tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) s x +
        tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) s y
  exact map_add _ _ _

/-- Helper for Lemma 15.105.2: the explicit tensor-square scalar action is additive in the
tensor-square variable. -/
lemma tensorSquare_right_baseChange_tensor_add_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (s t : B ⊗[A] B) (x : N ⊗[B] (L ⊗[A] B)) :
    (s + t) • x = s • x + t • x := by
  -- This is the `A`-linearity of the action homomorphism in the tensor-square variable.
  change
    tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) (s + t) x =
      tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) s x +
        tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) t x
  simp [tensorSquare_right_baseChange_tensor_action]

/-- Helper for Lemma 15.105.2: the tensor-square unit acts trivially on the mixed-base object
`N ⊗[B] (L ⊗[A] B)`. -/
lemma tensorSquare_right_baseChange_tensor_one_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (x : N ⊗[B] (L ⊗[A] B)) :
    (1 : B ⊗[A] B) • x = x := by
  -- Reduce first to pure outer tensors and then to pure inner tensors, where `1 ⊗ 1` acts
  -- by the obvious identity formula.
  induction x using TensorProduct.induction_on with
  | zero =>
      change
        tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L)
          (1 : B ⊗[A] B) 0 = 0
      simp
  | tmul n y =>
      induction y using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero]
          change
            tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L)
              (1 : B ⊗[A] B) 0 = 0
          simp
      | tmul l d =>
          simp [Algebra.TensorProduct.one_def]
      | add y z hy hz =>
          rw [TensorProduct.tmul_add, tensorSquare_right_baseChange_tensor_smul_add, hy, hz]
  | add x y hx hy =>
      rw [tensorSquare_right_baseChange_tensor_smul_add, hx, hy]

/-- Helper for Lemma 15.105.2: multiplication in `B ⊗[A] B` matches iterated explicit
tensor-square action on the mixed-base object. -/
lemma tensorSquare_right_baseChange_tensor_mul_smul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (s t : B ⊗[A] B) (x : N ⊗[B] (L ⊗[A] B)) :
    (s * t) • x = s • (t • x) := by
  -- As for the base tensor-square action, reduce successively to pure tensors in the scalar and
  -- mixed-base variables.
  have hsmul_zero (u : B ⊗[A] B) : u • (0 : N ⊗[B] (L ⊗[A] B)) = 0 := by
    change
      tensorSquare_right_baseChange_tensor_action (A := A) (B := B) (N := N) (L := L) u 0 = 0
    simp
  induction s using TensorProduct.induction_on with
  | zero =>
      have hzero_x : (0 : B ⊗[A] B) • x = 0 := hsmul_zero 0
      have hzero_tx : (0 : B ⊗[A] B) • (t • x) = 0 := hsmul_zero 0
      change ((0 : B ⊗[A] B) * t) • x = (0 : B ⊗[A] B) • (t • x)
      rw [zero_mul, hzero_x, hzero_tx]
  | tmul b₁ b₂ =>
      induction t using TensorProduct.induction_on with
      | zero =>
          have hzero_x : (0 : B ⊗[A] B) • x = 0 := hsmul_zero 0
          have hs_zero : (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (0 : N ⊗[B] (L ⊗[A] B)) = 0 :=
            hsmul_zero (b₁ ⊗ₜ[A] b₂)
          change
            ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (0 : B ⊗[A] B)) • x =
              (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((0 : B ⊗[A] B) • x)
          rw [mul_zero, hzero_x, hs_zero]
      | tmul c₁ c₂ =>
          induction x using TensorProduct.induction_on with
          | zero =>
              calc
                (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) •
                    (0 : N ⊗[B] (L ⊗[A] B))) = 0 := by
                      exact hsmul_zero _
                _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                      ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (0 : N ⊗[B] (L ⊗[A] B))) := by
                        rw [hsmul_zero]
                        symm
                        exact hsmul_zero _
          | tmul n y =>
              induction y using TensorProduct.induction_on with
              | zero =>
                  simp [hsmul_zero]
              | tmul l d =>
                  calc
                    (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) •
                        (n ⊗ₜ[B] (l ⊗ₜ[A] d) : N ⊗[B] (L ⊗[A] B)))
                        = ((b₁ * c₁) • n) ⊗ₜ[B] (l ⊗ₜ[A] ((b₂ * c₂) * d)) := by
                            simp [Algebra.TensorProduct.tmul_mul_tmul]
                    _ = (b₁ • (c₁ • n)) ⊗ₜ[B] (l ⊗ₜ[A] (b₂ * (c₂ * d))) := by
                          rw [smul_smul, mul_assoc]
                    _ = (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                          ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) •
                            (n ⊗ₜ[B] (l ⊗ₜ[A] d) : N ⊗[B] (L ⊗[A] B))) := by
                          simp
              | add y z hy hz =>
                  calc
                    (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) •
                        (n ⊗ₜ[B] (y + z)))
                        =
                          ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) •
                              (n ⊗ₜ[B] y) +
                            ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) •
                              (n ⊗ₜ[B] z) := by
                          rw [TensorProduct.tmul_add,
                            tensorSquare_right_baseChange_tensor_smul_add]
                    _ =
                          (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                              ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (n ⊗ₜ[B] y)) +
                            (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                              ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (n ⊗ₜ[B] z)) := by
                          rw [hy, hz]
                    _ =
                          (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                            (((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (n ⊗ₜ[B] y)) +
                              ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (n ⊗ₜ[B] z))) := by
                          rw [← tensorSquare_right_baseChange_tensor_smul_add]
                    _ =
                          (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                            ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (n ⊗ₜ[B] (y + z))) := by
                          rw [← tensorSquare_right_baseChange_tensor_smul_add,
                            TensorProduct.tmul_add]
          | add x y hx hy =>
              calc
                (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) • (x + y))
                    =
                      (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) • x) +
                        (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (c₁ ⊗ₜ[A] c₂ : B ⊗[A] B)) • y) := by
                      rw [tensorSquare_right_baseChange_tensor_smul_add]
                _ =
                      (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • x) +
                        (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • y) := by
                      rw [hx, hy]
                _ =
                      (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                        (((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • x) +
                          ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • y)) := by
                      rw [← tensorSquare_right_baseChange_tensor_smul_add]
                _ =
                      (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) •
                        ((c₁ ⊗ₜ[A] c₂ : B ⊗[A] B) • (x + y)) := by
                      rw [← tensorSquare_right_baseChange_tensor_smul_add]
      | add t₁ t₂ ht₁ ht₂ =>
          calc
            ((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * (t₁ + t₂)) • x
                =
                  (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * t₁) • x) +
                    (((b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) * t₂) • x) := by
                      rw [mul_add, tensorSquare_right_baseChange_tensor_add_smul]
            _ =
                  (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (t₁ • x) +
                    (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (t₂ • x) := by
                      rw [ht₁, ht₂]
            _ =
                  (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • (t₁ • x + t₂ • x) := by
                      rw [← tensorSquare_right_baseChange_tensor_smul_add]
            _ =
                  (b₁ ⊗ₜ[A] b₂ : B ⊗[A] B) • ((t₁ + t₂) • x) := by
                      rw [tensorSquare_right_baseChange_tensor_add_smul]
  | add s₁ s₂ hs₁ hs₂ =>
      calc
        ((s₁ + s₂) * t) • x = (s₁ * t) • x + (s₂ * t) • x := by
          rw [add_mul, tensorSquare_right_baseChange_tensor_add_smul]
        _ = s₁ • (t • x) + s₂ • (t • x) := by
          rw [hs₁, hs₂]
        _ = (s₁ + s₂) • (t • x) := by
          rw [tensorSquare_right_baseChange_tensor_add_smul]

/-- Helper for Lemma 15.105.2: the explicit tensor-square action upgrades the mixed-base object
to a module over `B ⊗[A] B`. -/
noncomputable instance tensorSquare_right_baseChange_tensor_module
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    Module (B ⊗[A] B) (N ⊗[B] (L ⊗[A] B)) :=
  Module.ofMinimalAxioms
    (tensorSquare_right_baseChange_tensor_smul_add (A := A) (B := B) (N := N) (L := L))
    (tensorSquare_right_baseChange_tensor_add_smul (A := A) (B := B) (N := N) (L := L))
    (tensorSquare_right_baseChange_tensor_mul_smul (A := A) (B := B) (N := N) (L := L))
    (tensorSquare_right_baseChange_tensor_one_smul (A := A) (B := B) (N := N) (L := L))

/-- Helper for Lemma 15.105.2: canceling the right base-change factor identifies
`N ⊗[B] (B ⊗[A] L)` with `N ⊗[A] L`. -/
noncomputable def tensorSquare_baseChange_cancel_right
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    N ⊗[B] (B ⊗[A] L) ≃ₗ[B] N ⊗[A] L :=
  -- This is exactly the owner-level `cancelBaseChange` equivalence.
  TensorProduct.AlgebraTensorModule.cancelBaseChange A B B N L

/-- Helper for Lemma 15.105.2: on pure tensors, canceling the right base-change factor sends
`n ⊗ (b ⊗ l)` to the left-factor normal form `(b • n) ⊗ l`. -/
@[simp] lemma tensorSquare_baseChange_cancel_right_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (n : N) (l : L) (b : B) :
    tensorSquare_baseChange_cancel_right (A := A) (B := B) (N := N) (L := L)
      (n ⊗ₜ[B] ((b : B) ⊗ₜ[A] l)) =
        (b • n) ⊗ₜ[A] l := by
  -- This is the owner computation rule for `cancelBaseChange`.
  simp [tensorSquare_baseChange_cancel_right]

/-- Helper for Lemma 15.105.2: rewriting through `tensorSquare_baseChange_cancel_right` produces
the source-faithful left-factor normal form on pure tensors. -/
@[simp] lemma tensorSquare_baseChange_cancel_right_tmul_left
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (n : N) (l : L) (b : B) :
    tensorSquare_baseChange_cancel_right (A := A) (B := B) (N := N) (L := L)
      (n ⊗ₜ[B] ((b : B) ⊗ₜ[A] l)) =
        (b • n) ⊗ₜ[A] l := by
  -- This is just the pure-tensor formula above, restated for the normal form used later.
  simpa using tensorSquare_baseChange_cancel_right_tmul
    (A := A) (B := B) (N := N) (L := L) n l b

/-- Helper for Lemma 15.105.2: the inverse base-change cancellation sends `n ⊗ l` to the
source normal form `n ⊗ (1 ⊗ l)`. -/
@[simp] lemma tensorSquare_baseChange_cancel_right_symm_tmul
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (n : N) (l : L) :
    (tensorSquare_baseChange_cancel_right (A := A) (B := B) (N := N) (L := L)).symm
      (n ⊗ₜ[A] l) =
        n ⊗ₜ[B] (((1 : B) ⊗ₜ[A] l) : B ⊗[A] L) := by
  -- Apply the forward computation rule and cancel the surrounding equivalence.
  apply (tensorSquare_baseChange_cancel_right (A := A) (B := B) (N := N) (L := L)).injective
  simp [tensorSquare_baseChange_cancel_right_tmul_left]

/-- Helper for Lemma 15.105.2: after distinguishing the left and right `B`-algebra structures on
`B ⊗[A] B`, the pushout cancellation theorem identifies `B ⊗[A] B ⊗[B] N` with the ordinary base
change `B ⊗[A] N`. -/
noncomputable def tensorSquare_baseChange_comm_equiv :
    (B ⊗[A] B) ⊗[B] N ≃ₗ[B] B ⊗[A] N :=
  -- TODO: instantiate `Algebra.IsPushout.cancelBaseChange A B B (B ⊗[A] B) N` with explicit
  -- left- and right-owner `B`-algebra structures on the tensor square; the remaining blocker is
  -- that Lean currently conflates those two branch instances when both source rings are literally
  -- the same type `B`.
  sorry

/-- Helper for Lemma 15.105.2: the tensor-square model `B ⊗[A] B ⊗[B] N` is the `B`-flat base
change model used in the final proof. -/
noncomputable abbrev tensorSquare_baseChange_comm_linear :
    (B ⊗[A] B) ⊗[B] N ≃ₗ[B] B ⊗[A] N :=
  tensorSquare_baseChange_comm_equiv (A := A) (B := B) (N := N)

/-- Helper for Lemma 15.105.2: the verified owner-level right-base-change comparison, recorded as
the currently available linear package before the later tensor-square upgrade. -/
noncomputable def tensorSquare_tensor_to_right_baseChange_linear
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    (B ⊗[A] B) ⊗[B] (N ⊗[B] L) ≃ₗ[B] N ⊗[B] (L ⊗[A] B) := by
  -- Route correction: keep the stable owner-level `B`-linear comparison explicit until the final
  -- tensor-square-linear packaging is available.
  exact tensorSquare_tensor_to_right_baseChange (A := A) (B := B) (N := N) (L := L)

/-- Helper for Lemma 15.105.2: the owner-level comparison sends zero to zero. -/
@[simp] lemma tensorSquare_tensor_to_right_baseChange_zero
    {L : Type*} [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L] :
    tensorSquare_tensor_to_right_baseChange (A := A) (B := B) (N := N) (L := L)
      (0 : (B ⊗[A] B) ⊗[B] (N ⊗[B] L)) =
        0 := by
  -- This is the zero-preservation of the underlying linear equivalence.
  simp [tensorSquare_tensor_to_right_baseChange]

local notation "TSq" => B ⊗[A] B

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Lemma 15.105.2: use tensor-square multiplication as the `TSq`-algebra structure
on `B`. -/
local instance tensorSquare_left_tensor_collapse_algebra : Algebra TSq B :=
  (lmul' A).toRingHom.toAlgebra

/-- Helper for Lemma 15.105.2: the left tensor inclusion `B → TSq` and multiplication
`TSq → B` form the scalar tower used by the mixed-base collapse owner. -/
lemma tensorSquare_left_tensor_collapse_isScalarTower : IsScalarTower B TSq B := by
  -- Route correction: the collapse owner uses the default left `B`-action on `TSq`, so the tower
  -- to package here is `B --(b ↦ b ⊗ 1)--> TSq --(multiply)--> B`.
  let leftAlg : Algebra B TSq := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra B TSq := leftAlg
  refine IsScalarTower.of_algebraMap_eq (R := B) (S := TSq) (A := B) fun b ↦ ?_
  -- After expanding the two algebra maps, the claim is the pure-tensor computation
  -- `(b ⊗ 1) ↦ b * 1 = b`.
  simp [leftAlg, RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.lmul'_apply_tmul]

/-- Helper for Lemma 15.105.2: install the scalar-tower bridge needed by the mixed-base
collapse owner. -/
local instance tensorSquare_left_tensor_collapse_isScalarTower_inst : IsScalarTower B TSq B :=
  tensorSquare_left_tensor_collapse_isScalarTower (A := A) (B := B)

/-- Helper for Lemma 15.105.2: under the right tensor inclusion, `algebraMap B TSq`
sends `b` to `1 ⊗ b`. -/
@[simp] lemma tensorSquare_rightAlgebra_algebraMap_tmul (b : B) :
    (show TSq from algebraMap B TSq b) = ((1 : B) ⊗ₜ[A] b : TSq) :=
  rfl

/-- Helper for Lemma 15.105.2: under the left tensor inclusion, `algebraMap B TSq`
sends `b` to `b ⊗ 1`. -/
@[simp] lemma tensorSquare_leftAlgebra_algebraMap_tmul (b : B) :
    let leftAlg : Algebra B TSq := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra B TSq := leftAlg
    (show TSq from algebraMap B TSq b) = (b ⊗ₜ[A] (1 : B) : TSq) := by
  intro leftAlg
  rfl

/-- Helper for Lemma 15.105.2: the left tensor inclusion `B → TSq` multiplies the first tensor
factor on pure tensors. -/
@[simp] lemma tensorSquare_leftAlgebra_smul_tmul (b b₁ b₂ : B) :
    b • (b₁ ⊗ₜ[A] b₂ : TSq) = ((b * b₁) ⊗ₜ[A] b₂ : TSq) :=
  rfl

/-- Helper for Lemma 15.105.2: after forcing the right `B`-algebra structure on `TSq`, scalar
multiplication acts on the second tensor factor of a pure tensor. -/
@[simp] lemma tensorSquare_right_owner_smul_tmul
    (b b₁ b₂ : B) :
    let rightAlg : Algebra B TSq := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra B TSq := rightAlg
    let _ : SMul B TSq := rightAlg.toSMul
    let _ : Module B TSq := rightAlg.toModule
    b • ((b₁ ⊗ₜ[A] b₂ : TSq)) = (b₁ ⊗ₜ[A] (b * b₂) : TSq) := by
  intro rightAlg
  dsimp
  -- Under the right tensor inclusion, scalar multiplication is multiplication by `1 ⊗ b`.
  rw [Algebra.smul_def]
  have h_right :
      (show TSq from algebraMap B TSq b) = ((1 : B) ⊗ₜ[A] b : TSq) := by
    rfl
  simp [h_right, Algebra.TensorProduct.tmul_mul_tmul]

/-- Helper for Lemma 15.105.2: after forcing the right `B`-algebra structure on `TSq`, that
right scalar action commutes with multiplication in `TSq`. -/
lemma tensorSquare_right_owner_smul_mul
    (b : B) (x y : TSq) :
    let rightAlg : Algebra B TSq := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra B TSq := rightAlg
    let _ : SMul B TSq := rightAlg.toSMul
    let _ : Module B TSq := rightAlg.toModule
    b • (x * y) = x * (b • y) := by
  intro rightAlg
  dsimp
  -- Compare both sides on pure tensors, where the right owner action is explicit.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x₁ x₂ =>
      induction y using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul y₁ y₂ =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          rw [tensorSquare_right_owner_smul_tmul]
          rw [tensorSquare_right_owner_smul_tmul]
          simp [Algebra.TensorProduct.tmul_mul_tmul, mul_left_comm]
      | add y₁ y₂ hy₁ hy₂ =>
          simp [mul_add]
  | add x₁ x₂ hx₁ hx₂ =>
      simp [add_mul]

/-- Helper for Lemma 15.105.2: left multiplication by an element of `B` commutes with
multiplication in the tensor-square ring. -/
lemma tensorSquare_left_owner_smul_mul
    (b : B) (x y : TSq) :
    b • (x * y) = x * (b • y) := by
  -- Compare both sides on pure tensors, where the left owner action is explicit.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x₁ x₂ =>
      induction y using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul y₁ y₂ =>
          simp [tensorSquare_leftAlgebra_smul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            mul_left_comm]
      | add y₁ y₂ hy₁ hy₂ =>
          simpa [mul_add, smul_add] using congrArg₂ HAdd.hAdd hy₁ hy₂
  | add x₁ x₂ hx₁ hx₂ =>
      simpa [add_mul, smul_add] using congrArg₂ HAdd.hAdd hx₁ hx₂

/-- Helper for Lemma 15.105.2: in the left-owner configuration used by the mixed-base collapse,
scalar multiplication by `b` can be moved across tensor-square multiplication. -/
lemma tensorSquare_left_tensor_collapse_left_owner_mul
    (b : B) (x y : TSq) :
    b • (x * y) = x * (b • y) := by
  -- This is exactly the verified left-owner multiplication identity, recorded under the later
  -- collapse notation so the remaining blocker is only the notation-level `SMulCommClass` rewrite.
  exact tensorSquare_left_owner_smul_mul (A := A) (B := B) b x y

/-- Helper for Lemma 15.105.2: the default left `B`-action and tensor-square multiplication
commute on `TSq`, providing the `SMulCommClass` needed by `TensorProduct.leftModule`. -/
local instance tensorSquare_left_tensor_collapse_smulCommClass : SMulCommClass B TSq TSq :=
  -- Under the right tensor inclusion `B → TSq`, scalar multiplication is multiplication by
  -- `1 ⊗ b`, so the commutation axiom is just associativity and commutativity in the tensor
  -- product ring.
  { smul_comm := fun b x y ↦ by
      -- TODO: rewrite this `SMulCommClass` goal to the multiplication form
      -- `b • (x * y) = x * (b • y)` and close it with
      -- `tensorSquare_left_tensor_collapse_left_owner_mul`.
      sorry }

/-- Helper for Lemma 15.105.2: the multiplication algebra `B ⊗[A] B → B` sends a pure tensor to
the product of its two entries. -/
@[simp] lemma tensorSquare_left_tensor_collapse_algebra_tmul (b₁ b₂ : B) :
    (show B from algebraMap TSq B (b₁ ⊗ₜ[A] b₂ : TSq)) = b₁ * b₂ := by
  -- This is the defining computation rule of the tensor-square multiplication map `lmul' A`.
  simp [tensorSquare_left_tensor_collapse_algebra, RingHom.algebraMap_toAlgebra,
    Algebra.TensorProduct.lmul'_apply_tmul]

/-- Helper for Lemma 15.105.2: the remaining mixed-base left tensor collapses by first canceling
the intermediate base change and then applying the left tensor unit. -/
noncomputable local instance tensorSquare_left_tensor_collapse_innerModule
    {M : Type*} [AddCommGroup M] [Module B M] :
    Module TSq (TSq ⊗[B] M) :=
  -- The collapse uses the standard left-factor tensor action on `TSq ⊗[B] M`.
  TensorProduct.leftModule

/-- Helper for Lemma 15.105.2: the remaining mixed-base left tensor collapses by first canceling
the intermediate base change and then applying the left tensor unit. -/
noncomputable def tensorSquare_left_tensor_collapse_linear
    {M : Type*} [AddCommGroup M] [Module B M] :
    B ⊗[TSq] (TSq ⊗[B] M) ≃ₗ[B] M :=
  -- TODO: after solving the owner package for `TensorProduct.leftModule`, this is the canonical
  -- composite `(TensorProduct.AlgebraTensorModule.cancelBaseChange B TSq B B M).trans
  -- (TensorProduct.lid B M)`.
  sorry

/-- Helper for Lemma 15.105.2: on pure tensors, the mixed-base collapse sends
`b ⊗ ((b₁ ⊗ b₂) ⊗ m)` to `(b * b₁ * b₂) • m`. -/
@[simp] lemma tensorSquare_left_tensor_collapse_tmul
    {M : Type*} [AddCommGroup M] [Module B M]
    (b b₁ b₂ : B) (m : M) :
    tensorSquare_left_tensor_collapse_linear (M := M)
      (b ⊗ₜ[TSq] (((b₁ ⊗ₜ[A] b₂ : TSq) ⊗ₜ[B] m))) =
        (b * b₁ * b₂) • m := by
  -- Expand the canonical collapse once: `cancelBaseChange_tmul` multiplies inside `TSq`, and
  -- `lid_tmul` then removes the final left tensor unit.
  -- TODO: once `tensorSquare_left_tensor_collapse_linear` is the canonical
  -- `cancelBaseChange.trans lid` composite, this is a one-line `simp` proof.
  sorry

-- Proof sketch: tensoring a short exact sequence of `B`-modules with `N` over `A` is exact
-- because `N` is `A`-flat. Reinterpret this as extension of scalars from `B` to `B ⊗[A] B`,
-- and then descend exactness back along the flat multiplication map
-- `B ⊗[A] B → B`, so tensoring over `B` with `N` is exact.
/-- Lemma 15.105.2: if the multiplication map `B ⊗[A] B → B` is flat and `N` is flat as an
`A`-module, then `N` is flat as a `B`-module. -/
@[stacks 092C]
theorem flat_of_flat_base_and_flat_tensorSquareMultiplication
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat)
    (hflatN : Module.Flat A N) :
    Module.Flat B N := by
  -- TODO: follow the textbook flatness chain once the two comparison equivalences above are
  -- owner-stable: base-change `N` to `B ⊗[A] N`, transport to `TSq ⊗[B] N`, compose flatness
  -- along `TSq → B`, base-change once more, and collapse the final mixed-base tensor back to `N`.
  sorry

/-- Bridge/view: over a weakly étale map `A → B`, every `A`-flat `B`-module is `B`-flat. -/
theorem Module.Flat.of_isWeaklyEtale [Algebra.IsWeaklyEtale A B]
    (hflatN : Module.Flat A N) :
    Module.Flat B N :=
  flat_of_flat_base_and_flat_tensorSquareMultiplication
    ‹Algebra.IsWeaklyEtale A B›.flat_tensorSquareMultiplication hflatN

end
