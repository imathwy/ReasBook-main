import Mathlib
import stacks_project.Chap10.Definition_10_133_1
import stacks_project.Chap10.Lemma_10_133_9
import stacks_project.Chap10.Lemma_10_150_7
import stacks_project.Chap10.Remark_10_133_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

/- Domain triage:
* primary domain: principal parts and differential operators under extension of scalars along a
  formally étale algebra map;
* sampled owner API:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `TensorProduct.AlgebraTensorModule.mk`,
  `principal_parts_linear_map_equiv_differential_operators`;
* best owner abstraction: the canonical scalar-extension map is already owned upstream by
  `TensorProduct.AlgebraTensorModule.mk`, while the principal-parts owner remains
  `principal_parts_module` together with the source-facing base-change map
  `principalPartsBaseChangeMap`;
* primitive data: the canonical extension-of-scalars map `M → S' ⊗[S] M` and the induced map on
  principal parts;
* derived API: bijectivity of the principal-parts comparison for formally étale maps and the
  resulting unique extension of differential operators.

Source/core/bridge triage:
* `source-facing`: the two clauses of Lemma `10.150.8`;
* `core/canonical`: `principal_parts_module`, `LinearMap.IsDifferentialOperatorOfOrder`, and the
  scalar-extension owner `TensorProduct.AlgebraTensorModule.mk`;
* `bridge/view`: the lifted comparison map
  `((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S')`. -/

section

variable {R S S' M N X : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Route correction: the unique-extension clause can already be carried out once the canonical
principal-parts comparison is known to be bijective, so this file first proves the representation
helpers and then finishes clause `(2)` by transport across that comparison. The remaining blocker
for clause `(1)` is the quotient-model conjugation promised in the source proof. -/

open scoped PrincipalParts

section HelperLemmas

variable {Q : Type u}
variable [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]

/-- Helper for Lemma 10.150.8: evaluating the linear map corresponding to a differential operator
on the universal principal-parts class recovers the underlying operator value. -/
theorem principal_parts_linear_map_equiv_symm_apply_universal_differential
    (k : ℕ) (D : differential_operators_order_le R S M k Q) (m : M) :
    (principal_parts_linear_map_equiv_differential_operators R S M k Q).symm D
      (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) = D.1 m := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Evaluate the identity `e (e.symm D) = D` at `m`.
  have h : (e (e.symm D)).1 m = D.1 m := by
    simpa using
      congrArg (fun E : differential_operators_order_le R S M k Q ↦ E.1 m)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 m = D.1 m
  exact h

/-- Helper for Lemma 10.150.8: evaluating the differential operator represented by a linear map
out of principal parts amounts to evaluating that linear map on the universal class. -/
theorem principal_parts_linear_map_equiv_apply_universal_differential
    (k : ℕ) (L : P^{k}_{S⁄R}(M) →ₗ[S] Q) (m : M) :
    ((principal_parts_linear_map_equiv_differential_operators R S M k Q L).1 m) =
      L (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Reduce the forward evaluation formula to the inverse-direction formula above.
  simpa [e] using
    (principal_parts_linear_map_equiv_symm_apply_universal_differential
      (R := R) (S := S) (M := M) (Q := Q) k (D := e L) m).symm

/-- Helper for Lemma 10.150.8: a linear map out of principal parts is determined by its values on
the universal differential classes. -/
theorem principal_parts_linear_map_eq_of_apply_universal_differential_eq
    (k : ℕ) {L₁ L₂ : P^{k}_{S⁄R}(M) →ₗ[S] Q}
    (h : ∀ m : M,
      L₁ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        L₂ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) :
    L₁ = L₂ := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- The representing equivalence turns equality on universal classes into equality of
  -- differential operators.
  apply e.injective
  ext m
  simpa [principal_parts_linear_map_equiv_apply_universal_differential] using h m

end HelperLemmas

/-- Helper for Lemma 10.150.8: the canonical principal-parts base-change map sends the universal
class `[m]` to the universal class of the image of `m`. -/
theorem principalPartsBaseChangeMap_apply_universal_differential
    (k : ℕ) (m : M) :
    (principalPartsBaseChangeMap k (mk S S' S' M (1 : S')) :
        P^{k}_{S⁄R}(M) →ₗ[S] P^{k}_{S'⁄R}(S' ⊗[S] M))
      (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        principal_parts_universal_differential (R := R) (S := S') (M := S' ⊗[S] M) k
          ((mk S S' S' M (1 : S')) m) := by
  -- Unfold the quotient-level construction and evaluate it on the basis class `[m]`.
  rw [principalPartsBaseChangeMap, principal_parts_universal_differential]
  change
    ((principal_parts_relation_submodule R S M k).mapQ
        (Submodule.restrictScalars S (principal_parts_relation_submodule R S' (S' ⊗[S] M) k))
        (((Finsupp.mapRange.linearMap (Algebra.linearMap S S')).comp
          (Finsupp.lmapDomain S S (mk S S' S' M (1 : S'))))) _)
      ((principal_parts_relation_submodule R S M k).mkQ (Finsupp.single m (1 : S))) =
        (principal_parts_relation_submodule R S' (S' ⊗[S] M) k).mkQ
          (Finsupp.single ((mk S S' S' M (1 : S')) m) (1 : S'))
  simp
  rfl

/-- Helper for Lemma 10.150.8: after lifting the canonical principal-parts comparison along
`S → S'`, the generator `1 ⊗ [m]` maps to the target universal class of `1 ⊗ m`. -/
theorem principalPartsFormallyEtaleBaseChangeMap_apply_tmul_universal_differential
    (k : ℕ) (m : M) :
    (((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S') :
        S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M))
      ((1 : S') ⊗ₜ[S]
        principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
      principal_parts_universal_differential (R := R) (S := S') (M := S' ⊗[S] M) k
        ((mk S S' S' M (1 : S')) m) := by
  -- Evaluate the lifted map on the distinguished tensor generator.
  rw [LinearMap.liftBaseChange_tmul]
  rw [one_smul]
  exact principalPartsBaseChangeMap_apply_universal_differential
    (R := R) (S := S) (S' := S') (M := M) k m

section TensorExtensionality

variable {Q : Type u}
variable [AddCommGroup Q] [Module S' Q] [Module S Q] [Module R Q]
variable [IsScalarTower S S' Q] [IsScalarTower R S Q] [IsScalarTower R S' Q]

/-- Helper for Lemma 10.150.8: an `S'`-linear map out of `S' ⊗[S] P^k_{S/R}(M)` is determined by
its values on the tensors `1 ⊗ [m]`. -/
theorem tensor_principal_parts_linear_map_eq_of_apply_tmul_universal_differential_eq
    (k : ℕ)
    {L₁ L₂ : S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] Q}
    (h : ∀ m : M,
      L₁ ((1 : S') ⊗ₜ[S]
        principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        L₂ ((1 : S') ⊗ₜ[S]
          principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) :
    L₁ = L₂ := by
  let K₁ : P^{k}_{S⁄R}(M) →ₗ[S] Q :=
    { toFun := fun p ↦ L₁ ((1 : S') ⊗ₜ[S] p)
      map_add' := by
        intro p q
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro s p
        -- Rewrite `s ⊗ p` as `(algebraMap S S' s) • (1 ⊗ p)` and use `S'`-linearity.
        calc
          L₁ ((1 : S') ⊗ₜ[S] (s • p)) = L₁ (((algebraMap S S' s : S') • ((1 : S') ⊗ₜ[S] p))) := by
            congr 1
            simpa [TensorProduct.smul_tmul', smul_eq_mul]
          _ = (algebraMap S S' s : S') • L₁ ((1 : S') ⊗ₜ[S] p) := by
            rw [map_smul]
          _ = s • L₁ ((1 : S') ⊗ₜ[S] p) := by
            simpa using
              (IsScalarTower.algebraMap_smul S S' s (L₁ ((1 : S') ⊗ₜ[S] p))) }
  let K₂ : P^{k}_{S⁄R}(M) →ₗ[S] Q :=
    { toFun := fun p ↦ L₂ ((1 : S') ⊗ₜ[S] p)
      map_add' := by
        intro p q
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro s p
        -- The same tensor-scalar rewrite gives the `S`-linearity of `K₂`.
        calc
          L₂ ((1 : S') ⊗ₜ[S] (s • p)) = L₂ (((algebraMap S S' s : S') • ((1 : S') ⊗ₜ[S] p))) := by
            congr 1
            simpa [TensorProduct.smul_tmul', smul_eq_mul]
          _ = (algebraMap S S' s : S') • L₂ ((1 : S') ⊗ₜ[S] p) := by
            rw [map_smul]
          _ = s • L₂ ((1 : S') ⊗ₜ[S] p) := by
            simpa using
              (IsScalarTower.algebraMap_smul S S' s (L₂ ((1 : S') ⊗ₜ[S] p))) }
  have hK : K₁ = K₂ := by
    -- Collapse the comparison to the source principal-parts module and use source extensionality.
    apply principal_parts_linear_map_eq_of_apply_universal_differential_eq
      (R := R) (S := S) (M := M) (Q := Q) k
    intro m
    simpa [K₁, K₂] using h m
  -- Once the restrictions agree on `1 ⊗ p`, tensor induction lifts that equality to all tensors.
  apply DFunLike.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a p
    calc
      L₁ (a ⊗ₜ[S] p) = a • L₁ ((1 : S') ⊗ₜ[S] p) := by
        rw [show (a ⊗ₜ[S] p : S' ⊗[S] P^{k}_{S⁄R}(M)) = a • ((1 : S') ⊗ₜ[S] p) by
          simpa using (TensorProduct.tmul_eq_smul_one_tmul (R := S) a p)]
        rw [map_smul]
      _ = a • K₁ p := by rfl
      _ = a • K₂ p := by rw [hK]
      _ = a • L₂ ((1 : S') ⊗ₜ[S] p) := by rfl
      _ = L₂ (a ⊗ₜ[S] p) := by
        rw [show (a ⊗ₜ[S] p : S' ⊗[S] P^{k}_{S⁄R}(M)) = a • ((1 : S') ⊗ₜ[S] p) by
          simpa using (TensorProduct.tmul_eq_smul_one_tmul (R := S) a p)]
        rw [map_smul]
  · intro x y hx hy
    simp [hx, hy]

end TensorExtensionality

section DiagonalTensorAction

/-- Helper for Lemma 10.150.8: left multiplication on `S`, regarded as an `R`-linear
endomorphism-valued map. This is the first factor of the diagonal action used in the quotient
presentation from Lemma `10.133.9`. -/
private def diagonal_left_scalar_end :
    S →ₗ[R] S →ₗ[R] S where
  toFun s := DistribSMul.toLinearMap R S s
  map_add' := by
    intro s t
    ext u
    simp [add_mul]
  map_smul' := by
    intro r s
    ext u
    simp [Algebra.smul_def, mul_assoc]

/-- Helper for Lemma 10.150.8: the `S`-action on `M`, regarded as an `R`-linear
endomorphism-valued map. This is the second factor of the diagonal action used in the quotient
presentation from Lemma `10.133.9`. -/
private def diagonal_module_scalar_end :
    S →ₗ[R] M →ₗ[R] M where
  toFun s := DistribSMul.toLinearMap R M s
  map_add' := by
    intro s t
    ext m
    simp [add_smul]
  map_smul' := by
    intro r s
    ext m
    simpa [LinearMap.smul_apply, Algebra.smul_def, smul_smul, mul_assoc] using
      (smul_assoc r s m)

/-- Helper for Lemma 10.150.8: the canonical diagonal action of `S ⊗[R] S` on `S ⊗[R] M`,
sending `(a ⊗ b, s ⊗ m)` to `as ⊗ bm`. -/
private def diagonal_tensor_action :
    S ⊗[R] S →ₗ[R] S ⊗[R] M →ₗ[R] S ⊗[R] M :=
  (TensorProduct.homTensorHomMap (RingHom.id R) S M S M).comp
    (TensorProduct.map diagonal_left_scalar_end diagonal_module_scalar_end)

/-- Helper for Lemma 10.150.8: the diagonal tensor action evaluates on pure tensors by the
expected textbook formula. -/
private theorem diagonal_tensor_action_tmul_tmul
    (a b s : S) (m : M) :
    diagonal_tensor_action ((a : S) ⊗ₜ[R] b) ((s : S) ⊗ₜ[R] m) =
      ((a * s : S) ⊗ₜ[R] (b • m)) := by
  -- Both tensor lifts were defined precisely so that pure tensors evaluate by the bilinear rule.
  simp [diagonal_tensor_action, diagonal_left_scalar_end, diagonal_module_scalar_end]

/-- Helper for Lemma 10.150.8: the diagonal tensor action is unital. -/
private theorem diagonal_tensor_action_one
    (x : S ⊗[R] M) :
    diagonal_tensor_action (1 : S ⊗[R] S) x = x := by
  -- It is enough to evaluate on pure tensors and extend additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [diagonal_tensor_action]
  · intro s m
    simpa [Algebra.TensorProduct.one_def] using
      diagonal_tensor_action_tmul_tmul (R := R) (S := S) (M := M) 1 1 s m
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

/-- Helper for Lemma 10.150.8: the diagonal tensor action is multiplicative in the
`S ⊗[R] S`-variable. -/
private theorem diagonal_tensor_action_mul
    (x y : S ⊗[R] S) (z : S ⊗[R] M) :
    diagonal_tensor_action (x * y) z =
      diagonal_tensor_action x (diagonal_tensor_action y z) := by
  -- Reduce the multiplicativity check to pure tensors in every variable.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [diagonal_tensor_action]
  · intro a b
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [diagonal_tensor_action]
    · intro c d
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp [diagonal_tensor_action]
      · intro s m
        simp [diagonal_tensor_action_tmul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_assoc, smul_smul]
      · intro z w hz hw
        rw [LinearMap.map_add, LinearMap.map_add, hz, hw]
        exact ((diagonal_tensor_action ((a : S) ⊗ₜ[R] b)).map_add
          (diagonal_tensor_action ((c : S) ⊗ₜ[R] d) z)
          (diagonal_tensor_action ((c : S) ⊗ₜ[R] d) w)).symm
    · intro y₁ y₂ hy₁ hy₂
      simp [mul_add, LinearMap.map_add, hy₁, hy₂]
  · intro x₁ x₂ hx₁ hx₂
    simp [add_mul, LinearMap.map_add, hx₁, hx₂]

/-- Helper for Lemma 10.150.8: the source tensor module carries the diagonal
`S ⊗[R] S`-module structure from Lemma `10.133.9`. This recreates the earlier local API so the
quotient-ring tensor presentation can be used in the current item file. -/
private instance diagonal_tensor_module :
    Module (S ⊗[R] S) (S ⊗[R] M) where
  smul x y := diagonal_tensor_action x y
  zero_smul y := by
    -- The action is linear in the algebra variable.
    exact LinearMap.congr_fun diagonal_tensor_action.map_zero y
  smul_zero x := by
    -- For fixed `x`, the action is linear in the tensor-module variable.
    exact (diagonal_tensor_action x).map_zero
  add_smul x y z := by
    -- Additivity in the acting tensor follows from the outer linear map.
    exact LinearMap.congr_fun (diagonal_tensor_action.map_add x y) z
  smul_add x y z := by
    -- Additivity in the module variable follows from the inner linear map.
    exact (diagonal_tensor_action x).map_add y z
  one_smul y := by
    -- The tensor `1 ⊗ 1` acts as the identity.
    simpa using diagonal_tensor_action_one (R := R) (S := S) (M := M) y
  mul_smul x y z := by
    -- Multiplication in `S ⊗[R] S` matches composition of the induced endomorphisms.
    simpa using diagonal_tensor_action_mul (R := R) (S := S) (M := M) x y z

/-- Helper for Lemma 10.150.8: restricting the diagonal action along `s ↦ s ⊗ 1` recovers the
usual left `S`-action on `S ⊗[R] M`. -/
private instance diagonal_tensor_isScalarTower :
    IsScalarTower S (S ⊗[R] S) (S ⊗[R] M) where
  smul_assoc s x y := by
    -- Check the compatibility on pure tensors and extend additively.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [diagonal_tensor_action]
    · intro a b
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro t m
        change
          diagonal_tensor_action (((s * a : S) ⊗ₜ[R] b)) ((t : S) ⊗ₜ[R] m) =
            s • diagonal_tensor_action ((a : S) ⊗ₜ[R] b) ((t : S) ⊗ₜ[R] m)
        rw [diagonal_tensor_action_tmul_tmul, diagonal_tensor_action_tmul_tmul]
        simp [TensorProduct.smul_tmul', smul_eq_mul, mul_assoc]
      · intro y z hy hz
        simp [smul_add, hy, hz]
    · intro x y hx hy
      simp [add_smul, hx, hy]

/-- Helper for Lemma 10.150.8: forgetting from the diagonal `S ⊗[R] S`-module structure on
`S ⊗[R] M` to the source `S`-module structure does not change the quotient object. -/
noncomputable def diagonal_tensor_quotient_restrictScalars_equiv
    (k : ℕ) :
    ((S ⊗[R] M) ⧸
      Submodule.restrictScalars S
        ((((KaehlerDifferential.ideal R S) ^ (k + 1)) •
          (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))) ≃ₗ[S]
      ((S ⊗[R] M) ⧸
        (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
          (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))) :=
  -- The quotient relation only depends on the underlying submodule carrier.
  Submodule.Quotient.restrictScalarsEquiv S
    (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
      (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))

end DiagonalTensorAction

section DiagonalTensorBaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Algebra.TensorProduct.right_isScalarTower

/-- Helper for Lemma 10.150.8: tensor symmetry rewrites the source generator `s ⊗ m` as the
right tensor `m ⊗ s`, which is the input shape used by the later pushout-cancellation route. -/
theorem source_tensor_comm_apply_tmul
    (s : S) (m : M) :
    (TensorProduct.comm R S M) ((s : S) ⊗ₜ[R] m) =
      m ⊗ₜ[R] s := by
  -- Proof comment: tensor symmetry literally swaps the two factors on pure tensors.
  simp [TensorProduct.comm_tmul]

/-- Helper for Lemma 10.150.8: inverse tensor symmetry sends the right tensor generator `m ⊗ s`
back to the source generator `s ⊗ m`. -/
theorem source_tensor_comm_symm_apply_tmul
    (m : M) (s : S) :
    (TensorProduct.comm R S M).symm (m ⊗ₜ[R] s) =
      ((s : S) ⊗ₜ[R] m) := by
  -- Proof comment: this is the inverse pure-tensor formula for tensor symmetry.
  simpa using (TensorProduct.comm_symm_tmul (R := R) (M := S) (N := M) s m)

/-- Helper for Lemma 10.150.8: collapsing the source tensor product along the `S`-action sends
`s ⊗ m` to `s • m`. This is the canonical source-side comparison before rebuilding the diagonal
tensor model. -/
noncomputable def source_tensor_to_module :
    S ⊗[R] M →ₗ[S] M :=
  (TensorProduct.lid S M).toLinearMap.comp
    (TensorProduct.mapOfCompatibleSMul S R S S M)

/-- Helper for Lemma 10.150.8: the source-side collapse map evaluates on pure tensors by scalar
multiplication. -/
theorem source_tensor_to_module_apply_tmul
    (s : S) (m : M) :
    source_tensor_to_module (R := R) (S := S) (M := M) ((s : S) ⊗ₜ[R] m) = s • m := by
  -- Proof comment: first pass to the balanced tensor product over `S`, then evaluate the left
  -- unit tensor equivalence.
  simp [source_tensor_to_module]

/-- Helper for Lemma 10.150.8: inserting `m` as the pure tensor `((1 ⊗ 1) ⊗ m)` in the diagonal
tensor model. This is the canonical target-side reconstruction map after collapsing the source. -/
noncomputable def module_to_diagonal_tensor :
    M →ₗ[S] ((S ⊗[R] S) ⊗[S] M) :=
  TensorProduct.mk S (S ⊗[R] S) M (((1 : S) ⊗ₜ[R] (1 : S)) : S ⊗[R] S)

/-- Helper for Lemma 10.150.8: after rebuilding the diagonal tensor model, multiplying `m` by `s`
becomes the textbook pure tensor `((s ⊗ 1) ⊗ m)`. -/
theorem module_to_diagonal_tensor_apply_smul
    (s : S) (m : M) :
    module_to_diagonal_tensor (R := R) (S := S) (M := M) (s • m) =
      (((s : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] m) := by
  -- Proof comment: rewrite `((1 ⊗ 1) ⊗ (s • m))` by moving the scalar `s` into the left tensor
  -- factor inside the balanced tensor product over `S`.
  simp [module_to_diagonal_tensor, TensorProduct.smul_tmul', smul_eq_mul]

/-- Helper for Lemma 10.150.8: the explicit source-to-target candidate comparison already sends
`s ⊗ m` to the textbook tensor `((s ⊗ 1) ⊗ m)`. This isolates the generator-level part of the
left-factor tensor presentation; the remaining blocker for the main theorem is the separate global
comparison between this left-factor model and the canonical right-factor base-change model. -/
theorem module_to_diagonal_tensor_comp_source_tensor_to_module_apply_tmul
    (s : S) (m : M) :
    module_to_diagonal_tensor (R := R) (S := S) (M := M)
        (source_tensor_to_module (R := R) (S := S) (M := M) ((s : S) ⊗ₜ[R] m)) =
      (((s : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] m) := by
  -- Route correction: the generator formula is now isolated through the canonical collapse and
  -- rebuild maps, so the unresolved work is the global inverse statement for this candidate map.
  rw [source_tensor_to_module_apply_tmul]
  exact module_to_diagonal_tensor_apply_smul (R := R) (S := S) (M := M) s m

/-- Helper for Lemma 10.150.8: the left-factor source-to-diagonal comparison map used in the
textbook tensor presentation. This records the generator-level map separately from the still-open
comparison with the canonical base-change equivalence. -/
noncomputable def diagonal_tensor_module_baseChangeMap :
    S ⊗[R] M →ₗ[S] ((S ⊗[R] S) ⊗[S] M) :=
  -- Proof comment: package the already isolated collapse-then-rebuild route as a single `S`-linear
  -- map so later quotient-model work can refer to it directly.
  module_to_diagonal_tensor (R := R) (S := S) (M := M) ∘ₗ
    source_tensor_to_module (R := R) (S := S) (M := M)

/-- Helper for Lemma 10.150.8: under the base-change identification, a pure tensor `s ⊗ m`
becomes the textbook pure tensor `(s ⊗ 1) ⊗ m`. -/
theorem diagonal_tensor_module_baseChangeMap_apply_tmul
    (s : S) (m : M) :
    diagonal_tensor_module_baseChangeMap (R := R) (S := S) (M := M)
      ((s : S) ⊗ₜ[R] m) =
        (((s : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] m) := by
  -- Proof comment: the new packaged map is definitionally the previously isolated
  -- collapse-then-rebuild candidate, so the pure-tensor formula is exactly the generator lemma
  -- proved just above.
  exact module_to_diagonal_tensor_comp_source_tensor_to_module_apply_tmul
    (R := R) (S := S) (M := M) s m

/-- Helper for Lemma 10.150.8: the canonical right-factor tensor model identifies
`M ⊗[R] S` with `((S ⊗[R] S) ⊗[S] M)`. This is the comparison object used later to bridge the
textbook left-factor model with mathlib's `rightComm`/`cancelBaseChange` route. -/
noncomputable def diagonal_tensor_right_factor_equiv :
    M ⊗[R] S ≃ₗ[S] ((S ⊗[R] S) ⊗[S] M) :=
  TensorProduct.AlgebraTensorModule.congr (R := R) (A := S)
      ((TensorProduct.lid S M).symm) (LinearEquiv.refl R S) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rightComm R S S S M S

/-- Helper for Lemma 10.150.8: the canonical right-factor tensor equivalence sends `m ⊗ s` to the
pure tensor `((1 ⊗ s) ⊗ m)`. -/
theorem diagonal_tensor_right_factor_equiv_apply_tmul
    (m : M) (s : S) :
    diagonal_tensor_right_factor_equiv (R := R) (S := S) (M := M)
      (m ⊗ₜ[R] s) =
        (((1 : S) ⊗ₜ[R] s) ⊗ₜ[S] m) := by
  -- Proof comment: first rewrite `m` as `1 ⊗ m`, then apply the heterobasic tensor right-comm
  -- equivalence on the resulting pure tensor.
  simp [diagonal_tensor_right_factor_equiv]

/-- Helper for Lemma 10.150.8: the inverse of the canonical right-factor tensor equivalence sends
`((a ⊗ b) ⊗ m)` to the right-factor tensor `(a • m) ⊗ b`. -/
theorem diagonal_tensor_right_factor_equiv_symm_apply_tmul_tmul
    (a b : S) (m : M) :
    (diagonal_tensor_right_factor_equiv (R := R) (S := S) (M := M)).symm
      (((a : S) ⊗ₜ[R] b) ⊗ₜ[S] m) =
        (a • m) ⊗ₜ[R] b := by
  -- Proof comment: unfold the explicit `rightComm`-based equivalence and read off the inverse
  -- formula on pure tensors.
  simp [diagonal_tensor_right_factor_equiv]

/-- Helper for Lemma 10.150.8: commuting the two tensor factors upgrades the right-factor source
presentation `M ⊗[R] S` to the left-factor source presentation `S ⊗[R] M` as an
`R`-linear symmetry map. -/
noncomputable def diagonal_right_factor_to_left_factor :
    M ⊗[R] S ≃ₗ[R] S ⊗[R] M :=
  TensorProduct.comm R M S

/-- Helper for Lemma 10.150.8: the source-side left/right tensor comparison sends `m ⊗ s` to
`s ⊗ m`. -/
theorem diagonal_right_factor_to_left_factor_apply_tmul
    (m : M) (s : S) :
    diagonal_right_factor_to_left_factor (R := R) (S := S) (M := M)
      (m ⊗ₜ[R] s) =
        ((s : S) ⊗ₜ[R] m) := by
  -- Proof comment: this is the pure-tensor formula for the tensor symmetry map.
  simp [diagonal_right_factor_to_left_factor, TensorProduct.comm_tmul]

/-- Helper for Lemma 10.150.8: the inverse tensor symmetry sends a left-factor pure tensor back
to the corresponding right-factor pure tensor. -/
theorem diagonal_right_factor_to_left_factor_symm_apply_tmul
    (s : S) (m : M) :
    (diagonal_right_factor_to_left_factor (R := R) (S := S) (M := M)).symm
      ((s : S) ⊗ₜ[R] m) =
        m ⊗ₜ[R] s := by
  -- Proof comment: this is the inverse pure-tensor formula for tensor symmetry.
  simpa [diagonal_right_factor_to_left_factor] using
    (TensorProduct.comm_symm_tmul (R := R) (M := M) (N := S) m s)

/-- Helper for Lemma 10.150.8: the source right-factor tensor convention `M ⊗[R] S` agrees
`R`-linearly with the textbook left-factor convention `S ⊗[R] M`. This records the honest tensor
symmetry available in the current module structures; the stronger `S`-linear comparison would
require a different source/target scalar-action package. -/
noncomputable def right_factor_tensor_to_left_factor :
    M ⊗[R] S ≃ₗ[R] S ⊗[R] M :=
  -- Route correction: the ambient `S`-module structures on these two tensor products do not match
  -- the plain commutor, so the reusable bridge available here is the underlying `R`-linear
  -- symmetry already isolated above.
  diagonal_right_factor_to_left_factor (R := R) (S := S) (M := M)

/-- Helper for Lemma 10.150.8: the `S`-linear right-to-left tensor comparison sends the pure tensor
`m ⊗ s` to `s ⊗ m`. -/
theorem right_factor_tensor_to_left_factor_apply_tmul
    (m : M) (s : S) :
    right_factor_tensor_to_left_factor (R := R) (S := S) (M := M)
      (m ⊗ₜ[R] s) =
        ((s : S) ⊗ₜ[R] m) := by
  -- Proof comment: after correcting the helper to the honest tensor commutor, the pure-tensor
  -- formula is exactly the already established source symmetry computation.
  exact diagonal_right_factor_to_left_factor_apply_tmul
    (R := R) (S := S) (M := M) m s

/-- Helper for Lemma 10.150.8: the inverse right-to-left tensor comparison sends the pure tensor
`s ⊗ m` back to `m ⊗ s`. -/
theorem right_factor_tensor_to_left_factor_symm_apply_tmul
    (s : S) (m : M) :
    (right_factor_tensor_to_left_factor (R := R) (S := S) (M := M)).symm
      ((s : S) ⊗ₜ[R] m) =
        m ⊗ₜ[R] s := by
  -- Proof comment: apply the forward pure-tensor formula and then use the inverse equality of a
  -- linear equivalence.
  apply (right_factor_tensor_to_left_factor (R := R) (S := S) (M := M)).injective
  simpa [right_factor_tensor_to_left_factor_apply_tmul]

/-- Helper for Lemma 10.150.8: the inner `S`-linear commutor `commRight` swaps pure tensors in
`S ⊗[R] S`. This isolates the source-faithful ambient factor swap needed for the textbook route. -/
theorem diagonal_tensor_commRight_apply_tmul
    (a b : S) :
    Algebra.TensorProduct.commRight R S S ((a : S) ⊗ₜ[R] b) =
        ((b : S) ⊗ₜ[R] a) := by
  -- Proof comment: this is exactly the pure-tensor formula for `commRight`.
  simp

/-- Helper for Lemma 10.150.8: the source-faithful ambient tensor object formed using the
right-factor `S`-action on `S ⊗[R] S`. This isolates the module convention that the source proof
uses, without perturbing the rest of the section's default tensor notation. -/
private abbrev diagonal_tensor_right_action_tensor : Type u :=
  let _ : Module S (S ⊗[R] S) :=
    Module.compHom (S ⊗[R] S)
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom
  ((S ⊗[R] S) ⊗[S] M)

/-- Helper for Lemma 10.150.8: the pure tensor `((a ⊗ b) ⊗ m)` inside the source-faithful
right-action ambient tensor object. This packages the only place where the alternate module
convention must be named explicitly. -/
private def diagonal_tensor_right_action_tmul_tmul
    (a b : S) (m : M) :
    diagonal_tensor_right_action_tensor (R := R) (S := S) (M := M) :=
  let _ : Module S (S ⊗[R] S) :=
    Module.compHom (S ⊗[R] S)
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom
  (((a : S) ⊗ₜ[R] b) ⊗ₜ[S] m)

/-- Helper for Lemma 10.150.8: the packaged pure tensor in the source-faithful right-action
ambient object is definitionally the displayed tensor `((a ⊗ b) ⊗ m)`. This records the new
ambient object concretely before the missing comparison map to the left-action convention is
constructed. -/
private theorem diagonal_tensor_right_action_tmul_tmul_def
    (a b : S) (m : M) :
    diagonal_tensor_right_action_tmul_tmul (R := R) (S := S) (M := M) a b m =
      (let _ : Module S (S ⊗[R] S) :=
          Module.compHom (S ⊗[R] S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom
        ; (((a : S) ⊗ₜ[R] b) ⊗ₜ[S] m)) := by
  -- Proof comment: this is just the unfolding equation for the packaged pure tensor in the
  -- source-faithful ambient object.
  rfl

/-- Helper for Lemma 10.150.8: the displayed pure tensor `((a ⊗ b) ⊗ m)` in the explicit
right-action ambient object can be rewritten back to the packaged notation
`diagonal_tensor_right_action_tmul_tmul`. This is the orientation used when later tensor
comparison maps are applied to pure tensors. -/
private theorem diagonal_tensor_right_action_tmul_tmul_eq_display
    (a b : S) (m : M) :
    (let _ : Module S (S ⊗[R] S) :=
          Module.compHom (S ⊗[R] S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom
        ; (((a : S) ⊗ₜ[R] b) ⊗ₜ[S] m)) =
      diagonal_tensor_right_action_tmul_tmul (R := R) (S := S) (M := M) a b m := by
  -- Proof comment: this is just the reverse orientation of the definitional packaged-tensor
  -- identity, recorded for later rewrite use.
  simpa using
    (diagonal_tensor_right_action_tmul_tmul_def (R := R) (S := S) (M := M) a b m).symm

/-- Helper for Lemma 10.150.8: in the current left-action ambient tensor object, moving the scalar
`b` from `m` back to the first tensor factor rewrites `((a ⊗ 1) ⊗ (b • m))` as
`((ab ⊗ 1) ⊗ m)`. This is the explicit rebalancing identity that shows why the ambient
left-factor inverse route must descend to the diagonal quotient before it can match the textbook
tensor `((a ⊗ b) ⊗ m)`. -/
theorem diagonal_tensor_left_action_rebalance
    (a b : S) (m : M) :
    (((a : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] (b • m)) =
      ((((a * b : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] m)) := by
  -- Proof comment: move `b` across the outer tensor product, then simplify the induced scalar
  -- action on the first tensor factor.
  calc
    (((a : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] (b • m)) =
        (b • (((a : S) ⊗ₜ[R] (1 : S))) ⊗ₜ[S] m) := by
          simpa using
            (TensorProduct.tmul_smul (R := S) (r := b)
              (((a : S) ⊗ₜ[R] (1 : S))) m)
    _ = ((((a * b : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] m)) := by
          simp [TensorProduct.smul_tmul', smul_eq_mul, mul_comm]

/-- Helper for Lemma 10.150.8: after applying the collapse-then-rebuild map to the source tensor
`a ⊗ (b • m)`, the current ambient tensor object produces the rebalanced tensor
`((ab ⊗ 1) ⊗ m)`. This packages the exact obstruction to getting the textbook tensor
`((a ⊗ b) ⊗ m)` before quotienting by the diagonal ideal. -/
theorem diagonal_tensor_module_baseChangeMap_apply_tmul_smul
    (a b : S) (m : M) :
    diagonal_tensor_module_baseChangeMap (R := R) (S := S) (M := M)
      ((a : S) ⊗ₜ[R] (b • m)) =
        ((((a * b : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[S] m)) := by
  -- Proof comment: start from the pure-tensor formula for the collapse-then-rebuild map and then
  -- apply the balanced rebalancing identity above.
  rw [diagonal_tensor_module_baseChangeMap_apply_tmul]
  exact diagonal_tensor_left_action_rebalance (R := R) (S := S) (M := M) a b m

end DiagonalTensorBaseChange

-- Proof sketch: first base change the quotient model from Lemma `10.133.9`, then apply the
-- general tensor-quotient equivalence. On the generator `1 ⊗ [m]`, both steps are computed by the
-- corresponding generator lemmas, so the image is the quotient class of `1 ⊗ (1 ⊗ m)`.
/-- Helper for Lemma 10.150.8: after base changing the quotient model of Lemma `10.133.9` and then
applying the general tensor-quotient equivalence, the source generator `1 ⊗ [m]` becomes the
intermediate quotient class of `1 ⊗ (1 ⊗ m)`. -/
theorem source_baseChange_tensor_quotient_apply_tmul_universal_differential
    (k : ℕ) (m : M) :
    let epp := principal_parts_module_equiv_tensor_quotient
      (R := R) (S := S) (M := M) k
    let ebase := epp.baseChange S S' _ _
    let eqt := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
      (R := S) (A := S') (B := S) (M := S') (N := S ⊗[R] M) _
    eqt (ebase ((1 : S') ⊗ₜ[S]
      principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) =
      Submodule.Quotient.mk ((1 : S') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) := by
  -- Unfold the base-changed quotient model and evaluate it on the source generator.
  dsimp
  rw [principal_parts_module_equiv_tensor_quotient_universal_differential
    (R := R) (S := S) (M := M) k m]
  simpa using
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_apply_tmul
      (R := S) (A := S') (B := S) (M := S') (N := S ⊗[R] M)
      (n := _) (x := (1 : S')) (y := ((1 : S) ⊗ₜ[R] m)))

/-- Helper for Lemma 10.150.8: once the source denominator has been transported through
`cancelBaseChange`, the descended quotient equivalence sends the intermediate source generator
`1 ⊗ (1 ⊗ m)` to the class of `1 ⊗ m`. -/
theorem source_intermediate_quotient_cancelBaseChange_equiv_apply_generator
    {nsrc : Submodule S' (S' ⊗[S] (S ⊗[R] M))}
    {nI : Submodule S' (S' ⊗[R] M)}
    (hmap :
      nsrc.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M).toLinearMap =
        nI)
    (m : M) :
    (Submodule.Quotient.equiv nsrc nI
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M) hmap)
      (Submodule.Quotient.mk ((1 : S') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))) =
        Submodule.Quotient.mk ((1 : S') ⊗ₜ[R] m) := by
  -- Proof comment: `Submodule.Quotient.equiv` is induced by `cancelBaseChange`, so it is enough
  -- to evaluate that equivalence on the displayed pure tensor.
  change
    Submodule.Quotient.mk
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M)
          ((1 : S') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))) =
      Submodule.Quotient.mk ((1 : S') ⊗ₜ[R] m)
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  simp

/-- Helper for Lemma 10.150.8: cancelling the redundant source-side base change on the acting ring
turns the right tensor inclusion into the left-factor base-change map
`S ⊗[R] S → S' ⊗[R] S`. -/
theorem source_cancelBaseChangeAlg_comp_includeRight :
    ((Algebra.TensorProduct.cancelBaseChange
        (R := R) (S := S) (T := S') (A := S') (B := S)).toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := S) (A := S') (B := S ⊗[R] S)).toRingHom) =
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom := by
  apply RingHom.ext
  intro z
  -- Proof comment: both ring maps are determined on pure tensors `s₁ ⊗ s₂`, where
  -- `cancelBaseChange` sends `1 ⊗ (s₁ ⊗ s₂)` to `algebraMap S S' s₁ ⊗ s₂`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro s₁ s₂
    change
      (Algebra.TensorProduct.cancelBaseChange
        (R := R) (S := S) (T := S') (A := S') (B := S))
        ((1 : S') ⊗ₜ[S] ((s₁ : S) ⊗ₜ[R] s₂)) =
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S))
        ((s₁ : S) ⊗ₜ[R] s₂)
    simp [Algebra.smul_def]
  · intro z₁ z₂ hz₁ hz₂
    have hz₁' :
        (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] z₁) =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₁ := by
      simpa using hz₁
    have hz₂' :
        (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] z₂) =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₂ := by
      simpa using hz₂
    calc
      (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] (z₁ + z₂)) =
        (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] z₁) +
          (Algebra.TensorProduct.cancelBaseChange
            (R := R) (S := S) (T := S') (A := S') (B := S))
            ((1 : S') ⊗ₜ[S] z₂) := by
              rw [TensorProduct.tmul_add, map_add]
      _ =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₁ +
          (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₂ := by
              rw [hz₁', hz₂']
      _ =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) (z₁ + z₂) := by
              rw [map_add]

/-- Helper for Lemma 10.150.8: the base-changed source diagonal ideal is contained in the
`Icomap` ideal appearing in Lemma `10.150.7`. -/
theorem source_baseChange_diagonalIdeal_map_le_iComap :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    Ideal.map sourceMap (KaehlerDifferential.ideal R S) ≤ Icomap := by
  dsimp
  -- Proof comment: rewrite the source diagonal ideal as the span of the standard generators
  -- `1 ⊗ s - s ⊗ 1`, map those generators across the left-factor base change, and then check that
  -- their images land in the target diagonal ideal after applying `tensorComparison`.
  rw [← KaehlerDifferential.span_range_eq_ideal (R := R) (S := S), Ideal.map_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with ⟨s, rfl⟩
  change
    (Algebra.TensorProduct.map
      (AlgHom.id R S') (IsScalarTower.toAlgHom R S S'))
      ((Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S))
        (((1 : S) ⊗ₜ[R] s) - (s ⊗ₜ[R] (1 : S)))) ∈
      KaehlerDifferential.ideal R S'
  simpa using
    (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := R)
      (algebraMap S S' s))

/-- Helper for Lemma 10.150.8: every element of `S' ⊗[R] S` differs from the tensor of its
product image by an element of the mapped source diagonal ideal. -/
theorem source_baseChange_sub_includeLeft_productMap_mem_mapped_diagonalIdeal
    (x : S' ⊗[R] S) :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let includeLeftS' : S' →ₐ[R] S' ⊗[R] S := Algebra.TensorProduct.includeLeft
    let sourceProduct : S' ⊗[R] S →ₐ[R] S' :=
      Algebra.TensorProduct.productMap (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')
    x - includeLeftS' (sourceProduct x) ∈
      Ideal.map sourceMap (KaehlerDifferential.ideal R S) := by
  dsimp
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a s
    have hgen :
        ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) ∈ KaehlerDifferential.ideal R S := by
      -- Proof comment: the source diagonal ideal is generated by the standard differences
      -- `1 ⊗ s - s ⊗ 1`.
      exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := R) s
    have hmap :
        ((1 : S') ⊗ₜ[R] s - (algebraMap S S' s : S') ⊗ₜ[R] (1 : S)) ∈
          Ideal.map
            ((Algebra.TensorProduct.map
              (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
            (KaehlerDifferential.ideal R S) := by
      -- Proof comment: base changing the standard generator gives the corresponding difference
      -- in `S' ⊗[R] S`.
      simpa using
        Ideal.mem_map_of_mem
          ((Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
          hgen
    have hsmul :
        (((Algebra.TensorProduct.includeLeft : S' →ₐ[R] S' ⊗[R] S) a) *
          (((1 : S') ⊗ₜ[R] s) - ((algebraMap S S' s : S') ⊗ₜ[R] (1 : S))) : S' ⊗[R] S) ∈
          Ideal.map
            ((Algebra.TensorProduct.map
              (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
            (KaehlerDifferential.ideal R S) := by
      -- Proof comment: multiplying the mapped diagonal generator by `a` produces the displayed
      -- pure-tensor difference.
      exact Ideal.mul_mem_left _ _ hmap
    simpa [Algebra.TensorProduct.productMap_apply_tmul, sub_eq_add_neg,
      mul_add, add_mul, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.tmul_mul_tmul,
      mul_assoc, mul_left_comm, mul_comm] using hsmul
  · intro y z hy hz
    -- Proof comment: the product map and `includeLeft` are additive, so the desired difference
    -- term is additive as well.
    have hrewrite :
        y + z -
            (Algebra.TensorProduct.productMap
              (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) (y + z) ⊗ₜ[R] (1 : S) =
          (y -
              (Algebra.TensorProduct.productMap
                (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) y ⊗ₜ[R] (1 : S)) +
            (z -
              (Algebra.TensorProduct.productMap
                (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) z ⊗ₜ[R] (1 : S)) := by
      rw [map_add, TensorProduct.add_tmul, sub_eq_add_neg, sub_eq_add_neg, neg_add]
      abel
    rw [hrewrite]
    exact Ideal.add_mem _ hy hz

/-- Helper for Lemma 10.150.8: the mapped source diagonal ideal is exactly the pulled-back target
diagonal ideal on `S' ⊗[R] S`. -/
theorem source_baseChange_diagonalIdeal_eq_iComap :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    Ideal.map sourceMap (KaehlerDifferential.ideal R S) = Icomap := by
  dsimp
  apply le_antisymm
  · exact source_baseChange_diagonalIdeal_map_le_iComap
      (R := R) (S := S) (S' := S')
  · intro x hx
    let includeLeftS' : S' →ₐ[R] S' ⊗[R] S := Algebra.TensorProduct.includeLeft
    let sourceProduct : S' ⊗[R] S →ₐ[R] S' :=
      Algebra.TensorProduct.productMap (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')
    have hdiff :
        x - includeLeftS' (sourceProduct x) ∈
          Ideal.map
            ((Algebra.TensorProduct.map
              (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
            (KaehlerDifferential.ideal R S) :=
      source_baseChange_sub_includeLeft_productMap_mem_mapped_diagonalIdeal
        (R := R) (S := S) (S' := S') x
    have hxker :
        ((Algebra.TensorProduct.map
          (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) x) ∈
          RingHom.ker (Algebra.TensorProduct.lmul' (S := S') R) := by
      -- Proof comment: membership in the pulled-back target diagonal ideal means exactly that the
      -- tensor-comparison image lands in the kernel of multiplication.
      simpa [KaehlerDifferential.ideal] using hx
    have hprod : sourceProduct x = 0 := by
      have hcomp :
          ((Algebra.TensorProduct.lmul' (S := S') R).comp
            (Algebra.TensorProduct.map
              (AlgHom.id R S') (IsScalarTower.toAlgHom R S S'))) x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      -- Proof comment: the source product map is the multiplication map after tensor comparison.
      simpa [sourceProduct, Algebra.TensorProduct.productMap_eq_comp_map] using hcomp
    simpa [sourceProduct, hprod] using hdiff

/-- Helper for Lemma 10.150.8: the identified source and target diagonal ideals remain equal after
taking the `(k + 1)`st power. -/
theorem source_baseChange_diagonalIdeal_pow_eq_iComap_pow
    (k : ℕ) :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    Ideal.map sourceMap ((KaehlerDifferential.ideal R S) ^ (k + 1)) =
      Icomap ^ (k + 1) := by
  -- Proof comment: once the degree-one diagonal ideals agree, functoriality of `Ideal.map` on
  -- powers upgrades the comparison to the powered denominators used in principal parts.
  dsimp
  let J : Ideal (S ⊗[R] S) := KaehlerDifferential.ideal R S
  let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
  let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
    (Algebra.TensorProduct.map
      (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
  let Icomap : Ideal (S' ⊗[R] S) :=
    Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
  have hdiag : Ideal.map sourceMap J = Icomap := by
    simpa [J, sourceMap, tensorComparison, Icomap] using
      source_baseChange_diagonalIdeal_eq_iComap (R := R) (S := S) (S' := S')
  calc
    Ideal.map sourceMap (J ^ (k + 1)) = (Ideal.map sourceMap J) ^ (k + 1) := by
      rw [Ideal.map_pow]
    _ = Icomap ^ (k + 1) := by
      simpa using congrArg (fun I : Ideal (S' ⊗[R] S) ↦ I ^ (k + 1)) hdiag

/-- Helper for Lemma 10.150.8: on the regular module `S' ⊗[R] S`, the powered transported source
denominator is exactly the powered pulled-back target denominator. -/
theorem source_baseChange_diagonalIdeal_pow_smul_top_eq_iComap_pow_smul_top
    (k : ℕ) :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    (Ideal.map sourceMap ((KaehlerDifferential.ideal R S) ^ (k + 1))) •
        (⊤ : Submodule (S' ⊗[R] S) (S' ⊗[R] S)) =
      (Icomap ^ (k + 1)) • (⊤ : Submodule (S' ⊗[R] S) (S' ⊗[R] S)) := by
  -- Proof comment: the regular module denominator is obtained by smearing the ideal over `⊤`, so
  -- the powered ideal equality lifts immediately to the corresponding submodules.
  dsimp
  exact congrArg
    (fun I : Ideal (S' ⊗[R] S) ↦
      I • (⊤ : Submodule (S' ⊗[R] S) (S' ⊗[R] S)))
    (source_baseChange_diagonalIdeal_pow_eq_iComap_pow
      (R := R) (S := S) (S' := S') k)

/-- Helper for Lemma 10.150.8: the quotient comparison from Lemma `10.150.7` sends the class of a
pure tensor `a ⊗ b` to the class of `a ⊗ algebraMap b`. This isolates the generator computation
that will later be tensored with `M` in the principal-parts comparison. -/
theorem formallyEtale_tensorProduct_quotientMap_pow_apply_mk_tmul
    [Algebra.FormallyEtale S S'] (k : ℕ) (a : S') (b : S) :
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
        S' ⊗[R] S →+* S' ⊗[R] S')
    let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
    let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
    ((Ideal.quotientMap (Jdiag ^ (k + 1)) tensorComparison
        (Jdiag.le_comap_pow tensorComparison (k + 1))) :
      (S' ⊗[R] S) ⧸ (Icomap ^ (k + 1)) →+* (S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1)))
      (Ideal.Quotient.mk (Icomap ^ (k + 1)) ((a : S') ⊗ₜ[R] b)) =
        Ideal.Quotient.mk (Jdiag ^ (k + 1)) ((a : S') ⊗ₜ[R] (algebraMap S S' b)) := by
  -- Proof comment: this is the defining pure-tensor formula for the quotient map induced by the
  -- tensor-comparison ring hom from Lemma `10.150.7`.
  let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
    (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
      S' ⊗[R] S →+* S' ⊗[R] S')
  let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
  let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
  change
    (Ideal.quotientMap (Jdiag ^ (k + 1)) tensorComparison
      (Jdiag.le_comap_pow tensorComparison (k + 1)))
      (Ideal.Quotient.mk (Icomap ^ (k + 1)) ((a : S') ⊗ₜ[R] b)) =
        Ideal.Quotient.mk (Jdiag ^ (k + 1)) ((a : S') ⊗ₜ[R] (algebraMap S S' b))
  rw [Ideal.quotientMap_mk]
  simp [tensorComparison]

-- Proof sketch: identify both source and target principal-parts modules with quotient models from
-- Lemma `10.133.9`; after tensoring the source quotient by `S'`, Lemma `10.150.7` identifies the
-- resulting diagonal-thickening quotient with the target quotient over `S'`. The canonical map
-- `((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S')` is exactly the map
-- induced by these identifications, so it is bijective.
/-- Lemma 10.150.8 (1): if `S → S'` is formally étale and `M' = S' ⊗[S] M`, then the canonical map
`S' ⊗[S] P^k_{S/R}(M) → P^k_{S'/R}(M')` is bijective. -/
theorem principalPartsFormallyEtaleBaseChangeMap_bijective [Algebra.FormallyEtale S S']
    (k : ℕ) :
    Function.Bijective
      (((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S') :
        S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M)) :=
  -- Route correction: the ring-level diagonal-ideal transport is now closed by
  -- `source_baseChange_diagonalIdeal_eq_iComap`, so the old denominator-transport blocker is gone.
  -- The remaining source-faithful work is to bridge the honest left-factor comparison map
  -- `diagonal_tensor_module_baseChangeMap` proved above with the canonical right-factor
  -- base-change equivalence coming from tensor associativity, then package principal parts as the
  -- ring-quotient tensor models from Lemma `10.133.9`, tensor the quotient comparison from Lemma
  -- `10.150.7` with `M`, and finally identify the conjugated canonical base-change map on the
  -- generators `1 ⊗ [m]`.
  -- TODO: construct the missing right-factor-to-left-factor tensor comparison, build the source
  -- and target ring-quotient tensor equivalences, compose them with the quotient comparison from
  -- Lemma `10.150.7`, and finish by
  -- `tensor_principal_parts_linear_map_eq_of_apply_tmul_universal_differential_eq`.
  sorry

-- Proof sketch: represent `D` by the corresponding `S`-linear map `P^k_{S/R}(M) → N` using
-- Lemma `10.133.3`, tensor that map with `S'`, and transport it across
-- `principalPartsFormallyEtaleBaseChangeMap_bijective` to obtain an `S'`-linear map
-- `P^k_{S'/R}(S' ⊗[S] M) → S' ⊗[S] N`. Then apply the same representation theorem again to recover
-- the unique differential operator extending `D`.
/-- Lemma 10.150.8 (2): every order-`k` differential operator `D : M → N` extends uniquely to an
order-`k` differential operator `S' ⊗[S] M → S' ⊗[S] N` along a formally étale map `S → S'`. -/
theorem existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale
    [Algebra.FormallyEtale S S'] {D : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    ∃! D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N,
      D'.comp ((mk S S' S' M (1 : S')).restrictScalars R) =
          ((mk S S' S' N (1 : S')).restrictScalars R).comp D ∧
        D'.IsDifferentialOperatorOfOrder S' k := by
  let F :
      S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M) :=
    (((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S') :
      S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M))
  let e :
      S' ⊗[S] P^{k}_{S⁄R}(M) ≃ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M) :=
    LinearEquiv.ofBijective F
      (principalPartsFormallyEtaleBaseChangeMap_bijective
        (R := R) (S := S) (S' := S') (M := M) k)
  let Dsrc : differential_operators_order_le R S M k N := ⟨D, hD⟩
  let γ : P^{k}_{S⁄R}(M) →ₗ[S] N :=
    (principal_parts_linear_map_equiv_differential_operators R S M k N).symm Dsrc
  let γtensor : S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] S' ⊗[S] N :=
    LinearMap.baseChange S' γ
  let γ' : P^{k}_{S'⁄R}(S' ⊗[S] M) →ₗ[S'] S' ⊗[S] N :=
    γtensor.comp e.symm.toLinearMap
  let D'pack : differential_operators_order_le R S' (S' ⊗[S] M) k (S' ⊗[S] N) :=
    principal_parts_linear_map_equiv_differential_operators R S' (S' ⊗[S] M) k
      (S' ⊗[S] N) γ'
  refine ⟨D'pack.1, ?_, ?_⟩
  · constructor
    · -- Compare the extension candidate with `D` on the generators `m ↦ 1 ⊗ m`.
      ext m
      calc
        D'pack.1 ((mk S S' S' M (1 : S')) m) =
            γ' (principal_parts_universal_differential (R := R) (S := S')
              (M := S' ⊗[S] M) k ((mk S S' S' M (1 : S')) m)) := by
              simpa [D'pack, principal_parts_linear_map_equiv_apply_universal_differential]
        _ = γ' (F
              ((1 : S') ⊗ₜ[S]
                principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) := by
              rw [principalPartsFormallyEtaleBaseChangeMap_apply_tmul_universal_differential
                (R := R) (S := S) (S' := S') (M := M) k m]
        _ = γtensor
              ((1 : S') ⊗ₜ[S]
                principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
              exact congrArg γtensor <| by
                simpa [e, F] using
                  (LinearEquiv.symm_apply_apply e
                    ((1 : S') ⊗ₜ[S]
                      principal_parts_universal_differential
                        (R := R) (S := S) (M := M) k m))
        _ = ((mk S S' S' N (1 : S')) (D m)) := by
              change (LinearMap.baseChange S' γ)
                ((1 : S') ⊗ₜ[S]
                  principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
                ((mk S S' S' N (1 : S')) (D m))
              rw [LinearMap.baseChange_tmul]
              simpa using congrArg (fun n : N ↦ (1 : S') ⊗ₜ[S] n)
                (principal_parts_linear_map_equiv_symm_apply_universal_differential
                  (R := R) (S := S) (M := M) (Q := N) k Dsrc m)
    · -- The represented target operator has the declared differential-operator order bound.
      exact D'pack.2
  · intro E hE
    rcases hE with ⟨hEcomp, hEorder⟩
    let Epack : differential_operators_order_le R S' (S' ⊗[S] M) k (S' ⊗[S] N) := ⟨E, hEorder⟩
    let η : P^{k}_{S'⁄R}(S' ⊗[S] M) →ₗ[S'] S' ⊗[S] N :=
      (principal_parts_linear_map_equiv_differential_operators R S' (S' ⊗[S] M) k
        (S' ⊗[S] N)).symm Epack
    have hηcomp : η.comp F = γtensor := by
      -- Compare the two source-side maps on the generators `1 ⊗ [m]`.
      apply tensor_principal_parts_linear_map_eq_of_apply_tmul_universal_differential_eq
        (R := R) (S := S) (S' := S') (M := M) (Q := S' ⊗[S] N) k
      intro m
      calc
        η (F
            ((1 : S') ⊗ₜ[S]
              principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) =
            η (principal_parts_universal_differential (R := R) (S := S')
              (M := S' ⊗[S] M) k ((mk S S' S' M (1 : S')) m)) := by
                rw [principalPartsFormallyEtaleBaseChangeMap_apply_tmul_universal_differential
                  (R := R) (S := S) (S' := S') (M := M) k m]
        _ = E ((mk S S' S' M (1 : S')) m) := by
              simpa [η]
                using
                  (principal_parts_linear_map_equiv_symm_apply_universal_differential
                    (R := R) (S := S') (M := S' ⊗[S] M) (Q := S' ⊗[S] N) k Epack
                    ((mk S S' S' M (1 : S')) m))
        _ = (((mk S S' S' N (1 : S')).restrictScalars R).comp D) m := by
              exact LinearMap.congr_fun hEcomp m
        _ = ((mk S S' S' N (1 : S')) (D m)) := by
              rfl
        _ = γtensor
            ((1 : S') ⊗ₜ[S]
              principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
              symm
              change (LinearMap.baseChange S' γ)
                ((1 : S') ⊗ₜ[S]
                  principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
                ((mk S S' S' N (1 : S')) (D m))
              rw [LinearMap.baseChange_tmul]
              simpa using congrArg (fun n : N ↦ (1 : S') ⊗ₜ[S] n)
                (principal_parts_linear_map_equiv_symm_apply_universal_differential
                  (R := R) (S := S) (M := M) (Q := N) k Dsrc m)
    have hη : η = γ' := by
      -- Surjectivity of `F` lets us transport the source-side equality back to target principal
      -- parts.
      apply DFunLike.ext
      intro x
      obtain ⟨y, rfl⟩ :=
        (principalPartsFormallyEtaleBaseChangeMap_bijective
          (R := R) (S := S) (S' := S') (M := M) k).2 x
      calc
        η (F y) = γtensor y := by
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun hηcomp y
        _ = γ' (F y) := by
              symm
              exact congrArg γtensor <| by
                simpa [e, F] using (LinearEquiv.symm_apply_apply e y)
    let epp := principal_parts_linear_map_equiv_differential_operators
      R S' (S' ⊗[S] M) k (S' ⊗[S] N)
    have hEpack : Epack = D'pack := by
      apply epp.symm.injective
      calc
        epp.symm Epack = η := rfl
        _ = γ' := hη
        _ = epp.symm D'pack := by
              simp [D'pack, epp]
    simpa [Epack, D'pack] using congrArg Subtype.val hEpack

end
