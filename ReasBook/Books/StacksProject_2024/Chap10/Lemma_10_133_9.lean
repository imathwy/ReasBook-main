import Mathlib
import StacksProject_2024.Chap10.Lemma_10_133_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

local notation "P^{" k "}_{" S "⁄" R "}(" M ")" => principal_parts_module R S M k

noncomputable section

universe u

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

local notation "JppSubmodule" k =>
  (Submodule.restrictScalars S
    (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
      (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))

/-- Helper for Lemma 10.133.9: left multiplication on `S` as an `R`-linear endomorphism. -/
private def principal_parts_left_scalar_end : S →ₗ[R] S →ₗ[R] S where
  toFun s := DistribSMul.toLinearMap R S s
  map_add' := by
    intro s t
    -- Left multiplication is additive in the scalar.
    ext u
    simp [add_mul]
  map_smul' := by
    intro r s
    -- The scalar parameter depends `R`-linearly on `s`.
    ext u
    simp [Algebra.smul_def, mul_assoc]

/-- Helper for Lemma 10.133.9: the `S`-action on `M` viewed as an `R`-linear endomorphism-valued
map. -/
private def principal_parts_module_scalar_end : S →ₗ[R] M →ₗ[R] M where
  toFun s := DistribSMul.toLinearMap R M s
  map_add' := by
    intro s t
    -- The module action is additive in the scalar.
    ext m
    simp [add_smul]
  map_smul' := by
    intro r s
    -- Restricting scalars along `R → S` makes the `S`-action `R`-linear.
    ext m
    simpa [LinearMap.smul_apply, Algebra.smul_def, smul_smul, mul_assoc] using
      (smul_assoc r s m)

/-- Helper for Lemma 10.133.9: the natural action of `S ⊗[R] S` on `S ⊗[R] M` sending
`(a ⊗ b, s ⊗ m)` to `as ⊗ bm`. -/
private def principal_parts_tensor_action :
    S ⊗[R] S →ₗ[R] S ⊗[R] M →ₗ[R] S ⊗[R] M :=
  (TensorProduct.homTensorHomMap (RingHom.id R) S M S M).comp
    (TensorProduct.map principal_parts_left_scalar_end
      principal_parts_module_scalar_end)

/-- Helper for Lemma 10.133.9: the natural tensor action on pure tensors multiplies the first
factor and acts on the module factor. -/
private theorem principal_parts_tensor_action_tmul_tmul
    (a b s : S) (m : M) :
    principal_parts_tensor_action ((a : S) ⊗ₜ[R] b) ((s : S) ⊗ₜ[R] m) =
      ((a * s : S) ⊗ₜ[R] (b • m)) := by
  -- Both tensor lifts are designed so that pure tensors evaluate by the defining bilinear rule.
  simp [principal_parts_tensor_action, principal_parts_left_scalar_end,
    principal_parts_module_scalar_end]

/-- Helper for Lemma 10.133.9: the tensor action is unital. -/
private theorem principal_parts_tensor_action_one (x : S ⊗[R] M) :
    principal_parts_tensor_action (1 : S ⊗[R] S) x = x := by
  -- It is enough to check the formula on pure tensors and extend additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [principal_parts_tensor_action]
  · intro s m
    simpa [Algebra.TensorProduct.one_def] using
      principal_parts_tensor_action_tmul_tmul (R := R) (S := S) (M := M) 1 1 s m
  · intro x y hx hy
    simp [LinearMap.map_add, hx, hy]

/-- Helper for Lemma 10.133.9: the tensor action is multiplicative in the
`S ⊗[R] S`-variable. -/
private theorem principal_parts_tensor_action_mul
    (x y : S ⊗[R] S) (z : S ⊗[R] M) :
    principal_parts_tensor_action (x * y) z =
      principal_parts_tensor_action x (principal_parts_tensor_action y z) := by
  -- Reduce the multiplicativity check to pure tensors in both algebra variables and in the
  -- module input.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [principal_parts_tensor_action]
  · intro a b
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [principal_parts_tensor_action]
    · intro c d
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp [principal_parts_tensor_action]
      · intro s m
        simp [principal_parts_tensor_action_tmul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_assoc, smul_smul]
      · intro z w hz hw
        rw [LinearMap.map_add, LinearMap.map_add, hz, hw]
        exact ((principal_parts_tensor_action ((a : S) ⊗ₜ[R] b)).map_add
          (principal_parts_tensor_action ((c : S) ⊗ₜ[R] d) z)
          (principal_parts_tensor_action ((c : S) ⊗ₜ[R] d) w)).symm
    · intro y₁ y₂ hy₁ hy₂
      simp [mul_add, LinearMap.map_add, hy₁, hy₂]
  · intro x₁ x₂ hx₁ hx₂
    simp [add_mul, LinearMap.map_add, hx₁, hx₂]

/-- Helper for Lemma 10.133.9: restricting the tensor action along `s ↦ s ⊗ 1` is the usual left
`S`-action on `S ⊗[R] M`. -/
private theorem principal_parts_tensor_action_left_restrict
    (s : S) (x : S ⊗[R] M) :
    principal_parts_tensor_action ((s : S) ⊗ₜ[R] (1 : S)) x = s • x := by
  -- On pure tensors, the restriction multiplies only the first tensor factor.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [principal_parts_tensor_action]
  · intro t m
    simpa [principal_parts_tensor_action_tmul_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  · intro x y hx hy
    simp [LinearMap.map_add, smul_add, hx, hy]

/-- The canonical `S ⊗[R] S`-module structure on `S ⊗[R] M`. -/
local instance principal_parts_tensor_module : Module (S ⊗[R] S) (S ⊗[R] M) where
  smul x y := principal_parts_tensor_action x y
  zero_smul y := by
    -- The tensor action is linear in the algebra variable.
    exact LinearMap.congr_fun principal_parts_tensor_action.map_zero y
  smul_zero x := by
    -- For fixed `x`, the action is linear in the tensor-module variable.
    exact (principal_parts_tensor_action x).map_zero
  add_smul x y z := by
    -- Additivity in the algebra variable comes from the outer linear map.
    exact LinearMap.congr_fun (principal_parts_tensor_action.map_add x y) z
  smul_add x y z := by
    -- Additivity in the tensor-module variable comes from the inner linear map.
    exact (principal_parts_tensor_action x).map_add y z
  one_smul y := by
    -- The tensor action of `1 ⊗ 1` is the identity.
    simpa using principal_parts_tensor_action_one (R := R) (S := S) (M := M) y
  mul_smul x y z := by
    -- Multiplication in `S ⊗[R] S` matches composition of the induced endomorphisms.
    simpa using principal_parts_tensor_action_mul (R := R) (S := S) (M := M) x y z

/-- Restricting the `S ⊗[R] S`-action along `s ↦ s ⊗ 1` recovers the usual left `S`-action. -/
local instance principal_parts_tensor_isScalarTower :
    IsScalarTower S (S ⊗[R] S) (S ⊗[R] M) where
  smul_assoc s x y := by
    -- The restricted action is computed by `s ⊗ 1`, so again it suffices to check pure tensors.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [principal_parts_tensor_action]
    · intro a b
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp [principal_parts_tensor_action]
      · intro t m
        change
          principal_parts_tensor_action (((s * a : S) ⊗ₜ[R] b)) ((t : S) ⊗ₜ[R] m) =
            s • principal_parts_tensor_action ((a : S) ⊗ₜ[R] b) ((t : S) ⊗ₜ[R] m)
        rw [principal_parts_tensor_action_tmul_tmul, principal_parts_tensor_action_tmul_tmul]
        simp [TensorProduct.smul_tmul', smul_eq_mul, mul_assoc]
      · intro y z hy hz
        simp [smul_add, hy, hz]
    · intro x y hx hy
      simp [add_smul, hx, hy]

/-- The `S`-linear map sending the basis vector `[m]` to `1 ⊗ m`. -/
private abbrev principal_parts_free_to_tensor : (M →₀ S) →ₗ[S] (S ⊗[R] M) :=
  Finsupp.linearCombination S (fun m ↦ (1 : S) ⊗ₜ[R] m)

/-- Helper for Lemma 10.133.9: the `n`th diagonal-ideal power acting on `S ⊗[R] M`. -/
private abbrev diagonal_power_submodule (n : ℕ) : Submodule (S ⊗[R] S) (S ⊗[R] M) :=
  ((KaehlerDifferential.ideal R S) ^ n) • (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))

/-- Helper for Lemma 10.133.9: the ordered product of diagonal generators attached to a list of
scalars. -/
private def diagonal_product : List S → S ⊗[R] S
  | [] => 1
  | g :: l =>
      diagonal_product l * (((1 : S) ⊗ₜ[R] g - g ⊗ₜ[R] (1 : S)) : S ⊗[R] S)

/-- Helper for Lemma 10.133.9: every factor in `diagonal_product l` contributes one copy of the
diagonal ideal. -/
private theorem diagonal_product_mem_kaehler_ideal_pow :
    ∀ l : List S,
      diagonal_product (R := R) (S := S) l ∈
        (KaehlerDifferential.ideal R S) ^ l.length := by
  intro l
  induction l with
  | nil =>
      -- The empty product is `1`, which lies in the zeroth power of any ideal.
      simpa [diagonal_product]
  | cons g l ih =>
      -- Appending one diagonal generator contributes one more factor of the diagonal ideal.
      rw [diagonal_product, List.length_cons, pow_succ]
      exact Ideal.mul_mem_mul ih
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := R) g)

/-- Helper for Lemma 10.133.9: a diagonal generator acting on `1 ⊗ m` produces the corresponding
scalar-commutator difference. -/
private theorem diagonal_generator_smul_universal_tensor (g : S) (m : M) :
    ((((1 : S) ⊗ₜ[R] g - g ⊗ₜ[R] (1 : S)) : S ⊗[R] S) • ((1 : S) ⊗ₜ[R] m)) =
      ((1 : S) ⊗ₜ[R] (g • m)) - (g : S) ⊗ₜ[R] m := by
  -- Expand the diagonal generator into two pure tensors and evaluate both actions explicitly.
  change
    principal_parts_tensor_action
        (((1 : S) ⊗ₜ[R] g - g ⊗ₜ[R] (1 : S)) : S ⊗[R] S) ((1 : S) ⊗ₜ[R] m) =
      ((1 : S) ⊗ₜ[R] (g • m)) - (g : S) ⊗ₜ[R] m
  rw [LinearMap.map_sub, LinearMap.sub_apply, principal_parts_tensor_action_tmul_tmul,
    principal_parts_tensor_action_tmul_tmul]
  simp

/-- Helper for Lemma 10.133.9: the left `S`-action commutes with the diagonal-product action. -/
private theorem diagonal_product_smul_commute (l : List S) (g : S) (x : S ⊗[R] M) :
    g • (diagonal_product (R := R) (S := S) l • x) =
      diagonal_product (R := R) (S := S) l • (g • x) := by
  -- Rewrite the outer `S`-action as multiplication by `g ⊗ 1`, then commute that tensor factor
  -- past `diagonal_product l` inside the commutative algebra `S ⊗[R] S`.
  calc
    g • (diagonal_product (R := R) (S := S) l • x) =
        principal_parts_tensor_action ((g : S) ⊗ₜ[R] (1 : S))
          (diagonal_product (R := R) (S := S) l • x) := by
          symm
          exact principal_parts_tensor_action_left_restrict (R := R) (S := S) (M := M) g
            (diagonal_product (R := R) (S := S) l • x)
    _ =
        principal_parts_tensor_action ((g : S) ⊗ₜ[R] (1 : S))
          (principal_parts_tensor_action (diagonal_product (R := R) (S := S) l) x) := by
          rfl
    _ =
        principal_parts_tensor_action
          (((g : S) ⊗ₜ[R] (1 : S)) * diagonal_product (R := R) (S := S) l) x := by
          rw [principal_parts_tensor_action_mul]
    _ =
        principal_parts_tensor_action
          (diagonal_product (R := R) (S := S) l * ((g : S) ⊗ₜ[R] (1 : S))) x := by
          simp [mul_comm]
    _ =
        principal_parts_tensor_action (diagonal_product (R := R) (S := S) l)
          (principal_parts_tensor_action ((g : S) ⊗ₜ[R] (1 : S)) x) := by
          rw [principal_parts_tensor_action_mul]
    _ = diagonal_product (R := R) (S := S) l •
          principal_parts_tensor_action ((g : S) ⊗ₜ[R] (1 : S)) x := by
          rfl
    _ = diagonal_product (R := R) (S := S) l • (g • x) := by
          rw [principal_parts_tensor_action_left_restrict]

-- Proof sketch: the additive, base-ring linear, and iterated commutator generators defining
-- `principal_parts_relation_submodule k` map to elements of `J^(k+1)(S ⊗[R] M)`, so the map
-- `[m] ↦ class of 1 ⊗ m` descends to the principal-parts quotient.
/-- The principal-parts relations vanish in the tensor-product quotient model. -/
private theorem principal_parts_relation_submodule_le_tensor_quotient_ker (k : ℕ) :
    principal_parts_relation_submodule R S M k ≤
      LinearMap.ker
        (((JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ).comp
          (principal_parts_free_to_tensor : (M →₀ S) →ₗ[S] (S ⊗[R] M))) := by
  -- TODO: follow the source commutator recursion after unfolding the private imported generator,
  -- prove its image is `diagonal_product l • (1 ⊗ m)`, and conclude with
  -- `diagonal_product_mem_kaehler_ideal_pow`.
  sorry

/-- The map `P^k_{S/R}(M) → (S ⊗[R] M)/J^(k+1)(S ⊗[R] M)` induced by `m ↦ 1 ⊗ m`. -/
private def principal_parts_module_to_tensor_quotient (k : ℕ) :
    P^{k}_{S⁄R}(M) →ₗ[S] ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M))) :=
  (principal_parts_relation_submodule R S M k).liftQ
    (((JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ).comp
      (principal_parts_free_to_tensor : (M →₀ S) →ₗ[S] (S ⊗[R] M)))
    (principal_parts_relation_submodule_le_tensor_quotient_ker k)

/-- Helper for Lemma 10.133.9: the forward quotient map sends the universal generator of
`P^k_{S/R}(M)` to the class of `1 ⊗ m`. -/
private theorem principal_parts_module_to_tensor_quotient_universal_differential
    (k : ℕ) (m : M) :
    principal_parts_module_to_tensor_quotient k (principal_parts_universal_differential k m) =
      (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ ((1 : S) ⊗ₜ[R] m) := by
  -- Both quotient constructions are defined on the same generator `[m]`.
  have hmkQ := LinearMap.congr_fun
    ((principal_parts_relation_submodule R S M k).liftQ_mkQ
      (((JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ).comp
        (principal_parts_free_to_tensor : (M →₀ S) →ₗ[S] (S ⊗[R] M)))
      (principal_parts_relation_submodule_le_tensor_quotient_ker k))
    (Finsupp.single m (1 : S))
  simpa [principal_parts_module_to_tensor_quotient, principal_parts_universal_differential,
    principal_parts_free_to_tensor, Finsupp.linearCombination_single] using hmkQ

/-- Helper for Lemma 10.133.9: tensor-lift an `R`-linear map `M → N` to an `S`-linear map
`S ⊗[R] M → N`. -/
private abbrev tensor_lift_of
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : M →ₗ[R] N) : S ⊗[R] M →ₗ[S] N :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight D)

/-- The `S`-linear map sending `s ⊗ m` to `s • [m]` in `P^k_{S/R}(M)`. -/
private abbrev tensor_to_principal_parts_module (k : ℕ) :
    S ⊗[R] M →ₗ[S] P^{k}_{S⁄R}(M) :=
  tensor_lift_of (R := R) (S := S) (M := M)
    (principal_parts_universal_differential k)

/-- Helper for Lemma 10.133.9: the universal differential operator into principal parts has order
at most `k`. -/
private theorem principal_parts_universal_differential_isDifferentialOperatorOfOrder
    (k : ℕ) :
    (principal_parts_universal_differential (R := R) (S := S) (M := M) k).IsDifferentialOperatorOfOrder S k := by
  -- The representing equivalence sends the identity map on `P^k_{S/R}(M)` to the universal
  -- differential operator.
  let e := principal_parts_linear_map_equiv_differential_operators R S M k (P^{k}_{S⁄R}(M))
  have hId :
      (((e (LinearMap.id : P^{k}_{S⁄R}(M) →ₗ[S] P^{k}_{S⁄R}(M))) :
          differential_operators_order_le R S M k (P^{k}_{S⁄R}(M))).1).IsDifferentialOperatorOfOrder S k := by
    change
      (((e (LinearMap.id : P^{k}_{S⁄R}(M) →ₗ[S] P^{k}_{S⁄R}(M))) :
          differential_operators_order_le R S M k (P^{k}_{S⁄R}(M))).1) ∈
        differential_operators_order_le_submodule R S M k (P^{k}_{S⁄R}(M))
    exact
      ((e (LinearMap.id : P^{k}_{S⁄R}(M) →ₗ[S] P^{k}_{S⁄R}(M))) :
        differential_operators_order_le R S M k (P^{k}_{S⁄R}(M))).2
  simpa [e] using hId

/-- Helper for Lemma 10.133.9: multiplying by a diagonal generator in `S ⊗[R] S` and then
applying the tensor lift attached to `D` is the same as tensor-lifting the scalar commutator of
`D` with that scalar. -/
private theorem tensor_lift_diagonal_generator_eq_scalarCommutator
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : M →ₗ[R] N) (g : S) (x : S ⊗[R] M) :
    tensor_lift_of (R := R) (S := S) (M := M) D
        ((((1 : S) ⊗ₜ[R] g - g ⊗ₜ[R] (1 : S)) : S ⊗[R] S) • x) =
      tensor_lift_of (R := R) (S := S) (M := M) (D.scalarCommutator g) x := by
  -- The diagonal generator action and the tensor lift are both additive in `x`, so pure tensors
  -- suffice.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro s m
    change
    tensor_lift_of (R := R) (S := S) (M := M) D
          (principal_parts_tensor_action
            (((1 : S) ⊗ₜ[R] g - g ⊗ₜ[R] (1 : S)) : S ⊗[R] S) ((s : S) ⊗ₜ[R] m)) =
        tensor_lift_of (R := R) (S := S) (M := M) (D.scalarCommutator g) ((s : S) ⊗ₜ[R] m)
    rw [LinearMap.map_sub, LinearMap.sub_apply, principal_parts_tensor_action_tmul_tmul,
      principal_parts_tensor_action_tmul_tmul]
    rw [LinearMap.map_sub]
    simp [LinearMap.scalarCommutator_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      smul_smul, mul_assoc, mul_left_comm, mul_comm]
  · intro x y hx hy
    simp [smul_add, LinearMap.map_add, hx, hy]

/-- Helper for Lemma 10.133.9: composing `principal_parts_free_to_tensor` with the tensor lift
back to principal parts recovers the presentation quotient map. -/
private theorem tensor_to_principal_parts_module_comp_principal_parts_free_to_tensor
    (k : ℕ) :
    (tensor_to_principal_parts_module k).comp
        (principal_parts_free_to_tensor : (M →₀ S) →ₗ[S] (S ⊗[R] M)) =
      (principal_parts_relation_submodule R S M k).mkQ := by
  apply Finsupp.lhom_ext
  intro m s
  have hsingle : (Finsupp.single m s : M →₀ S) = s • Finsupp.single m (1 : S) := by
    ext a
    by_cases h : a = m
    · subst h
      simp
    · simp [h]
  -- The free module is generated by single basis vectors, and the tensor lift sends `1 ⊗ m`
  -- back to the universal class of `m`.
  calc
    ((tensor_to_principal_parts_module k).comp
        (principal_parts_free_to_tensor : (M →₀ S) →ₗ[S] (S ⊗[R] M)))
        (Finsupp.single m s) =
      (tensor_to_principal_parts_module k) (s • ((1 : S) ⊗ₜ[R] m)) := by
        simp [principal_parts_free_to_tensor, Finsupp.linearCombination_single]
    _ = s • principal_parts_universal_differential k m := by
      rw [LinearMap.map_smul]
      simp [tensor_to_principal_parts_module, tensor_lift_of]
    _ = (principal_parts_relation_submodule R S M k).mkQ (Finsupp.single m s) := by
      change
        s • (principal_parts_relation_submodule R S M k).mkQ (Finsupp.single m (1 : S)) =
          (principal_parts_relation_submodule R S M k).mkQ (Finsupp.single m s)
      rw [← LinearMap.map_smul, hsingle]

-- Route correction: the remaining proof should follow the source order-induction on differential
-- operator order, using `tensor_lift_diagonal_generator_eq_scalarCommutator` and span induction
-- over `KaehlerDifferential.submodule_span_range_eq_ideal`.
/-- The tensor-product map to principal parts kills `J^(k+1)(S ⊗[R] M)`. -/
private theorem principal_parts_tensor_submodule_le_module_ker (k : ℕ) :
    (JppSubmodule k : Submodule S (S ⊗[R] M)) ≤
      LinearMap.ker (tensor_to_principal_parts_module k) := by
  -- TODO: prove the general source-faithful order-induction statement for tensor lifts and
  -- specialize it to `principal_parts_universal_differential`.
  sorry

/-- The inverse map `(S ⊗[R] M)/J^(k+1)(S ⊗[R] M) → P^k_{S/R}(M)`. -/
private def tensor_quotient_to_principal_parts_module (k : ℕ) :
    ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M))) →ₗ[S] P^{k}_{S⁄R}(M) :=
  (JppSubmodule k : Submodule S (S ⊗[R] M)).liftQ
    (tensor_to_principal_parts_module k)
    (principal_parts_tensor_submodule_le_module_ker k)

/-- Helper for Lemma 10.133.9: the forward quotient map composed with the tensor lift agrees with
the tensor-product quotient map on pure tensors, hence on all tensors. -/
private theorem principal_parts_module_to_tensor_quotient_comp_tensor_to_principal_parts_module
    (k : ℕ) :
    (principal_parts_module_to_tensor_quotient k).comp
        (tensor_to_principal_parts_module k) =
      (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ := by
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro s m
    -- Evaluate both `S`-linear maps on a pure tensor.
    calc
      ((principal_parts_module_to_tensor_quotient k).comp
          (tensor_to_principal_parts_module k)) (s ⊗ₜ[R] m) =
        principal_parts_module_to_tensor_quotient k (s • principal_parts_universal_differential k m) := by
          simp [LinearMap.comp_apply, tensor_to_principal_parts_module, tensor_lift_of]
      _ = s • principal_parts_module_to_tensor_quotient k
            (principal_parts_universal_differential k m) := by
          rw [LinearMap.map_smul]
      _ = s • (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ ((1 : S) ⊗ₜ[R] m) := by
          rw [principal_parts_module_to_tensor_quotient_universal_differential]
      _ = (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ (s ⊗ₜ[R] m) := by
          have hsmul : s • ((1 : S) ⊗ₜ[R] m) = (s : S) ⊗ₜ[R] m := by
            simpa using TensorProduct.smul_tmul' (R := R) s (1 : S) m
          change
            (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ (s • ((1 : S) ⊗ₜ[R] m)) =
              (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ (s ⊗ₜ[R] m)
          simpa [hsmul]
  · intro x y hx hy
    simpa [LinearMap.map_add, hx, hy]

-- Proof sketch: both composites are determined on the generators `[m]` of the principal-parts
-- presentation, where they are tautologically the identity.
/-- The tensor-product quotient map followed by its inverse recovers `P^k_{S/R}(M)`. -/
private theorem tensor_quotient_to_principal_parts_module_comp_principal_parts_module_to_tensor_quotient
    (k : ℕ) :
    (tensor_quotient_to_principal_parts_module k).comp
        (principal_parts_module_to_tensor_quotient k) =
      (LinearMap.id : P^{k}_{S⁄R}(M) →ₗ[S] P^{k}_{S⁄R}(M)) := by
  have hcomp :
      ((tensor_quotient_to_principal_parts_module k).comp
          (principal_parts_module_to_tensor_quotient k)).comp
        (principal_parts_relation_submodule R S M k).mkQ =
      (principal_parts_relation_submodule R S M k).mkQ := by
    -- After precomposing with the surjective presentation quotient map, both composites reduce to
    -- the explicit map on free generators.
    rw [LinearMap.comp_assoc, principal_parts_module_to_tensor_quotient]
    rw [((principal_parts_relation_submodule R S M k).liftQ_mkQ
      (((JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ).comp
        (principal_parts_free_to_tensor : (M →₀ S) →ₗ[S] (S ⊗[R] M)))
      (principal_parts_relation_submodule_le_tensor_quotient_ker k))]
    rw [← LinearMap.comp_assoc, tensor_quotient_to_principal_parts_module]
    rw [((JppSubmodule k : Submodule S (S ⊗[R] M)).liftQ_mkQ
      (tensor_to_principal_parts_module k)
      (principal_parts_tensor_submodule_le_module_ker k))]
    exact tensor_to_principal_parts_module_comp_principal_parts_free_to_tensor k
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (principal_parts_relation_submodule R S M k) q
  simpa using LinearMap.congr_fun hcomp x

-- Proof sketch: both composites are determined on pure tensors `s ⊗ m`; the induced maps agree
-- there with the identity after passing to the quotient by `J^(k+1)`.
/-- The inverse map followed by the tensor-product quotient map recovers the quotient model. -/
private theorem principal_parts_module_to_tensor_quotient_comp_tensor_quotient_to_principal_parts_module
    (k : ℕ) :
    (principal_parts_module_to_tensor_quotient k).comp
        (tensor_quotient_to_principal_parts_module k) =
      (LinearMap.id :
        ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M))) →ₗ[S]
          ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M)))) := by
  have hcomp :
      ((principal_parts_module_to_tensor_quotient k).comp
          (tensor_quotient_to_principal_parts_module k)).comp
        (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ =
      (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ := by
    -- Precomposing with the quotient map exposes the pure-tensor computation proved above.
    rw [LinearMap.comp_assoc, tensor_quotient_to_principal_parts_module]
    rw [((JppSubmodule k : Submodule S (S ⊗[R] M)).liftQ_mkQ
      (tensor_to_principal_parts_module k)
      (principal_parts_tensor_submodule_le_module_ker k))]
    exact principal_parts_module_to_tensor_quotient_comp_tensor_to_principal_parts_module k
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (JppSubmodule k : Submodule S (S ⊗[R] M)) q
  simpa using LinearMap.congr_fun hcomp x

/-- Lemma 10.133.9: the `k`th module of principal parts `P^k_{S/R}(M)` is canonically isomorphic to
`(S ⊗[R] M)/J^(k + 1)(S ⊗[R] M)` where `J = ker(S ⊗[R] S → S)` and `S` acts through
multiplication by `s ⊗ 1`. -/
noncomputable def principal_parts_module_equiv_tensor_quotient (k : ℕ) :
    P^{k}_{S⁄R}(M) ≃ₗ[S]
      ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M))) :=
  LinearEquiv.ofLinear
    (principal_parts_module_to_tensor_quotient k)
    (tensor_quotient_to_principal_parts_module k)
    (principal_parts_module_to_tensor_quotient_comp_tensor_quotient_to_principal_parts_module k)
    (tensor_quotient_to_principal_parts_module_comp_principal_parts_module_to_tensor_quotient k)

-- Proof sketch: the forward map is induced from the free-module map `[m] ↦ 1 ⊗ m`, so evaluating it
-- on the universal class of `m` gives exactly the class of `1 ⊗ m` in the tensor-product quotient.
/-- Under the canonical equivalence, the universal differential operator corresponds to the class of
`1 ⊗ m` in the tensor-product quotient model. -/
theorem principal_parts_module_equiv_tensor_quotient_universal_differential (k : ℕ) (m : M) :
    principal_parts_module_equiv_tensor_quotient k
        (principal_parts_universal_differential k m) =
      (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ ((1 : S) ⊗ₜ[R] m) := by
  -- The equivalence acts by its forward linear map, already computed on universal generators.
  exact principal_parts_module_to_tensor_quotient_universal_differential k m
