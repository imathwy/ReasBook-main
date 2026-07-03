import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_133_9 (from Chap10) -/
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

/-! ### Lemma_10_133_10 (from Chap10) -/
noncomputable section

universe u v

open LinearMap

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: algebraic de Rham differentials on exterior powers of Kähler differentials;
* sampled owner API: `LinearMap.IsDifferentialOperatorOfOrder`, `deRhamDifferentialFamily`,
  `isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily`, and `KaehlerDifferential.D`;
* owner abstraction: the canonical recursive family `deRhamDifferentialFamily A B`;
* primitive data vs. derived API: the primitive object is the canonical de Rham differential
  family from Lemma `10.132.2`, while “the `p`th differential is first-order” is derived
  theorem-level API and should be stated directly for that owner rather than via a parallel pair of
  parameters `δ` and `hd`.
-/

variable (A B)

/-- Helper for Lemma 10.133.10: in degree `0`, the scalar commutator of the de Rham differential
is multiplication by the exact form `d b`. -/
theorem de_rham_degree_zero_scalar_commutator_apply
    (b x : B) :
    (deRhamDifferentialFamily A B 0).scalarCommutator b x =
      x • KaehlerDifferential.D A B b :=
  -- TODO: rewrite degree `0` forms to `B`, expand `LinearMap.scalarCommutator_apply`, and use the
  -- Leibniz rule for `KaehlerDifferential.D A B` to isolate the surviving `x • d b` term.
  sorry

/-- Helper for Lemma 10.133.10: the degree-zero de Rham differential is a first-order
differential operator. -/
theorem de_rham_degree_zero_is_order_one :
    (deRhamDifferentialFamily A B 0).IsDifferentialOperatorOfOrder B 1 :=
  -- TODO: after the previous commutator formula is stabilized, rewrite the order-zero condition
  -- for `Ω^[0][B⁄A] = B` and check the resulting `B`-linearity by a one-line scalar-associativity
  -- simplification.
  sorry

/-- Helper for Lemma 10.133.10: on basic degree-one forms, the scalar commutator retains only the
leftmost exact factor `d b`. -/
theorem de_rham_degree_one_scalar_commutator_smul_D
    (b c x : B) :
    (deRhamDifferentialFamily A B 1).scalarCommutator b (c • KaehlerDifferential.D A B x) =
      c • exteriorPower.ιMulti B 2
        (Fin.cases (KaehlerDifferential.D A B b) fun _ ↦ KaehlerDifferential.D A B x) :=
  -- TODO: expand the scalar commutator, rewrite the two degree-one differentials by
  -- `hd.degree_one`, apply the Leibniz rule to `d (b * c)`, and cancel the `b • d c ∧ d x`
  -- contribution via multilinearity of `exteriorPower.ιMulti`.
  sorry

/-- Helper for Lemma 10.133.10: on basic higher-degree forms, the scalar commutator again retains
only the new leftmost exact factor `d b`. -/
theorem de_rham_higher_scalar_commutator_smul_iMulti
    (q : ℕ) (b c : B) (fs : Fin (q + 2) → B) :
    (deRhamDifferentialFamily A B (q + 2)).scalarCommutator b
        (c • exteriorPower.ιMulti B (q + 2) (fun i ↦ KaehlerDifferential.D A B (fs i))) =
      c • exteriorPower.ιMulti B (q + 3)
        (Fin.cases (KaehlerDifferential.D A B b) fun i ↦ KaehlerDifferential.D A B (fs i)) :=
  -- TODO: follow the same commutator-plus-Leibniz calculation as in degree `1`, but with
  -- `hd.higher` and the higher exterior-power multilinearity on the leftmost wedge factor.
  sorry

/-- Helper for Lemma 10.133.10: every positive-degree de Rham differential is first-order. -/
theorem de_rham_positive_degree_is_order_one
    (q : ℕ) :
    (deRhamDifferentialFamily A B (q + 1)).IsDifferentialOperatorOfOrder B 1 :=
  -- TODO: use the two generator calculations above and a `B`-span induction on exact one-forms,
  -- respectively basic wedges of exact one-forms, to show each scalar commutator is order `0`.
  sorry

/-- Lemma 10.133.10: in the canonical relative de Rham complex of `B` over `A`, the universal
derivation and all positive-degree de Rham differentials are differential operators of order `1`.
-/
-- Proof sketch: for degree `0`, expand the scalar commutator of `δ 0` and use
-- `IsExteriorPowerDeRhamDifferential.degree_zero` to identify it with the universal derivation.
-- For higher degrees, evaluate the commutator of `δ (i + 1)` on basic forms and use the de Rham
-- rule encoded by `IsExteriorPowerDeRhamDifferential` to see that each commutator is `B`-linear,
-- hence order `0`.
theorem de_rham_differentials_are_order_one_differential_operators
    (p : ℕ) :
    (deRhamDifferentialFamily A B p).IsDifferentialOperatorOfOrder B 1 := by
  cases p with
  | zero =>
      -- Degree `0` is the universal derivation, handled directly from Leibniz.
      exact de_rham_degree_zero_is_order_one (A := A) (B := B)
  | succ q =>
      -- Positive degrees are controlled by the scalar commutator on basic generators.
      exact de_rham_positive_degree_is_order_one (A := A) (B := B) q

end

/-! ### Lemma_10_133_11 (from Chap10) -/
/-
Domain triage:
* primary domain: relative differential operators on modules over a generated algebra, controlled
  by the scalar-commutator owner predicate;
* sampled owner API:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LinearMap.isDifferentialOperatorOfOrder_succ_iff`,
  `LinearMap.isDifferentialOperatorOfOrder_comp`,
  `differential_operators_order_le_submodule`;
* best owner abstraction: the order-`k` differential-operator submodule together with the induced
  subalgebra of scalars whose commutator with `D` has order `k`;
* primitive data: an `A`-linear map `D` and the recursive scalar-commutator condition;
* derived API: the generator criterion below, obtained by proving the good scalars form an
  `A`-subalgebra and then applying `Algebra.adjoin_le`.

Source/core/bridge triage:
* source-facing: the Stacks-project generator criterion for checking order `k + 1`;
* core/canonical: `LinearMap.IsDifferentialOperatorOfOrder` and
  `differential_operators_order_le_submodule`;
* bridge/view: none beyond the internal use of the order-bounded submodule packaging.
-/

universe u

section

variable {A : Type u} {B : Type u} {I : Type u} {M : Type u} {N : Type u}
variable [CommSemiring A] [CommSemiring B] [Algebra A B]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module B M] [Module B N] [Module A M] [Module A N]
variable [IsScalarTower A B M] [IsScalarTower A B N]

namespace LinearMap

-- Proof sketch: let `S` be the set of `g : B` such that `D.scalarCommutator g` has order `k`.
-- Using the commutator formulas for `g + g'` and `g * g'`, together with stability under sums
-- and composition from the differential-operator calculus, `S` is an `A`-subalgebra of `B`.
-- Since `S` contains every generator `g i`, the hypothesis `Algebra.adjoin A (Set.range g) = ⊤`
-- implies `S = ⊤`, so the recursive characterization of order `k + 1` holds for all `g : B`.
/-- Lemma 10.133.11: if `g : I → B` generates `B` as an `A`-algebra, then an `A`-linear map
`D : M → N` is a differential operator of order `k + 1` as soon as each scalar commutator with a
generator `g i` is a differential operator of order `k`. -/
theorem isDifferentialOperatorOfOrder_succ_of_generator_scalarCommutator
    (g : I → B) (hgen : Algebra.adjoin A (Set.range g) = ⊤) {D : M →ₗ[A] N} {k : ℕ}
    (hD : ∀ i : I,
      (D.scalarCommutator (g i)).IsDifferentialOperatorOfOrder B k) :
    D.IsDifferentialOperatorOfOrder B (k + 1) := by
  rw [isDifferentialOperatorOfOrder_succ_iff D k]
  let orderLe : Submodule B (M →ₗ[A] N) := differential_operators_order_le_submodule A B M k N
  have lsmul_isDifferentialOperatorOfOrder_zero {P : Type u}
      [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P] (b : B) :
      (Algebra.lsmul A A P b : Module.End A P).IsDifferentialOperatorOfOrder B 0 := by
    rw [isDifferentialOperatorOfOrder_zero_iff]
    intro c m
    simp [smul_smul, mul_comm]
  let good : Subalgebra A B :=
    { carrier := { b | D.scalarCommutator b ∈ orderLe }
      algebraMap_mem' := by
        intro a
        have hcomm : D.scalarCommutator (algebraMap A B a) = 0 := by
          ext m
          simp
        change D.scalarCommutator (algebraMap A B a) ∈ orderLe
        rw [hcomm]
        exact orderLe.zero_mem
      add_mem' := by
        intro x y hx hy
        have hxy : D.scalarCommutator (x + y) = D.scalarCommutator x + D.scalarCommutator y := by
          ext m
          simp [sub_eq_add_neg, add_smul, map_add]
          ac_rfl
        simpa [hxy] using orderLe.add_mem hx hy
      mul_mem' := by
        intro x y hx hy
        have hx' : (D.scalarCommutator x).IsDifferentialOperatorOfOrder B k := hx
        have hy' : (D.scalarCommutator y).IsDifferentialOperatorOfOrder B k := hy
        let Ly : Module.End A M := Algebra.lsmul A A M y
        let Lx : Module.End A N := Algebra.lsmul A A N x
        have hy0 : Ly.IsDifferentialOperatorOfOrder B 0 := by
          simpa [Ly] using lsmul_isDifferentialOperatorOfOrder_zero y
        have hx0 : Lx.IsDifferentialOperatorOfOrder B 0 := by
          simpa [Lx] using lsmul_isDifferentialOperatorOfOrder_zero x
        have hleft : (D.scalarCommutator x).comp (Algebra.lsmul A A M y : Module.End A M) ∈ orderLe := by
          let commx : M →ₗ[A] N := D.scalarCommutator x
          have hcommx : commx.IsDifferentialOperatorOfOrder B k := by
            simpa [commx] using hx'
          have hleft' :
              (commx.comp Ly).IsDifferentialOperatorOfOrder B (0 + k) :=
            isDifferentialOperatorOfOrder_comp hy0 hcommx
          simpa [commx, Ly, zero_add] using
            hleft'
        have hright : (Algebra.lsmul A A N x : Module.End A N).comp (D.scalarCommutator y) ∈ orderLe := by
          let commy : M →ₗ[A] N := D.scalarCommutator y
          have hcommy : commy.IsDifferentialOperatorOfOrder B k := by
            simpa [commy] using hy'
          have hright' :
              (Lx.comp commy).IsDifferentialOperatorOfOrder B (k + 0) :=
            isDifferentialOperatorOfOrder_comp hcommy hx0
          simpa [commy, Lx, Nat.add_zero] using
            hright'
        have hxy :
            D.scalarCommutator (x * y) =
              (D.scalarCommutator x).comp (Algebra.lsmul A A M y : Module.End A M) +
                (Algebra.lsmul A A N x : Module.End A N).comp (D.scalarCommutator y) := by
          ext m
          simp [sub_eq_add_neg, mul_smul]
        simpa [hxy] using orderLe.add_mem hleft hright }
  have hgood : Algebra.adjoin A (Set.range g) ≤ good := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    exact hD i
  have htop : (⊤ : Subalgebra A B) ≤ good := by
    rw [← hgen]
    exact hgood
  intro b
  simpa [good] using htop (show b ∈ (⊤ : Subalgebra A B) from by simp)

end LinearMap

end

/-! ### Lemma_10_133_12 (from Chap10) -/
universe u

section

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

variable {A : Type u} {B : Type u} {M : Type u} {N : Type u}
variable [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B)
variable [AddCommGroup M] [AddCommGroup N]
variable [Module B M] [Module B N] [Module A M] [Module A N]
variable [IsScalarTower A B M] [IsScalarTower A B N]

/- Domain-style sampling for Lemma 10.133.12:
- primary domain: relative differential operators under localization of the ambient algebra;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LocalizedModule.equivTensorProduct`,
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`;
- best owner abstraction: the canonical base-change extension theorem for formally étale maps,
  specialized here to the localization map `B → Localization S`;
- primitive data: an `A`-linear map `D : M →ₗ[A] N` together with the owner predicate
  `D.IsDifferentialOperatorOfOrder B k`;
- derived API: the localization-specific extension/uniqueness statement, obtained by transporting
  the formally étale base-change owner along `LocalizedModule.equivTensorProduct`.

Source/core/bridge triage:
- `source-facing`: the localization statement in the wording of Lemma 10.133.12;
- `core/canonical`: the later chapter owner
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`;
- `bridge/view`: the identification of localized modules with tensor-product base change via
  `LocalizedModule.equivTensorProduct`. -/

-- Proof sketch: specialize the canonical formally étale base-change extension theorem to the
-- localization map `B → Localization S`, then transport the resulting tensor-product operator
-- across `LocalizedModule.equivTensorProduct`. The extension identity is checked on generators
-- `m ↦ m/1`, and the order condition is preserved because the transport maps are
-- `Localization S`-linear, hence order `0`.
/-- Helper for Lemma 10.133.12: after the localization/tensor-product identification, the
canonical map `m ↦ m/1` matches the tensor-product generator map `m ↦ 1 ⊗ m`. -/
lemma localizedModule_equivTensorProduct_comp_mkLinearMap
    (P : Type u) [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P] :
    (((LocalizedModule.equivTensorProduct S P).restrictScalars A).toLinearMap).comp
        ((LocalizedModule.mkLinearMap S P).restrictScalars A) =
      (TensorProduct.AlgebraTensorModule.mk B (Localization S) (Localization S) P
          (1 : Localization S)).restrictScalars A := by
  ext p
  -- Both sides send `p` to the tensor `1 ⊗ p`.
  simp [LinearMap.comp_apply, Localization.mk_one_eq_algebraMap]

/-- Helper for Lemma 10.133.12: a `Localization S`-linear map is an order-`0` differential
operator after restricting scalars to `A`. -/
lemma restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
    {P Q : Type u} [AddCommGroup P] [AddCommGroup Q]
    [Module (Localization S) P] [Module (Localization S) Q]
    [Module A P] [Module A Q]
    [IsScalarTower A (Localization S) P] [IsScalarTower A (Localization S) Q]
    (f : P →ₗ[Localization S] Q) :
    (f.restrictScalars A).IsDifferentialOperatorOfOrder (Localization S) 0 := by
  -- Order `0` means commuting with every scalar from `Localization S`.
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro g p
  simpa using f.map_smul g p

/-- Lemma 10.133.12: an `A`-linear differential operator `D : M → N` of order `k` extends
uniquely to an `A`-linear differential operator `S⁻¹M → S⁻¹N` of the same order. -/
lemma existsUnique_localizedModule_extension_of_isDifferentialOperatorOfOrder
    {D : M →ₗ[A] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder B k) :
    ∃! E : LocalizedModule S M →ₗ[A] LocalizedModule S N,
      E.comp ((LocalizedModule.mkLinearMap S M).restrictScalars A) =
          ((LocalizedModule.mkLinearMap S N).restrictScalars A).comp D ∧
        E.IsDifferentialOperatorOfOrder (Localization S) k := by
  let eM : LocalizedModule S M ≃ₗ[A] Localization S ⊗[B] M :=
    (LocalizedModule.equivTensorProduct S M).restrictScalars A
  let eN : LocalizedModule S N ≃ₗ[A] Localization S ⊗[B] N :=
    (LocalizedModule.equivTensorProduct S N).restrictScalars A
  let tensorMkM : M →ₗ[A] Localization S ⊗[B] M :=
    (TensorProduct.AlgebraTensorModule.mk B (Localization S) (Localization S) M
      (1 : Localization S)).restrictScalars A
  let tensorMkN : N →ₗ[A] Localization S ⊗[B] N :=
    (TensorProduct.AlgebraTensorModule.mk B (Localization S) (Localization S) N
      (1 : Localization S)).restrictScalars A
  let EfromTensor :
      (Localization S ⊗[B] M →ₗ[A] Localization S ⊗[B] N) →
        LocalizedModule S M →ₗ[A] LocalizedModule S N :=
    fun F => eN.symm.toLinearMap.comp (F.comp eM.toLinearMap)
  let tensorOfLocalized :
      (LocalizedModule S M →ₗ[A] LocalizedModule S N) →
        Localization S ⊗[B] M →ₗ[A] Localization S ⊗[B] N :=
    fun F => eN.toLinearMap.comp (F.comp eM.symm.toLinearMap)
  haveI : Algebra.FormallyEtale B (Localization S) :=
    Algebra.FormallyEtale.of_isLocalization S
  rcases
      existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale
        (R := A) (S := B) (S' := Localization S) (M := M) (N := N) hD with
    ⟨Dtensor, hDtensor, hDtensor_unique⟩
  let E : LocalizedModule S M →ₗ[A] LocalizedModule S N := EfromTensor Dtensor
  refine ⟨E, ?_, ?_⟩
  constructor
  · -- Push the extension identity to the tensor side, where it is exactly the owner theorem.
    ext m
    apply eN.injective
    have hMkM :
        eM (LocalizedModule.mk m 1) = tensorMkM m := by
      simpa [LocalizedModule.mkLinearMap_apply, eM, tensorMkM, LinearMap.comp_apply] using
        DFunLike.congr_fun
          (localizedModule_equivTensorProduct_comp_mkLinearMap
            (A := A) (B := B) (S := S) M) m
    have hMkN :
        eN ((LocalizedModule.mkLinearMap S N) (D m)) = tensorMkN (D m) := by
      simpa [eN, tensorMkN, LinearMap.comp_apply] using
        DFunLike.congr_fun
          (localizedModule_equivTensorProduct_comp_mkLinearMap
            (A := A) (B := B) (S := S) N) (D m)
    calc
      eN ((E.comp ((LocalizedModule.mkLinearMap S M).restrictScalars A)) m)
          = Dtensor (tensorMkM m) := by
              suffices hEval : Dtensor (eM (LocalizedModule.mk m 1)) = Dtensor (tensorMkM m) by
                simpa [E, EfromTensor, eN, LocalizedModule.mkLinearMap_apply,
                  LinearMap.comp_apply] using hEval
              rw [hMkM]
      _ = tensorMkN (D m) := by
            simpa [tensorMkM, tensorMkN, LinearMap.comp_apply] using
              DFunLike.congr_fun hDtensor.1 m
      _ = eN (((LocalizedModule.mkLinearMap S N).restrictScalars A).comp D m) := by
            rw [LinearMap.comp_apply]
            exact hMkN.symm
  · -- The transport maps are `Localization S`-linear, hence order `0`, so the order bound
    -- survives conjugation.
    have heM_zero :
        eM.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eM] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S M).toLinearMap)
    have heNsymm_zero :
        eN.symm.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eN] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S N).symm.toLinearMap)
    have hmid :
        (Dtensor.comp eM.toLinearMap).IsDifferentialOperatorOfOrder (Localization S) k := by
      simpa [eM, Nat.zero_add] using
        LinearMap.isDifferentialOperatorOfOrder_comp heM_zero hDtensor.2
    simpa [E, EfromTensor, Nat.add_zero] using
      LinearMap.isDifferentialOperatorOfOrder_comp hmid heNsymm_zero
  · intro F hF
    rcases hF with ⟨hF_extends, hF_order⟩
    let Ftensor : Localization S ⊗[B] M →ₗ[A] Localization S ⊗[B] N :=
      tensorOfLocalized F
    have heMsymm_zero :
        eM.symm.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eM] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S M).symm.toLinearMap)
    have heN_zero :
        eN.toLinearMap.IsDifferentialOperatorOfOrder (Localization S) 0 := by
      simpa [eN] using
        restrictScalars_isDifferentialOperatorOfOrder_zero_of_localization_linear
          (A := A) (S := S) ((LocalizedModule.equivTensorProduct S N).toLinearMap)
    have hFtensor_extends :
        Ftensor.comp tensorMkM = tensorMkN.comp D := by
      ext m
      have hMkM :
          eM ((LocalizedModule.mkLinearMap S M) m) = tensorMkM m := by
        simpa [eM, tensorMkM, LinearMap.comp_apply] using
          DFunLike.congr_fun
            (localizedModule_equivTensorProduct_comp_mkLinearMap
              (A := A) (B := B) (S := S) M) m
      have hMkN :
          eN ((LocalizedModule.mkLinearMap S N) (D m)) = tensorMkN (D m) := by
        simpa [eN, tensorMkN, LinearMap.comp_apply] using
          DFunLike.congr_fun
            (localizedModule_equivTensorProduct_comp_mkLinearMap
              (A := A) (B := B) (S := S) N) (D m)
      calc
        Ftensor (tensorMkM m)
            = eN (F ((LocalizedModule.mkLinearMap S M) m)) := by
                rw [← hMkM]
                simp [Ftensor, tensorOfLocalized, eM, eN, LinearMap.comp_apply]
        _ = eN (((LocalizedModule.mkLinearMap S N).restrictScalars A).comp D m) := by
              simpa [LinearMap.comp_apply] using DFunLike.congr_fun hF_extends m
        _ = tensorMkN (D m) := hMkN
    have hFtensor_order :
        Ftensor.IsDifferentialOperatorOfOrder (Localization S) k := by
      have hmid :
          (F.comp eM.symm.toLinearMap).IsDifferentialOperatorOfOrder (Localization S) k := by
        simpa [eM, Nat.zero_add] using
          LinearMap.isDifferentialOperatorOfOrder_comp heMsymm_zero hF_order
      simpa [Ftensor, tensorOfLocalized, eN, Nat.add_zero] using
        LinearMap.isDifferentialOperatorOfOrder_comp hmid heN_zero
    have hFtensor_eq : Ftensor = Dtensor := hDtensor_unique Ftensor ⟨hFtensor_extends, hFtensor_order⟩
    ext x
    apply eN.injective
    have hEval := DFunLike.congr_fun hFtensor_eq (eM x)
    simpa [Ftensor, E, EfromTensor, tensorOfLocalized, eM, eN, LinearMap.comp_apply] using hEval

end

/-! ### Lemma_10_133_13 (from Chap10) -/
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
