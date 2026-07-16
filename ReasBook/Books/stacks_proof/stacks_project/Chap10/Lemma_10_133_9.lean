import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_133_3

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
    · simp
    · intro a b
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
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

omit [Module S M] [IsScalarTower R S M] in
/-- Helper for Chap10 Lemma 10 133 9: the free-to-tensor map on a single basis vector. -/
private theorem principal_parts_free_to_tensor_single (m : M) (s : S) :
    principal_parts_free_to_tensor (R := R) (S := S) (M := M) (Finsupp.single m s) =
      s • ((1 : S) ⊗ₜ[R] m) := by
  -- The map is the linear combination map with coefficient vector `m ↦ 1 ⊗ m`.
  simp [principal_parts_free_to_tensor, Finsupp.linearCombination_single]

/-- Helper for Lemma 10.133.9: the `n`th diagonal-ideal power acting on `S ⊗[R] M`. -/
private abbrev diagonal_power_submodule (n : ℕ) : Submodule (S ⊗[R] S) (S ⊗[R] M) :=
  ((KaehlerDifferential.ideal R S) ^ n) • (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))

/-- Helper for Chap10 Lemma 10 133 9: membership in `JppSubmodule` is membership in the raw
diagonal-power submodule. -/
private theorem mem_jppSubmodule_iff_diagonalPower (k : ℕ) (x : S ⊗[R] M) :
    x ∈ (JppSubmodule k : Submodule S (S ⊗[R] M)) ↔
      x ∈ diagonal_power_submodule (R := R) (S := S) (M := M) (k + 1) := by
  -- This records the definitional bridge once, keeping later proofs in the raw submodule spelling.
  rfl

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

/-- Helper for Chap10 Lemma 10 133 9: acting by a consed diagonal product on `1 ⊗ m` is the
recursive scalar-commutator expression. -/
private theorem diagonal_product_cons_smul_universal_tensor (g : S) (l : List S) (m : M) :
    diagonal_product (R := R) (S := S) (g :: l) • ((1 : S) ⊗ₜ[R] m) =
      diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] (g • m)) -
        g • (diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] m)) := by
  -- Expand the new diagonal factor and commute the outer left `S`-action past the old product.
  have hleft : g • ((1 : S) ⊗ₜ[R] m) = (g : S) ⊗ₜ[R] m := by
    simpa using TensorProduct.smul_tmul' (R := R) g (1 : S) m
  rw [diagonal_product, mul_smul, diagonal_generator_smul_universal_tensor, smul_sub]
  rw [diagonal_product_smul_commute]
  rw [hleft]

/-- Helper for Chap10 Lemma 10 133 9: a length `k + 1` diagonal product acting on `1 ⊗ m`
belongs to the principal-parts tensor quotient submodule. -/
private theorem diagonal_product_smul_universal_tensor_mem_Jpp
    (k : ℕ) {l : List S} (hl : l.length = k + 1) (m : M) :
    diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] m) ∈
      (JppSubmodule k : Submodule S (S ⊗[R] M)) := by
  -- The diagonal product contributes `k + 1` ideal factors, while `1 ⊗ m` lies in the top
  -- tensor submodule, so their product lies in the defining submodule of the quotient model.
  rw [mem_jppSubmodule_iff_diagonalPower]
  have hprod :
      diagonal_product (R := R) (S := S) l ∈
        (KaehlerDifferential.ideal R S) ^ (k + 1) := by
    simpa [hl] using diagonal_product_mem_kaehler_ideal_pow (R := R) (S := S) l
  have htop :
      ((1 : S) ⊗ₜ[R] m) ∈
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)) := by
    exact Submodule.mem_top
  change (diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] m) ∈
    ((KaehlerDifferential.ideal R S) ^ (k + 1)) •
      (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))
  exact AddSubmonoid.smul_mem_smul hprod htop

/-- Helper for Chap10 Lemma 10 133 9: the quotient-valued diagonal-product map on `M`. -/
private def diagonalProductToQuotient (k : ℕ) (l : List S) :
    M →ₗ[R] ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M))) :=
  (((JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ).restrictScalars R).comp
    ((principal_parts_tensor_action (R := R) (S := S) (M := M)
        (diagonal_product (R := R) (S := S) l)).comp
      (TensorProduct.mk R S M (1 : S)))

/-- Helper for Chap10 Lemma 10 133 9: the quotient-valued diagonal-product map evaluates by
applying the diagonal product to `1 ⊗ m` and then taking the quotient class. -/
private theorem diagonalProductToQuotient_apply (k : ℕ) (l : List S) (m : M) :
    diagonalProductToQuotient (R := R) (S := S) (M := M) k l m =
      (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ
        (diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] m)) := by
  -- This is just the computation rule for the two composed linear maps defining the operator.
  rfl

/-- Helper for Chap10 Lemma 10 133 9: a diagonal-product operator whose list has length `k + 1`
is zero in the tensor quotient. -/
private theorem diagonalProductToQuotient_eq_zero_of_length
    (k : ℕ) {l : List S} (hl : l.length = k + 1) :
    diagonalProductToQuotient (R := R) (S := S) (M := M) k l = 0 := by
  -- Pointwise, the quotient class is zero because the diagonal-product vector lies in `J^(k+1)`.
  ext m
  rw [diagonalProductToQuotient_apply, LinearMap.zero_apply]
  exact (Submodule.Quotient.mk_eq_zero
    (JppSubmodule k : Submodule S (S ⊗[R] M))).mpr
      (diagonal_product_smul_universal_tensor_mem_Jpp (R := R) (S := S) (M := M) k hl m)

/-- Helper for Chap10 Lemma 10 133 9: taking a scalar commutator of the diagonal-product operator
conses the scalar onto the diagonal-product list. -/
private theorem diagonalProductToQuotient_scalarCommutator
    (k : ℕ) (l : List S) (g : S) :
    (diagonalProductToQuotient (R := R) (S := S) (M := M) k l).scalarCommutator g =
      diagonalProductToQuotient (R := R) (S := S) (M := M) k (g :: l) := by
  ext m
  -- The recursive diagonal-product identity is exactly the scalar-commutator formula after
  -- passing to the quotient.
  calc
    ((diagonalProductToQuotient (R := R) (S := S) (M := M) k l).scalarCommutator g) m =
        (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ
          (diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] (g • m))) -
          g • (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ
            (diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] m)) := by
          simp [diagonalProductToQuotient_apply]
    _ =
        (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ
          (diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] (g • m)) -
            g • (diagonal_product (R := R) (S := S) l • ((1 : S) ⊗ₜ[R] m))) := by
          rw [← LinearMap.map_smul, ← LinearMap.map_sub]
    _ =
        (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ
          (diagonal_product (R := R) (S := S) (g :: l) • ((1 : S) ⊗ₜ[R] m)) := by
          rw [diagonal_product_cons_smul_universal_tensor]
    _ = diagonalProductToQuotient (R := R) (S := S) (M := M) k (g :: l) m := by
          rw [diagonalProductToQuotient_apply]

/-- Helper for Chap10 Lemma 10 133 9: the quotient-valued diagonal-product operator has order
bounded by the number of missing diagonal factors. -/
private theorem diagonalProductToQuotient_isDifferentialOperatorOfOrder
    (k q : ℕ) (l : List S) (hlen : l.length + q = k) :
    (diagonalProductToQuotient (R := R) (S := S) (M := M) k l).IsDifferentialOperatorOfOrder S q := by
  induction q generalizing l with
  | zero =>
      -- At order zero, every scalar commutator has length `k + 1`, hence vanishes in the quotient.
      rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
      intro g m
      have hconsLength : (g :: l).length = k + 1 := by
        simp only [List.length_cons]
        omega
      have hzero :
          diagonalProductToQuotient (R := R) (S := S) (M := M) k (g :: l) = 0 :=
        diagonalProductToQuotient_eq_zero_of_length (R := R) (S := S) (M := M) k hconsLength
      have hcomm :
          ((diagonalProductToQuotient (R := R) (S := S) (M := M) k l).scalarCommutator g) m =
            0 := by
        rw [diagonalProductToQuotient_scalarCommutator, hzero]
        rfl
      simpa [LinearMap.scalarCommutator_apply, sub_eq_zero] using hcomm
  | succ q ih =>
      -- A successor-order commutator is the diagonal-product operator with one more scalar, so
      -- the induction hypothesis applies with the length equation shifted by one.
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
      intro g
      rw [diagonalProductToQuotient_scalarCommutator]
      refine ih (g :: l) ?_
      simp only [List.length_cons]
      omega

/-- Helper for Chap10 Lemma 10 133 9: the empty diagonal-product operator has order at most `k`. -/
private theorem diagonalProductToQuotient_nil_isDifferentialOperatorOfOrder (k : ℕ) :
    (diagonalProductToQuotient (R := R) (S := S) (M := M) k []).IsDifferentialOperatorOfOrder S k := by
  -- The empty list has length zero, so it is missing exactly `k` diagonal factors.
  exact diagonalProductToQuotient_isDifferentialOperatorOfOrder
    (R := R) (S := S) (M := M) k k [] (by simp)

/-- Helper for Chap10 Lemma 10 133 9: the quotient-valued differential operator represented by
the tensor quotient model. -/
private def tensorQuotientDifferentialOperator (k : ℕ) :
    differential_operators_order_le R S M k
      ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M))) :=
  ⟨diagonalProductToQuotient (R := R) (S := S) (M := M) k [],
    diagonalProductToQuotient_nil_isDifferentialOperatorOfOrder (R := R) (S := S) (M := M) k⟩

/-- Helper for Chap10 Lemma 10 133 9: evaluating a represented differential operator on a
universal class evaluates the underlying operator on the source element. -/
private theorem principalParts_linearMapEquiv_symm_apply_universalDifferential
    (k : ℕ) {Q : Type u} [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (D : differential_operators_order_le R S M k Q) (m : M) :
    (principal_parts_linear_map_equiv_differential_operators R S M k Q).symm D
        (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
      D.1 m := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Apply the identity `e (e.symm D) = D` to the element `m`.
  have h : (e (e.symm D)).1 m = D.1 m := by
    simpa using
      congrArg (fun E : differential_operators_order_le R S M k Q ↦ E.1 m)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 m = D.1 m
  exact h

/-- Helper for Chap10 Lemma 10 133 9: evaluating the represented operator attached to a linear
map out of principal parts means evaluating that map on the universal class. -/
private theorem principalParts_linearMapEquiv_apply_universalDifferential
    (k : ℕ) {Q : Type u} [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    (L : P^{k}_{S⁄R}(M) →ₗ[S] Q) (m : M) :
    ((principal_parts_linear_map_equiv_differential_operators R S M k Q L).1 m) =
      L (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Reduce the formula to the corresponding computation for `e.symm`.
  simpa [e] using
    (principalParts_linearMapEquiv_symm_apply_universalDifferential
      (R := R) (S := S) (M := M) (k := k) (Q := Q) (D := e L) m).symm

/-- Helper for Chap10 Lemma 10 133 9: maps out of principal parts are determined by their values
on the universal differential classes. -/
private theorem principalParts_linearMap_ext_universalDifferential
    (k : ℕ) {Q : Type u} [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    {f g : P^{k}_{S⁄R}(M) →ₗ[S] Q}
    (h : ∀ m : M,
      f (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        g (principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) :
    f = g := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- The representing equivalence turns equality on universal classes into pointwise equality of
  -- the represented differential operators.
  apply e.injective
  ext m
  simpa [principalParts_linearMapEquiv_apply_universalDifferential] using h m

/-- The map `P^k_{S/R}(M) → (S ⊗[R] M)/J^(k+1)(S ⊗[R] M)` induced by `m ↦ 1 ⊗ m`. -/
private def principal_parts_module_to_tensor_quotient (k : ℕ) :
    P^{k}_{S⁄R}(M) →ₗ[S] ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M))) :=
  (principal_parts_linear_map_equiv_differential_operators R S M k
      ((S ⊗[R] M) ⧸ (JppSubmodule k : Submodule S (S ⊗[R] M)))).symm
    (tensorQuotientDifferentialOperator (R := R) (S := S) (M := M) k)

/-- Helper for Lemma 10.133.9: the forward quotient map sends the universal generator of
`P^k_{S/R}(M)` to the class of `1 ⊗ m`. -/
private theorem principal_parts_module_to_tensor_quotient_universal_differential
    (k : ℕ) (m : M) :
    principal_parts_module_to_tensor_quotient k (principal_parts_universal_differential k m) =
      (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ ((1 : S) ⊗ₜ[R] m) := by
  -- The representing equivalence evaluates on the universal class by applying the represented
  -- quotient-valued operator, whose empty diagonal product is the identity action.
  calc
    principal_parts_module_to_tensor_quotient k (principal_parts_universal_differential k m) =
        (tensorQuotientDifferentialOperator (R := R) (S := S) (M := M) k).1 m := by
          exact principalParts_linearMapEquiv_symm_apply_universalDifferential
            (R := R) (S := S) (M := M) (k := k)
            (D := tensorQuotientDifferentialOperator (R := R) (S := S) (M := M) k) m
    _ = (JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ ((1 : S) ⊗ₜ[R] m) := by
          rw [tensorQuotientDifferentialOperator, diagonalProductToQuotient_apply]
          simp [diagonal_product]

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
    simp [sub_eq_add_neg, smul_smul, mul_comm]
  · intro x y hx hy
    simp [smul_add, LinearMap.map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 133 9: the next diagonal-power submodule is obtained by one
Kähler-ideal action on the previous diagonal-power submodule. -/
private theorem diagonal_power_succ_smul_top (n : ℕ) :
    diagonal_power_submodule (R := R) (S := S) (M := M) (n + 1) =
      (KaehlerDifferential.ideal R S) •
        diagonal_power_submodule (R := R) (S := S) (M := M) n := by
  -- Normalize the ideal power once and use the associativity of ideal actions on submodules.
  rw [diagonal_power_submodule, diagonal_power_submodule, pow_succ']
  exact (Submodule.mul_smul (KaehlerDifferential.ideal R S) ((KaehlerDifferential.ideal R S) ^ n)
    (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))

/-- Helper for Chap10 Lemma 10 133 9: a tensor lift kills the Kähler-ideal multiple of a
diagonal-power submodule when all scalar commutators kill that diagonal power pointwise. -/
private theorem tensor_lift_kaehlerIdeal_smul_diagonalPower_apply_eq_zero
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (D : M →ₗ[R] N)
    (hkill : ∀ g : S, ∀ y : S ⊗[R] M,
      y ∈ diagonal_power_submodule (R := R) (S := S) (M := M) n →
        tensor_lift_of (R := R) (S := S) (M := M) (D.scalarCommutator g) y = 0)
    {x : S ⊗[R] M}
    (hx : x ∈ (KaehlerDifferential.ideal R S) •
      diagonal_power_submodule (R := R) (S := S) (M := M) n) :
    tensor_lift_of (R := R) (S := S) (M := M) D x = 0 := by
  -- First decompose an element of the product submodule into sums of ideal generators acting on
  -- the diagonal-power submodule.
  refine AddSubmonoid.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    -- The Kähler ideal is spanned over `S` by the diagonal generators `1 ⊗ g - g ⊗ 1`.
    have hrS :
        r ∈ Submodule.span S (Set.range fun g : S =>
          ((1 : S) ⊗ₜ[R] g - g ⊗ₜ[R] (1 : S) : S ⊗[R] S)) := by
      rw [KaehlerDifferential.submodule_span_range_eq_ideal R S]
      exact hr
    refine Submodule.span_induction
      (p := fun a _ ↦ tensor_lift_of (R := R) (S := S) (M := M) D (a • y) = 0)
      ?_ ?_ ?_ ?_ hrS
    · intro z hz
      rcases hz with ⟨g, rfl⟩
      -- A diagonal generator turns the tensor lift into the tensor lift of the scalar
      -- commutator, which vanishes by hypothesis on the diagonal-power submodule.
      rw [tensor_lift_diagonal_generator_eq_scalarCommutator]
      exact hkill g y (by exact hy)
    · simp
    · intro a b _ _ ha hb
      rw [add_smul, LinearMap.map_add, ha, hb, add_zero]
    · intro s a _ ha
      rw [smul_assoc, LinearMap.map_smul, ha, smul_zero]
  · intro x y hx0 hy0
    -- Additivity of the tensor lift handles sums in the product submodule.
    simp [LinearMap.map_add, hx0, hy0]

/-- Helper for Chap10 Lemma 10 133 9: if all scalar commutators kill a diagonal-power submodule,
then the original tensor lift kills one further Kähler-ideal multiple. -/
private theorem tensor_lift_kaehlerIdeal_smul_diagonalPower_le_ker
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (D : M →ₗ[R] N)
    (hkill : ∀ g : S,
      Submodule.restrictScalars S (diagonal_power_submodule (R := R) (S := S) (M := M) n) ≤
        LinearMap.ker (tensor_lift_of (R := R) (S := S) (M := M) (D.scalarCommutator g))) :
    Submodule.restrictScalars S
        ((KaehlerDifferential.ideal R S) •
          diagonal_power_submodule (R := R) (S := S) (M := M) n) ≤
      LinearMap.ker (tensor_lift_of (R := R) (S := S) (M := M) D) := by
  intro x hx
  rw [LinearMap.mem_ker]
  -- Convert the kernel hypothesis to the pointwise annihilation form and apply the raw
  -- Kähler-ideal action lemma.
  refine tensor_lift_kaehlerIdeal_smul_diagonalPower_apply_eq_zero
    (R := R) (S := S) (M := M) n D ?_ hx
  intro g y hy
  exact LinearMap.mem_ker.mp ((hkill g) hy)

-- Proof sketch: an element of `J^(k+1)(S ⊗[R] M)` is a sum of terms with `k + 1` diagonal
-- factors. Each diagonal factor turns the tensor lift into the scalar commutator of the underlying
-- map, lowering the differential-operator order by one.
/-- Helper for Chap10 Lemma 10 133 9: an order-`k` operator kills the `(k + 1)`st diagonal-ideal
power acting on `S ⊗[R] M`. -/
private theorem tensor_lift_diagonal_power_smul_top_le_ker_of_order
    {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (k : ℕ) (D : M →ₗ[R] N) (hD : D.IsDifferentialOperatorOfOrder S k) :
    Submodule.restrictScalars S
        (diagonal_power_submodule (R := R) (S := S) (M := M) (k + 1)) ≤
      LinearMap.ker (tensor_lift_of (R := R) (S := S) (M := M) D) := by
  induction k generalizing D with
  | zero =>
      -- A zero-order operator has zero scalar commutators, so the Kähler-ideal step kills `J • ⊤`.
      rw [diagonal_power_succ_smul_top]
      refine tensor_lift_kaehlerIdeal_smul_diagonalPower_le_ker
        (R := R) (S := S) (M := M) 0 D ?_
      intro g x hx
      rw [LinearMap.mem_ker]
      have hcomm : D.scalarCommutator g = 0 := by
        ext m
        rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at hD
        simpa [LinearMap.scalarCommutator_apply] using sub_eq_zero.mpr (hD g m)
      rw [hcomm]
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp [tensor_lift_of]
      · intro s m
        simp [tensor_lift_of]
      · intro x y hx hy
        simp [LinearMap.map_add, hx, hy]
  | succ k ih =>
      -- The successor step applies the Kähler-ideal lemma to the scalar commutators, whose order is
      -- lowered by the recursive definition of differential operator order.
      rw [diagonal_power_succ_smul_top]
      refine tensor_lift_kaehlerIdeal_smul_diagonalPower_le_ker
        (R := R) (S := S) (M := M) (k + 1) D ?_
      intro g
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD
      exact ih (D.scalarCommutator g) (hD g)

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
  -- Specialize the diagonal-power annihilation theorem to the universal differential operator.
  simpa [tensor_to_principal_parts_module, diagonal_power_submodule] using
    tensor_lift_diagonal_power_smul_top_le_ker_of_order
      (R := R) (S := S) (M := M) k
      (principal_parts_universal_differential (R := R) (S := S) (M := M) k)
      (principal_parts_universal_differential_isDifferentialOperatorOfOrder
        (R := R) (S := S) (M := M) k)

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
  -- The principal-parts quotient is generated by the universal differential classes, so it is
  -- enough to check the composite there.
  refine principalParts_linearMap_ext_universalDifferential (R := R) (S := S) (M := M) k ?_
  intro m
  calc
    ((tensor_quotient_to_principal_parts_module k).comp
        (principal_parts_module_to_tensor_quotient k))
        (principal_parts_universal_differential k m) =
        tensor_quotient_to_principal_parts_module k
          ((JppSubmodule k : Submodule S (S ⊗[R] M)).mkQ ((1 : S) ⊗ₜ[R] m)) := by
          rw [LinearMap.comp_apply, principal_parts_module_to_tensor_quotient_universal_differential]
    _ = tensor_to_principal_parts_module k ((1 : S) ⊗ₜ[R] m) := by
          have hmkQ := LinearMap.congr_fun
            (((JppSubmodule k : Submodule S (S ⊗[R] M)).liftQ_mkQ
            (tensor_to_principal_parts_module k)
            (principal_parts_tensor_submodule_le_module_ker k)))
            ((1 : S) ⊗ₜ[R] m)
          simpa [tensor_quotient_to_principal_parts_module] using hmkQ
    _ = principal_parts_universal_differential k m := by
          simp [tensor_to_principal_parts_module, tensor_lift_of]
    _ = (LinearMap.id : P^{k}_{S⁄R}(M) →ₗ[S] P^{k}_{S⁄R}(M))
          (principal_parts_universal_differential k m) := by
          rfl

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

/-- Chap10 Lemma 10 133 9: the `k`th module of principal parts `P^k_{S/R}(M)` is canonically isomorphic to
`(S ⊗[R] M)/J^(k + 1)(S ⊗[R] M)` where `J = ker(S ⊗[R] S → S)` and `S` acts through
multiplication by `s ⊗ 1`. -/
@[stacks 0H90]
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
