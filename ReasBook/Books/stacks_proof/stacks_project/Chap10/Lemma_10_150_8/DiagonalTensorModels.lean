import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_133_1
import stacks_proof.stacks_project.Chap10.Lemma_10_133_9
import stacks_proof.stacks_project.Chap10.Lemma_10_150_7

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

section

variable {R S S' M N X : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

open scoped PrincipalParts

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
def diagonal_tensor_action :
    S ⊗[R] S →ₗ[R] S ⊗[R] M →ₗ[R] S ⊗[R] M :=
  (TensorProduct.homTensorHomMap (RingHom.id R) S M S M).comp
    (TensorProduct.map diagonal_left_scalar_end diagonal_module_scalar_end)

/-- Helper for Lemma 10.150.8: the diagonal tensor action evaluates on pure tensors by the
expected textbook formula. -/
theorem diagonal_tensor_action_tmul_tmul
    (a b s : S) (m : M) :
    diagonal_tensor_action ((a : S) ⊗ₜ[R] b) ((s : S) ⊗ₜ[R] m) =
      ((a * s : S) ⊗ₜ[R] (b • m)) := by
  -- Both tensor lifts were defined precisely so that pure tensors evaluate by the bilinear rule.
  simp [diagonal_tensor_action, diagonal_left_scalar_end, diagonal_module_scalar_end]

/-- Helper for Lemma 10.150.8: the diagonal tensor action is unital. -/
theorem diagonal_tensor_action_one
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
theorem diagonal_tensor_action_mul
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
instance diagonal_tensor_module :
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
instance diagonal_tensor_isScalarTower :
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

end
