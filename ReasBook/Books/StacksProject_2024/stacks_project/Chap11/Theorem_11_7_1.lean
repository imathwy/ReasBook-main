import Mathlib
import StacksProject_2024.Chap11.Lemma_11_4_6
import StacksProject_2024.Chap11.Lemma_11_4_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Subalgebra

open scoped TensorProduct

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : Subalgebra k A)
variable [IsSimpleRing B]

/- Theorem 11.7.1 is `source-facing`: its public statements are about the canonical owner
abstraction `Subalgebra.centralizer`, so the results live on the `Subalgebra` owner namespace
rather than behind file-local wrapper names. The supporting `core/canonical` API is the
simple-module double-centralizer equivalence from Lemma 11.4.6 together with the tensor-product
simplicity bridge from Lemma 11.4.7, so no extra local wrapper is introduced here. -/
local notation "C" => centralizer k (B : Set A)

/-- Helper for Theorem 11.7.1: every finite-dimensional nontrivial `k`-algebra admits a simple
left submodule of its regular module. -/
private theorem exists_simple_regular_submodule
    {R : Type v} [Ring R] [Algebra k R] [FiniteDimensional k R] [Nontrivial R] :
    ∃ M : Submodule R R, IsSimpleModule R M := by
  -- Reuse the earlier finite-algebra existence theorem rather than rebuilding the Artinian
  -- argument locally.
  simpa using finite_algebra_exists_simple_submodule_regular (k := k) (A := R)

/-- Helper for Theorem 11.7.1: a simple left module over the finite-dimensional algebra `A`
is finite dimensional over `k`. -/
private theorem simple_module_finite_dimensional
    {R : Type v} [Ring R] [Algebra k R] [FiniteDimensional k R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [IsSimpleModule R M] :
    FiniteDimensional k M := by
  -- This is exactly the finite-dimensionality statement already proved for simple modules over
  -- finite-dimensional algebras.
  simpa using finite_algebra_simple_module_finite_dimensional (k := k) (A := R) (M := M)

/-- Helper for Theorem 11.7.1: under the simple-module double-centralizer equivalence, an element
of `A` acts on `M` by its original scalar action. -/
private theorem simple_module_double_centralizer_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (a : A) (m : M) :
    simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) a m = a • m := by
  -- The imported double-centralizer equivalence is definitionally the original `A`-action.
  rfl

/-- Helper for Theorem 11.7.1: under the simple-module double-centralizer equivalence,
multiplication in `A` acts by composition on `M`. -/
private theorem simple_module_double_centralizer_mul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (a b : A) (m : M) :
    simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) (a * b) m =
      a • (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) b m) := by
  -- Evaluate the multiplicativity of the double-centralizer map at the vector `m`.
  have hmul :=
    congrArg (fun f : Module.End (Module.End A M) M ↦ f m)
      ((simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)).map_mul a b)
  simpa [simple_module_double_centralizer_apply] using hmul

/-- Helper for Theorem 11.7.1: if the endomorphism ring of a nonzero module is central over `k`,
then the coefficient division ring is central over `k` as well. -/
private theorem endomorphism_ring_isCentral_of_central
    {D : Type v} {M : Type v} [DivisionRing D] [AddCommGroup M] [Module D M] [Nontrivial M]
    [Algebra k D] [Module k M] [IsScalarTower k D M]
    [Algebra.IsCentral k (Module.End D M)] :
    Algebra.IsCentral k D := by
  refine ⟨fun x hx ↦ ?_⟩
  -- Turn a central element of `D` into the corresponding scalar endomorphism of `M`.
  have hxD : x ∈ Set.center D := by
    rw [Semigroup.mem_center_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y
    exact hx y
  let fx : Module.End D M := Module.End.smulLeft x hxD
  have hfx : fx ∈ Subalgebra.center k (Module.End D M) := by
    -- Every `D`-linear endomorphism commutes with scalar multiplication by `x`.
    rw [Subalgebra.mem_center_iff]
    intro f
    ext m
    simp [fx]
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hfx
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  refine ⟨a, ?_⟩
  -- Evaluate the equality of scalar endomorphisms on one nonzero vector to recover the scalar.
  apply smul_left_injective D hm
  have hEval := congrArg (fun f : Module.End D M ↦ f m) ha
  simp [fx, Algebra.algebraMap_eq_smul_one] at hEval
  simpa using hEval.symm

/-- Helper for Theorem 11.7.1: if `L = Module.End A M` for a simple `A`-module `M`, then `L` is
central over `k` whenever `A` is central over `k`. -/
private theorem simple_module_end_isCentral
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [Algebra.IsCentral k A] :
    Algebra.IsCentral k (Module.End A M) := by
  -- First transfer centrality from `A` to the double-centralizer endomorphism ring of `M`.
  let e := simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)
  letI : Algebra.IsCentral k (Module.End (Module.End A M) M) :=
    Algebra.IsCentral.of_algEquiv k A (Module.End (Module.End A M) M) e
  letI : Nontrivial M := IsSimpleModule.nontrivial A M
  letI : DecidableEq (Module.End A M) := Classical.decEq _
  letI : DivisionRing (Module.End A M) := Module.End.instDivisionRing
  -- Then descend centrality from that endomorphism ring back to `Module.End A M`.
  exact endomorphism_ring_isCentral_of_central (k := k) (D := Module.End A M) (M := M)

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: the left action of `B` commutes with every `A`-linear
endomorphism of the chosen simple module. -/
private theorem subalgebra_action_commutes
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (b : B) (l : Module.End A M) (m : M) :
    (b : A) • (l m) = l ((b : A) • m) := by
  -- This is the `A`-linearity of `l` specialized to the scalar `b`.
  exact (l.map_smul (b : A) m).symm

/-- Helper for Theorem 11.7.1: the subalgebra `B` acts on the chosen simple `A`-module by
restriction of the ambient `A`-action. -/
private noncomputable def subalgebra_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    B →ₐ[k] Module.End k M :=
  { toFun := fun b ↦
      { toFun := fun m ↦ (b : A) • m
        map_add' := fun m n ↦ smul_add (b : A) m n
        map_smul' := fun c m ↦ by
          -- The `B`-action is `k`-linear because it comes from the `A`-module structure.
          simpa using (smul_comm c (b : A) m).symm }
    map_one' := by
      ext m
      simp
    map_mul' := by
      intro b₁ b₂
      ext m
      simp [mul_smul]
    map_zero' := by
      ext m
      simp
    map_add' := by
      intro b₁ b₂
      ext m
      simp [add_smul]
    commutes' := by
      intro c
      ext m
      simp }

/-- Helper for Theorem 11.7.1: every `A`-linear endomorphism of `M` is naturally `k`-linear. -/
private noncomputable def moduleEnd_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Module.End A M →ₐ[k] Module.End k M :=
  { toFun := fun l ↦ LinearMap.restrictScalars k l
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl
    commutes' := by
      intro c
      ext m
      simp [Algebra.algebraMap_eq_smul_one] }

/-- Helper for Theorem 11.7.1: the commuting `B`- and `End_A(M)`-actions on `M` induce the
canonical tensor-product action. -/
private noncomputable def tensor_product_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    TensorProduct k B (Module.End A M) →ₐ[k] Module.End k M :=
  Algebra.TensorProduct.lift
    (subalgebra_action_to_End (k := k) (A := A) (B := B))
    (moduleEnd_action_to_End (k := k) (A := A))
    (fun b l ↦ by
      -- The two generator actions commute because every `A`-linear endomorphism commutes with the
      -- ambient `A`-action restricted to `B`.
      ext m
      exact subalgebra_action_commutes (k := k) (A := A) (B := B) b l m)

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: on a pure tensor, the tensor-product action is the expected
composition of the `B`-action and the `End_A(M)`-action. -/
private theorem tensor_product_action_to_End_tmul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (b : B) (l : Module.End A M) (m : M) :
    tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) (b ⊗ₜ[k] l) m =
      (b : A) • l m := by
  -- Evaluate the defining tensor-product lift on a pure tensor.
  rw [tensor_product_action_to_End, Algebra.TensorProduct.lift_tmul]
  simp [subalgebra_action_to_End, moduleEnd_action_to_End]

/-- Helper for Theorem 11.7.1: the tensor-product action on `M` obtained from the commuting
`B`- and `Module.End A M`-actions. -/
private noncomputable abbrev tensor_product_module
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Module (TensorProduct k B (Module.End A M)) M :=
  Module.compHom M (tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M)).toRingHom

/-- Helper for Theorem 11.7.1: the tensor-linear endomorphism ring attached to the action of
`B ⊗[k] Module.End A M` on `M`. -/
private noncomputable abbrev tensor_product_moduleEnd
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] : Type v :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  Module.End (TensorProduct k B (Module.End A M)) M

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: the tensor action on `M` sends a pure tensor `b ⊗ l` to the
expected composite of the `B`-action and the endomorphism `l`. -/
private theorem tensor_product_tmul_smul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (b : B) (l : Module.End A M) (m : M) :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ((b ⊗ₜ[k] l : TensorProduct k B (Module.End A M)) • m) = (b : A) • l m := by
  -- Unfold the module structure only once and then use the pure-tensor evaluation lemma.
  simpa [tensor_product_module] using
    tensor_product_action_to_End_tmul_apply (k := k) (A := A) (B := B) (M := M) b l m

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: the left tensor generator acts through the original `B`-action on
the simple `A`-module. -/
private theorem tensor_product_action_to_End_includeLeft_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (b : B) (m : M) :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ((Algebra.TensorProduct.includeLeft :
        B →ₐ[k] TensorProduct k B (Module.End A M)) b) • m =
      (b : A) • m := by
  -- Rewrite `includeLeft b` as `b ⊗ 1` and evaluate the tensor action on that generator.
  dsimp [tensor_product_module]
  simpa [Algebra.TensorProduct.includeLeft_apply] using
    tensor_product_tmul_smul_apply (k := k) (A := A) (B := B) (M := M) b
      (1 : Module.End A M) m

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: the right tensor generator acts through evaluation by
`Module.End A M`. -/
private theorem tensor_product_action_to_End_includeRight_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (l : Module.End A M) (m : M) :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) • m = l m := by
  -- Rewrite `includeRight l` as `1 ⊗ l` and evaluate the tensor action on that generator.
  dsimp [tensor_product_module]
  simpa [Algebra.TensorProduct.includeRight_apply] using
    tensor_product_tmul_smul_apply (k := k) (A := A) (B := B) (M := M) (1 : B) l m

-- Restriction-of-scalars is proved by checking commutation with the right tensor generator.
omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: a tensor-linear endomorphism commutes with the right tensor
generator, so it is linear over `Module.End A M`. -/
private theorem tensor_linear_endomorphism_restricts_to_moduleEnd_map_smul
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ∀ f : Module.End (TensorProduct k B (Module.End A M)) M,
      ∀ l : Module.End A M, ∀ m : M, f (l • m) = l • f m := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  intro f l m
  -- Restrict the tensor-linear map along the generator `1 ⊗ l`.
  have hsmul :=
    f.map_smul
      ((Algebra.TensorProduct.includeRight :
          Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) m
  change
    f ((((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) :
          TensorProduct k B (Module.End A M)) • m) =
      (((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) :
          TensorProduct k B (Module.End A M)) • f m at hsmul
  rw [tensor_product_action_to_End_includeRight_apply,
    tensor_product_action_to_End_includeRight_apply] at hsmul
  simpa using hsmul

private noncomputable def tensor_linear_endomorphism_restricts_to_moduleEnd
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    Module.End (TensorProduct k B (Module.End A M)) M → Module.End (Module.End A M) M :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  fun f ↦
    { toFun := f
      map_add' := f.map_add
      map_smul' :=
        tensor_linear_endomorphism_restricts_to_moduleEnd_map_smul
          (k := k) (A := A) (B := B) (M := M) f }

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: a tensor-linear endomorphism also commutes with the left tensor
generator coming from the subalgebra `B`. -/
private theorem tensor_linear_endomorphism_commutes_with_subalgebra_action
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ∀ f : Module.End (TensorProduct k B (Module.End A M)) M,
      ∀ b : B, ∀ m : M, f ((b : A) • m) = (b : A) • f m := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  intro f b m
  -- Restrict the tensor-linear map along the generator `b ⊗ 1`.
  have hsmul :=
    f.map_smul
      ((Algebra.TensorProduct.includeLeft :
          B →ₐ[k] TensorProduct k B (Module.End A M)) b) m
  change
    f ((((Algebra.TensorProduct.includeLeft :
        B →ₐ[k] TensorProduct k B (Module.End A M)) b) :
          TensorProduct k B (Module.End A M)) • m) =
      (((Algebra.TensorProduct.includeLeft :
        B →ₐ[k] TensorProduct k B (Module.End A M)) b) :
          TensorProduct k B (Module.End A M)) • f m at hsmul
  rw [tensor_product_action_to_End_includeLeft_apply,
    tensor_product_action_to_End_includeLeft_apply] at hsmul
  simpa using hsmul

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: the endomorphism of `M` coming from a tensor-linear map commutes
with the `B`-action, hence arises from the centralizer of `B` in `A`. -/
private theorem tensor_linear_endomorphism_centralizes_subalgebra
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ∀ f : Module.End (TensorProduct k B (Module.End A M)) M,
      let a :=
        (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)).symm
          ((tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M)) f)
      a ∈ centralizer k (B : Set A) := by
  intro f
  let e := simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)
  let a : A :=
    e.symm
      ((tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M)) f)
  have ha :
      e a =
        (tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M)) f := by
    -- The chosen `a` is defined by pulling the restricted endomorphism back through `e`.
    simp [a, e]
  rw [Subalgebra.mem_centralizer_iff]
  intro b hb
  -- Pull the commutation relation back through the injective double-centralizer equivalence.
  apply e.injective
  ext m
  let b' : B := ⟨b, hb⟩
  have ha_apply : ∀ m : M, e a m = f m := by
    -- Evaluating the defining equality of `a` recovers the original tensor-linear map.
    intro m
    have hEval :=
      congrArg (fun g : Module.End (Module.End A M) M ↦ g m) ha
    simpa [tensor_linear_endomorphism_restricts_to_moduleEnd] using hEval
  calc
    e (b * a) m = b • e a m := by
      rw [simple_module_double_centralizer_mul_apply]
    _ = b • f m := by rw [ha_apply]
    _ = f (b • m) := by
      symm
      simpa [b'] using
        tensor_linear_endomorphism_commutes_with_subalgebra_action
          (k := k) (A := A) (B := B) (M := M) f b' m
    _ = e a (b • m) := by rw [ha_apply]
    _ = e (a * b) m := by
      rw [← simple_module_double_centralizer_apply (k := k) (A := A) (M := M) b m]
      simpa using
        (simple_module_double_centralizer_mul_apply (k := k) (A := A) (M := M) a b m).symm

-- Tensor-linearity of a centralizing element is checked first on pure tensors and then extended
-- by tensor induction.
omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: an element of the centralizer acts linearly for the tensor-product
module structure on `M`. -/
private theorem centralizer_to_tensor_end_map_smul
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ∀ c : C, ∀ x : TensorProduct k B (Module.End A M), ∀ m : M,
      simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1 (x • m) =
        x • simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1 m := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  intro c x
  -- Check tensor-linearity on generators and extend by tensor induction.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · intro m
    simpa using
      (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1).map_zero
  · intro b l m
    have hc' : c.1 ∈ centralizer k (B : Set A) := c.2
    rw [Subalgebra.mem_centralizer_iff] at hc'
    have hc : c.1 * (b : A) = (b : A) * c.1 := (hc' b b.2).symm
    calc
      simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1
          (((b ⊗ₜ[k] l : TensorProduct k B (Module.End A M)) : TensorProduct k B (Module.End A M)) • m) =
          c.1 • ((b : A) • l m) := by
            rw [tensor_product_tmul_smul_apply]
            rw [simple_module_double_centralizer_apply]
      _ = ((c.1 * (b : A)) : A) • l m := by
        simp [mul_smul]
      _ = (((b : A) * c.1) : A) • l m := by
        rw [hc]
      _ = (b : A) • (c.1 • l m) := by
        simp [mul_smul]
      _ = (b : A) • l
          (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1 m) := by
            congr 1
            simpa [simple_module_double_centralizer_apply] using
              (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1).map_smul l m
      _ = ((b ⊗ₜ[k] l : TensorProduct k B (Module.End A M)) : TensorProduct k B (Module.End A M)) •
          simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1 m := by
            rw [tensor_product_tmul_smul_apply]
  · intro x y hx hy m
    rw [add_smul, map_add, hx m, hy m, add_smul]

private noncomputable def centralizer_to_tensor_end
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    C → Module.End (TensorProduct k B (Module.End A M)) M :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  fun c ↦
    { toFun := simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1
      map_add' :=
        (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1).map_add
      map_smul' :=
        centralizer_to_tensor_end_map_smul (k := k) (A := A) (B := B) (M := M) c }

/-- Helper for Theorem 11.7.1: the inverse bridge from tensor-linear endomorphisms back to the
centralizer of `B` in `A`. -/
private noncomputable def tensor_end_to_centralizer
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    Module.End (TensorProduct k B (Module.End A M)) M → C :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  fun f ↦
    let a :=
      (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)).symm
        ((tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M)) f)
    ⟨a, tensor_linear_endomorphism_centralizes_subalgebra (k := k) (A := A) (B := B) (M := M) f⟩

/-- Helper for Theorem 11.7.1: sending a centralizer element to a tensor-linear endomorphism and
then pulling it back recovers the original centralizer element. -/
private theorem tensor_end_to_centralizer_left_inv
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M]
    (c : C) :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    tensor_end_to_centralizer (k := k) (A := A) (B := B) (M := M)
        (centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) c) = c := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  let e := simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)
  apply Subtype.ext
  change
    e.symm
        ((tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M))
          (centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) c)) = c.1
  have hRestrict :
      (tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M))
        (centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) c) =
        e c.1 := by
    -- Both endomorphisms act on `M` by the original `A`-action of `c`.
    ext m
    rfl
  rw [hRestrict, e.symm_apply_apply]

/-- Helper for Theorem 11.7.1: every tensor-linear endomorphism is recovered after passing to the
centralizer and back through the bridge. -/
private theorem centralizer_to_tensor_end_right_inv
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    ∀ f : tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M),
      centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M)
        (tensor_end_to_centralizer (k := k) (A := A) (B := B) (M := M) f) = f := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  intro f
  let e := simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)
  let a : A :=
    e.symm
      ((tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M)) f)
  have ha :
      e a =
        (tensor_linear_endomorphism_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M)) f := by
    -- The element `a` was defined by pulling `f` back through the double-centralizer equivalence.
    simp [a, e]
  ext m
  -- Evaluate the defining equality of `a` at `m` and then unfold the two bridge maps.
  have hEval := congrArg (fun g : Module.End (Module.End A M) M ↦ g m) ha
  simpa [a, tensor_end_to_centralizer, centralizer_to_tensor_end,
    tensor_linear_endomorphism_restricts_to_moduleEnd] using hEval

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: the tensor-product action on `M` is compatible with the ambient
`k`-scalar action. -/
private theorem tensor_product_module_isScalarTower
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    IsScalarTower k (TensorProduct k B (Module.End A M)) M := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  refine ⟨?_⟩
  intro c x m
  -- Evaluate the scalar-compatibility of the tensor-product action at the vector `x • m`.
  change tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) (c • x) m =
    c • (tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) x m)
  rw [Algebra.smul_def]
  have hmul :=
    congrArg
      (fun f : Module.End k M ↦ f m)
      ((tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M)).map_mul
        (algebraMap k (TensorProduct k B (Module.End A M)) c) x)
  have hcomm :=
    congrArg
      (fun f : Module.End k M ↦
        f (tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) x m))
      ((tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M)).commutes c)
  exact hmul.trans <| by
    simpa [Algebra.algebraMap_eq_smul_one] using hcomm

/-- Helper for Theorem 11.7.1: the bridge from the centralizer to tensor-linear endomorphisms
respects multiplication. -/
private theorem centralizer_to_tensor_end_map_mul
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    ∀ c d : C,
      centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) (c * d) =
        centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) c *
          centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) d := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  intro c d
  -- Compare the two endomorphisms pointwise on `M`.
  ext m
  simpa [centralizer_to_tensor_end] using
    simple_module_double_centralizer_mul_apply (k := k) (A := A) (M := M) c.1 d.1 m

/-- Helper for Theorem 11.7.1: the bridge from the centralizer to tensor-linear endomorphisms
respects addition. -/
private theorem centralizer_to_tensor_end_map_add
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    ∀ c d : C,
      centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) (c + d) =
        centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) c +
          centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) d := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  intro c d
  -- The bridge is defined from the additive algebra equivalence `A ≃ₐ[k] End_{End_A(M)}(M)`.
  ext m
  simpa [centralizer_to_tensor_end] using
    congrArg
      (fun f : Module.End (Module.End A M) M ↦ f m)
      ((simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)).map_add c.1 d.1)

/-- Helper for Theorem 11.7.1: the bridge from the centralizer to tensor-linear endomorphisms
commutes with the scalar `k`-action. -/
private theorem centralizer_to_tensor_end_commutes
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    ∀ c : k,
      centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M)
          (algebraMap k C c) =
        algebraMap k (Module.End (TensorProduct k B (Module.End A M)) M) c := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  intro c
  -- Both sides act on `M` by scalar multiplication with `c`.
  ext m
  simp [centralizer_to_tensor_end, Algebra.algebraMap_eq_smul_one]

/-- Helper for Theorem 11.7.1: the bridge from the centralizer to tensor-linear endomorphisms
preserves the identity element. -/
private theorem centralizer_to_tensor_end_map_one
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) (1 : C) =
      1 := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  -- The unit in the centralizer acts on `M` as the identity map.
  ext m
  simp [centralizer_to_tensor_end, simple_module_double_centralizer_apply]

/-- Helper for Theorem 11.7.1: the bridge from the centralizer to tensor-linear endomorphisms
preserves zero. -/
private theorem centralizer_to_tensor_end_map_zero
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M) (0 : C) =
      0 := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  -- The zero element acts on `M` by the zero endomorphism.
  ext m
  simp [centralizer_to_tensor_end, simple_module_double_centralizer_apply]

/-- Helper for Theorem 11.7.1: the bridge from the centralizer to tensor-linear endomorphisms
bundles into a `k`-algebra homomorphism. -/
private noncomputable def centralizer_to_tensor_end_as_algHom
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    C →ₐ[k] Module.End (TensorProduct k B (Module.End A M)) M :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  { toFun := centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M)
    map_one' := centralizer_to_tensor_end_map_one (k := k) (A := A) (B := B) (M := M)
    map_mul' := centralizer_to_tensor_end_map_mul (k := k) (A := A) (B := B) (M := M)
    map_zero' := centralizer_to_tensor_end_map_zero (k := k) (A := A) (B := B) (M := M)
    map_add' := centralizer_to_tensor_end_map_add (k := k) (A := A) (B := B) (M := M)
    commutes' := centralizer_to_tensor_end_commutes (k := k) (A := A) (B := B) (M := M) }

/-- Helper for Theorem 11.7.1: the bridge from the centralizer to tensor-linear endomorphisms is
bijective, with inverse given by `tensor_end_to_centralizer`. -/
private theorem centralizer_to_tensor_end_bijective
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    Function.Bijective (centralizer_to_tensor_end (k := k) (A := A) (B := B) (M := M)) := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  refine ⟨?_ , ?_⟩
  · -- Injectivity is exactly the proved left-inverse identity.
    exact Function.LeftInverse.injective
      (tensor_end_to_centralizer_left_inv (k := k) (A := A) (B := B) (M := M))
  · -- Surjectivity is exactly the proved right-inverse identity.
    exact Function.RightInverse.surjective
      (centralizer_to_tensor_end_right_inv (k := k) (A := A) (B := B) (M := M))

/-- Helper for Theorem 11.7.1: the packaged algebra-hom version of the bridge is bijective. -/
private theorem centralizer_to_tensor_end_as_algHom_bijective
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    Function.Bijective ⇑(centralizer_to_tensor_end_as_algHom (k := k) (A := A) (B := B) (M := M)) := by
  -- The bundled algebra hom has the same underlying function as the raw bridge map.
  simpa [centralizer_to_tensor_end_as_algHom] using
    (centralizer_to_tensor_end_bijective (k := k) (A := A) (B := B) (M := M))

/-- Helper for Theorem 11.7.1: the centralizer of `B` identifies with the endomorphism algebra of
`M` viewed as a module over `B ⊗[k] Module.End A M`. -/
private noncomputable def centralizer_algEquiv_tensor_end
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    C ≃ₐ[k] Module.End (TensorProduct k B (Module.End A M)) M :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  AlgEquiv.ofBijective
    (centralizer_to_tensor_end_as_algHom (k := k) (A := A) (B := B) (M := M))
    (centralizer_to_tensor_end_as_algHom_bijective (k := k) (A := A) (B := B) (M := M))

/-- Helper for Theorem 11.7.1: once `R = B ⊗[k] Module.End A M` is simple, the endomorphism ring
of the finite `R`-module `M` is simple as well. -/
private theorem tensor_end_isSimpleRing
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M]
    (hR : IsSimpleRing (TensorProduct k B (Module.End A M))) :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    -- TODO: choose a simple regular `R`-submodule `S`, package the decomposition
    -- `M ≃ₗ[R] Fin n → S`, and transport `IsSimpleRing.matrix` across the resulting
    -- endomorphism-ring matrix equivalence once the local `R`-module instance on
    -- `Fin n → S` is stabilized.
    IsSimpleRing (Module.End (TensorProduct k B (Module.End A M)) M) := sorry

/-- Helper for Theorem 11.7.1: for `R = B ⊗[k] Module.End A M`, the source dimension identity
`[R : k] [End_R(M) : k] = dim_k(M)^2` follows from the matrix model over a simple `R`-module. -/
private theorem tensor_end_finrank_formula
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M]
    (hR : IsSimpleRing (TensorProduct k B (Module.End A M))) :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    Module.finrank k (TensorProduct k B (Module.End A M)) *
        Module.finrank k (Module.End (TensorProduct k B (Module.End A M)) M) =
      -- TODO: reuse the same decomposition `M ≃ₗ[R] Fin n → S`, compute the `k`-dimension of
      -- `M` and `End_R(M)` through the matrix model, and insert
      -- `simple_module_finrank_formula (A := R) (M := S)` after the local `R`-module structure
      -- on `Fin n → S` is packaged in a stable way.
      (Module.finrank k M) ^ 2 := sorry

-- Proof sketch: choose a simple left `A`-module `M`, let `L := Module.End A M`, and rewrite the
-- centralizer of `B` as the endomorphism ring of `M` as a right `B ⊗[k] Lᵐᵒᵖ`-module. The tensor
-- product algebra is simple by the earlier tensor-product lemma, so the endomorphism ring is
-- simple by the finite-module structure theorem for simple algebras.
/-- Theorem 11.7.1 (1): if `A` is a finite central simple `k`-algebra and `B` is a simple
subalgebra of `A`, then the centralizer of `B` in `A` is simple. -/
theorem isSimpleRing_centralizer :
    -- TODO: choose a simple `A`-module `M`, form `R = B ⊗[k] End_A(M)`, use
    -- `centralizer_algEquiv_tensor_end` to identify `C` with `End_R(M)`, and transport
    -- `tensor_end_isSimpleRing`.
    IsSimpleRing C := sorry

-- Proof sketch: with the same simple `A`-module `M` and `L := Module.End A M`, identify
-- `B ⊗[k] Lᵐᵒᵖ` and the centralizer `C` with matrix algebras over opposite division rings, then
-- compare the resulting dimension formulas from the simple-module structure theorem.
/-- Theorem 11.7.1 (2): if `C` is the centralizer of a simple subalgebra `B ⊆ A`, then
`[A : k] = [B : k] [C : k]`. -/
theorem finrank_mul_finrank_centralizer :
    Module.finrank k A =
      -- TODO: combine `simple_module_finrank_formula` for `A` with
      -- `tensor_end_finrank_formula` for `R = B ⊗[k] End_A(M)`, rewrite
      -- `Module.finrank_tensorProduct`, and cancel the positive factor
      -- `Module.finrank k (Module.End A M)`.
      Module.finrank k B * Module.finrank k C := sorry

-- Proof sketch: both dimension identities appearing in the bicentralizer argument share the
-- positive factor `[C : k]`, so one can cancel that factor before applying the finite-dimensional
-- inclusion criterion for subalgebras.
omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: if two centralizer dimension formulas inside `A` share the same
positive factor `[C : k]`, then their remaining factors agree. -/
private theorem finrank_eq_of_centralizer_dimension_formulas
    (hB : Module.finrank k A = Module.finrank k B * Module.finrank k C)
    (hC :
      Module.finrank k A =
        Module.finrank k C * Module.finrank k (centralizer k (C : Set A))) :
    Module.finrank k B = Module.finrank k (centralizer k (C : Set A)) := by
  -- Move the common factor `[C : k]` to the left in both formulas so cancellation applies.
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos <| by
    calc
      Module.finrank k C * Module.finrank k B = Module.finrank k A := by
        rw [Nat.mul_comm, hB]
      _ = Module.finrank k C * Module.finrank k (centralizer k (C : Set A)) := hC

-- Proof sketch: apply the dimension formula again to the inclusion `C ⊆ A`, where `C` is the
-- centralizer of `B`, to show that the centralizer of `C` has the same `k`-dimension as `B`;
-- combine this with the obvious inclusion `B ≤ C_A(C)` to deduce equality.
/-- Theorem 11.7.1 (3): if `C` is the centralizer of a simple subalgebra `B ⊆ A`, then the
centralizer of `C` in `A` is exactly `B`. -/
theorem centralizer_centralizer_eq :
    centralizer k (C : Set A) = B := by
  letI : IsSimpleRing C := B.isSimpleRing_centralizer A
  have hBC' : B ≤ centralizer k ((centralizer k (B : Set A)) : Set A) :=
    Subalgebra.le_centralizer_centralizer (R := k) (s := B)
  have hBC : B ≤ centralizer k (C : Set A) := hBC'
  have hdimB := B.finrank_mul_finrank_centralizer A
  have hdimC := (centralizer k (B : Set A)).finrank_mul_finrank_centralizer A
  -- Cancel the positive common factor `Module.finrank k C` in the two dimension formulas.
  have hfin :
      Module.finrank k B = Module.finrank k (centralizer k (C : Set A)) := by
    -- Reuse the shared-factor cancellation step as a standalone finite-dimensional lemma.
    exact finrank_eq_of_centralizer_dimension_formulas (A := A) (B := B) hdimB hdimC
  -- The inclusion plus equal finite dimensions forces equality of the two subalgebras.
  exact (Subalgebra.eq_of_le_of_finrank_eq hBC hfin).symm

end

end Subalgebra
