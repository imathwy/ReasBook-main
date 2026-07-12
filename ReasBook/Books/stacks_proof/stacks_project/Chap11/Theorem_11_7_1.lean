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
  -- Route correction: use the built-in `k`-linearity of the tensor-product action map, which
  -- avoids rewriting the tensor scalar action through multiplication by hand.
  simpa using
    congrArg
      (fun f : Module.End k M ↦ f m)
      ((tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M)).map_smul c x)

/-- Helper for Theorem 11.7.1: the tensor-linear endomorphism ring attached to the action of
`B ⊗[k] Module.End A M` on `M`. -/
private noncomputable abbrev tensor_product_moduleEnd
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] : Type v :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  Module.End (TensorProduct k B (Module.End A M)) M

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: the tensor-linear endomorphism type inherits its ring structure
from the ambient endomorphism ring once the tensor action on `M` is fixed. -/
private noncomputable instance tensor_product_moduleEnd_ring
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Ring (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  infer_instance

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: tensor-linear endomorphisms are naturally a `k`-module via the
ambient scalar action on endomorphisms. -/
private noncomputable instance tensor_product_moduleEnd_module
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Module k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  infer_instance

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: tensor-linear endomorphisms form a `k`-algebra under scalar
multiplication by endomorphisms of `M`. -/
private noncomputable instance tensor_product_moduleEnd_algebra
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Algebra k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) := by
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  infer_instance

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: tensor-linear endomorphisms of `M` form a finite-dimensional
`k`-vector space. -/
private theorem tensor_product_moduleEnd_finiteDimensional
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    FiniteDimensional k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) := by
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  let forgetEnd :
      tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M) →ₗ[k] Module.End k M :=
    { toFun := fun f ↦
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun c x ↦ by
            simpa [Algebra.smul_def] using f.map_smul ((algebraMap k R) c) x }
      map_add' := fun f g ↦ rfl
      map_smul' := fun c f ↦ rfl }
  have hforget : Function.Injective forgetEnd := by
    intro f g hfg
    ext x
    exact congrArg (fun h : Module.End k M ↦ h x) hfg
  exact FiniteDimensional.of_injective forgetEnd hforget

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
    -- The zero tensor acts by the zero endomorphism on both sides.
    change (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1) 0 = 0
    exact map_zero _
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
            -- Route correction: restate the goal in the native `Module.End A M`-linear form
            -- before invoking `map_smul`, so instance search stays on the endomorphism action.
            change
              simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1 (l • m) =
                l • simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) c.1 m
            exact
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

omit [IsSimpleRing B] in
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

omit [IsSimpleRing B] in
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

omit [IsSimpleRing B] in
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

omit [IsSimpleRing B] in
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

omit [IsSimpleRing B] in
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
  simp [centralizer_to_tensor_end]

omit [IsSimpleRing B] in
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
  simp [centralizer_to_tensor_end]

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

omit [IsSimpleRing B] in
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

omit [IsSimpleRing B] in
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

/-- Helper for Theorem 11.7.1: the centralizer of `B` identifies with the tensor-linear
endomorphism algebra of `M`. -/
private noncomputable def centralizer_algEquiv_tensor_end
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    C ≃ₐ[k] tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M) :=
  letI : Module (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  AlgEquiv.ofBijective
    (centralizer_to_tensor_end_as_algHom (k := k) (A := A) (B := B) (M := M))
    (centralizer_to_tensor_end_as_algHom_bijective (k := k) (A := A) (B := B) (M := M))

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: the public alias
`tensor_product_moduleEnd` is definitionally the canonical endomorphism ring `Module.End R M`
for `R = B ⊗[k] Module.End A M`. -/
private noncomputable abbrev tensorProductModuleEndAlgEquiv
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M) ≃ₐ[k]
      Module.End (TensorProduct k B (Module.End A M)) M := by
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  change Module.End R M ≃ₐ[k] Module.End R M
  refine
    { __ := RingEquiv.refl (Module.End R M)
      commutes' := ?_ }
  intro c
  rfl

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: the direct-normal-form endomorphism ring
`End_{B ⊗[k] End_A(M)}(M)` packaged behind a stable alias so later theorem headers do not
re-elaborate the tensor-product action infrastructure. -/
private noncomputable abbrev tensorEndDirectType
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] : Type v :=
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  Module.End R M

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: a linear equivalence with `Fin n → S` rewrites the
`k`-dimension as `n * dim_k(S)`. -/
private theorem finrank_eq_mul_finrank_of_linearEquivPi
    {R : Type v} [Ring R] [Algebra k R] {n : ℕ}
    {S : Type*} [AddCommGroup S] [Module R S] [Module k S] [IsScalarTower k R S]
    {N : Type*} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    [FiniteDimensional k S] [FiniteDimensional k N]
    (e : N ≃ₗ[R] (Fin n → S)) :
    Module.finrank k N = n * Module.finrank k S := by
  -- Compare `k`-dimensions by forgetting the `R`-action and using the standard finrank formula
  -- for a finite product of `n` copies of `S`.
  calc
    Module.finrank k N = Module.finrank k (Fin n → S) := by
      simpa using (e.restrictScalars k).finrank_eq
    _ = n * Module.finrank k S := finrank_fin_fun (k := k) (V := S) n

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: over a finite-dimensional simple `k`-algebra `R`, the
endomorphism ring of any finite nontrivial left `R`-module is simple. -/
private theorem finiteModuleEndIsSimpleRing
    {R : Type v} [Ring R] [Algebra k R] [FiniteDimensional k R] [IsSimpleRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Nontrivial N] [Module.Finite R N]
    [Module k N] [IsScalarTower k R N] [FiniteDimensional k N] :
    IsSimpleRing (Module.End R N) := by
  classical
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  obtain ⟨S, hS⟩ := exists_simple_regular_submodule (k := k) (R := R)
  letI : IsSimpleModule R ↥S := hS
  letI : DivisionRing (Module.End R ↥S) := Module.End.instDivisionRing
  letI : IsSimpleRing (Module.End R ↥S) := inferInstance
  letI : FiniteDimensional k ↥S := simple_module_finite_dimensional (k := k) (R := R) (M := ↥S)
  obtain ⟨n, ⟨eN⟩⟩ := finite_module_equiv_pi_of_simple_module (A := R) (M := ↥S) (N := N)
  have hN :
      Module.finrank k N = n * Module.finrank k ↥S :=
    finrank_eq_mul_finrank_of_linearEquivPi (k := k) eN
  have hNpos : 0 < Module.finrank k N := Module.finrank_pos
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hn0, zero_mul] at hN
    exact (Nat.ne_of_gt hNpos) hN
  letI : NeZero n := ⟨Nat.ne_zero_of_lt hnpos⟩
  let eEnd :
      Module.End R N ≃ₐ[k] Matrix (Fin n) (Fin n) (Module.End R ↥S) :=
    (eN.conjAlgEquiv k).trans (endVecAlgEquivMatrixEnd (Fin n) k R ↥S)
  -- Transport simplicity from the explicit matrix model, where the coefficient ring is the
  -- division algebra `Module.End R S`.
  have hMatrix : IsSimpleRing (Matrix (Fin n) (Fin n) (Module.End R ↥S)) :=
    IsSimpleRing.matrix (Fin n) (Module.End R ↥S)
  exact IsSimpleRing.of_ringEquiv eEnd.toRingEquiv.symm hMatrix

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: over a finite-dimensional simple `k`-algebra `R`, a finite
nontrivial left `R`-module `N` satisfies `[R : k] [End_R(N) : k] = dim_k(N)^2`. -/
private theorem finiteModuleEndFinrankFormula
    {R : Type v} [Ring R] [Algebra k R] [FiniteDimensional k R] [IsSimpleRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Nontrivial N] [Module.Finite R N]
    [Module k N] [IsScalarTower k R N] [FiniteDimensional k N] :
    Module.finrank k R * Module.finrank k (Module.End R N) = (Module.finrank k N) ^ 2 := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  obtain ⟨S, hS⟩ := exists_simple_regular_submodule (k := k) (R := R)
  letI : IsSimpleModule R ↥S := hS
  letI : FiniteDimensional k ↥S := simple_module_finite_dimensional (k := k) (R := R) (M := ↥S)
  letI : FiniteDimensional k (Module.End R ↥S) :=
    simple_module_endomorphism_finite_dimensional (k := k) (A := R) (M := ↥S)
  obtain ⟨n, ⟨eN⟩⟩ := finite_module_equiv_pi_of_simple_module (A := R) (M := ↥S) (N := N)
  let eEnd :
      Module.End R N ≃ₐ[k] Matrix (Fin n) (Fin n) (Module.End R ↥S) :=
    (eN.conjAlgEquiv k).trans (endVecAlgEquivMatrixEnd (Fin n) k R ↥S)
  have hN :
      Module.finrank k N = n * Module.finrank k ↥S :=
    finrank_eq_mul_finrank_of_linearEquivPi (k := k) eN
  have hEnd :
      Module.finrank k (Module.End R N) = n * n * Module.finrank k (Module.End R ↥S) := by
    calc
      Module.finrank k (Module.End R N) =
          Module.finrank k (Matrix (Fin n) (Fin n) (Module.End R ↥S)) := by
        exact eEnd.toLinearEquiv.finrank_eq
      _ = n * n * Module.finrank k (Module.End R ↥S) := by
        simpa using (Module.finrank_matrix k (Module.End R ↥S) (Fin n) (Fin n))
  -- Compute both dimensions in the same simple-module model and then normalize the arithmetic.
  calc
    Module.finrank k R * Module.finrank k (Module.End R N)
        = Module.finrank k R * (n * n * Module.finrank k (Module.End R ↥S)) := by
            rw [hEnd]
    _ = n * n * (Module.finrank k R * Module.finrank k (Module.End R ↥S)) := by
          simp [Nat.mul_assoc, Nat.mul_left_comm]
    _ = n * n * (Module.finrank k ↥S) ^ 2 := by
          rw [simple_module_finrank_formula (k := k) (A := R) (M := ↥S)]
    _ = (n * Module.finrank k ↥S) ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (Module.finrank k N) ^ 2 := by
          simpa [hN]

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: once
`R = B ⊗[k] Module.End A M` is simple, the direct endomorphism ring `Module.End R M` is simple. -/
private theorem tensorEndDirect_isSimpleRing
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M]
    (hR : IsSimpleRing (TensorProduct k B (Module.End A M))) :
    IsSimpleRing (tensorEndDirectType (k := k) (A := A) (B := B) (M := M)) := by
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  letI : IsSimpleRing R := hR
  letI : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  letI : Nontrivial M := IsSimpleModule.nontrivial A M
  -- Route correction: discharge the heavy matrix-model argument once in the generic
  -- `Module.End R N` theorem and specialize it here through a single `change`.
  change IsSimpleRing (Module.End R M)
  exact finiteModuleEndIsSimpleRing (k := k) (R := R) (N := M)

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: for
`R = B ⊗[k] Module.End A M`, the direct endomorphism ring `Module.End R M` satisfies the source
dimension identity `[R : k] [End_R(M) : k] = dim_k(M)^2`. -/
private theorem tensorEndDirect_finrankFormula
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M]
    (hR : IsSimpleRing (TensorProduct k B (Module.End A M))) :
    Module.finrank k (TensorProduct k B (Module.End A M)) *
        Module.finrank k (tensorEndDirectType (k := k) (A := A) (B := B) (M := M)) =
      (Module.finrank k M) ^ 2 := by
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M :=
    tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
  letI : IsSimpleRing R := hR
  letI : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  letI : Nontrivial M := IsSimpleModule.nontrivial A M
  -- Route correction: keep the dimension argument in the canonical spelling `Module.End R M`
  -- and only transport back to the public alias at the theorem boundary.
  change Module.finrank k R * Module.finrank k (Module.End R M) = (Module.finrank k M) ^ 2
  exact finiteModuleEndFinrankFormula (k := k) (R := R) (N := M)

omit [IsSimpleRing B] in
/-- Helper for Chap11 Theorem 11 7 1: the centralizer and the direct endomorphism ring
`Module.End (B ⊗[k] Module.End A M) M` have the same `k`-dimension. -/
private theorem centralizerFinrank_eq_tensorEndDirect
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] :
    let R := TensorProduct k B (Module.End A M)
    letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k R M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    Module.finrank k C = Module.finrank k (Module.End R M) := by
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M := tensor_product_module_isScalarTower
    (k := k) (A := A) (B := B) (M := M)
  let e :=
    (centralizer_algEquiv_tensor_end (k := k) (A := A) (B := B) (M := M)).trans
      (tensorProductModuleEndAlgEquiv (k := k) (A := A) (B := B) (M := M))
  -- Compare finite dimensions across the single explicit centralizer-to-endomorphism bridge.
  exact e.toLinearEquiv.finrank_eq

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.7.1: once `R = B ⊗[k] Module.End A M` is simple, the tensor-linear
endomorphism ring of the finite `R`-module `M` is simple as well. -/
private theorem tensor_end_isSimpleRing
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M]
    (hR : IsSimpleRing (TensorProduct k B (Module.End A M))) :
    letI : Module (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module (k := k) (A := A) (B := B) (M := M)
    letI : IsScalarTower k (TensorProduct k B (Module.End A M)) M :=
      tensor_product_module_isScalarTower (k := k) (A := A) (B := B) (M := M)
    IsSimpleRing (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) := by
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M := tensor_product_module_isScalarTower
    (k := k) (A := A) (B := B) (M := M)
  have hDirect :
      IsSimpleRing (tensorEndDirectType (k := k) (A := A) (B := B) (M := M)) :=
    tensorEndDirect_isSimpleRing (k := k) (A := A) (B := B) (M := M) hR
  change IsSimpleRing (Module.End R M) at hDirect
  -- Route correction: prove simplicity in the direct `Module.End R M` normal form and transport
  -- back to the public alias only once.
  exact IsSimpleRing.of_ringEquiv
    (tensorProductModuleEndAlgEquiv (k := k) (A := A) (B := B) (M := M)).toRingEquiv.symm
    hDirect

omit [IsSimpleRing B] in
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
        Module.finrank k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) =
      (Module.finrank k M) ^ 2 := by
  let R := TensorProduct k B (Module.End A M)
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M := tensor_product_module_isScalarTower
    (k := k) (A := A) (B := B) (M := M)
  have hDirect :
      Module.finrank k R * Module.finrank k
          (tensorEndDirectType (k := k) (A := A) (B := B) (M := M)) =
        (Module.finrank k M) ^ 2 :=
    tensorEndDirect_finrankFormula (k := k) (A := A) (B := B) (M := M) hR
  change Module.finrank k R * Module.finrank k (Module.End R M) = (Module.finrank k M) ^ 2 at hDirect
  have hEnd :
      Module.finrank k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) =
        Module.finrank k (Module.End R M) :=
    (tensorProductModuleEndAlgEquiv (k := k) (A := A) (B := B) (M := M)).toLinearEquiv.finrank_eq
  -- Rewrite the endomorphism finrank through the explicit alias bridge and reuse the direct formula.
  calc
    Module.finrank k R *
        Module.finrank k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M))
      = Module.finrank k R * Module.finrank k (Module.End R M) := by rw [hEnd]
    _ = (Module.finrank k M) ^ 2 := hDirect

/-- Helper for Chap11 Theorem 11 7 1: for a simple `A`-module `M`, the tensor product
`B ⊗[k] Module.End_A(M)` is simple because the endomorphism algebra is finite-central over `k`. -/
private theorem tensorProductWithModuleEnd_isSimpleRing
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] :
    IsSimpleRing (TensorProduct k B (Module.End A M)) := by
  let L := Module.End A M
  letI : DecidableEq L := Classical.decEq _
  letI : DivisionRing L := Module.End.instDivisionRing
  letI : FiniteDimensional k L :=
    simple_module_endomorphism_finite_dimensional (k := k) (A := A) (M := M)
  letI : Algebra.IsCentral k L := simple_module_end_isCentral (k := k) (A := A) (M := M)
  -- The tensor-product factor `L = End_A(M)` is the finite-central division algebra used in the source argument.
  exact
    isSimpleRing_tensorProduct_of_finite_central_factor
      (k := k) (A := B) (A' := L) (Or.inr ⟨inferInstance, inferInstance⟩)

-- Proof sketch: choose a simple left `A`-module `M`, let `L := Module.End A M`, and rewrite the
-- centralizer of `B` as the endomorphism ring of `M` as a right `B ⊗[k] Lᵐᵒᵖ`-module. The tensor
-- product algebra is simple by the earlier tensor-product lemma, so the endomorphism ring is
-- simple by the finite-module structure theorem for simple algebras.
/-- Chap11 Theorem 11 7 1: part (1). If `A` is a finite central simple `k`-algebra and `B` is a
simple subalgebra of `A`, then the centralizer of `B` in `A` is simple. -/
@[stacks 074T]
theorem isSimpleRing_centralizer :
    IsSimpleRing C := by
  obtain ⟨M, hM⟩ := exists_simple_regular_submodule (k := k) (R := A)
  letI : IsSimpleModule A M := hM
  letI : FiniteDimensional k M := simple_module_finite_dimensional (k := k) (R := A) (M := M)
  let L := Module.End A M
  letI : DecidableEq L := Classical.decEq _
  letI : DivisionRing L := Module.End.instDivisionRing
  letI : FiniteDimensional k L :=
    simple_module_endomorphism_finite_dimensional (k := k) (A := A) (M := M)
  letI : Algebra.IsCentral k L := simple_module_end_isCentral (k := k) (A := A) (M := M)
  let R := TensorProduct k B L
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M := tensor_product_module_isScalarTower
    (k := k) (A := A) (B := B) (M := M)
  have hTensorSimple : IsSimpleRing R := by
    -- Reuse the file-local tensor-product simplicity package instead of rebuilding the endomorphism factor.
    simpa [R, L] using
      (tensorProductWithModuleEnd_isSimpleRing (k := k) (A := A) (B := B) (M := M))
  have hEndSimple :
      IsSimpleRing (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) :=
    tensor_end_isSimpleRing (k := k) (A := A) (B := B) (M := M) hTensorSimple
  let e := centralizer_algEquiv_tensor_end (k := k) (A := A) (B := B) (M := M)
  -- Transport simplicity across the already-constructed centralizer equivalence.
  exact IsSimpleRing.of_ringEquiv e.toRingEquiv.symm hEndSimple

-- Proof sketch: with the same simple `A`-module `M` and `L := Module.End A M`, identify
-- `B ⊗[k] Lᵐᵒᵖ` and the centralizer `C` with matrix algebras over opposite division rings, then
-- compare the resulting dimension formulas from the simple-module structure theorem.
/-- Theorem 11.7.1 (2): if `C` is the centralizer of a simple subalgebra `B ⊆ A`, then
`[A : k] = [B : k] [C : k]`. -/
@[stacks 074T]
theorem finrank_mul_finrank_centralizer :
    Module.finrank k A =
      Module.finrank k B * Module.finrank k C := by
  obtain ⟨M, hM⟩ := exists_simple_regular_submodule (k := k) (R := A)
  letI : IsSimpleModule A M := hM
  letI : FiniteDimensional k M := simple_module_finite_dimensional (k := k) (R := A) (M := M)
  let L := Module.End A M
  letI : DecidableEq L := Classical.decEq _
  letI : DivisionRing L := Module.End.instDivisionRing
  letI : FiniteDimensional k L :=
    simple_module_endomorphism_finite_dimensional (k := k) (A := A) (M := M)
  letI : Algebra.IsCentral k L := simple_module_end_isCentral (k := k) (A := A) (M := M)
  let R := TensorProduct k B L
  letI : Module R M := tensor_product_module (k := k) (A := A) (B := B) (M := M)
  letI : IsScalarTower k R M := tensor_product_module_isScalarTower
    (k := k) (A := A) (B := B) (M := M)
  have hTensorSimple : IsSimpleRing R := by
    -- Reuse the same packaged tensor-product simplicity input as in part (1).
    simpa [R, L] using
      (tensorProductWithModuleEnd_isSimpleRing (k := k) (A := A) (B := B) (M := M))
  have hAformula :
      Module.finrank k A * Module.finrank k L = (Module.finrank k M) ^ 2 := by
    -- Compute the `A`-side dimension using the simple `A`-module `M`.
    simpa [L] using (simple_module_finrank_formula (k := k) (A := A) (M := M))
  have hRformula :
      Module.finrank k R *
          Module.finrank k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) =
        (Module.finrank k M) ^ 2 :=
    -- Compute the tensor-product side in the same simple-module model.
    tensor_end_finrank_formula (k := k) (A := A) (B := B) (M := M) hTensorSimple
  have hCformula :
      Module.finrank k C = Module.finrank k (Module.End R M) :=
    -- Compare the centralizer with the direct endomorphism ring through the canonical bridge.
    centralizerFinrank_eq_tensorEndDirect (k := k) (A := A) (B := B) (M := M)
  have hMain :
      Module.finrank k A * Module.finrank k L =
        Module.finrank k B * Module.finrank k L * Module.finrank k C := by
    -- Rewrite the tensor-product dimension formula in the normalized `[A:k][L:k]` form.
    calc
      Module.finrank k A * Module.finrank k L = (Module.finrank k M) ^ 2 := hAformula
      _ = Module.finrank k R *
            Module.finrank k (tensor_product_moduleEnd (k := k) (A := A) (B := B) (M := M)) := by
        symm
        exact hRformula
      _ = (Module.finrank k B * Module.finrank k L) * Module.finrank k C := by
        rw [Module.finrank_tensorProduct, hCformula]
      _ = Module.finrank k B * Module.finrank k L * Module.finrank k C := by
        simp [Nat.mul_assoc]
  -- Cancel the positive factor `[L : k]` to recover the desired centralizer dimension formula.
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos <| by
    calc
      Module.finrank k L * Module.finrank k A = Module.finrank k A * Module.finrank k L := by
        rw [Nat.mul_comm]
      _ = Module.finrank k B * Module.finrank k L * Module.finrank k C := hMain
      _ = Module.finrank k L * (Module.finrank k B * Module.finrank k C) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm]

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
@[stacks 074T]
theorem centralizer_centralizer_eq :
    centralizer k (C : Set A) = B := by
  letI : IsSimpleRing C := isSimpleRing_centralizer (k := k) (A := A) (B := B)
  have hB :
      Module.finrank k A = Module.finrank k B * Module.finrank k C :=
    finrank_mul_finrank_centralizer (k := k) (A := A) (B := B)
  have hC :
      Module.finrank k A =
        Module.finrank k C * Module.finrank k (centralizer k (C : Set A)) :=
    finrank_mul_finrank_centralizer (k := k) (A := A) (B := C)
  have hfin :
      Module.finrank k B = Module.finrank k (centralizer k (C : Set A)) :=
    finrank_eq_of_centralizer_dimension_formulas (k := k) (A := A) (B := B) hB hC
  have hle : B ≤ centralizer k (C : Set A) :=
    Subalgebra.le_centralizer_centralizer (R := k) (s := B)
  -- The bicentralizer contains `B`, and the dimension computation shows this inclusion is an equality.
  exact (Subalgebra.eq_of_le_of_finrank_eq hle hfin).symm

end

end Subalgebra
