import Mathlib
import StacksProject_2024.Chap11.Lemma_11_4_6
import StacksProject_2024.Chap11.Lemma_11_4_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CSA

open ConjAct
open scoped TensorProduct

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable {B : Type w} [Ring B] [Algebra k B] [IsSimpleRing B]

/-- Helper for Theorem 11.6.1: a simple `k`-algebra mapping into a finite-dimensional
`k`-algebra is itself finite-dimensional. -/
lemma simple_source_algHom_finiteDimensional (h : B →ₐ[k] A) : FiniteDimensional k B := by
  -- The source is simple, so any algebra map into the nontrivial target `A` is injective.
  exact FiniteDimensional.of_injective h.toLinearMap (RingHom.injective h.toRingHom)

section

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: the action of `B` on a left `A`-module induced by an algebra map
commutes with every `A`-linear endomorphism. -/
lemma tensor_action_commutes {M : Type*} [AddCommGroup M] [Module A M]
    (h : B →ₐ[k] A) (b : B) (l : Module.End A M) (m : M) :
    (h b : A) • (l m) = l ((h b : A) • m) := by
  -- The endomorphism `l` is `A`-linear, so it commutes with the scalar action of `h b`.
  simpa using (l.map_smul (h b) m).symm

end

/-- Helper for Theorem 11.6.1: every finite-dimensional nontrivial `k`-algebra admits a simple
left submodule of its regular module. -/
private theorem exists_simple_regular_submodule
    {R : Type v} [Ring R] [Algebra k R] [FiniteDimensional k R] [Nontrivial R] :
    ∃ M : Submodule R R, IsSimpleModule R M := by
  -- Reuse the earlier existence theorem instead of rebuilding the Artinian argument here.
  simpa using finite_algebra_exists_simple_submodule_regular (k := k) (A := R)

/-- Helper for Theorem 11.6.1: a simple left module over the finite-dimensional algebra `A`
is finite dimensional over `k`. -/
private theorem simple_module_finite_dimensional
    {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] :
    FiniteDimensional k M := by
  -- This is exactly the finite-dimensionality result proved earlier for simple modules.
  simpa using finite_algebra_simple_module_finite_dimensional (k := k) (A := A) (M := M)

/-- Helper for Theorem 11.6.1: under the double-centralizer equivalence, an element of `A`
acts on `M` by the original scalar action. -/
private theorem simple_module_double_centralizer_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (a : A) (m : M) :
    simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) a m = a • m := by
  -- The imported equivalence is definitionally induced by the original `A`-action.
  rfl

/-- Helper for Theorem 11.6.1: under the double-centralizer equivalence, multiplication in `A`
acts by composition on `M`. -/
private theorem simple_module_double_centralizer_mul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (a b : A) (m : M) :
    simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) (a * b) m =
      a • (simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M) b m) := by
  -- Evaluate multiplicativity of the double-centralizer map at `m`.
  have hmul :=
    congrArg (fun f : Module.End (Module.End A M) M ↦ f m)
      ((simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)).map_mul a b)
  simpa [simple_module_double_centralizer_apply] using hmul

/-- Helper for Theorem 11.6.1: if the endomorphism ring of a nonzero module is central over `k`,
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
  -- Evaluate on one nonzero vector to recover the scalar in `D`.
  apply smul_left_injective D hm
  have hEval := congrArg (fun f : Module.End D M ↦ f m) ha
  simp [fx, Algebra.algebraMap_eq_smul_one] at hEval
  simpa using hEval.symm

/-- Helper for Theorem 11.6.1: if `L = Module.End A M` for a simple `A`-module `M`, then `L` is
central over `k` whenever `A` is central over `k`. -/
private theorem moduleEnd_isCentral
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
  -- Then descend centrality from the endomorphism ring back to `Module.End A M`.
  exact endomorphism_ring_isCentral_of_central (k := k) (D := Module.End A M) (M := M)

/-- Helper for Theorem 11.6.1: the algebra map `h : B →ₐ[k] A` induces a left `B`-action on the
simple `A`-module `M`. -/
private noncomputable def algHom_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    B →ₐ[k] Module.End k M :=
  { toFun := fun b ↦
      { toFun := fun m ↦ (h b : A) • m
        map_add' := fun m n ↦ smul_add (h b : A) m n
        map_smul' := fun c m ↦ by
          -- The `B`-action is `k`-linear because it is induced from the ambient `A`-action.
          simpa [smul_assoc] using (smul_comm (h b : A) c m) }
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

/-- Helper for Theorem 11.6.1: every `A`-linear endomorphism of `M` is naturally `k`-linear. -/
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

/-- Helper for Theorem 11.6.1: the commuting `B`- and `End_A(M)`-actions on `M` induce the
canonical tensor-product action used in the source proof. -/
private noncomputable def tensor_product_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    TensorProduct k B (Module.End A M) →ₐ[k] Module.End k M :=
  Algebra.TensorProduct.lift
    (algHom_action_to_End (k := k) (A := A) h)
    (moduleEnd_action_to_End (k := k) (A := A))
    (fun b l ↦ by
      -- The two generator actions commute because every `A`-linear endomorphism commutes with the
      -- ambient `A`-action restricted along `h`.
      ext m
      change (h b : A) • l m = l ((h b : A) • m)
      exact tensor_action_commutes (A := A) h b l m)

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: on a pure tensor, the source-faithful tensor-product action is the
expected map `m ↦ l ((h b) • m)`. -/
private theorem tensor_product_action_to_End_tmul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (b : B) (l : Module.End A M) (m : M) :
    tensor_product_action_to_End (k := k) (A := A) h (b ⊗ₜ[k] l) m =
      l ((h b : A) • m) := by
  -- Evaluate the defining tensor-product lift on a pure tensor.
  simp [tensor_product_action_to_End, algHom_action_to_End, moduleEnd_action_to_End]

/-- Helper for Theorem 11.6.1: use a separate reducible wrapper for each algebra map
`h : B →ₐ[k] A` so the two tensor-product module structures live on different Lean types while
sharing the same underlying simple `A`-module `M`. -/
private noncomputable abbrev TensorTwist
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (_h : B →ₐ[k] A) : Type v :=
  M

/-- Helper for Theorem 11.6.1: the `R := B ⊗[k] Module.End A M`-module structure on the wrapped
copy of `M` induced by the algebra map `h`. -/
private noncomputable abbrev tensor_twist_module
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    Module (TensorProduct k B (Module.End A M)) (TensorTwist (A := A) (B := B) (M := M) h) :=
  Module.compHom (TensorTwist (A := A) (B := B) (M := M) h)
    (tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) h).toRingHom

/-- Helper for Theorem 11.6.1: the wrapped copy `TensorTwist h` carries the canonical tensor
product module structure induced by `h`. -/
private noncomputable instance tensor_twist_module_inst
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    Module (TensorProduct k B (Module.End A M)) (TensorTwist (A := A) (B := B) (M := M) h) :=
  tensor_twist_module (k := k) (A := A) (B := B) (M := M) h

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: the wrapped tensor action is compatible with the original
`k`-vector-space structure on `M`. -/
private theorem tensor_twist_isScalarTower
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    IsScalarTower k (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h) := by
  let R := TensorProduct k B (Module.End A M)
  refine IsScalarTower.of_algebraMap_smul ?_
  intro c m
  change tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) h (algebraMap k R c) m =
    c • m
  have hcomm :=
    congrArg (fun l : Module.End k M ↦ l m)
      ((tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) h).commutes c)
  simpa [Algebra.algebraMap_eq_smul_one] using hcomm

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: on a pure tensor, the wrapped `R`-action attached to `h` is still
the source action `m ↦ l ((h b) • m)`. -/
private theorem tensor_twist_tmul_smul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (b : B) (l : Module.End A M) (m : TensorTwist (A := A) (B := B) (M := M) h) :
    letI : Module (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) h) :=
      tensor_twist_module (k := k) (A := A) (B := B) (M := M) h
    ((b ⊗ₜ[k] l : TensorProduct k B (Module.End A M)) • m) = l ((h b : A) • m) := by
  -- Unfold the wrapped module structure once and then reuse the pure-tensor evaluation lemma.
  dsimp [tensor_twist_module, TensorTwist]
  simpa using
    tensor_product_action_to_End_tmul_apply (k := k) (A := A) (B := B) (M := M) h b l m

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: the left tensor generator acts on the wrapped module through the
original `B`-action induced by `h`. -/
private theorem tensor_twist_includeLeft_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (b : B) (m : TensorTwist (A := A) (B := B) (M := M) h) :
    letI : Module (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) h) :=
      tensor_twist_module (k := k) (A := A) (B := B) (M := M) h
    ((Algebra.TensorProduct.includeLeft :
        B →ₐ[k] TensorProduct k B (Module.End A M)) b) • m =
      (h b : A) • m := by
  -- Rewrite `includeLeft b` as `b ⊗ 1` and evaluate the wrapped tensor action on that generator.
  dsimp [tensor_twist_module, TensorTwist]
  simpa [Algebra.TensorProduct.includeLeft_apply] using
    tensor_twist_tmul_smul_apply (k := k) (A := A) (B := B) (M := M) h b
      (1 : Module.End A M) m

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: the right tensor generator acts on the wrapped module by
evaluation of `Module.End A M`. -/
private theorem tensor_twist_includeRight_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (l : Module.End A M) (m : TensorTwist (A := A) (B := B) (M := M) h) :
    letI : Module (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) h) :=
      tensor_twist_module (k := k) (A := A) (B := B) (M := M) h
    ((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) • m = l m := by
  -- Rewrite `includeRight l` as `1 ⊗ l` and evaluate the wrapped tensor action on that generator.
  dsimp [tensor_twist_module, TensorTwist]
  simpa [Algebra.TensorProduct.includeRight_apply] using
    tensor_twist_tmul_smul_apply (k := k) (A := A) (B := B) (M := M) h (1 : B) l m

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: the wrapped `R`-module is finite because its underlying
`k`-vector space is still `M`. -/
private theorem tensor_twist_module_finite
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] (h : B →ₐ[k] A)
    [Module (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h)]
    [IsScalarTower k (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h)] :
    Module.Finite (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h) := by
  -- Transport the known finite-dimensional `k`-structure across the wrapper and restrict scalars.
  let R := TensorProduct k B (Module.End A M)
  letI : FiniteDimensional k (TensorTwist (A := A) (B := B) (M := M) h) := by
    simpa [TensorTwist]
  exact Module.Finite.of_restrictScalars_finite k R (TensorTwist (A := A) (B := B) (M := M) h)

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: an `R`-linear equivalence between the `g`- and `f`-twists already
commutes with the right-factor action of `Module.End A M`. -/
private theorem intertwiner_restricts_to_moduleEnd_map_smul
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M]
    (f g : B →ₐ[k] A)
    (φ :
      TensorTwist (A := A) (B := B) (M := M) g ≃ₗ[TensorProduct k B (Module.End A M)]
        TensorTwist (A := A) (B := B) (M := M) f) :
    ∀ l : Module.End A M, ∀ m : M, φ (l • m) = l • φ m := by
  -- Restrict the tensor-linear equivalence along the generator `1 ⊗ l`.
  intro l m
  let m' : TensorTwist (A := A) (B := B) (M := M) g := m
  change φ (l m') = l (φ m')
  have hsmul :=
    φ.map_smul
      ((Algebra.TensorProduct.includeRight :
          Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) m'
  calc
    φ (l m') = φ (((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) • m') := by
      rw [(tensor_twist_includeRight_apply (k := k) (A := A) (B := B) (M := M) g l m').symm]
    _ = ((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) • φ m' := hsmul
    _ = l (φ m') := by
      rw [tensor_twist_includeRight_apply (k := k) (A := A) (B := B) (M := M) f l (φ m')]

/-- Helper for Theorem 11.6.1: an `R`-linear equivalence between the two twists becomes an
`L`-linear automorphism of the underlying simple `A`-module `M`. -/
private noncomputable def intertwiner_restricts_to_moduleEnd
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M]
    (f g : B →ₐ[k] A)
    (φ :
      TensorTwist (A := A) (B := B) (M := M) g ≃ₗ[TensorProduct k B (Module.End A M)]
        TensorTwist (A := A) (B := B) (M := M) f) :
    M ≃ₗ[Module.End A M] M :=
  { toFun := φ
    invFun := φ.symm
    left_inv := φ.left_inv
    right_inv := φ.right_inv
    map_add' := φ.map_add
    map_smul' := intertwiner_restricts_to_moduleEnd_map_smul
      (k := k) (A := A) (B := B) (M := M) f g φ }

omit [IsSimpleRing B] in
/-- Helper for Theorem 11.6.1: an `R`-linear equivalence between the two twists produces the
conjugating unit in `A`. -/
private theorem intertwiner_to_conjugating_unit
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M]
    (f g : B →ₐ[k] A)
    (φ :
      TensorTwist (A := A) (B := B) (M := M) g ≃ₗ[TensorProduct k B (Module.End A M)]
        TensorTwist (A := A) (B := B) (M := M) f) :
    ∃ x : Aˣ,
      f = (MulSemiringAction.toAlgEquiv k A (toConjAct x)).toAlgHom.comp g := by
  -- First convert the tensor-linear intertwiner into an automorphism of `M` commuting with `L`.
  let ψ := intertwiner_restricts_to_moduleEnd (k := k) (A := A) (B := B) (M := M) f g φ
  let u : Units (Module.End (Module.End A M) M) :=
    { val := ψ.toLinearMap
      inv := ψ.symm.toLinearMap
      val_inv := by
        ext m
        exact ψ.apply_symm_apply m
      inv_val := by
        ext m
        exact ψ.symm_apply_apply m }
  let e := simple_module_double_centralizer_algEquiv (k := k) (A := A) (M := M)
  let x : Aˣ := Units.map e.symm.toMonoidHom u
  refine ⟨x, ?_⟩
  ext b
  -- Use the left generator `b ⊗ 1` to read the intertwining relation inside the tensor action.
  have hcomm : ∀ m : M, ψ ((g b : A) • m) = (f b : A) • ψ m := by
    intro m
    let m' : TensorTwist (A := A) (B := B) (M := M) g := m
    change φ ((g b : A) • m') = (f b : A) • φ m'
    have hsmul :=
      φ.map_smul
        ((Algebra.TensorProduct.includeLeft :
            B →ₐ[k] TensorProduct k B (Module.End A M)) b) m'
    calc
      φ ((g b : A) • m') =
          φ (((Algebra.TensorProduct.includeLeft :
            B →ₐ[k] TensorProduct k B (Module.End A M)) b) • m') := by
        rw [(tensor_twist_includeLeft_apply (k := k) (A := A) (B := B) (M := M) g b m').symm]
      _ = ((Algebra.TensorProduct.includeLeft :
          B →ₐ[k] TensorProduct k B (Module.End A M)) b) • φ m' := hsmul
      _ = (f b : A) • φ m' := by
        rw [tensor_twist_includeLeft_apply (k := k) (A := A) (B := B) (M := M) f b (φ m')]
  have hx_unit : Units.map e.toMonoidHom x = u := by
    ext m
    simp [x, e]
  have hx_apply : e (x : A) = ψ.toLinearMap := by
    simpa [u] using congrArg Units.val hx_unit
  have hmul : f b * (x : A) = (x : A) * g b := by
    -- Pull the intertwining relation back through the double-centralizer equivalence.
    apply e.injective
    ext m
    calc
      e (f b * (x : A)) m = (f b : A) • e (x : A) m := by
        simpa using
          simple_module_double_centralizer_mul_apply
            (k := k) (A := A) (M := M) (f b) (x : A) m
      _ = (f b : A) • ψ m := by
        simpa using congrArg (fun T : Module.End (Module.End A M) M ↦ (f b : A) • T m) hx_apply
      _ = ψ ((g b : A) • m) := by
        rw [hcomm m]
      _ = e (x : A) ((g b : A) • m) := by
        simpa using
          (congrArg (fun T : Module.End (Module.End A M) M ↦ T ((g b : A) • m)) hx_apply).symm
      _ = e ((x : A) * g b) m := by
        simpa using
          simple_module_double_centralizer_mul_apply (k := k) (A := A) (M := M) (x : A) (g b) m
  -- Rewrite the conjugation automorphism in multiplicative form and cancel the right factor `x`.
  change f b = ↑x * g b * ↑(x⁻¹)
  calc
    f b = f b * ((x : A) * ↑(x⁻¹)) := by
      simp
    _ = f b * ↑x * ↑(x⁻¹) := by
      simp [mul_assoc]
    _ = ↑x * g b * ↑(x⁻¹) := by
      simpa [mul_assoc] using congrArg (fun a : A ↦ a * ↑(x⁻¹)) hmul

/- Domain-style sampling for Theorem 11.6.1:
- primary domain: Skolem-Noether theory for algebra homomorphisms into a finite central simple
  algebra, expressed through the canonical conjugation action of units;
- relevant owner declarations sampled:
  `ConjAct.toConjAct`,
  `MulSemiringAction.toAlgEquiv`,
  `CSA.isAzumaya`,
  `IsAzumaya.AlgHom.mulLeftRight_bij`;
- best owner abstraction: the core/canonical owner for the target-side symmetry is the conjugation
  action of `Aˣ` on `A`, viewed as `A ≃ₐ[k] A` via `MulSemiringAction.toAlgEquiv`;
- primitive data: `A : CSA k`, a simple `k`-algebra `B`, and algebra maps `f g : B →ₐ[k] A`;
- derived API: the source-facing Skolem-Noether conjugacy statement below, together with the
  pointwise inner-automorphism bridge in Lemma 11.6.2.

Layer triage:
- `source-facing`: the theorem that two `k`-algebra maps into a finite central simple algebra are
  conjugate by a unit;
- `core/canonical`: the conjugation action `toConjAct` transported to algebra automorphisms by
  `MulSemiringAction.toAlgEquiv`;
- `bridge/view`: the downstream specialization turning equality of algebra maps into the usual
  pointwise formula for automorphisms. -/

-- Proof sketch: choose a simple left `A`-module `M`, set `L := Module.End A M`, and give `M`
-- two compatible `B ⊗[k] Lᵐᵒᵖ`-module structures induced by `f` and `g`. The tensor product is
-- simple by the previous finite-central tensor-product lemma, so these module structures are
-- isomorphic; the intertwiner lies in the commutant of `L`, hence comes from a unit of `A`, and
-- the induced algebra automorphism of `A` is the canonical conjugation action by that unit.
/-- Theorem 11.6.1: if `A` is a finite central simple `k`-algebra, `B` is a simple `k`-algebra,
and `f g : B →ₐ[k] A` are `k`-algebra homomorphisms, then `f` and `g` are conjugate by a unit of
`A`. -/
theorem algHom_inner_conjugate (f g : B →ₐ[k] A) :
    ∃ x : Aˣ,
      f = (MulSemiringAction.toAlgEquiv k A (toConjAct x)).toAlgHom.comp g := by
  classical
  -- Route correction: return to the textbook simple-module proof instead of the regular
  -- bimodule route, so the governing object is `M` with commutant `L := Module.End A M`.
  obtain ⟨M, hM⟩ := exists_simple_regular_submodule (k := k) (R := A)
  letI : IsSimpleModule A M := hM
  letI : FiniteDimensional k M := simple_module_finite_dimensional (k := k) (A := A)
  let L := Module.End A M
  letI : DecidableEq L := Classical.decEq _
  letI : DivisionRing L := Module.End.instDivisionRing
  letI : FiniteDimensional k L := simple_module_endomorphism_finite_dimensional
      (k := k) (A := A) (M := M)
  letI : Algebra.IsCentral k L := moduleEnd_isCentral (k := k) (A := A) (M := M)
  have hBfin : FiniteDimensional k B := simple_source_algHom_finiteDimensional (A := A) f
  letI : FiniteDimensional k B := hBfin
  let R := TensorProduct k B L
  have hTensorSimple : IsSimpleRing R := by
    -- This is the source step asserting simplicity of `B ⊗[k] L`.
    exact
      isSimpleRing_tensorProduct_of_finite_central_factor
        (k := k) (A := B) (A' := L) (Or.inr ⟨inferInstance, inferInstance⟩)
  letI : IsSimpleRing R := hTensorSimple
  letI : IsScalarTower k R (TensorTwist (A := A) (B := B) (M := M) f) :=
    by
      change IsScalarTower k (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) f)
      simpa using tensor_twist_isScalarTower (k := k) (A := A) (B := B) (M := M) f
  letI : IsScalarTower k R (TensorTwist (A := A) (B := B) (M := M) g) :=
    by
      change IsScalarTower k (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) g)
      simpa using tensor_twist_isScalarTower (k := k) (A := A) (B := B) (M := M) g
  letI : Module.Finite R (TensorTwist (A := A) (B := B) (M := M) f) :=
    tensor_twist_module_finite (k := k) (A := A) (B := B) (M := M) f
  letI : Module.Finite R (TensorTwist (A := A) (B := B) (M := M) g) :=
    tensor_twist_module_finite (k := k) (A := A) (B := B) (M := M) g
  have hfinrank :
      Module.finrank k (TensorTwist (A := A) (B := B) (M := M) g) =
        Module.finrank k (TensorTwist (A := A) (B := B) (M := M) f) := by
    -- Both wrapped modules are definitionally the same `k`-vector space `M`.
    simp [TensorTwist]
  obtain ⟨φ⟩ :=
    (finite_modules_linear_equiv_iff_finrank_eq
      (k := k) (A := R)
      (M := TensorTwist (A := A) (B := B) (M := M) g)
      (N := TensorTwist (A := A) (B := B) (M := M) f)).2 hfinrank
  -- The source proof now restricts the intertwiner to the commutant of `L` and pulls it back to
  -- a unit of `A`.
  exact intertwiner_to_conjugating_unit (k := k) (A := A) (B := B) (M := M) f g φ

end CSA
