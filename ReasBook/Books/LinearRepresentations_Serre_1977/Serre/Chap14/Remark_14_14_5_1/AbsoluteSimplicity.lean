import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

/-!
# Hom-base-change reduction for the splitting-field theorem

This module reduces Serre's `d_E = 1` (field level) to **absolute simplicity**: for a
finite-dimensional `k`-representation `ρ`, the endomorphism dimension
`finrank k (IntertwiningMap ρ ρ)` is bounded by `finrank k̄ (IntertwiningMap ρ̄ ρ̄)` over the
algebraic closure `k̄`, where `ρ̄ = scalarExtension ρ`.  Combined with the algebraically-closed
Schur lemma (`FDRep.finrank_hom_simple_simple`), this shows that if `ρ̄` is irreducible then
`finrank k (IntertwiningMap ρ ρ) = 1`.

The bound is realized by base change of intertwiners: a self-intertwiner `f` of `ρ`, viewed as an
endomorphism, base-changes to an endomorphism `a • baseChange f` of `ρ̄` which is again an
intertwiner; the resulting `k̄`-linear map `k̄ ⊗_k Hom_k(ρ,ρ) → Hom_k̄(ρ̄,ρ̄)` is injective.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Representation

variable {k : Type u} [Field k] {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

local notation "k̄" => AlgebraicClosure k

section FiniteDimensional

variable [FiniteDimensional k V]

/-- The bundled `k`-linear inclusion of self-intertwiners into all endomorphisms. -/
private def inclHom : IntertwiningMap ρ ρ →ₗ[k] (V →ₗ[k] V) where
  toFun f := f.toLinearMap
  map_add' f g := rfl
  map_smul' a f := by simpa using IntertwiningMap.toLinearMap_smul a f

@[simp] private theorem inclHom_apply (f : IntertwiningMap ρ ρ) :
    inclHom ρ f = f.toLinearMap := rfl

omit [FiniteDimensional k V] in
/-- The canonical base-change map `k̄ ⊗_k End_k V → End_k̄ V̄` sends `a ⊗ h` to `a • baseChange h`. -/
private theorem tensorProduct_tmul (a : k̄) (h : V →ₗ[k] V) :
    LinearMap.tensorProduct k k̄ V V (a ⊗ₜ[k] h) = a • LinearMap.baseChange k̄ h := by
  simp [LinearMap.tensorProduct]

/-- The canonical base-change map equals the composite of the two finite-free equivalences
`lTensorHomEquivHomLTensor` and `liftBaseChangeEquiv`. -/
private theorem tensorProduct_eq_comp (x : k̄ ⊗[k] (V →ₗ[k] V)) :
    LinearMap.tensorProduct k k̄ V V x =
      LinearMap.liftBaseChange k̄ (lTensorHomEquivHomLTensor k V k̄ V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a h =>
      apply LinearMap.ext
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b v =>
          simp only [tensorProduct_tmul, lTensorHomEquivHomLTensor_apply, LinearMap.smul_apply,
            LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
            TensorProduct.lTensorHomToHomLTensor_apply, TensorProduct.smul_tmul', smul_eq_mul,
            mul_comm]
      | add y z hy hz => simp only [map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The canonical base-change map `k̄ ⊗_k End_k V → End_k̄ V̄` is **bijective** (for `V`
finite-dimensional): it is the composite of the two finite-free Hom/base-change equivalences. -/
private theorem tensorProduct_bijective :
    Function.Bijective (LinearMap.tensorProduct k k̄ V V) := by
  have hcomp :
      (⇑(LinearMap.tensorProduct k k̄ V V)) =
        (⇑(LinearMap.liftBaseChangeEquiv (R := k) (M := V) (N := k̄ ⊗[k] V) k̄)) ∘
          (⇑(lTensorHomEquivHomLTensor k V k̄ V)) := by
    funext x; exact tensorProduct_eq_comp x
  rw [hcomp]
  exact (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)

private theorem tensorProduct_injective :
    Function.Injective (LinearMap.tensorProduct k k̄ V V) :=
  tensorProduct_bijective.injective

/-- **End base change is an isomorphism.** For `V` finite-dimensional, the canonical map
`k̄ ⊗_k End_k V ≃ End_k̄ (k̄ ⊗_k V)` is a `k̄`-linear equivalence. -/
def endBaseChangeEquiv :
    k̄ ⊗[k] (V →ₗ[k] V) ≃ₗ[k̄] (k̄ ⊗[k] V →ₗ[k̄] k̄ ⊗[k] V) :=
  LinearEquiv.ofBijective (LinearMap.tensorProduct k k̄ V V) tensorProduct_bijective

@[simp] theorem endBaseChangeEquiv_tmul (a : k̄) (h : V →ₗ[k] V) :
    endBaseChangeEquiv (k := k) (V := V) (a ⊗ₜ[k] h) = a • LinearMap.baseChange k̄ h := by
  simp only [endBaseChangeEquiv, LinearEquiv.ofBijective_apply, tensorProduct_tmul]

omit [FiniteDimensional k V] in
/-- `ρ̄ g` is the base change of `ρ g`. -/
private theorem scalarExtension_apply_eq_baseChange (g : G) :
    (scalarExtension (k := k̄) ρ) g = LinearMap.baseChange k̄ (ρ g) := rfl

omit [FiniteDimensional k V] in
private theorem scalarExtension_linHom_tmul (g : G) (a : k̄) (h : V →ₗ[k] V) :
    (scalarExtension (k := k̄) (linHom ρ ρ)) g (a ⊗ₜ[k] h) = a ⊗ₜ[k] ((linHom ρ ρ) g h) := rfl

/-- `endBaseChangeEquiv` is `G`-equivariant: it intertwines the scalar-extended conjugation action
`scalarExtension (linHom ρ ρ)` with the conjugation action `linHom ρ̄ ρ̄` downstairs. -/
theorem endBaseChangeEquiv_comm (g : G) (x : k̄ ⊗[k] (V →ₗ[k] V)) :
    endBaseChangeEquiv ((scalarExtension (k := k̄) (linHom ρ ρ)) g x) =
      (linHom (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ)) g
        (endBaseChangeEquiv x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero,
      LinearEquiv.map_zero]
  | tmul a h =>
      rw [scalarExtension_linHom_tmul, endBaseChangeEquiv_tmul, endBaseChangeEquiv_tmul,
        linHom_apply, linHom_apply, scalarExtension_apply_eq_baseChange,
        scalarExtension_apply_eq_baseChange, LinearMap.smul_comp, LinearMap.comp_smul,
        ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  | add x y hx hy =>
      rw [LinearMap.map_add, LinearEquiv.map_add, LinearEquiv.map_add, LinearMap.map_add,
        hx, hy]

/-- Invariants of a representation as the kernel of the single difference map `u ↦ (g ↦ W g u - u)`. -/
private theorem invariants_eq_ker_pi {R : Type*} [CommRing R] {U : Type*} [AddCommGroup U]
    [Module R U] [Fintype G] (W : Representation R G U) :
    invariants W = LinearMap.ker (LinearMap.pi (fun g => W g - LinearMap.id)) := by
  ext u
  simp only [mem_invariants, LinearMap.mem_ker, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.id_coe, id_eq, funext_iff, Pi.zero_apply, sub_eq_zero]

/-- **Flat base change of invariants.** For a finite-dimensional representation `W`, the dimension
of the invariants is preserved under scalar extension to the algebraic closure. -/
theorem finrank_invariants_scalarExtension_eq [Finite G] {U : Type u} [AddCommGroup U]
    [Module k U] [FiniteDimensional k U] (W : Representation k G U) :
    Module.finrank k̄ (invariants (scalarExtension (k := k̄) W))
      = Module.finrank k (invariants W) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  set δ : U →ₗ[k] (G → U) := LinearMap.pi (fun g => W g - LinearMap.id) with hδdef
  set e := TensorProduct.piRight k k̄ k̄ (fun _ : G => U) with hedef
  set Φ := TensorProduct.AlgebraTensorModule.lTensor k̄ k̄ δ with hΦdef
  -- The scalar-extended difference map is `piRight ∘ (lTensor δ)`.
  have hfactor :
      LinearMap.pi (fun g => (scalarExtension (k := k̄) W) g - LinearMap.id)
        = (e.toLinearMap).comp Φ := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
        funext g
        rw [hΦdef, hedef]
        simp only [LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.lTensor_tmul, hδdef,
          TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, LinearMap.pi_apply,
          LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe]
        show (scalarExtension (k := k̄) W) g (a ⊗ₜ[k] u) - a ⊗ₜ[k] u = a ⊗ₜ[k] (W g u - u)
        rw [show (scalarExtension (k := k̄) W) g = LinearMap.baseChange k̄ (W g) from rfl,
          LinearMap.baseChange_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hker : invariants (scalarExtension (k := k̄) W) = LinearMap.ker Φ := by
    rw [invariants_eq_ker_pi, hfactor, LinearMap.ker_comp,
      LinearMap.ker_eq_bot.mpr e.injective, Submodule.comap_bot]
  have hinj : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor k̄ k̄ (LinearMap.ker δ).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (LinearMap.ker δ).subtype
      (LinearMap.ker δ).injective_subtype
  rw [hker, hΦdef, Module.Flat.ker_lTensor_eq, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_baseChange (R := k̄) (S := k) (M' := LinearMap.ker δ),
    ← invariants_eq_ker_pi]

/-- **End base change is a dimension-preserving isomorphism (brick 2).** The `k`-dimension of the
self-intertwiners of `ρ` equals the `k̄`-dimension of the self-intertwiners of its scalar extension
to the algebraic closure: `End_{k[G]}(S) ⊗ k̄ ≅ End_{k̄[G]}(S⊗k̄)`. -/
theorem finrank_intertwiningMap_eq_scalarExtension [Finite G] :
    Module.finrank k̄
        (IntertwiningMap (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ))
      = Module.finrank k (IntertwiningMap ρ ρ) := by
  -- `endBaseChangeEquiv` carries the invariants of `scalarExtension (linHom ρ ρ)` onto those of
  -- `linHom ρ̄ ρ̄`, by its `G`-equivariance.
  have hmap :
      Submodule.map endBaseChangeEquiv.toLinearMap
          (invariants (scalarExtension (k := k̄) (linHom ρ ρ)))
        = invariants (linHom (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ)) := by
    ext y
    simp only [Submodule.mem_map, mem_invariants]
    constructor
    · rintro ⟨x, hx, rfl⟩ g
      simp only [LinearEquiv.coe_toLinearMap]
      rw [← endBaseChangeEquiv_comm, hx g]
    · intro hy
      refine ⟨endBaseChangeEquiv.symm y, fun g => ?_, by simp⟩
      apply endBaseChangeEquiv.injective
      rw [endBaseChangeEquiv_comm, LinearEquiv.apply_symm_apply, hy g]
  rw [← (invariantsEquivIntertwiningMap (scalarExtension (k := k̄) ρ)
        (scalarExtension (k := k̄) ρ)).finrank_eq,
    ← (invariantsEquivIntertwiningMap ρ ρ).finrank_eq,
    ← finrank_invariants_scalarExtension_eq (linHom ρ ρ), ← hmap,
    ← (endBaseChangeEquiv.submoduleMap
        (invariants (scalarExtension (k := k̄) (linHom ρ ρ)))).finrank_eq]

/-- The `k̄`-linear base-change map `k̄ ⊗_k Hom_k(ρ,ρ) → End_k̄ V̄`. -/
private def bigPsi : k̄ ⊗[k] IntertwiningMap ρ ρ →ₗ[k̄] (k̄ ⊗[k] V →ₗ[k̄] k̄ ⊗[k] V) :=
  (LinearMap.tensorProduct k k̄ V V).comp (LinearMap.baseChange k̄ (inclHom ρ))

@[simp] private theorem bigPsi_tmul (a : k̄) (f : IntertwiningMap ρ ρ) :
    bigPsi ρ (a ⊗ₜ[k] f) = a • LinearMap.baseChange k̄ f.toLinearMap := by
  unfold bigPsi
  rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, inclHom_apply, tensorProduct_tmul]

private theorem bigPsi_injective : Function.Injective (bigPsi ρ) := by
  have hbase : Function.Injective (LinearMap.baseChange k̄ (inclHom ρ)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    refine Module.Flat.lTensor_preserves_injective_linearMap (inclHom ρ) ?_
    intro f g hfg
    exact IntertwiningMap.ext (by simpa using hfg)
  unfold bigPsi
  rw [LinearMap.coe_comp]
  exact tensorProduct_injective.comp hbase

omit [FiniteDimensional k V] in
/-- Base change of an intertwiner commutes with `ρ̄ g`. -/
private theorem baseChange_comm (f : IntertwiningMap ρ ρ) (g : G) :
    LinearMap.baseChange k̄ (ρ g) ∘ₗ LinearMap.baseChange k̄ f.toLinearMap
      = LinearMap.baseChange k̄ f.toLinearMap ∘ₗ LinearMap.baseChange k̄ (ρ g) := by
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  congr 1
  exact (f.isIntertwining' g).symm

/-- The image of `bigPsi` consists of self-intertwiners of `ρ̄`. -/
private theorem bigPsi_mem_invariants (x : k̄ ⊗[k] IntertwiningMap ρ ρ) :
    bigPsi ρ x ∈
      (linHom (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ)).invariants := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
      rw [mem_invariants]
      intro g
      rw [bigPsi_tmul, linHom_apply, scalarExtension_apply_eq_baseChange,
        scalarExtension_apply_eq_baseChange, LinearMap.smul_comp, LinearMap.comp_smul]
      congr 1
      have hgg : (ρ g) ∘ₗ (ρ g⁻¹) = LinearMap.id := by
        rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
      rw [← LinearMap.comp_assoc, baseChange_comm, LinearMap.comp_assoc,
        ← LinearMap.baseChange_comp, hgg, LinearMap.baseChange_id, LinearMap.comp_id]
  | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- `bigPsi` corestricted to the self-intertwiners of `ρ̄`. -/
private def bigPsi' : k̄ ⊗[k] IntertwiningMap ρ ρ →ₗ[k̄]
    (linHom (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ)).invariants :=
  (bigPsi ρ).codRestrict _ (bigPsi_mem_invariants ρ)

private theorem bigPsi'_injective : Function.Injective (bigPsi' ρ) := by
  intro x y h
  exact bigPsi_injective ρ (congrArg Subtype.val h)

/-- **Hom base change for intertwiners.** The `k`-dimension of the self-intertwiners of `ρ` is at
most the `k̄`-dimension of the self-intertwiners of its scalar extension to the algebraic closure.
Reduces Serre's `d_E = 1` to absolute simplicity of `ρ`. -/
theorem finrank_intertwiningMap_le_scalarExtension :
    Module.finrank k (IntertwiningMap ρ ρ) ≤
      Module.finrank k̄
        (IntertwiningMap (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ)) := by
  have h1 : Module.finrank k (IntertwiningMap ρ ρ)
      = Module.finrank k̄ (k̄ ⊗[k] IntertwiningMap ρ ρ) :=
    (Module.finrank_baseChange (R := k̄) (S := k) (M' := IntertwiningMap ρ ρ)).symm
  have h2 :
      Module.finrank k̄
        ((linHom (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ)).invariants)
        = Module.finrank k̄
          (IntertwiningMap (scalarExtension (k := k̄) ρ) (scalarExtension (k := k̄) ρ)) :=
    (invariantsEquivIntertwiningMap (scalarExtension (k := k̄) ρ)
      (scalarExtension (k := k̄) ρ)).finrank_eq
  rw [h1, ← h2]
  exact LinearMap.finrank_le_finrank_of_injective (bigPsi'_injective ρ)

end FiniteDimensional

end Representation
