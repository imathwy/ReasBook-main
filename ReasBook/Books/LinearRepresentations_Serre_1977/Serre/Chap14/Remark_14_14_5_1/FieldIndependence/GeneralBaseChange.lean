import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

/-!
# Hom-base-change reduction for an arbitrary field extension

This module generalizes the End base-change dimension equality from the algebraic-closure case
(`Serre/Chap14/Remark_14_14_5_1/AbsoluteSimplicity.lean`) to an **arbitrary field extension**
`k₀ → K`.  For a finite-dimensional `k₀`-representation `ρ`, the endomorphism dimension of the
scalar extension `scalarExtension (k := K) ρ` over `K` equals the endomorphism dimension of `ρ`
over `k₀`:
`finrank K (IntertwiningMap ρ_K ρ_K) = finrank k₀ (IntertwiningMap ρ ρ)`.

The proof is the equality chain from `AbsoluteSimplicity.lean` with `k̄ = AlgebraicClosure k`
replaced by a general extension `K`; it uses only flat base change, finite-free Hom equivalences,
and `Module.finrank_baseChange`, never `IsAlgClosed`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Representation

variable {k₀ : Type u} [Field k₀] {G : Type u} [Group G]
variable {W : Type u} [AddCommGroup W] [Module k₀ W]
variable {K : Type u} [Field K] [Algebra k₀ K]
variable (ρ : Representation k₀ G W)

section FiniteDimensional

variable [FiniteDimensional k₀ W]

omit [FiniteDimensional k₀ W] in
/-- The canonical base-change map `K ⊗_{k₀} End_{k₀} W → End_K W_K` sends `a ⊗ h` to
`a • baseChange h`. -/
private theorem tensorProduct_tmul (a : K) (h : W →ₗ[k₀] W) :
    LinearMap.tensorProduct k₀ K W W (a ⊗ₜ[k₀] h) = a • LinearMap.baseChange K h := by
  simp [LinearMap.tensorProduct]

/-- The canonical base-change map equals the composite of the two finite-free equivalences
`lTensorHomEquivHomLTensor` and `liftBaseChangeEquiv`. -/
private theorem tensorProduct_eq_comp (x : K ⊗[k₀] (W →ₗ[k₀] W)) :
    LinearMap.tensorProduct k₀ K W W x =
      LinearMap.liftBaseChange K (lTensorHomEquivHomLTensor k₀ W K W x) := by
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

/-- The canonical base-change map `K ⊗_{k₀} End_{k₀} W → End_K W_K` is **bijective** (for `W`
finite-dimensional): it is the composite of the two finite-free Hom/base-change equivalences. -/
private theorem tensorProduct_bijective :
    Function.Bijective (LinearMap.tensorProduct k₀ K W W) := by
  have hcomp :
      (⇑(LinearMap.tensorProduct k₀ K W W)) =
        (⇑(LinearMap.liftBaseChangeEquiv (R := k₀) (M := W) (N := K ⊗[k₀] W) K)) ∘
          (⇑(lTensorHomEquivHomLTensor k₀ W K W)) := by
    funext x; exact tensorProduct_eq_comp x
  rw [hcomp]
  exact (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)

private theorem tensorProduct_injective :
    Function.Injective (LinearMap.tensorProduct k₀ K W W) :=
  tensorProduct_bijective.injective

/-- **End base change is an isomorphism.** For `W` finite-dimensional, the canonical map
`K ⊗_{k₀} End_{k₀} W ≃ End_K (K ⊗_{k₀} W)` is a `K`-linear equivalence. -/
def endBaseChangeEquivGeneral :
    K ⊗[k₀] (W →ₗ[k₀] W) ≃ₗ[K] (K ⊗[k₀] W →ₗ[K] K ⊗[k₀] W) :=
  LinearEquiv.ofBijective (LinearMap.tensorProduct k₀ K W W) tensorProduct_bijective

@[simp] theorem endBaseChangeEquivGeneral_tmul (a : K) (h : W →ₗ[k₀] W) :
    endBaseChangeEquivGeneral (k₀ := k₀) (W := W) (K := K) (a ⊗ₜ[k₀] h)
      = a • LinearMap.baseChange K h := by
  simp only [endBaseChangeEquivGeneral, LinearEquiv.ofBijective_apply, tensorProduct_tmul]

omit [FiniteDimensional k₀ W] in
/-- `ρ_K g` is the base change of `ρ g`. -/
private theorem scalarExtension_apply_eq_baseChange (g : G) :
    (scalarExtension (k := K) ρ) g = LinearMap.baseChange K (ρ g) := rfl

omit [FiniteDimensional k₀ W] in
private theorem scalarExtension_linHom_tmul (g : G) (a : K) (h : W →ₗ[k₀] W) :
    (scalarExtension (k := K) (linHom ρ ρ)) g (a ⊗ₜ[k₀] h)
      = a ⊗ₜ[k₀] ((linHom ρ ρ) g h) := rfl

/-- `endBaseChangeEquivGeneral` is `G`-equivariant: it intertwines the scalar-extended conjugation action
`scalarExtension (linHom ρ ρ)` with the conjugation action `linHom ρ_K ρ_K` downstairs. -/
theorem endBaseChangeEquivGeneral_comm (g : G) (x : K ⊗[k₀] (W →ₗ[k₀] W)) :
    endBaseChangeEquivGeneral ((scalarExtension (k := K) (linHom ρ ρ)) g x) =
      (linHom (scalarExtension (k := K) ρ) (scalarExtension (k := K) ρ)) g
        (endBaseChangeEquivGeneral x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero,
      LinearEquiv.map_zero]
  | tmul a h =>
      rw [scalarExtension_linHom_tmul, endBaseChangeEquivGeneral_tmul, endBaseChangeEquivGeneral_tmul,
        linHom_apply, linHom_apply, scalarExtension_apply_eq_baseChange,
        scalarExtension_apply_eq_baseChange, LinearMap.smul_comp, LinearMap.comp_smul,
        ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  | add x y hx hy =>
      rw [LinearMap.map_add, LinearEquiv.map_add, LinearEquiv.map_add, LinearMap.map_add,
        hx, hy]

/-- Invariants of a representation as the kernel of the single difference map
`u ↦ (g ↦ W g u - u)`. -/
private theorem invariants_eq_ker_pi {R : Type*} [CommRing R] {U : Type*} [AddCommGroup U]
    [Module R U] [Fintype G] (W : Representation R G U) :
    invariants W = LinearMap.ker (LinearMap.pi (fun g => W g - LinearMap.id)) := by
  ext u
  simp only [mem_invariants, LinearMap.mem_ker, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.id_coe, id_eq, funext_iff, Pi.zero_apply, sub_eq_zero]

/-- **Flat base change of invariants.** For a finite-dimensional representation `W`, the dimension
of the invariants is preserved under scalar extension along the field extension `k₀ → K`. -/
theorem finrank_invariants_scalarExtension_eq_general [Finite G] {U : Type u} [AddCommGroup U]
    [Module k₀ U] [FiniteDimensional k₀ U] (W : Representation k₀ G U) :
    Module.finrank K (invariants (scalarExtension (k := K) W))
      = Module.finrank k₀ (invariants W) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  set δ : U →ₗ[k₀] (G → U) := LinearMap.pi (fun g => W g - LinearMap.id) with hδdef
  set e := TensorProduct.piRight k₀ K K (fun _ : G => U) with hedef
  set Φ := TensorProduct.AlgebraTensorModule.lTensor K K δ with hΦdef
  -- The scalar-extended difference map is `piRight ∘ (lTensor δ)`.
  have hfactor :
      LinearMap.pi (fun g => (scalarExtension (k := K) W) g - LinearMap.id)
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
        show (scalarExtension (k := K) W) g (a ⊗ₜ[k₀] u) - a ⊗ₜ[k₀] u = a ⊗ₜ[k₀] (W g u - u)
        rw [show (scalarExtension (k := K) W) g = LinearMap.baseChange K (W g) from rfl,
          LinearMap.baseChange_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hker : invariants (scalarExtension (k := K) W) = LinearMap.ker Φ := by
    rw [invariants_eq_ker_pi, hfactor, LinearMap.ker_comp,
      LinearMap.ker_eq_bot.mpr e.injective, Submodule.comap_bot]
  have hinj : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor K K (LinearMap.ker δ).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (LinearMap.ker δ).subtype
      (LinearMap.ker δ).injective_subtype
  rw [hker, hΦdef, Module.Flat.ker_lTensor_eq, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_baseChange (R := K) (S := k₀) (M' := LinearMap.ker δ),
    ← invariants_eq_ker_pi]

/-- **End base change is a dimension-preserving isomorphism.** The `k₀`-dimension of the
self-intertwiners of `ρ` equals the `K`-dimension of the self-intertwiners of its scalar extension
along the field extension `k₀ → K`. -/
theorem finrank_intertwiningMap_eq_baseChange [Finite G] :
    Module.finrank K
        (IntertwiningMap (scalarExtension (k := K) ρ) (scalarExtension (k := K) ρ))
      = Module.finrank k₀ (IntertwiningMap ρ ρ) := by
  -- `endBaseChangeEquivGeneral` carries the invariants of `scalarExtension (linHom ρ ρ)` onto those of
  -- `linHom ρ_K ρ_K`, by its `G`-equivariance.
  have hmap :
      Submodule.map endBaseChangeEquivGeneral.toLinearMap
          (invariants (scalarExtension (k := K) (linHom ρ ρ)))
        = invariants (linHom (scalarExtension (k := K) ρ) (scalarExtension (k := K) ρ)) := by
    ext y
    simp only [Submodule.mem_map, mem_invariants]
    constructor
    · rintro ⟨x, hx, rfl⟩ g
      simp only [LinearEquiv.coe_toLinearMap]
      rw [← endBaseChangeEquivGeneral_comm, hx g]
    · intro hy
      refine ⟨endBaseChangeEquivGeneral.symm y, fun g => ?_, by simp⟩
      apply endBaseChangeEquivGeneral.injective
      rw [endBaseChangeEquivGeneral_comm, LinearEquiv.apply_symm_apply, hy g]
  rw [← (invariantsEquivIntertwiningMap (scalarExtension (k := K) ρ)
        (scalarExtension (k := K) ρ)).finrank_eq,
    ← (invariantsEquivIntertwiningMap ρ ρ).finrank_eq,
    ← finrank_invariants_scalarExtension_eq_general (K := K) (linHom ρ ρ), ← hmap,
    ← (endBaseChangeEquivGeneral.submoduleMap
        (invariants (scalarExtension (k := K) (linHom ρ ρ)))).finrank_eq]

end FiniteDimensional

end Representation
