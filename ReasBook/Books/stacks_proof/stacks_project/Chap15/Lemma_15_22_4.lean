import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct nonZeroDivisors
open Module

/-
Domain-style sampling:
- primary domain: commutative algebra of torsion-free modules under flat base change;
- sampled owner API:
  `Module.IsTorsionFree`,
  `TensorProduct`,
  `Module.Flat`,
  `LinearEquiv.moduleIsTorsionFree`;
- best owner abstraction: the canonical owner is the tensor-product base change `S ⊗[R] M`,
  with `Module.IsTorsionFree` as the target owner predicate;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for `R' ⊗[R] M`;
  `core/canonical`: the tensor-product base-change object together with the owner predicate
    `Module.IsTorsionFree`;
  `bridge/view`: no extra bridge owner is needed here, since the source statement already lives on
    the canonical tensor-product base change and no direct downstream file uses an intermediate
    `IsBaseChange` formulation.

Primitive data are the flat algebra `R → S` and the torsion-free `R`-module `M`. The tensor
product `S ⊗[R] M` is already the canonical base-change object, so this file should expose only the
source-facing theorem instead of introducing an additional owner-level wrapper theorem.
-/

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
variable [Flat R R'] [AddCommGroup M] [Module R M] [IsTorsionFree R M]

omit [IsDomain R] in
/-- Helper for Lemma 15.22.4: the canonical map from a torsion-free module to its fraction-field
base change is injective. -/
lemma fractionRing_tensor_mk_injective :
    Function.Injective
      (TensorProduct.mk R (FractionRing R) M 1 : M →ₗ[R] ((FractionRing R) ⊗[R] M)) := by
  -- Torsion-freeness exactly says that every element of `R⁰` acts injectively on `M`.
  rw [IsLocalizedModule.injective_iff_isRegular (S := R⁰)
    (f := TensorProduct.mk R (FractionRing R) M 1)]
  intro s
  exact (le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) s).isSMulRegular

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free in
omit [IsTorsionFree R M] in
/-- Helper for Lemma 15.22.4: after tensoring the fraction-field embedding with the flat algebra
`R'`, the codomain is torsion-free over `R'`. -/
lemma fractionRing_tensor_baseChange_isTorsionFree :
    IsTorsionFree R' (R' ⊗[R] ((FractionRing R) ⊗[R] M)) := by
  let K := FractionRing R
  let T := R' ⊗[R] K
  let _ : Algebra K T := Algebra.TensorProduct.rightAlgebra
  let _ : IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) T := IsLocalization.tensor
    (S := R') (A := K) R⁰
  have _ : IsTorsionFree R R' := by
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.2 Module.Flat.torsion_eq_bot
  have hnonzero : Algebra.algebraMapSubmonoid R' R⁰ ≤ R'⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective R R') (le_refl R⁰)
  let _ : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hnonzero
  -- Over the fraction field, every module is flat, so tensoring once more with `T` stays flat.
  have hflat_tensor : Module.Flat T (T ⊗[K] (K ⊗[R] M)) := by infer_instance
  have htorsionfree_over_T : IsTorsionFree T (T ⊗[K] (K ⊗[R] M)) := by
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.2 Module.Flat.torsion_eq_bot
  -- Cancel the intermediate `K`-base change to rewrite the auxiliary module as `T ⊗[R] M`.
  let cancelEquiv : T ⊗[R] M ≃ₗ[T] T ⊗[K] (K ⊗[R] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R K T T M).symm
  have htorsionfree_left : IsTorsionFree T (T ⊗[R] M) :=
    cancelEquiv.injective.moduleIsTorsionFree _ fun t x => cancelEquiv.map_smul t x
  let _ : FaithfulSMul R' T := (faithfulSMul_iff_algebraMap_injective R' T).2 <|
    IsLocalization.injective _ hnonzero
  have htorsionfree_left_restrict : IsTorsionFree R' (T ⊗[R] M) :=
    Module.IsTorsionFree.trans_faithfulSMul R' T (T ⊗[R] M)
  -- Finally reassociate the three tensor factors back to the codomain used in the main proof.
  let assocEquiv : (T ⊗[R] M) ≃ₗ[R'] R' ⊗[R] (K ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.assoc R R R' R' K M
  exact assocEquiv.symm.injective.moduleIsTorsionFree _ fun r x => assocEquiv.symm.map_smul r x

/-- Lemma 15.22.4: if `R → R'` is a flat homomorphism of domains and `M` is a torsion-free
`R`-module, then the base-changed module `R' ⊗[R] M` is a torsion-free `R'`-module. -/
@[stacks 0AXM]
theorem isTorsionFree_baseChange_of_flat :
    IsTorsionFree R' (R' ⊗[R] M) := by
  let f : M →ₗ[R] (FractionRing R ⊗[R] M) := TensorProduct.mk R (FractionRing R) M 1
  -- The source proof first embeds `M` into its fraction-field tensor.
  have hf : Function.Injective f := fractionRing_tensor_mk_injective (R := R) (M := M)
  -- Flatness of `R'` preserves that injection after tensoring on the left.
  have hf_baseChange : Function.Injective (f.baseChange R') := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := R') f hf)
  -- The codomain of this tensored map is torsion-free over `R'`.
  have hcodomain :
      IsTorsionFree R' (R' ⊗[R] ((FractionRing R) ⊗[R] M)) :=
    fractionRing_tensor_baseChange_isTorsionFree (R := R) (R' := R') (M := M)
  -- Pull torsion-freeness back along the injective base-changed localization map.
  exact hf_baseChange.moduleIsTorsionFree _ fun r x => (f.baseChange R').map_smul r x

end
