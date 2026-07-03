import Mathlib

open LinearMap TensorProduct MulOpposite
open scoped TensorProduct

attribute [local instance] TensorProduct.Algebra.module

universe u v w

section

variable {k : Type u} {K : Type v} {V : Type w}
variable [Field k] [DivisionRing K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

/- Domain triage:
- primary domain: tensor products and submodules with commuting left/right scalar actions over a
  `k`-algebra `K`.
- sampled owner declarations: `Subbimodule.toSubmodule`, `Submodule.baseChange`,
  `Submodule.baseChange_eq_span`, `Submodule.map_comap_eq`.
- `source-facing`: a `k`-submodule of `V ⊗[k] K` stable under left and right multiplication on the
  `K`-factor, viewed through the canonical factor-swap `TensorProduct.comm k V K`.
- `core/canonical`: after commuting factors, a `K`-`K` subbimodule
  `W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)`.
- `bridge/view`: the corresponding `K`-submodule `Subbimodule.toSubmodule W` and its source-model
  transport back to `V ⊗[k] K`.

Primitive data vs derived API:
- primitive owner data: the ambient `K`-`K` subbimodule on `K ⊗[k] V`, and the source-facing
  `k`-submodule together with its left/right stability data;
- derived/source-facing data: the underlying left `K`-submodule, together with the corresponding
  generation/base change descriptions in the two tensor models.
-/

/-- Right multiplication on the `K`-factor of `K ⊗[k] V` is the canonical `Kᵐᵒᵖ`-action coming
from the first tensor factor. -/
@[simp] theorem op_smul_eq_rTensor_mulRight (a : K) (x : K ⊗[k] V) :
    op a • x = (((mulRight k a).rTensor V) : K ⊗[k] V →ₗ[k] K ⊗[k] V) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b v =>
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

section TwoSidedSubmodule

variable [Algebra.IsCentral k K]

/-- Lemma 11.4.3, source-facing bridge/view: for a `k`-vector space `V` and a central
`k`-division algebra `K`, a `k`-submodule of `V ⊗[k] K` stable under left and right
multiplication on the `K`-factor is obtained by transporting back the left `K`-span of the
intersection of its commuted image with `1 ⊗ V`. -/
theorem two_sided_submodule_eq_generated_by_inter_tmul_one
    (W : Submodule k (V ⊗[k] K))
    (hW_left :
      ∀ a : K,
        Set.MapsTo (((mulLeft k a).lTensor V) : V ⊗[k] K →ₗ[k] V ⊗[k] K) W W)
    (hW_right :
      ∀ a : K,
        Set.MapsTo (((mulRight k a).lTensor V) : V ⊗[k] K →ₗ[k] V ⊗[k] K) W W)
    :
    let W' : Submodule k (K ⊗[k] V) := W.map (TensorProduct.comm k V K).toLinearMap
    ((Submodule.span K ↑(W' ⊓ LinearMap.range (mk k K V 1))).restrictScalars k).map
      (TensorProduct.comm k K V).toLinearMap = W := by
  sorry

/-- Core/canonical bridge for Lemma 11.4.3: for a `k`-vector space `V` and a central
`k`-division algebra `K`, a two-sided `K`-submodule of `K ⊗[k] V` is the base change of its
contraction along `v ↦ 1 ⊗ v`. -/
theorem two_sided_submodule_eq_baseChange_comap_one_tmul
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    let V' := ((Subbimodule.toSubmodule W).restrictScalars k).comap
      (mk k K V 1)
    V'.baseChange K = Subbimodule.toSubmodule W := sorry

/-- Bridge/view companion to Lemma 11.4.3, in the commuted owner model `K ⊗[k] V`: for a central
`k`-division algebra `K`, a two-sided `K`-submodule is the left `K`-span of its intersection with
`1 ⊗ V`. -/
theorem two_sided_submodule_comm_eq_generated_by_inter_tmul_one
    (W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] V)) :
    Submodule.span K ↑((Subbimodule.toSubmodule W).restrictScalars k ⊓
      LinearMap.range (mk k K V 1)) = Subbimodule.toSubmodule W := by
  simpa [Submodule.baseChange_eq_span, Submodule.map_comap_eq, inf_comm] using
    two_sided_submodule_eq_baseChange_comap_one_tmul W

end TwoSidedSubmodule

end
