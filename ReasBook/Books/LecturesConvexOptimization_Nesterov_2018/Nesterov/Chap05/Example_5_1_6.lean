import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Corollary_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_2_8
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_7
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Example 5.1.6 lies in the Chapter 5 self-concordance / strong-convexity / Hessian-Lipschitz
domain.

Sampled owner-style declarations:
* `StrongConvexOn`, the canonical owner for whole-space strong convexity;
* `HasLipschitzContinuousHessian` and the theorem-surface notation `f ∈ C22[L₃]` from
  `Definition_5_0_7`, the canonical chapter owner for whole-space Hessian-Lipschitz smoothness;
* `fderiv ℝ (hessian f) x u` from `Definition_5_0_8`, the canonical Chapter 5 owner for the
  directional derivative of the Hessian operator;
* `IsSelfConcordantOnWith.of_thirdDerivative_operator_le` from `Corollary_5_1_1`, the canonical
  owner-level bridge from the operator inequality to `IsSelfConcordantOnWith`;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the stronger Chapter 5 owner that packages
  open-convex `C³` self-concordance data.

Source/core/bridge triage:
* source-facing: the Hessian-operator inequality
  `D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)} ∇²f(x)` at a point `x`, obtained from
  `StrongConvexOn Set.univ σ2 f`, `f ∈ C22[L3]`, and the pointwise `C³` regularity needed to
  interpret `D³f(x)[u]`;
* core/canonical: `StrongConvexOn Set.univ σ2 f`, `f ∈ C22[L3]`, `fderiv ℝ (hessian f) x u`,
  `hessian f x`, and `‖u‖[f; x]`;
* bridge/view: `IsSelfConcordantOnWith.of_thirdDerivative_operator_le`, which converts this
  source-facing operator inequality into the Chapter 5 owner `IsSelfConcordantOnWith`.

Primitive data:
* the objective `f`;
* the strong-convexity parameter `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* the owner hypotheses `StrongConvexOn Set.univ σ2 f` and `f ∈ C22[L3]`;
* the pointwise regularity witness `ContDiffAt ℝ 3 f x`, needed to interpret the operator
  `fderiv ℝ (hessian f) x u` as the genuine third derivative `D³f(x)[u]`.

Derived API:
* the operator inequality
  `fderiv ℝ (hessian f) x u ≤
    ((L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)}) • ∇² f(x)`;
* under the extra bridge hypothesis `ContDiff ℝ 3 f`, the Chapter 5 owner
  `IsSelfConcordantOnWith Set.univ
    (Real.toNNReal ((L3 : ℝ) / (2 * σ2 * Real.sqrt σ2))) f`.

This refinement keeps Example 5.1.6 itself at the source-facing `StrongConvexOn + C22[L₃]`
layer and exposes its main conclusion directly on the canonical Hessian owner
`fderiv ℝ (hessian f) x u`. The stronger global `C³` packaging into
`IsSelfConcordantOnWith` remains a separate bridge theorem obtained through
`IsSelfConcordantOnWith.of_thirdDerivative_operator_le`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {f : E → ℝ} {σ2 : ℝ} {L3 : NNReal}

namespace StrongConvexOn

variable (hf_strong : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2) (hf_hessian : f ∈ C22[L3])
include hf_strong hσ2 hf_hessian

-- Proof sketch: use `ContDiffAt ℝ 3 f x` to identify `fderiv ℝ (hessian f) x u` with the genuine
-- directional third derivative operator `D³f(x)[u]`. The `C22[L₃]` hypothesis gives the operator
-- norm bound `‖D³f(x)[u]‖ ≤ L₃ ‖u‖`, while strong convexity yields the Loewner lower bound
-- `σ₂ • 1 ≤ hessian f x`, hence `‖v‖ ≤ ‖v‖[f; x] / √σ₂` for every `v`. Applying this estimate to
-- both slots of the bilinear operator `D³f(x)[u]` gives
-- `D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖[f; x] • ∇²f(x)`.
/-- Example 5.1.6: if `f` is strongly convex on all of `E` with parameter `σ₂`, belongs to the
chapter smoothness class `C22[L₃]`, and is `C³` at `x`, then the directional derivative of its
Hessian satisfies the operator inequality
`D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)} ∇²f(x)`. This keeps the example at the
source-facing operator layer used by Corollary 5.1.1. -/
theorem thirdDerivative_operator_le_of_mem_C22
    {x u : E} (h_contDiffAt : ContDiffAt ℝ 3 f x) :
    fderiv ℝ (hessian f) x u ≤
      (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) • hessian f x := sorry

-- Proof sketch: use `IsSelfConcordantOnWith.of_thirdDerivative_operator_le` with
-- `dom = Set.univ`.
-- The preceding theorem supplies the operator inequality with coefficient
-- `2 * (L₃ / (2 * σ₂ * √σ₂))`, while `hf_strong` gives convexity on `Set.univ` and the global
-- hypothesis `h_contDiff` provides the required `C³` regularity on `Set.univ`.
/-- Bridge theorem: adding the separate `C³` hypothesis upgrades the operator estimate from
Example 5.1.6 to the Chapter 5 owner `IsSelfConcordantOnWith`; the modulus is converted to the
owner `strongConvexSelfConcordanceConstant σ₂ L₃`. -/
theorem isSelfConcordantOnWith_of_mem_C22_contDiff
    (h_contDiff : ContDiff ℝ 3 f) :
    IsSelfConcordantOnWith Set.univ
      (strongConvexSelfConcordanceConstant σ2 L3) f := by
  refine IsSelfConcordantOnWith.of_thirdDerivative_operator_le isOpen_univ ?_ ?_ ?_
  · simpa using h_contDiff.contDiffOn
  · simpa [strongConvexOn_zero] using (hf_strong.mono hσ2.le : StrongConvexOn Set.univ 0 f)
  · intro x _hx u
    change fderiv ℝ (hessian f) x u ≤
      (2 * (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) * ‖u‖[f; x]) •
        hessian f x
    have hthird :
        fderiv ℝ (hessian f) x u ≤
          (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) • hessian f x :=
      hf_strong.thirdDerivative_operator_le_of_mem_C22 hσ2 hf_hessian
        (show ContDiffAt ℝ 3 f x from h_contDiff.contDiffAt)
    rw [two_mul_coe_strongConvexSelfConcordanceConstant hσ2]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hthird

omit hf_strong hσ2 hf_hessian

end StrongConvexOn

end
