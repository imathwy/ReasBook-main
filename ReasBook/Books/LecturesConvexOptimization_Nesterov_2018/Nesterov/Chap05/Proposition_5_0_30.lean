import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_16
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_1_3
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_27
import LecturesConvexOptimization_Nesterov_2018.Chap05.Proposition_5_0_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 5.0.30 lies in the chapter's Fenchel-conjugacy / third-order differential-calculus
domain.

Sampled owner-style declarations:
* `fenchelDual` / notation `f⋆` in `Definition_5_0_27`, the chapter owner for the Fenchel dual;
* `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical finite-value
  domain / finite-real-part owners for `EReal`-valued functions;
* `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y` on `dom f`;
* `gradient` / notation `∇`, the canonical first-order owner for the branch equation
  `∇ f (xStar s) = s`;
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order owner;
* `fderiv ℝ (hessian g) x h` in `Definition_5_0_8`, the chapter owner for third derivatives;
* `fenchelConjugate_hessian_eq_inverse` in `Proposition_5_0_29`, the chapter owner for the
  preceding inverse-Hessian identity on `dom (f⋆)`;
* `exists_continuousLinearEquiv_fderiv_symm_eq` in mathlib, the canonical local-inverse
  differentiability bridge for genuine invertible Fréchet derivatives.

Best owner abstraction:
* source-facing: the third-derivative formula for `extendedRealRealPart (f⋆)` along a chosen
  Fenchel-maximizer branch `xStar : E → E` on `dom (f⋆)`;
* core/canonical: `extendedRealRealPart (f⋆)`, `hessian`, `∇`, and `IsMaxOn`;
* bridge/view: the prior identity
  `hessian (extendedRealRealPart (f⋆)) s = (hessian (withTopRealPart f) (xStar s)).inverse`.

Primitive data:
* the primal `WithTop ℝ`-valued function `f`;
* a branch `xStar : E → E` on `dom (f⋆)`;
* the source-facing facts that `xStar s` is the Fenchel-support maximizer at `s`,
  lies in `interior (dom f)`, and has invertible primal Hessian at those branch points.

Derived API:
* the branch derivative identity
  `HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s`, exposed as the public bridge
  theorem `fenchelConjugate_maximizerBranch_hasFDerivAt` and recovered from the unique interior
  maximizer branch via the local-inverse / gradient bridge;
* the third-derivative formula for `extendedRealRealPart (f⋆)`;
* the actual inverse-Hessian presentation recovered from Proposition 5.0.29 under the explicit
  invertibility hypothesis.

Source/core/bridge triage:
* source-facing: the branchwise `D³ f_*` formula on `dom (f⋆)`;
* core/canonical: the dual Hessian owner `hessian (extendedRealRealPart (f⋆))`;
* bridge/view: the reusable inverse-Hessian identity supplied separately by
  `fenchelConjugate_hessian_eq_inverse`, together with the branch-differentiability bridge theorem
  `fenchelConjugate_maximizerBranch_hasFDerivAt`.

The previous version kept a local copy of the inverse-Hessian relation as primitive data and used
Lean's totalized `ContinuousLinearMap.inverse` without recording either genuine invertibility or
the derivative of the maximizing branch. That weakened the textbook meaning. This refinement
restores the Proposition 5.0.29 owner hypotheses, keeps the branch `xStar` source-facing, exposes
the missing branch-differentiability data `DxStar(s) = ∇² f_*(s)` as a reusable bridge theorem
derived from the unique interior maximizer branch and the local-inverse / gradient bridge, and no
longer smuggles that step in as primitive theorem data. The first-order branch equation is not
retained as primitive data here, because this file reuses the upstream inverse-Hessian owner
theorem rather than reproving it. -/

section

-- Proof sketch: first derive `HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s`
-- as a reusable bridge theorem from the unique interior Fenchel-maximizer branch and the local-
-- inverse / gradient bridge around `xStar s`. Then differentiate the genuine inverse-Hessian
-- identity from Proposition 5.0.29 along that branch. The bridge step itself is only `C²`; the
-- `C³` hypothesis is used only for differentiating the primal Hessian at `xStar s`, and the
-- explicit invertibility hypothesis makes that inverse an actual inverse rather than Lean's
-- totalized fallback.
/-- The Fenchel-maximizer branch is differentiable with derivative
`∇² (extendedRealRealPart (f⋆)) s` at every dual-domain point once the maximizing branch is
unique, interior, and has genuinely invertible primal Hessian there. This is the public bridge
from the chosen Fenchel-support maximizer branch to the canonical dual Hessian owner used in
Proposition 5.0.30. -/
theorem fenchelConjugate_maximizerBranch_hasFDerivAt
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    {s : E} (hs : s ∈ dom (f⋆)) :
    HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s := by
  sorry

/-- Proposition 5.0.30: let `xStar : E → E` be a chosen Fenchel-support maximizer branch on
`dom (f⋆)`. Assume `xStar s ∈ interior (dom f)` and the primal Hessian at `xStar s` is genuinely
invertible. Then the derivative of the dual Hessian at `s` is the third-derivative composition
formula obtained by differentiating the genuine inverse-Hessian identity from Proposition 5.0.29
along the public branch derivative `DxStar(s) = ∇² (extendedRealRealPart (f⋆)) s`.
This remains the source-facing branch theorem; the inverse-Hessian relation and the branch
differentiability are both reused through the upstream owner theorem
`fenchelConjugate_hessian_eq_inverse` and the public bridge theorem
`fenchelConjugate_maximizerBranch_hasFDerivAt` rather than copied as primitive theorem data. -/
theorem fenchelConjugate_hessianDerivative_formula
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    {s : E} (hs : s ∈ dom (f⋆))
    (h : E) :
    fderiv ℝ (hessian (extendedRealRealPart (f⋆))) s h =
      -((hessian (extendedRealRealPart (f⋆)) s).comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (extendedRealRealPart (f⋆)) s))) := by
  have hxStar_hasFDerivAt :
      HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s :=
    fenchelConjugate_maximizerBranch_hasFDerivAt (hf_contDiff.of_le (by norm_num)) hxStar_mem
      hxStar_isMaximizer hxStar_unique hxStar_hessian_invertible hs
  sorry

end
