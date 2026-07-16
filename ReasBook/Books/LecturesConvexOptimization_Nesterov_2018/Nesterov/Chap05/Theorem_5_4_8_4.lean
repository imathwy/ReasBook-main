import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.RealProdL2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_3_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_4_7_6
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_8_9
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_8_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

/- Theorem 5.4.8.4 lies in the Chapter 5 self-concordant-barrier / epigraph domain for
`x ↦ x log x`.

Sampled owner declarations:
* `entropyEpigraphCone`, `entropyEpigraphConeBarrier`, and
  `entropyEpigraphConeBarrier_is_three_self_concordant_barrier` from `Theorem_5_4_7_6`, the
  upstream Chapter 5 owner/view for the entropy-epigraph cone and its canonical `3`-barrier;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the chapter
  owner theorem for affine pullbacks of self-concordant barriers;
* `Q₃` and `mem_Q₃_iff` from `Definition_5_4_8_9`, the source-facing owner/view for the textbook
  epigraph;
* `separableLogBarrierF3` and `separableLogBarrierF3_apply` from `Definition_5_4_8_10`, the
  source-facing owner/view for `F₃`.

Best owner abstraction:
* source-facing: the textbook epigraph `Q₃` and barrier `F₃`;
* core/canonical: `entropyEpigraphConeBarrier_is_three_self_concordant_barrier` together with
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`;
* bridge/view: the affine slice `((x, 1), t)` identifying `Q₃` and `F₃` with the upstream cone
  and barrier owners.

Primitive data:
* the canonical source-facing owners `Q₃` and `F₃`;
* the upstream cone/barrier owners from `Theorem_5_4_7_6`.

Derived API:
* the slice-domain bridge `((x, 1), t) ∈ interior entropyEpigraphCone ↔ (x, t) ∈ interior Q₃`;
* the direct slice identity `F₃ (x, t) = entropyEpigraphConeBarrier ((x, 1), t)`;
* the source-facing `3`-self-concordant-barrier theorem for `F₃`, obtained as an affine pullback.

This file therefore keeps `Q₃` and `F₃` source-facing, but removes the impression of a second
independent owner-level barrier theorem by presenting them through the `x₂ = 1` affine slice of
the upstream entropy-epigraph cone barrier. -/

local notation "F₃" => separableLogBarrierF3

-- Proof sketch: `interior entropyEpigraphCone` is the strict version of the entropy-epigraph
-- cone inequalities. On the slice `x₂ = 1`, this becomes `x > 0` and `t > x log x`, which is
-- exactly `interior Q₃`.
/-- On the affine slice `((x, 1), t)`, membership in `interior entropyEpigraphCone` is exactly
membership in `interior Q₃`. -/
theorem mem_interior_entropyEpigraphCone_secondUnitSlice_iff (x t : ℝ) :
    ((x, 1), t) ∈ interior entropyEpigraphCone ↔ (x, t) ∈ interior Q₃ := sorry

-- Proof sketch: the interior of the canonical closed epigraph from Definition 5.4.8.9 is
-- obtained by replacing the boundary inequalities `x ≥ 0` and `t ≥ x log x` with the strict
-- inequalities `x > 0` and `t > x log x`.
/-- A pair `(x, t)` lies in the interior of the canonical epigraph for Definition 5.4.8.9
exactly when `x > 0` and `t > x log x`. -/
theorem mem_interior_constrainedEpigraph_xlogx_iff {x t : ℝ} :
    (x, t) ∈ interior Q₃ ↔
      0 < x ∧ t > x * Real.log x := sorry

-- Proof sketch: identify the interior of the canonical closed epigraph from
-- Definition 5.4.8.9 with the affine slice `x₂ = 1` of the canonical entropy-epigraph cone
-- from Theorem 5.4.7.6. The upstream barrier theorem pulls back along the affine map
-- `p ↦ ((p.1, 1), p.2)`, and the slice-domain bridge together with the defining slice formula
-- for `F₃` identify the result with the source-facing owners `Q₃` and `F₃`.
/-- Theorem 5.4.8.4: the function `F₃(x, t) = -\log x - \log (t - x \log x)` is a
`3`-self-concordant barrier for the epigraph
`Q₃ = {(x, t) ∈ \mathbb{R}^2 \mid x ≥ 0,\ t ≥ x \log x}` of `x \log x`, with the convention
`0 \log 0 = 0`. -/
theorem separableLogBarrierF3_is_three_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith (interior Q₃) (3 : NNReal) F₃ := by
  let g : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).toContinuousAffineMap +ᵥ
      ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (1 : ℝ)), (0 : ℝ))
  have hg_apply (p : ℝ × ℝ) : g p = ((p.1, 1), p.2) := by
    simp [g]
  let hslice :
      IsSelfConcordantBarrierOnWith
        (g ⁻¹' interior entropyEpigraphCone)
        (3 : NNReal)
        (entropyEpigraphConeBarrier ∘ g) :=
    entropyEpigraphConeBarrier_is_three_self_concordant_barrier.comp_continuousAffineMap
      g
  have hdom : g ⁻¹' interior entropyEpigraphCone = interior Q₃ := by
    ext p
    change g p ∈ interior entropyEpigraphCone ↔ p ∈ interior Q₃
    rw [hg_apply]
    simpa using mem_interior_entropyEpigraphCone_secondUnitSlice_iff p.1 p.2
  have hfun : entropyEpigraphConeBarrier ∘ g = F₃ := by
    funext p
    change entropyEpigraphConeBarrier (g p) = F₃ p
    rw [hg_apply]
    change separableLogBarrierF3 p = separableLogBarrierF3 p
    rfl
  simpa [hdom, hfun] using hslice
