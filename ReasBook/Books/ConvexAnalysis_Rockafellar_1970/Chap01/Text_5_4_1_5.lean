import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_5_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.5 asserts that for a convex set `C`, the distance-to-set function
  `x ↦ d(x, C)` is convex.
- `core/canonical`: the owner abstractions are the chapter distance notation `d(x, C)` from
  `Defintion_4_8_3`, the previous identity
  `infimal_convolution_norm_indicator_eq_distanceToSet` from `Text_5_4_1_4`, the norm-convexity
  theorem `Function.isConvex_norm`, the indicator bridge `indicator_isConvex_iff`, and the
  binary infimal-convolution convexity theorem `Function.IsConvex.infimal_convolution`.
- `bridge/view`: the corollary identifies `d(·, C)` with the infimal convolution of the norm and
  the indicator of `C`, then applies the convexity owners for those two factors.

Domain-style sampling used here:
- `Function.isConvex_norm`;
- `indicator_isConvex_iff`;
- `Function.IsConvex.infimal_convolution`;
- `infimal_convolution_norm_indicator_eq_distanceToSet`.

Ambient minimization: although the source states the result on `ℝ^n`, every owner used here lives
on an arbitrary real seminormed space, so the public statement is kept at that intrinsic level.
-/

private theorem infimal_convolution_norm_indicator_eq_distanceToSet_withTopBot
    (C : Set E) :
    (((norm : E → ℝ).toWithTopBot) □ (δ[ℝ](· | C))) =
      fun x : E ↦ ⨅ z : C, ((dist x z : ℝ) : WithTopBot ℝ) := by
  funext x
  rw [infimal_convolution_apply]
  calc
    (⨅ y : E, ((‖y‖ : ℝ) : WithTopBot ℝ) + δ[ℝ](x - y | C)) =
        ⨅ y : E, if x - y ∈ C then ((‖y‖ : ℝ) : WithTopBot ℝ) else ⊤ := by
      refine iInf_congr fun y ↦ ?_
      by_cases hy : x - y ∈ C <;> simp [indicator_def, hy]
    _ = ⨅ y : E, ⨅ (_ : x - y ∈ C), ((‖y‖ : ℝ) : WithTopBot ℝ) := by
      refine iInf_congr fun y ↦ ?_
      by_cases hy : x - y ∈ C <;> simp [hy]
    _ = ⨅ y : {y : E // x - y ∈ C}, ((‖(y : E)‖ : ℝ) : WithTopBot ℝ) := by
      rw [iInf_subtype']
    _ = ⨅ z : C, ((dist x z : ℝ) : WithTopBot ℝ) := by
      let e : {y : E // x - y ∈ C} ≃ C := sub_mem_equiv_set_member (C := C) x
      refine Equiv.iInf_congr e ?_
      intro y
      simp [e, sub_mem_equiv_set_member]

-- Proof sketch: the canonical `WithTopBot` distance view is the infimal convolution of the norm
-- with the indicator of `C`. The norm and indicator are convex, and neither takes the value
-- `⊥`, so binary infimal-convolution convexity applies.
/-- Text 5.4.1.5: for a convex set `C`, the distance-to-set function `x ↦ d(x, C)` is convex.
The source states this on `ℝ^n`; the canonical chapter owner statement is valid on any real
seminormed space. -/
theorem distanceToSet_isConvex
    (C : Set E) (hC : Convex ℝ C) :
    (fun x : E ↦ ⨅ z : C, ((dist x z : ℝ) : WithTopBot ℝ)).IsConvex ℝ := by
  classical
  have hconv : ((((norm : E → ℝ).toWithTopBot) □ (δ(· | C)))).IsConvex ℝ :=
    Function.IsConvex.infimal_convolution Function.isConvex_norm
      (by
        intro x
        exact (WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe (‖x‖ : ℝ))).ne')
      ((indicator_isConvex_iff C).2 hC)
      (by
        intro x
        by_cases hx : x ∈ C
        · rw [indicator_of_mem C hx]
          exact (WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe (0 : ℝ))).ne'
        · rw [indicator_of_notMem C hx]
          exact top_ne_bot)
  have hEq :
      (((norm : E → ℝ).toWithTopBot) □ (fun z ↦ if z ∈ C then (0 : WithTopBot ℝ) else ⊤)) =
        fun x : E ↦ ⨅ z : C, ((dist x z : ℝ) : WithTopBot ℝ) := by
    simpa [indicator_def] using
      infimal_convolution_norm_indicator_eq_distanceToSet_withTopBot (C := C)
  exact hEq ▸ hconv

end
