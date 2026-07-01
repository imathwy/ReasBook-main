import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_5_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

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

-- Proof sketch: `Text_5_4_1_4` rewrites `d(·, C)` as the infimal convolution of the norm with
-- the indicator of `C`. The norm is convex by `Function.isConvex_norm`, and the indicator is
-- convex exactly when `C` is convex by `indicator_isConvex_iff`. Then apply
-- `Function.IsConvex.infimal_convolution` and rewrite back to `d(·, C)`.
/-- Text 5.4.1.5: for a convex set `C`, the distance-to-set function `x ↦ d(x, C)` is convex.
The source states this on `ℝ^n`; the canonical chapter owner statement is valid on any real
seminormed space. -/
theorem distanceToSet_isConvex
    (C : Set E) (hC : Convex ℝ C) :
    (fun x ↦ (d(x, C) : WithTopBot ℝ)).IsConvex ℝ := by
  classical
  have hconv : ((((norm : E → ℝ).toWithTopBot) □ (δ(· | C)))).IsConvex ℝ :=
    Function.IsConvex.infimal_convolution Function.isConvex_norm
      ((indicator_isConvex_iff C).2 hC)
  have hEq :
      (((norm : E → ℝ).toWithTopBot) □ (fun z ↦ if z ∈ C then (0 : WithTopBot ℝ) else ⊤)) =
        fun x ↦ (d(x, C) : WithTopBot ℝ) := by
    funext x
    simpa [indicator_def] using
      congrArg (fun F : E → WithTopBot ℝ => F x)
        (infimal_convolution_norm_indicator_eq_distanceToSet (C := C))
  exact hEq ▸ hconv

end
