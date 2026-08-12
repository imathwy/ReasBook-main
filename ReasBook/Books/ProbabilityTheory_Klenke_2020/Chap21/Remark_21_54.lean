import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_52

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

/-- The path obtained by integrating a real function from `0` to `t`. -/
def indefiniteIntegralPath (f : ℝ → ℝ) : PathSpace where
  toFun t := ∫ s in (0 : ℝ)..(t : ℝ), f s
  continuous_toFun := by
    sorry

/-- The positive Jordan-variation part `G_t^+ = (V_t^1(G) + G_t) / 2`. -/
def positiveVariationPart (G : PathSpace) : NNReal → ℝ :=
  fun t ↦ (variationProcess G t + G t) / 2

/-- The negative Jordan-variation part `G_t^- = (V_t^1(G) - G_t) / 2`. -/
def negativeVariationPart (G : PathSpace) : NNReal → ℝ :=
  fun t ↦ (variationProcess G t - G t) / 2

/-- The signed Lebesgue--Stieltjes integral on `[0,t]`, defined from the Jordan decomposition of a
signed measure. -/
def signedLebesgueStieltjesIntegralUpTo
    (F : ℝ → ℝ) (μ : SignedMeasure ℝ) (t : NNReal) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.posPart -
    ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.negPart

-- Proof sketch: view `t ↦ ∫_0^t f(s) ds` as an absolutely continuous path on every compact
-- interval `[0, t]`; its variation on that interval is the integral of `|f|`, and therefore the
-- path has locally bounded variation on `[0, ∞)`.
/-- A locally integrable density defines a path of locally bounded variation on `[0, ∞)`. -/
theorem locallyBoundedVariationOn_univ_indefiniteIntegralPath
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyBoundedVariationOn (indefiniteIntegralPath f) univ := sorry

-- Proof sketch: absolute continuity identifies the variation of the indefinite integral on
-- `[0, t]` with the integral of the absolute value of the density.
/-- Remark 21.54 (1): if `G_t = ∫_0^t f(s) ds` for a locally integrable density `f`, then the
variation path of `G` is given by the integral of `|f|`. -/
theorem variationProcess_indefiniteIntegralPath_eq_intervalIntegral_abs
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (t : NNReal) :
    variationProcess (indefiniteIntegralPath f) t = ∫ s in (0 : ℝ)..(t : ℝ), |f s| := sorry

-- Proof sketch: every increment of `G = G⁺ - G⁻` is bounded in absolute value by the sum of the
-- corresponding monotone increments of `G⁺` and `G⁻`; taking the supremum over partitions yields
-- the claimed variation bound.
/-- Remark 21.54 (2): if `G = G⁺ - G⁻` with `G⁺` and `G⁻` continuous monotone increasing, then the
variation increment of `G` on `[s,t]` is bounded by the sum of the increments of `G⁺` and `G⁻`. -/
theorem variationOnFromTo_sub_le_add_of_monotone
    {G Gplus Gminus : PathSpace} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) {s t : NNReal} (hst : s ≤ t) :
    variationOnFromTo G univ s t ≤
      (Gplus t - Gplus s) + (Gminus t - Gminus s) := sorry

-- Proof sketch: `G⁺` and `G⁻` are monotone on `univ`, hence each has locally bounded variation;
-- the interval estimate in `variationOnFromTo_sub_le_add_of_monotone` then yields the same
-- property for `G`.
/-- A difference of two continuous monotone increasing paths has locally bounded variation on
`[0, ∞)`. -/
theorem locallyBoundedVariationOn_univ_of_sub_monotone
    {G Gplus Gminus : PathSpace} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) :
    LocallyBoundedVariationOn G univ := sorry

-- Proof sketch: for a path of locally bounded variation, `variationProcess G` is monotone, and
-- the classical inequalities `-V_t^1(G) ≤ G_t ≤ V_t^1(G)` imply that `(V_t^1(G) ± G_t)/2`
-- inherit monotonicity.
/-- Remark 21.54 (3): if `G` has locally bounded variation on `[0, ∞)`, then the canonical
Jordan-variation parts
`G_t^+ = (V_t^1(G) + G_t)/2` and `G_t^- = (V_t^1(G) - G_t)/2` are monotone increasing. -/
theorem monotone_positive_and_negative_variationParts_of_locallyBoundedVariationOn
    {G : PathSpace} (hG : LocallyBoundedVariationOn G univ) :
    Monotone (positiveVariationPart G) ∧ Monotone (negativeVariationPart G) := sorry

-- Proof sketch: expand the definitions of `positiveVariationPart` and `negativeVariationPart`; the
-- `variationProcess` terms cancel algebraically.
/-- The positive and negative variation parts reconstruct the original path by subtraction. -/
theorem positiveVariationPart_sub_negativeVariationPart (G : PathSpace) :
    positiveVariationPart G - negativeVariationPart G = G := sorry

/-- Unfolding `signedLebesgueStieltjesIntegralUpTo` gives the Jordan-decomposition formula for the
signed Lebesgue--Stieltjes integral on `[0,t]`. -/
theorem signedLebesgueStieltjesIntegralUpTo_eq
    (F : ℝ → ℝ) (μ : SignedMeasure ℝ) (t : NNReal) :
    signedLebesgueStieltjesIntegralUpTo F μ t =
      ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.posPart -
        ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.negPart :=
  rfl
