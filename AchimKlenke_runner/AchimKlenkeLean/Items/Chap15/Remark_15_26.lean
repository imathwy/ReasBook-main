import AchimKlenkeLean.Items.Chap15.Corollary_15_25
import AchimKlenkeLean.Items.Chap16.Definition_16_20

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

noncomputable section

-- Proof sketch: identify the characteristic function of `measureConvolutionPower μ n` as the `n`th
-- power of `charFun μ`, compare it with the characteristic function of the scaled law using the
-- assumed scaling identity, and conclude by uniqueness of characteristic functions.
/-- A characteristic-function scaling law yields strict stability with index `α` in the canonical
owner abstraction `IsStableWithIndex` once the owner side conditions are supplied explicitly. -/
theorem isStableWithIndex_of_charFun_scaling
    (μ : ProbabilityMeasure ℝ) {α : ℝ}
    (hμ_not_dirac : ∀ x : ℝ, μ ≠ diracProba x)
    (hα : α ∈ Set.Ioc (0 : ℝ) 2)
    (hφ : ∀ n : ℕ+, ∀ t : ℝ,
      charFun μ t ^ (n : ℕ) = charFun μ (((n : ℝ) ^ (1 / α)) * t)) :
    IsStableWithIndex μ α := sorry

-- Proof sketch: compute both sides from the explicit formula
-- `exp (-|r t|^α)` and use `|r * ((n : ℝ) ^ (1 / α) * t)|^α = n * |r * t|^α`.
/-- The symmetric stable characteristic functions satisfy the scaling identity that characterizes
strict stability. -/
theorem symmetricStableCharFun_charFun_scaling
    {α r : ℝ} (hα₀ : 0 < α) :
    ∀ n : ℕ+, ∀ t : ℝ,
      symmetricStableCharFun α r t ^ (n : ℕ) =
        symmetricStableCharFun α r (((n : ℝ) ^ (1 / α)) * t) := sorry

-- Proof sketch: combine `hμ` with `symmetricStableCharFun_charFun_scaling` and invoke
-- `isStableWithIndex_of_charFun_scaling`; the extra hypothesis `r ≠ 0` rules out the Dirac case
-- `symmetricStableCharFun α 0 = 1`.
/-- Remark 15.26: every probability law whose characteristic function is
`t ↦ exp (-|r t|^α)` with `r ≠ 0` is strictly stable with index `α`. -/
theorem isStableWithIndex_of_charFun_eq_symmetricStableCharFun
    (μ : ProbabilityMeasure ℝ) {α r : ℝ}
    (hα : α ∈ Set.Ioc (0 : ℝ) 2) (hr : r ≠ 0)
    (hμ : ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t) :
    IsStableWithIndex μ α := by
  apply isStableWithIndex_of_charFun_scaling μ
  · sorry
  · exact hα
  · intro n t
    rw [hμ, symmetricStableCharFun_charFun_scaling hα.1, ← hμ]

-- Proof sketch: extend the existence statement from Corollary 15.25 to all `α ∈ (0,2]`, keep the
-- source-facing symmetric law visible, and combine the resulting characteristic-function identity
-- with `isStableWithIndex_of_charFun_eq_symmetricStableCharFun`.
/-- Remark 15.26: for every `α ∈ (0,2]` and every nonzero `r ∈ ℝ`, there exists a symmetric
probability law on `ℝ` with characteristic function `t ↦ exp (-|r t|^α)`, and this law is
strictly stable with index `α`. -/
theorem exists_symmetricProbabilityMeasure_isStableWithIndex_charFun_eq_symmetricStableCharFun
    (α r : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 2) (hr : r ≠ 0) :
    ∃ μ : ProbabilityMeasure ℝ, ((μ : Measure ℝ)).IsNegInvariant ∧
      IsStableWithIndex μ α ∧
      ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t := sorry
