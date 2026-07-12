import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Source-facing strict `α`-stability for real probability laws. Unlike the chapter owner
`IsStableWithIndex`, this predicate keeps the textbook positivity and scaling law visible without
baking in the later conclusion that `α ≤ 2`. -/
def IsStrictlyStableWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  0 < α ∧
    (∀ x : ℝ, μ ≠ diracProba x) ∧
      ∀ n : ℕ+,
        μ ^ (n : ℕ) =
          map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) 0).aemeasurable

/-- Source-facing broad `α`-stability for real probability laws. This keeps the centering data in
the public interface while deferring only the later upper bound `α ≤ 2` to a bridge lemma. -/
def IsBroadlyStableWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  0 < α ∧
    (∀ x : ℝ, μ ≠ diracProba x) ∧
      ∃ d : ℕ+ → ℝ,
        ∀ n : ℕ+,
          μ ^ (n : ℕ) =
            map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable

variable {μ : ProbabilityMeasure ℝ} {α : ℝ}

namespace IsStrictlyStableWithIndex

/-- On the admissible index range, the source-facing strict `α`-stability predicate specializes to
the chapter owner abstraction `IsStableWithIndex`. -/
theorem toIsStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) (hα : α ≤ 2) :
    IsStableWithIndex μ α :=
  ⟨hμ.2.1, ⟨hμ.1, hα⟩, hμ.2.2⟩

end IsStrictlyStableWithIndex

namespace IsBroadlyStableWithIndex

/-- On the admissible index range, the source-facing broad `α`-stability predicate specializes to
the chapter owner abstraction `IsStableInBroadSenseWithIndex`. -/
theorem toIsStableInBroadSenseWithIndex
    (hμ : IsBroadlyStableWithIndex μ α) (hα : α ≤ 2) :
    IsStableInBroadSenseWithIndex μ α :=
  ⟨hμ.2.1, ⟨hμ.1, hα⟩, hμ.2.2⟩

end IsBroadlyStableWithIndex

-- Proof sketch: pass to the chapter owner abstraction on the admissible range via
-- `IsStrictlyStableWithIndex.toIsStableWithIndex`, rewrite the resulting scaling law on
-- characteristic functions, and choose `n` comparable to `|t|^{-α}` to obtain the Hölder bound
-- near the origin.
/-- Exercise 16.2.1 (1): if a real probability law is strictly stable with index `α`, then its
characteristic function satisfies `|φ(t) - 1| ≤ C |t|^α` for all sufficiently small `t`. -/
theorem norm_charFun_sub_one_le_const_mul_rpow_of_isStrictlyStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      ‖charFun (μ : Measure ℝ) t - 1‖ ≤ C * Real.rpow |t| α := sorry

-- Proof sketch: combine the small-frequency bound from item (1) with the second-order criterion
-- from Exercise 15.3.2; for `α > 2`, the source-facing strict `α`-stability relation forces the
-- characteristic function to be flatter than quadratic at the origin, hence the law is the Dirac
-- mass at `0`.
/-- Exercise 16.2.1 (2): a strictly stable real probability law with index `α > 2` is
necessarily the Dirac mass at `0`. -/
theorem eq_dirac_zero_of_two_lt_of_isStrictlyStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) (hα : 2 < α) :
    (μ : Measure ℝ) = Measure.dirac 0 := sorry

-- Proof sketch: adapt the argument from item (2) to the source-facing affine scaling relation for
-- broad `α`-stability, absorbing the centering term into the characteristic-function identity and
-- then applying the same quadratic flatness criterion at the origin.
/-- Exercise 16.2.1 (3): a broadly stable real probability law with index `α > 2` is
necessarily the Dirac mass at `0`. -/
theorem eq_dirac_zero_of_two_lt_of_isBroadlyStableWithIndex
    (hμ : IsBroadlyStableWithIndex μ α) (hα : 2 < α) :
    (μ : Measure ℝ) = Measure.dirac 0 := sorry

end MeasureTheory.ProbabilityMeasure
