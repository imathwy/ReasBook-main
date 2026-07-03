import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_8
import AchimKlenkeLean.Items.Chap21.Definition_21_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

namespace MeasureTheory
namespace Filtration

private noncomputable abbrev completedRightLimitMeasurableSpace
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    MeasurableSpace (NullMeasurableSpace Ω μ) :=
  @NullMeasurableSpace.instMeasurableSpace Ω (ℱ₊ t) (μ.trim (ℱ₊.le t))

-- Proof sketch: if `s ≤ t`, then `ℱ₊ s ≤ ℱ₊ t`. Completing with respect to the corresponding
-- trimmed measures preserves the monotonicity of the ambient null-measurable σ-algebras.
private theorem completed_right_continuous_filtration_mono
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    Monotone (completedRightLimitMeasurableSpace μ ℱ) := sorry

-- Proof sketch: a set that is null-measurable for the trimmed measure
-- `μ.trim (ℱ₊.le t)` is also null-measurable for `μ`, since the trimmed measure is
-- induced from `μ` on a smaller σ-algebra.
private theorem completed_right_continuous_filtration_le
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    completedRightLimitMeasurableSpace μ ℱ t ≤
      (show MeasurableSpace (NullMeasurableSpace Ω μ) from inferInstance) := sorry

/-- The textbook filtration `ℱ^{+,*}` obtained by completing each right-limit σ-algebra
`ℱ_t^+` with respect to the trimmed measure at time `t`. -/
noncomputable def completed_right_continuous_filtration
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    Filtration NNReal (show MeasurableSpace (NullMeasurableSpace Ω μ) from inferInstance) where
  seq t := completedRightLimitMeasurableSpace μ ℱ t
  mono' := completed_right_continuous_filtration_mono μ ℱ
  le' := completed_right_continuous_filtration_le μ ℱ

/-- Lean notation `ℱ^+*[μ]`, formalizing the textbook completed augmentation `ℱ^{+,*}`. -/
scoped[MeasureTheory] notation:arg ℱ "^+*[" μ "]" =>
  Filtration.completed_right_continuous_filtration μ ℱ

/- The source notation `ℱ^{+,*}` is formalized by `ℱ^+*[μ]`, the filtration
`completed_right_continuous_filtration μ ℱ`
on the completed measurable space `NullMeasurableSpace Ω μ`. -/

/- At time `t`, the filtration `ℱ^+*[μ]` is the null-measurable completion of the right-limit
`σ`-algebra `ℱ_t^+` with respect to the trimmed measure `μ.trim (ℱ₊.le t)`. -/
theorem completed_right_continuous_filtration_apply
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    (ℱ^+*[μ]) t =
      @NullMeasurableSpace.instMeasurableSpace Ω (ℱ₊ t) (μ.trim (ℱ₊.le t)) := rfl

/- A set is measurable for `(ℱ^+*[μ]) t` exactly when it is null-measurable for the trimmed
measure on the right-limit `σ`-algebra `ℱ₊ t`. -/
theorem measurableSet_completed_right_continuous_filtration_iff
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) {s : Set Ω} :
    MeasurableSet[(ℱ^+*[μ]) t] s ↔
      @NullMeasurableSet Ω (ℱ₊ t) s (μ.trim (ℱ₊.le t)) := Iff.rfl

/- The completed right-continuous filtration `ℱ^+*[μ]` satisfies the chapter owner property
`UsualConditions` for the completed measure `μ.completion`. -/
-- Proof sketch: right continuity comes from the defining use of `ℱ.rightCont`, and completeness at
-- time `0` is built into the passage from `μ` to `μ.completion`.
theorem completed_right_continuous_filtration_usual_conditions
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    UsualConditions (ℱ^+*[μ]) μ.completion := sorry

end Filtration

open ProbabilityTheory

-- Proof sketch: for `s ≤ t`, the martingale identity `E[B_t | ℱ_u] = B_u` holds for every
-- `u ∈ Ioi s`. Passing to the right-limit `ℱ_s⁺ = ⋂ u > s, ℱ_u` identifies the conditional
-- expectation of `B_t` with the almost sure limit of `B_u` as `u ↓ s`, and almost sure continuity
-- of Brownian paths turns that limit into `B_s`. Completing `ℱ_s⁺` with respect to `μ` does not
-- change conditional expectations after passing to `μ.completion`.
/-- Exercise 21.4.5: if a Brownian motion is a martingale for `ℱ`, then it is also a martingale
for the completed right-continuous filtration `ℱ^+*[μ]`, formalizing the textbook augmentation
`ℱ^{+,*}`. The filtration-side owner theorem is
`Filtration.completed_right_continuous_filtration_usual_conditions`; this is the Brownian-motion
corollary justified by the exercise. -/
theorem brownian_martingale_completed_right_continuous_filtration
    {μ : Measure Ω} {ℱ : Filtration NNReal mΩ} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (hBm : Martingale B ℱ μ) :
    Martingale B (ℱ^+*[μ]) μ.completion := sorry

end MeasureTheory
