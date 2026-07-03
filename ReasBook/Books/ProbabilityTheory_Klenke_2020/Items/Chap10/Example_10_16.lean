import ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: apply optional stopping to the martingale `X` at the bounded stopping time
-- `τ_{a,b} = hittingAfter X ({a, b} : Set ℤ) 0`, obtained from the canonical owner theorem
-- `Adapted.isStoppingTime_hittingAfter`; use that the event
-- `{hittingAfter X ({a, b} : Set ℤ) 0 = hittingAfter X ({a} : Set ℤ) 0}` is exactly the event
-- that the walk hits the negative level `a` before the positive level `b`, and solve the
-- resulting affine equation for the hitting probability.
/-- Example 10.16: for a one-dimensional symmetric simple random walk starting at `0`, the
probability of hitting the negative level `a` before the positive level `b` is `b / (b - a)`. -/
theorem symmetricSimpleRandomWalk_prob_hitLeftBeforeRight
    (P : Measure Ω) (X : ℕ → Ω → ℤ)
    (hX_zero : X 0 = 0)
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
    (hX_law : ∀ n,
      HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)
    {a b : ℤ} (ha : a < 0) (hb : 0 < b) :
    P {ω | hittingAfter X ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω} =
      ENNReal.ofReal ((b : ℝ) / (b - a : ℝ)) := sorry
