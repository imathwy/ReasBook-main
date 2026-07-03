import ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_36
import ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/- Example 10.17 is `source-facing`: its public content is the expected-value identity for the
two-sided hitting time `τ_{a,b}` and the divergence of the one-sided hitting time `τ_a`. The
`core/canonical` owner layer is the real-valued walk `Xℝ` with its natural filtration `ℱX`, the
square-integrable martingale owner theorem
`symmetricSimpleRandomWalk_squareIntegrable_martingale`, and the canonical hitting-time API
`MeasureTheory.hittingAfter` together with `Adapted.isStoppingTime_hittingAfter`. This file keeps
only those source-facing consequences and does not introduce a parallel wrapper around that owner
data. -/
section SymmetricSimpleRandomWalk

variable {P : Measure Ω} {X : ℕ → Ω → ℤ}
variable (hX_zero : X 0 = 0)
variable (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
variable (hX_law : ∀ n,
  HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)

local notation "Xℝ" => fun n ω ↦ (X n ω : ℝ)
local notation "ℱX" =>
  Filtration.natural Xℝ (symmetricSimpleRandomWalk_real_stronglyMeasurable hX_zero hX_law)
local instance : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure

include hX_zero hX_indep hX_law

-- Proof sketch: use `symmetricSimpleRandomWalk_real_stronglyMeasurable` and
-- `symmetricSimpleRandomWalk_squareIntegrable_martingale` to obtain the owner martingale data for
-- `Xℝ` on `ℱX`, apply Theorem 10.4 to the stopped square martingale `X_n^2 - n`, invoke optional
-- stopping for the bounded truncations of `τ_{a,b}`, and then insert the two-sided hitting
-- probabilities from the preceding example to identify the terminal second moment.
/-- Example 10.17 (1): for a symmetric simple random walk started at `0`, the expected first time
to hit either `a < 0` or the right boundary `b : ℕ` is `|a| b`. In Lean this is stated as an
extended expectation of the canonical hitting time `τ_{a,b}`. -/
theorem symmetricSimpleRandomWalk_lintegral_twoSidedHittingTime
    {a : ℤ} {b : ℕ} (ha : a < 0) :
    lintegral P
      (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, (b : ℤ)} : Set ℤ) 0 ω)) =
      (Int.natAbs a * b : ℝ≥0∞) := sorry

-- Proof sketch: the two-sided hitting times `τ_{a,b}` increase almost surely to `τ_a` as
-- `b → ∞`; apply monotone convergence to the first clause and use that the right-hand side
-- `|a| b` tends to `∞`.
/-- Example 10.17 (2): for a symmetric simple random walk started at `0`, the expected one-sided
hitting time of a negative level `a` is infinite. In Lean this is stated as the extended
expectation of `τ_a`. -/
theorem symmetricSimpleRandomWalk_lintegral_levelHittingTime_eq_top
    {a : ℤ} (ha : a < 0) :
    lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a} : Set ℤ) 0 ω)) = ∞ := sorry

end SymmetricSimpleRandomWalk
