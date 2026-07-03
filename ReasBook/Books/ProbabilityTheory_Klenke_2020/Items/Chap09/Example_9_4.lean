import ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u

noncomputable section

/-- The symmetric law on `ℤ` giving mass `1 / 2` to both `1` and `-1`. -/
def symmetricRademacherLaw : Measure ℤ :=
  ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℤ)) +
    ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℤ))

-- Proof sketch: both summands are finite Dirac probability fragments with masses `1 / 2`, so the
-- total mass of `symmetricRademacherLaw` is `1`.
/-- The symmetric Rademacher law is a probability measure on `ℤ`. -/
theorem symmetricRademacherLaw_isProbabilityMeasure :
    IsProbabilityMeasure symmetricRademacherLaw := sorry

instance : IsProbabilityMeasure symmetricRademacherLaw :=
  symmetricRademacherLaw_isProbabilityMeasure

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: evaluate the two Dirac masses on the singleton `{1}` and add the contributions.
/-- The symmetric Rademacher law assigns probability `1 / 2` to the step `1`. -/
theorem symmetricRademacherLaw_apply_singleton_one :
    symmetricRademacherLaw ({1} : Set ℤ) = 1 / 2 := sorry

-- Proof sketch: the increment maps have the symmetric Rademacher law and therefore take values in
-- the discrete countable space `ℤ`; recursively write `X n` as a finite sum of those increments
-- starting from `X 0 = 0`, then compose with the coercion `ℤ → ℝ`.
/-- The real-valued version of a symmetric simple random walk is strongly measurable at every time
index. -/
theorem symmetricSimpleRandomWalk_real_stronglyMeasurable
    {P : Measure Ω} {X : ℕ → Ω → ℤ} (hX_zero : X 0 = 0)
    (hX_law : ∀ n, HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P) :
    ∀ n, StronglyMeasurable (fun ω ↦ (X n ω : ℝ)) := sorry

-- Proof sketch: unfold `randomWalkProcess` at time `0`; the sum over `Finset.range 0` is empty.
/-- The canonical random-walk process associated with `Y` starts at the origin. -/
theorem randomWalkProcess_zero (Y : ℕ → Ω → ℤ) :
    randomWalkProcess Y 0 = 0 := sorry

-- Proof sketch: compare the two consecutive partial sums; the `Finset.range (n + 1)` sum differs
-- from the `Finset.range n` sum by exactly the last term `Y n`.
/-- The one-step increment of the partial-sum walk is the original increment `Y n`. -/
theorem randomWalkProcess_increment (Y : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    randomWalkProcess Y (n + 1) ω - randomWalkProcess Y n ω = Y n ω := sorry

-- Proof sketch: use `HasIndepIncrements.of_nat` and the identity
-- `randomWalkProcess Y (t (i + 1)) - randomWalkProcess Y (t i)` as the sum over a disjoint block
-- of the independent increment sequence `Y`.
/-- If the increment sequence `Y` is independent, then its partial-sum walk has independent
increments. -/
theorem randomWalkProcess_hasIndepIncrements
    (P : Measure Ω) (Y : ℕ → Ω → ℤ) (hY_indep : iIndepFun Y P) :
    HasIndepIncrements (randomWalkProcess Y) P := sorry

-- Proof sketch: rewrite the one-step increment of `randomWalkProcess Y` as `Y n` and apply the
-- assumed law of `Y n`.
/-- If each `Y n` has the symmetric Rademacher law, then so does each one-step increment of the
partial-sum walk. -/
theorem randomWalkProcess_increment_hasLaw
    (P : Measure Ω) (Y : ℕ → Ω → ℤ)
    (hY_law : ∀ n, HasLaw (Y n) symmetricRademacherLaw P) (n : ℕ) :
    HasLaw (fun ω ↦ randomWalkProcess Y (n + 1) ω - randomWalkProcess Y n ω)
      symmetricRademacherLaw P := sorry

-- Proof sketch: apply the chapter owner theorem giving independent increments for
-- `randomWalkProcess Y`, then identify each one-step increment with `Y n`.
/-- Example 9.4: if the increments `Y_n` are independent and each has the symmetric Rademacher
law, then the random walk `randomWalkProcess Y` has the canonical independent-increments owner
property and the symmetric Rademacher one-step increment law. Together with
`randomWalkProcess_zero`, this is the canonical `0`-based Lean formulation of the textbook process
`X_t = ∑_{n=1}^t Y_n`. -/
theorem partial_sums_form_symmetric_simple_random_walk
    (P : Measure Ω) (Y : ℕ → Ω → ℤ)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) symmetricRademacherLaw P) :
    HasIndepIncrements (randomWalkProcess Y) P ∧
      ∀ n,
        HasLaw (fun ω ↦ randomWalkProcess Y (n + 1) ω - randomWalkProcess Y n ω)
          symmetricRademacherLaw P := sorry
