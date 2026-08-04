import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Example_3_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_4_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_53
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace ProbabilityTheory

/-- Helper for Example 17.59: the product unit-interval law on `Fin n → I`. -/
abbrev uniformCube (n : ℕ) : Measure (Fin n → I) :=
  (ProbabilityMeasure.pi
    (fun _ : Fin n ↦ (⟨(volume : Measure I), inferInstance⟩ : ProbabilityMeasure I)) :
      Measure (Fin n → I))

/-- Helper for Example 17.59: the one-trial threshold count on the unit interval. -/
abbrev thresholdIndicator (p : I) : I → ℕ :=
  fun u ↦ if u ≤ p then 1 else 0

/-- Helper for Example 17.59: on `ℕ`, the initial segment `Set.Iio 1` is the singleton `{0}`. -/
lemma setIioOne_eq_singleton : (Set.Iio 1 : Set ℕ) = {0} := by
  -- Proof comment: `0` is the only natural number strictly below `1`.
  ext x
  simp [Set.mem_Iio]

/-- Helper for Example 17.59: a subset of `Set.Iio 1` is either empty or `{0}`. -/
lemma eq_empty_or_singleton_zero_of_subset_Iio_one {s : Set ℕ} (hs : s ⊆ Set.Iio 1) :
    s = ∅ ∨ s = {0} := by
  -- Proof comment: after rewriting `Set.Iio 1` as `{0}`, only the two obvious subsets remain.
  have hs' : s ⊆ ({0} : Set ℕ) := by
    simpa [setIioOne_eq_singleton] using hs
  by_cases h0 : 0 ∈ s
  · right
    ext x
    constructor
    · intro hx
      have : x = 0 := by
        simpa using hs' hx
      simp [this]
    · intro hx
      have : x = 0 := by simpa using hx
      simpa [this] using h0
  · left
    ext x
    constructor
    · intro hx
      have : x = 0 := by
        simpa using hs' hx
      exact h0 (this ▸ hx)
    · intro hx
      simp at hx

/-- Helper for Example 17.59: the one-trial threshold map is measurable. -/
theorem measurable_thresholdIndicator (p : I) :
    Measurable (thresholdIndicator p) := by
  -- Proof comment: the codomain `ℕ` is discrete, so every nat-valued map is measurable.
  simpa [thresholdIndicator] using
    Measurable.piecewise (s := Set.Iic p) measurableSet_Iic measurable_const measurable_const

/-- Helper for Example 17.59: the one-trial threshold count has the one-trial binomial law. -/
theorem thresholdIndicator_hasLaw_binomialOne (p : I) :
    HasLaw (thresholdIndicator p) (Bin(1, p)) (volume : Measure I) := by
  refine ⟨measurable_thresholdIndicator p |>.aemeasurable, ?_⟩
  -- Proof comment: compare the pushforward law and `Bin(1, p)` on singleton atoms.
  refine Measure.ext_of_singleton fun k ↦ ?_
  by_cases hk0 : k = 0
  · subst hk0
    rw [Measure.map_apply (measurable_thresholdIndicator p) (measurableSet_singleton 0)]
    have hpreimage : thresholdIndicator p ⁻¹' ({0} : Set ℕ) = Set.Ioi p := by
      ext u
      simp [thresholdIndicator]
    rw [hpreimage]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [unitInterval.volume_Ioi, binomial_apply_singleton_toReal 1 0 p]
    simp [p.2.2]
  · by_cases hk1 : k = 1
    · subst hk1
      rw [Measure.map_apply (measurable_thresholdIndicator p) (measurableSet_singleton 1)]
      have hpreimage : thresholdIndicator p ⁻¹' ({1} : Set ℕ) = Set.Iic p := by
        ext u
        simp [thresholdIndicator]
      rw [hpreimage]
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      rw [unitInterval.volume_Iic, binomial_apply_singleton_toReal 1 1 p]
      simp [p.2.1]
    · have hk2 : 1 < k := by
        omega
      rw [Measure.map_apply (measurable_thresholdIndicator p) (measurableSet_singleton k)]
      have hpreimage : thresholdIndicator p ⁻¹' ({k} : Set ℕ) = (∅ : Set I) := by
        ext u
        by_cases hu : u ≤ p <;> simp [thresholdIndicator, hu, hk0, hk1, eq_comm]
      rw [hpreimage, measure_empty]
      rw [← ENNReal.ofReal_zero]
      rw [← ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top (measure_ne_top _ _)]
      rw [binomial_apply_singleton_toReal 1 k p]
      have hchoose : Nat.choose 1 k = 0 := Nat.choose_eq_zero_of_lt hk2
      simp [hchoose]

/-- Helper for Example 17.59: the tail component of
`MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0` is the usual successor tail. -/
lemma piFinSuccAboveZeroSndEqSuccTailI (n : ℕ) :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0 =
      fun y : Fin (n + 1) → I ↦ fun i : Fin n ↦ y i.succ := by
  -- Proof comment: the standard split equivalence removes the zero coordinate and leaves the
  -- remaining coordinates in successor order.
  funext y
  funext i
  simp [Fin.tail]

/-- Helper for Example 17.59: splitting off the zero coordinate sends `uniformCube (n + 1)` to the
product law of the head coordinate and the successor tail. -/
lemma uniformCube_map_piFinSuccAboveZero (n : ℕ) :
    (uniformCube (n + 1)).map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0) =
      (volume : Measure I).prod (uniformCube n) := by
  -- Proof comment: this is the canonical `piFinSuccAbove` measure-preserving split specialized to
  -- the unit-interval product law.
  simpa [uniformCube, Fin.zero_succAbove] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ (volume : Measure I)) 0).map_eq

/-- The number of coordinates among `n` unit-interval samples that fall below the threshold `p`. -/
def binomialUniformCount (n : ℕ) (p : I) : (Fin n → I) → ℕ :=
  fun y ↦ ∑ i, if y i ≤ p then 1 else 0

-- Proof sketch: each summand `y ↦ if y i ≤ p then 1 else 0` is measurable because evaluation at a
-- coordinate is measurable and `ℕ` carries the discrete measurable space; finite sums preserve
-- measurability.
/-- The threshold-count map is measurable on the finite unit cube `I^n`. -/
theorem measurable_binomialUniformCount (n : ℕ) (p : I) :
    Measurable (binomialUniformCount n p) := by
  -- Proof comment: each `0/1` summand is measurable, and finite sums preserve measurability.
  classical
  simpa [binomialUniformCount] using
    Finset.measurable_sum Finset.univ fun i _ ↦
      Measurable.piecewise
        (measurableSet_setOf.2 <| by fun_prop)
        measurable_const
        measurable_const

/-- Helper for Example 17.59: separating the first coordinate turns the `(n + 1)`-count into a
one-trial count plus the tail `n`-count. -/
theorem binomialUniformCount_succ (n : ℕ) (p : I) (y : Fin (n + 1) → I) :
    binomialUniformCount (n + 1) p y =
      thresholdIndicator p (y 0) + binomialUniformCount n p (fun i ↦ y (Fin.succ i)) := by
  -- Proof comment: split the finite sum into the zero coordinate and the remaining tail.
  rw [binomialUniformCount, Fin.sum_univ_succ]
  simp [thresholdIndicator, binomialUniformCount]

end ProbabilityTheory
