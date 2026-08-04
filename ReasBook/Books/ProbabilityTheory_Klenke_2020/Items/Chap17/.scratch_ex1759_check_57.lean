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

end ProbabilityTheory
