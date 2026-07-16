import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: decompose according to the first index where `|S_k|` crosses `t`, compare this
-- event with the large-deviation events for the terminal differences `S_n - S_k`, use
-- independence, and optimize the union bound to obtain the factor `3`.
/-- Exercise 5.4.1: for independent real random variables `X₁, …, Xₙ` with partial sums
`S_k = X₁ + ⋯ + X_k`, Etemadi's inequality bounds the probability that one of the absolute partial
sums reaches `t` by three times the largest tail probability at level `t / 3`. This is the
canonical `0`-based Lean version using the chapter's existing `partialSum`; for the textbook
sequence `X₁, X₂, …`, apply it to `fun k ↦ X (k + 1)`. -/
theorem etemadi_inequality_abs_partial_sums (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P) {t : ℝ} (ht : 0 < t) :
    P (absHitEvent X n t) ≤
      3 *
        (Finset.Icc 1 n).sup fun k ↦
          P {ω | t / 3 ≤ |partialSum X k ω|} := sorry
