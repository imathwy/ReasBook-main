import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_1
import ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_37

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: use the canonical owner hypothesis `IsIID (fun n ↦ X (n + 1)) P` to obtain the
-- measurability and common-law data needed for the pushforward law of
-- `standardizedPartialSum P (fun k ↦ X (k + 1)) n`, then apply the classical Berry--Esseen
-- inequality with the intrinsic variance and third absolute moment of `X 1`.
/-- Theorem 15.51: Berry--Esseen. If `X₁, X₂, …` are iid real random variables with mean `0`,
positive variance, and finite third absolute moment, then for every positive integer `n` the
Kolmogorov distance between the law of `S_n^*` and the standard normal cdf `cdf (gaussianReal 0
1)` is bounded by
`0.8 * absoluteMoment (X 1) 3 P / ((Real.sqrt (Var[X 1; P]))^3 * √n)`. -/
theorem berry_esseen_bound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    sSup
        (Set.range fun x : ℝ ↦
          |cdf
              (ProbabilityMeasure.map ⟨P, inferInstance⟩
                (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
                  (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)) x -
            cdf (gaussianReal 0 1) x|) ≤
      (0.8 : ℝ) * absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := sorry
