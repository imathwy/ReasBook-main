import Mathlib
import ProbabilityTheory_Klenke_2020.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Chap05.Definition_5_1
import ProbabilityTheory_Klenke_2020.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: prove the forward direction by the Baum--Katz complete convergence theorem for
-- i.i.d. real random variables, which forces finiteness of the `γ`-th absolute moment and zero
-- mean. For the reverse direction, start from the same moment and centering assumptions and apply
-- the Baum--Katz estimate to the deviation events of the normalized partial sums.
/-- Theorem 5.32: Baum and Katz (1965). For an i.i.d. real sequence `X₀, X₁, …`, the weighted
series `∑ n^(γ - 2) P[|S_n| / n > ε]` of deviation probabilities is summable for every `ε > 0` if
and only if the `γ`-th absolute moment of `X₀` is finite and `X₀` has mean `0`, where
`Sₙ = X₀ + ⋯ + Xₙ₋₁` is the chapter's canonical `partialSum`. The i.i.d. assumption is expressed
via the project's canonical shorthand `IsIID`. For the textbook indexing `X₁, X₂, …`, apply this
statement to `fun k ↦ X (k + 1)`. -/
theorem baum_katz_complete_convergence_iff_integrable_abs_rpow_and_mean_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    {γ ε : ℝ} (hγ : 1 < γ) (hε : 0 < ε) :
    Summable
      (fun n : ℕ ↦
        Real.rpow (n + 1 : ℝ) (γ - 2) *
          (P {ω | |partialSum X (n + 1) ω| / (n + 1 : ℝ) > ε}).toReal) ↔
      Integrable (fun ω ↦ Real.rpow |X 0 ω| γ) P ∧ P[X 0] = 0 := sorry

-- Proof sketch: this is the same Baum--Katz criterion, but repackaged through the chapter's
-- canonical centeredness predicate `IsCentered`. The source-facing theorem above remains the main
-- entry because the textbook states the mean-zero condition directly.
/-- Theorem 5.32, canonical centeredness view: the Baum--Katz complete-convergence criterion can
also be read as finite `γ`-moment together with the chapter's centeredness predicate on `X₀`. -/
theorem baum_katz_complete_convergence_iff_integrable_abs_rpow_and_isCentered
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    {γ ε : ℝ} (hγ : 1 < γ) (hε : 0 < ε) :
    Summable
      (fun n : ℕ ↦
        Real.rpow (n + 1 : ℝ) (γ - 2) *
          (P {ω | |partialSum X (n + 1) ω| / (n + 1 : ℝ) > ε}).toReal) ↔
      Integrable (fun ω ↦ Real.rpow |X 0 ω| γ) P ∧ IsCentered (X 0) P := sorry
