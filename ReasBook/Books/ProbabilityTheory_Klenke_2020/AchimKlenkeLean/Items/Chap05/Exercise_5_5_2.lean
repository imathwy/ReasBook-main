import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_36

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Lebesgue measure restricted to the unit interval `[0,1]`.
local notation "unitIntervalVolume" => volume.restrict (Set.Icc (0 : ℝ) 1)

noncomputable section

-- Proof sketch: use the tail-sum identity `E[N] = ∑_{n ≥ 0} P(S_{n+1} ≤ t)`, identify the law of
-- each finite partial sum with the Irwin--Hall distribution from the i.i.d. and uniform-law
-- assumptions, compute `P(S_n ≤ t)` by the inclusion-exclusion formula for the Irwin--Hall CDF,
-- and then interchange the resulting finite and infinite sums.
/-- Exercise 5.5.2 in the chapter's canonical owner API: if `X 0, X 1, …` are independent and
each has the uniform law on `[0,1]`, then the expected renewal count at time `t : NNReal` is the
Irwin--Hall closed form. This is the canonical `NNReal`-time version of the textbook formula for
positive real times. -/
theorem uniform_unit_renewal_count_mean
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P)
    (t : NNReal) :
    P[fun ω ↦ (renewalCountingProcess X t ω : ℝ)] =
      -1 + ∑ k ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (-1 : ℝ) ^ k * Real.exp ((t : ℝ) - k) * ((t : ℝ) - k) ^ k / (Nat.factorial k : ℝ) := sorry

/-- Textbook positive-real phrasing of Exercise 5.5.2, obtained by specializing the canonical
`NNReal`-time theorem to `Real.toNNReal T`. -/
theorem uniform_unit_renewal_count_mean_of_pos
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) unitIntervalVolume P)
    {T : ℝ} (hT : 0 < T) :
    P[fun ω ↦ (renewalCountingProcess X (Real.toNNReal T) ω : ℝ)] =
      -1 + ∑ k ∈ Finset.range (Nat.floor T + 1),
        (-1 : ℝ) ^ k * Real.exp (T - k) * (T - k) ^ k / (Nat.factorial k : ℝ) := by
  simpa [Real.toNNReal_of_nonneg hT.le] using
    uniform_unit_renewal_count_mean P X hX_iid hX0_law (Real.toNNReal T)
