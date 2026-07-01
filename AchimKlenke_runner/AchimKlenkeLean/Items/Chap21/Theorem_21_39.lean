import Mathlib
import AchimKlenkeLean.Items.Chap21.Theorem_21_30

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

local notation "Ω" => BrownianPathSpace

/-- The oscillation of a path `ω` on the compact interval `[0, N]` at time scale `δ`. -/
def compactIntervalOscillation (N : ℕ) (ω : Ω) (δ : NNReal) : ℝ :=
  sSup {r : ℝ | ∃ s t : Set.Icc (0 : NNReal) N, dist (s : NNReal) (t : NNReal) ≤ δ ∧
    r = |ω s - ω t|}

-- Proof sketch: every value appearing in the defining supremum is an absolute value, hence
-- nonnegative, so the supremum is also nonnegative.
/-- The compact-interval oscillation is always nonnegative. -/
theorem compactIntervalOscillation_nonneg (N : ℕ) (ω : Ω) (δ : NNReal) :
    0 ≤ compactIntervalOscillation N ω δ := sorry

-- Proof sketch: specialize mathlib's Arzelà--Ascoli theorem for the compact-open topology on
-- `C([0, ∞), ℝ)` to the covering by compact intervals `[0, N]`. On each such interval the
-- canonical owner condition is equicontinuity of the family `A`, while boundedness of the values
-- at time `0` controls the pointwise ranges on all compact intervals by continuity of the paths.
/-- Canonical compact-open formulation of the Arzelà--Ascoli criterion on Brownian path space:
relative compactness is equivalent to bounded initial values and equicontinuity on every compact
time interval. -/
theorem brownianPathSpace_relativelyCompact_iff_bounded_eval_zero_and_equicontinuousOn_compacts
    (A : Set Ω) :
    IsCompact (closure A) ↔
      Bornology.IsBounded ((fun ω : Ω ↦ ω 0) '' A) ∧
        ∀ N : ℕ, EquicontinuousOn ((↑) : A → NNReal → ℝ) (Icc (0 : NNReal) N) := sorry

-- Proof sketch: on a fixed compact interval `[0, N]`, the oscillation modulus tends to `0`
-- uniformly on `A` exactly when the restricted family is equicontinuous there. This is the metric
-- reformulation of equicontinuity in terms of uniform control of `|ω s - ω t|` for nearby times.
/-- On `[0, N]`, the textbook vanishing oscillation condition is equivalent to the canonical
equicontinuity predicate for the family `A`. -/
theorem set_equicontinuousOn_Icc_iff_tendsto_compactIntervalOscillation
    (A : Set Ω) (N : ℕ) :
    EquicontinuousOn ((↑) : A → NNReal → ℝ) (Icc (0 : NNReal) N) ↔
      Filter.Tendsto
        (fun δ : NNReal ↦ sSup ((fun ω : Ω ↦ compactIntervalOscillation N ω δ) '' A))
        (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds (0 : ℝ)) := sorry

-- Proof sketch: the compact-convergence topology on `Ω = C([0, ∞), ℝ)` is the topology of
-- uniform convergence on compact sets. The condition at time `0` gives the pointwise boundedness
-- needed to control values on each compact interval, while the vanishing oscillation condition is
-- the textbook equicontinuity criterion on `[0, N]`. Translate these two concrete hypotheses to
-- the hypotheses of the Arzelà--Ascoli theorem for continuous maps and conversely read off the
-- two conditions from relative compactness.
/-- Theorem 21.39: a subset of `C([0, ∞), ℝ)` is relatively compact exactly when its values at
time `0` are bounded and its compact-interval oscillations vanish uniformly as the mesh tends to
`0`. -/
theorem brownianPathSpace_relativelyCompact_iff_arzelaAscoli (A : Set Ω) :
    IsCompact (closure A) ↔
      Bornology.IsBounded ((fun ω : Ω ↦ ω 0) '' A) ∧
        ∀ N : ℕ,
          Filter.Tendsto
            (fun δ : NNReal ↦ sSup ((fun ω : Ω ↦ compactIntervalOscillation N ω δ) '' A))
            (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds (0 : ℝ)) := by
  rw [brownianPathSpace_relativelyCompact_iff_bounded_eval_zero_and_equicontinuousOn_compacts]
  constructor
  · rintro ⟨h0, hA⟩
    refine ⟨h0, fun N ↦ ?_⟩
    exact (set_equicontinuousOn_Icc_iff_tendsto_compactIntervalOscillation A N).mp (hA N)
  · rintro ⟨h0, hA⟩
    refine ⟨h0, fun N ↦ ?_⟩
    exact (set_equicontinuousOn_Icc_iff_tendsto_compactIntervalOscillation A N).mpr (hA N)
