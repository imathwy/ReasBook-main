import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap10.Example_10_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open unitInterval

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

private noncomputable def biasedRademacherPMF (p : unitInterval) : PMF ℤ :=
  (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).map (fun b ↦ cond b (1 : ℤ) (-1))

/-- The biased Rademacher law on `ℤ` that assigns mass `p` to `1` and mass `1 - p` to `-1`. -/
def biasedRademacherLaw (p : ℝ) : Measure ℤ :=
  (ENNReal.ofReal p • Measure.dirac (1 : ℤ)) +
    (ENNReal.ofReal (1 - p) • Measure.dirac (-1 : ℤ))

-- Proof sketch: rewrite the two-point `ℤ`-valued law as the pushforward of the canonical
-- Bernoulli PMF along `Bool → ℤ`, `true ↦ 1`, `false ↦ -1`.
private theorem biasedRademacherLaw_eq_biasedRademacherPMF_toMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    biasedRademacherLaw p = (biasedRademacherPMF ⟨p, hp0, hp1⟩).toMeasure := sorry

-- Proof sketch: both Dirac summands are finite probability fragments with weights `p` and `1-p`;
-- when `0 ≤ p ≤ 1`, these nonnegative weights sum to `1`.
/-- The biased Rademacher law is a probability measure whenever `p ∈ [0, 1]`. -/
theorem biasedRademacherLaw_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (biasedRademacherLaw p) := by
  simpa [biasedRademacherLaw_eq_biasedRademacherPMF_toMeasure hp0 hp1] using
    (show IsProbabilityMeasure ((biasedRademacherPMF ⟨p, hp0, hp1⟩).toMeasure) from inferInstance)

/-- The ratio `r = (1 - p) / p` appearing in the exponential martingale for the biased gambler's
ruin walk. -/
def gamblerRuinRatio (p : ℝ) : ℝ :=
  (1 - p) / p

-- Proof sketch: use the exponential transform `Z_n = r^(X_n)` with `r = (1 - p) / p`, observe
-- that this is a martingale by the one-step computation `𝔼[r^{Y_n}] = 1`, stop at the first hit of
-- `{0, N}`, and solve the resulting linear equation for the ruin probability. The walk itself is
-- expressed directly through the chapter owner `randomWalkProcess`, and the ruin event uses the
-- canonical hitting-time language `τ_{0,N} = τ_0`.
/-- Example 10.19: for a gambler's ruin walk started from capital `kB`, with i.i.d. increments
`Y_i ∈ {-1, 1}` satisfying `𝔓[Y_i = 1] = p` and `𝔓[Y_i = -1] = 1 - p`, the probability that B is
ruined before reaching the positive total capital `N` is `(r^kB - r^N) / (1 - r^N)` with
`r = (1 - p) / p`. -/
theorem gamblerRuinProbability_eq
    {P : Measure Ω} {Y : ℕ → Ω → ℤ} {p : ℝ} {kB N : ℕ}
    (hN : 0 < N) (hkB : kB ≤ N) (hp0 : 0 < p) (hp1 : p < 1) (hp_ne_half : p ≠ 1 / 2)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (biasedRademacherLaw p) P) :
    by
      haveI : IsProbabilityMeasure (biasedRademacherLaw p) :=
        biasedRademacherLaw_isProbabilityMeasure hp0.le hp1.le
      letI : IsProbabilityMeasure P := (hY_law 0).isProbabilityMeasure
      let X : ℕ → Ω → ℤ := fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω
      exact
        (P {ω | hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω =
            hittingAfter X ({0} : Set ℤ) 0 ω}).toReal =
          ((gamblerRuinRatio p) ^ kB - (gamblerRuinRatio p) ^ N) /
            (1 - (gamblerRuinRatio p) ^ N) := sorry

-- Proof sketch: apply `gamblerRuinProbability_eq` to the genuine finite-capital instances with
-- total capital `N + kB + 1`, rewrite
-- `(r^kB - r^(N + kB + 1)) / (1 - r^(N + kB + 1)) =
--   r^kB * (1 - r^(N + 1)) / (1 - r^(N + kB + 1))`,
-- use `0 < r < 1` when `1 / 2 < p < 1`, and pass to the limit `N → ∞`.
/-- With `kB` fixed and `p > 1 / 2`, the ruin probabilities for the finite-capital gambler's ruin
problems with total capital `kB + 1, kB + 2, …` converge to `r^kB`. -/
theorem gamblerRuinProbability_tendsto_infiniteCapital
    {P : Measure Ω} {Y : ℕ → Ω → ℤ} {p : ℝ} {kB : ℕ}
    (hp_half : 1 / 2 < p) (hp1 : p < 1)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (biasedRademacherLaw p) P) :
    by
      have hp0 : 0 < p := lt_trans (by norm_num) hp_half
      haveI : IsProbabilityMeasure (biasedRademacherLaw p) :=
        biasedRademacherLaw_isProbabilityMeasure hp0.le hp1.le
      letI : IsProbabilityMeasure P := (hY_law 0).isProbabilityMeasure
      exact
        Filter.Tendsto
          (fun N : ℕ ↦
            let totalCapital := N + kB + 1
            let X : ℕ → Ω → ℤ := fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω
            (P {ω | hittingAfter X ({0, (totalCapital : ℤ)} : Set ℤ) 0 ω =
                hittingAfter X ({0} : Set ℤ) 0 ω}).toReal)
          Filter.atTop
          (nhds ((gamblerRuinRatio p) ^ kB)) := sorry
