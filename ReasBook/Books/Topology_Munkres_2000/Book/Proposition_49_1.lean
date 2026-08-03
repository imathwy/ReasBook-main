import Topology_Munkres_2000.Book.Proposition_49_1.Differentiability
import Topology_Munkres_2000.Book.Example_49_1.LargeSecants
import Mathlib.Analysis.Calculus.Deriv.Slope

open Set Filter
open scoped UnitIntervalSecant

namespace UnitIntervalSecant

/-- Helper for Proposition 49.1: membership in every `U_{n}` supplies a
pointwise secant magnitude larger than `n` at scale at most `1 / n`. -/
private lemma exists_scale_large_maxMagnitude (f : C(unitInterval, ℝ))
    (hf : ∀ n : ℕ, 2 ≤ n → f ∈ U_{n}) (x : unitInterval) {n : ℕ}
    (hn : 2 ≤ n) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / (n : ℝ) ∧ (n : ℝ) < Δ f (x, h) := by
  -- Extract the common scale from `U_n` and compare its infimum with the
  -- secant magnitude at the fixed point `x`.
  obtain ⟨h, hpos, hnscale, hninf⟩ := mem_largeSecantSet.mp (hf n hn)
  have hnreal : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have htwoPos : (0 : ℝ) < 2 := by
    norm_num
  have hhalf : h ≤ 1 / 2 :=
    hnscale.trans (one_div_le_one_div_of_le htwoPos hnreal)
  refine ⟨h, hpos, hnscale, ?_⟩
  exact hninf.trans_le (infMagnitude_le f h hpos hhalf x)

/-- The strict large-secant hypotheses prevent the secant magnitudes from
converging to a finite limit as the positive displacement tends to zero. -/
theorem maxMagnitude_not_tendsto (f : C(unitInterval, ℝ))
    (hf : ∀ n : ℕ, 2 ≤ n → f ∈ U_{n}) (x : unitInterval) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℝ ↦ Δ f (x, h))
      (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds L) := by
  -- Choose at stage `k` a scale witnessing the hypothesis for `k + 2`.
  classical
  have hkTwo (k : ℕ) : 2 ≤ k + 2 := by
    omega
  choose h hpos hscale hlarge using fun k : ℕ ↦
    exists_scale_large_maxMagnitude f hf x (n := k + 2) (hkTwo k)
  have hupper : ∀ k : ℕ, h k ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hcast : (k : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) := by
      norm_num
    have hdenominatorPos : (0 : ℝ) < (k : ℝ) + 1 := by
      positivity
    exact (hscale k).trans (one_div_le_one_div_of_le hdenominatorPos hcast)
  -- The selected positive scales are squeezed to zero and remain in the
  -- positive half-interval used in the statement.
  have hzero : Tendsto h atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat ?_ ?_
    · exact Eventually.of_forall fun k ↦ le_of_lt (hpos k)
    · exact Eventually.of_forall hupper
  have hwithin : Tendsto h atTop (nhdsWithin 0 (Ioc 0 (1 / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero, Eventually.of_forall fun k ↦ ⟨hpos k, ?_⟩⟩
    have htwo : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      norm_num
    have htwoPos : (0 : ℝ) < 2 := by
      norm_num
    exact (hscale k).trans (one_div_le_one_div_of_le htwoPos htwo)
  -- Along the same scales the secant magnitudes dominate the natural numbers,
  -- hence tend to `atTop`.
  have hmagnitude : Tendsto (fun k ↦ Δ f (x, h k)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    exact Eventually.of_forall fun k ↦ le_trans (Nat.cast_le.mpr (Nat.le_add_right k 2))
      (le_of_lt (hlarge k))
  -- A finite limit would persist along the selected scales, contradicting
  -- their divergence to `atTop`.
  rintro ⟨L, hlimit⟩
  exact not_tendsto_nhds_of_tendsto_atTop hmagnitude L (hlimit.comp hwithin)

/-- Helper for Proposition 49.1: a derivative within `[0, 1]` controls the
absolute right secant magnitudes along positive displacements tending to zero. -/
private lemma rightSecantMagnitude_tendsto {g : ℝ → ℝ} {g' x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hx1 : x < 1)
    (hg : HasDerivWithinAt g g' (Icc (0 : ℝ) 1) x) :
    Tendsto (fun h : ℝ ↦ |(g (x + h) - g x) / h|)
      (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds |g'|) := by
  -- Positive displacements tend to zero and, eventually, keep `x + h`
  -- inside the interval while avoiding `x` itself.
  have hzero : Tendsto (fun h : ℝ ↦ h) (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 (Ioc 0 (1 / 2)), h < 1 - x :=
    hzero.eventually (Iio_mem_nhds (sub_pos.mpr hx1))
  have hargument : Tendsto (fun h : ℝ ↦ x + h)
      (nhdsWithin 0 (Ioc 0 (1 / 2)))
      (nhdsWithin x (Icc (0 : ℝ) 1 \ {x})) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa only [add_zero] using tendsto_const_nhds.add hzero
    · filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hlt
      have hupper : x + h ≤ 1 := by
        linarith
      refine ⟨⟨add_nonneg hx.1 (le_of_lt hh.1), hupper⟩, ?_⟩
      simpa only [mem_singleton_iff] using
        (ne_of_gt (lt_add_of_pos_right x hh.1))
  -- Compose the canonical slope limit with `h ↦ x + h`, then normalize the
  -- slope denominator to `h`.
  have hslope : Tendsto (fun h : ℝ ↦ slope g x (x + h))
      (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds g') := by
    simpa only [Function.comp_def] using
      (hasDerivWithinAt_iff_tendsto_slope.mp hg).comp hargument
  simpa only [slope_def_field, add_sub_cancel_left] using hslope.abs

/-- Helper for Proposition 49.1: a derivative within `[0, 1]` controls the
absolute left secant magnitudes along positive displacements tending to zero. -/
private lemma leftSecantMagnitude_tendsto {g : ℝ → ℝ} {g' x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hx0 : 0 < x)
    (hg : HasDerivWithinAt g g' (Icc (0 : ℝ) 1) x) :
    Tendsto (fun h : ℝ ↦ |(g (x - h) - g x) / (-h)|)
      (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds |g'|) := by
  -- Positive displacements tend to zero and, eventually, keep `x - h`
  -- inside the interval while avoiding `x` itself.
  have hzero : Tendsto (fun h : ℝ ↦ h) (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 (Ioc 0 (1 / 2)), h < x :=
    hzero.eventually (Iio_mem_nhds hx0)
  have hargument : Tendsto (fun h : ℝ ↦ x - h)
      (nhdsWithin 0 (Ioc 0 (1 / 2)))
      (nhdsWithin x (Icc (0 : ℝ) 1 \ {x})) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa only [sub_zero] using tendsto_const_nhds.sub hzero
    · filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hlt
      refine ⟨⟨le_of_lt (sub_pos.mpr hlt),
        (sub_le_self x (le_of_lt hh.1)).trans hx.2⟩, ?_⟩
      have hne : x - h ≠ x := by
        linarith [hh.1]
      simpa only [mem_singleton_iff] using hne
  -- Compose the canonical slope limit with `h ↦ x - h`; the small algebraic
  -- identity below puts the denominator in the public secant API's form.
  have hslope : Tendsto (fun h : ℝ ↦ slope g x (x - h))
      (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds g') := by
    simpa only [Function.comp_def] using
      (hasDerivWithinAt_iff_tendsto_slope.mp hg).comp hargument
  have hdenominator (h : ℝ) : x - h - x = -h := by
    ring
  simpa only [slope_def_field, hdenominator] using hslope.abs

/-- Helper for Proposition 49.1: differentiability of an extension within the
closed unit interval forces the project-specific secant maximum `Δ` to converge. -/
private lemma maxMagnitude_tendsto_of_hasDerivWithinAt (f : C(unitInterval, ℝ))
    (g : ℝ → ℝ) (hgf : ∀ y : unitInterval, g y = f y) (x : unitInterval)
    {g' : ℝ} (hg : HasDerivWithinAt g g' (Icc (0 : ℝ) 1) x) :
    Tendsto (fun h : ℝ ↦ Δ f (x, h))
      (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds |g'|) := by
  have hx : (x : ℝ) ∈ Icc (0 : ℝ) 1 := x.property
  have hzero : Tendsto (fun h : ℝ ↦ h) (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  by_cases hxzero : (x : ℝ) = 0
  · -- At the left endpoint only the right secant is available for positive `h`.
    have hxone : (x : ℝ) < 1 := by
      linarith
    have hright := rightSecantMagnitude_tendsto hx hxone hg
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hplus : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hh.1]
      · linarith [hh.2]
    have hminus : (x : ℝ) - h ∉ Icc (0 : ℝ) 1 := by
      intro hm
      linarith [hm.1, hh.1]
    rw [maxMagnitude_eq_right f x h hplus hminus]
    rw [← hgf ⟨(x : ℝ) + h, hplus⟩, ← hgf x]
  · by_cases hxone : (x : ℝ) = 1
    · -- At the right endpoint only the left secant is available for positive `h`.
      have hxpos : (0 : ℝ) < x := by
        linarith
      have hleft := leftSecantMagnitude_tendsto hx hxpos hg
      apply hleft.congr'
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hminus : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · linarith [hh.2]
        · linarith [hh.1]
      have hplus : (x : ℝ) + h ∉ Icc (0 : ℝ) 1 := by
        intro hp
        linarith [hp.2, hh.1]
      rw [maxMagnitude_eq_left f x h hminus hplus]
      rw [← hgf ⟨(x : ℝ) - h, hminus⟩, ← hgf x]
    · -- At an interior point both secants are eventually available, so `Δ`
      -- is their maximum and both terms have the same limit.
      have hxpos : (0 : ℝ) < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
      have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne hx.2 hxone
      have hright := rightSecantMagnitude_tendsto hx hxlt hg
      have hleft := leftSecantMagnitude_tendsto hx hxpos hg
      have hsecants : Tendsto
          (fun h : ℝ ↦ max |(g ((x : ℝ) + h) - g x) / h|
            |(g ((x : ℝ) - h) - g x) / (-h)|)
          (nhdsWithin 0 (Ioc 0 (1 / 2))) (nhds |g'|) := by
        simpa only [max_self] using hright.max hleft
      have hsmallRight : ∀ᶠ h : ℝ in nhdsWithin 0 (Ioc 0 (1 / 2)),
          h < 1 - (x : ℝ) :=
        hzero.eventually (Iio_mem_nhds (sub_pos.mpr hxlt))
      have hsmallLeft : ∀ᶠ h : ℝ in nhdsWithin 0 (Ioc 0 (1 / 2)),
          h < (x : ℝ) :=
        hzero.eventually (Iio_mem_nhds hxpos)
      apply hsecants.congr'
      filter_upwards [self_mem_nhdsWithin, hsmallRight, hsmallLeft] with h hh hr hl
      have hplus : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact add_nonneg hx.1 (le_of_lt hh.1)
        · linarith
      have hminus : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact le_of_lt (sub_pos.mpr hl)
        · exact (sub_le_self (x : ℝ) (le_of_lt hh.1)).trans hx.2
      rw [maxMagnitude_eq_max f x h hplus hminus]
      rw [← hgf ⟨(x : ℝ) + h, hplus⟩, ← hgf x,
        ← hgf ⟨(x : ℝ) - h, hminus⟩]

/-- Proposition 49.1: every function belonging to each strict large-secant set
`Uₙ` for `n ≥ 2` is nowhere differentiable within the closed unit interval. -/
theorem largeSecantSet_iInter_nondifferentiable (f : C(unitInterval, ℝ))
    (hf : ∀ n : ℕ, 2 ≤ n → f ∈ U_{n}) :
    ClosedUnitInterval.IsNowhereDifferentiable f := by
  -- For any extension and point, differentiability would give a finite limit
  -- for `Δ`, contradicting the unbounded scales supplied by all the `U_n`.
  intro g hgf x hdiff
  have hg : HasDerivWithinAt g (derivWithin g (Icc (0 : ℝ) 1) x)
      (Icc (0 : ℝ) 1) x := hdiff.hasDerivWithinAt
  have hlimit := maxMagnitude_tendsto_of_hasDerivWithinAt f g hgf x hg
  exact maxMagnitude_not_tendsto f hf x
    ⟨|derivWithin g (Icc (0 : ℝ) 1) x|, hlimit⟩

end UnitIntervalSecant
