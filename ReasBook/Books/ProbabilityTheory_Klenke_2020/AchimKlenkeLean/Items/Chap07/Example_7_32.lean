import ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped MeasureTheory

/- Example 7.32 (1): the textbook assertion that a measure on `ℝ` given by a density with respect
to Lebesgue measure is absolutely continuous with respect to Lebesgue measure is the canonical
theorem `withDensity_absolutelyContinuous`, specialized to `volume`. -/
recall withDensity_absolutelyContinuous

private theorem volume_absolutelyContinuous_withDensity_of_ae_pos (f : ℝ → ENNReal)
    (hf : AEMeasurable f volume) (hpos : ∀ᵐ x ∂volume, 0 < f x) :
    volume ≪ volume.withDensity f := by
  refine withDensity_absolutelyContinuous' hf ?_
  filter_upwards [hpos] with x hx
  exact ne_of_gt hx

-- Proof sketch: combine `withDensity_absolutelyContinuous` with
-- `withDensity_absolutelyContinuous'`; by `Measure.ae_le_iff_absolutelyContinuous`, the resulting
-- two one-sided absolute-continuity statements are exactly the canonical characterization of
-- equivalence of measures.
/-- Example 7.32 (2): In (i), if the density is positive almost everywhere, then the density
measure induces the same almost-everywhere filter as Lebesgue measure. -/
theorem withDensity_volume_ae_eq_of_ae_pos (f : ℝ → ENNReal)
    (hf : AEMeasurable f volume) (hpos : ∀ᵐ x ∂volume, 0 < f x) :
    ae (volume.withDensity f) = ae volume := by
  apply le_antisymm
  · exact ae_le_iff_absolutelyContinuous.mpr (withDensity_absolutelyContinuous volume f)
  · exact ae_le_iff_absolutelyContinuous.mpr
      (volume_absolutelyContinuous_withDensity_of_ae_pos f hf hpos)

-- Proof sketch: the set where `f = 0` has zero mass for `volume.withDensity f`; if that set has
-- positive Lebesgue measure, then `volume` cannot be absolutely continuous with respect to the
-- density measure.
/-- Example 7.32 (3): In (i), if the zero set of the density has positive Lebesgue measure, then
Lebesgue measure is not absolutely continuous with respect to the density measure. -/
theorem not_absolutelyContinuous_volume_withDensity_of_zero_set (f : ℝ → ENNReal)
    (hf : AEMeasurable f volume) (hzero : 0 < volume {x | f x = 0}) :
    ¬ volume ≪ volume.withDensity f := by
  intro h
  have hdisj : {x | f x ≠ 0} ∩ {x | f x = 0} = ∅ := by
    ext x
    simp
  have h_withDensity_zero : volume.withDensity f {x | f x = 0} = 0 := by
    rw [withDensity_apply_eq_zero' hf]
    simp [hdisj]
  have h_volume_zero : volume {x | f x = 0} = 0 := h h_withDensity_zero
  exact (not_lt_of_ge (le_of_eq h_volume_zero)) hzero

-- Proof sketch: when `0 < p < 1`, both atoms of `Bool` have positive `Ber_p`-mass, so every
-- `Ber_p`-null measurable set is empty and hence also `Ber_q`-null.
/-- Example 7.32 (4): In (ii), if `p ∈ (0,1)`, then every Bernoulli law `Ber_q` is absolutely
continuous with respect to `Ber_p`. -/
theorem bernoulli_absolutelyContinuous_of_zero_lt_lt_one (p q : NNReal) (hq : q ≤ 1)
    (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    (PMF.bernoulli q hq).toMeasure ≪ (PMF.bernoulli p hp_lt_one.le).toMeasure := sorry

private theorem bernoulli_extreme_le_one {p : NNReal} (hp_extreme : p = 0 ∨ p = 1) : p ≤ 1 := by
  rcases hp_extreme with rfl | rfl <;> simp

-- Proof sketch: if `p` is `0` or `1`, then `Ber_p` is a Dirac mass; absolute continuity of
-- `Ber_q` with respect to this Dirac measure forces `Ber_q` to be the same Dirac mass.
/-- Example 7.32 (5): In (ii), if `p ∈ {0,1}`, then `Ber_q ≪ Ber_p` holds exactly when `q = p`. -/
theorem bernoulli_absolutelyContinuous_iff_of_extreme (p q : NNReal) (hq : q ≤ 1)
    (hp_extreme : p = 0 ∨ p = 1) :
    (PMF.bernoulli q hq).toMeasure ≪
      (PMF.bernoulli p (bernoulli_extreme_le_one hp_extreme)).toMeasure ↔ q = p :=
  sorry

-- Proof sketch: for degenerate `Ber_p`, the only way for `Ber_q` and `Ber_p` to be supported on
-- disjoint atoms is for `Ber_q` to be the complementary Dirac measure, i.e. `q = 1 - p`.
/-- Example 7.32 (6): In (ii), if `p ∈ {0,1}`, then `Ber_q` and `Ber_p` are singular exactly when
`q = 1 - p`. -/
theorem bernoulli_mutuallySingular_iff_of_extreme (p q : NNReal) (hq : q ≤ 1)
    (hp_extreme : p = 0 ∨ p = 1) :
    (PMF.bernoulli q hq).toMeasure ⟂ₘ
      (PMF.bernoulli p (bernoulli_extreme_le_one hp_extreme)).toMeasure ↔ q = 1 - p := sorry

-- Proof sketch: `Poi_β` has full support on `ℕ` when `β > 0`, whereas `Poi_0` is the Dirac mass at
-- `0`; compare null sets with the singleton `{0}`.
/-- Example 7.32 (7): In (iii), `Poi_α` is absolutely continuous with respect to `Poi_β` exactly
when `β > 0` or `α = 0`. -/
theorem poissonMeasure_absolutelyContinuous_iff (α β : NNReal) :
    poissonMeasure α ≪ poissonMeasure β ↔ 0 < β ∨ α = 0 := sorry

-- Proof sketch: apply the strong law of large numbers to the coordinate projections under each
-- Bernoulli product measure; the empirical means converge almost surely to the parameter, so the
-- full-measure convergence sets are disjoint when `p ≠ q`.
/-- Example 7.32 (8): In (iv), the infinite Bernoulli product measures with distinct parameters are
mutually singular. -/
theorem bernoulli_infiniteProduct_mutuallySingular_of_ne (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≠ q) :
    infinitePi (fun _ : ℕ ↦ (PMF.bernoulli p hp).toMeasure) ⟂ₘ
      infinitePi (fun _ : ℕ ↦ (PMF.bernoulli q hq).toMeasure) := sorry
