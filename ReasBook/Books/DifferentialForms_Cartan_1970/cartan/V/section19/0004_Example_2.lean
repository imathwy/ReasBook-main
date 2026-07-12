import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex
open Filter
open scoped Topology

noncomputable section

-- Semantic recall note: `lean_leansearch` was unavailable in this session; local API recall used
-- `Complex.integerComplement`,
-- `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`, and
-- `PeriodPair.order_weierstrassP`.

/-- The `n`-th summand in the integer square-pole series. -/
def integer_square_pole_series_term (n : ℤ) (z : ℂ) : ℂ :=
  1 / (z - (n : ℂ)) ^ (2 : ℕ)

/-- Example 2 (1): the meromorphic series `∑ n : ℤ, 1 / (z - n)^2` defines a complex-valued
function by summing over all integers. -/
noncomputable def integer_square_pole_series (z : ℂ) : ℂ :=
  ∑' n : ℤ, integer_square_pole_series_term n z

/-- Bridge/view: the chapter series may be reindexed into the canonical `z + n` form used by the
cotangent-derivative expansion in mathlib. The restriction to `integerComplement` is only needed
for downstream comparisons with the cotangent expansion, not for this reindexing itself. -/
theorem integer_square_pole_series_eq_tsum_add_int {z : ℂ} :
    integer_square_pole_series z = ∑' n : ℤ, 1 / (z + (n : ℂ)) ^ (2 : ℕ) := by
  -- Reindex the integer sum by negation to switch from `z - n` to `z + n`.
  rw [integer_square_pole_series]
  conv_lhs => rw [← Equiv.tsum_eq (Equiv.neg ℤ)]
  refine tsum_congr fun n ↦ ?_
  simp [integer_square_pole_series_term, sub_eq_add_neg]

/-- Helper for Example 2: the comparison series `∑ 4 / |n|^2` is summable in the Lean
normalization where the zero term is `0`. -/
private theorem summable_integer_square_majorant :
    Summable (fun n : ℤ ↦ 4 * (((|n| : ℝ) ^ 2)⁻¹)) := by
  -- This is the standard `ℤ`-summable square-decay majorant.
  have hbase : Summable (fun n : ℤ ↦ ((|n| : ℝ) ^ 2)⁻¹) := by
    refine (EisensteinSeries.linear_right_summable (0 : ℂ) (0 : ℤ) (k := (2 : ℤ))
      (by norm_num)).norm.congr ?_
    intro n
    calc
      ‖((((0 : ℤ) : ℂ) * (0 : ℂ) + (n : ℂ)) ^ (2 : ℕ))⁻¹‖ = ‖((n : ℂ) ^ (2 : ℕ))⁻¹‖ := by
        simp
      _ = (‖(n : ℂ)‖ ^ 2)⁻¹ := by simp [norm_inv, norm_pow]
      _ = ((|n| : ℝ) ^ 2)⁻¹ := by simp [Complex.norm_intCast]
  exact hbase.mul_left 4

/-- Helper for Example 2: a term with pole at `n` is controlled by the square-decay majorant once
`n` is at least twice as far from the origin as the evaluation point. -/
private theorem integer_square_pole_series_term_norm_le_majorant {R : ℝ} {z : ℂ} {n : ℤ}
    (hz : ‖z‖ ≤ R) (hn : 2 * R ≤ ‖(n : ℂ)‖) :
    ‖integer_square_pole_series_term n z‖ ≤ 4 * (((|n| : ℝ) ^ 2)⁻¹) := by
  by_cases hnzero : n = 0
  · have hRnonneg : 0 ≤ R := le_trans (norm_nonneg z) hz
    have hRle : R ≤ 0 := by
      have hzero : 2 * R ≤ 0 := by simpa [hnzero] using hn
      linarith
    have hRzero : R = 0 := le_antisymm hRle hRnonneg
    have hzzero : z = 0 := by
      apply norm_eq_zero.mp
      rw [hRzero] at hz
      exact le_antisymm hz (norm_nonneg _)
    simp [integer_square_pole_series_term, hnzero, hzzero]
  -- The reverse triangle inequality gives the lower bound `‖z - n‖ ≥ ‖n‖ / 2`.
  have htriangle : ‖(n : ℂ)‖ ≤ ‖(n : ℂ) - z‖ + ‖z‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      norm_add_le ((n : ℂ) - z) z
  have hhalf : ‖z‖ ≤ ‖(n : ℂ)‖ / 2 := by
    linarith
  have hlower : ‖(n : ℂ)‖ / 2 ≤ ‖z - (n : ℂ)‖ := by
    have h' : ‖(n : ℂ)‖ - ‖z‖ ≤ ‖(n : ℂ) - z‖ := by
      linarith
    have h'' : ‖(n : ℂ)‖ / 2 ≤ ‖(n : ℂ)‖ - ‖z‖ := by
      linarith
    calc
      ‖(n : ℂ)‖ / 2 ≤ ‖(n : ℂ)‖ - ‖z‖ := h''
      _ ≤ ‖(n : ℂ) - z‖ := h'
      _ = ‖z - (n : ℂ)‖ := by rw [norm_sub_rev]
  have hterm :
      ‖integer_square_pole_series_term n z‖ = (‖z - (n : ℂ)‖ ^ 2)⁻¹ := by
    simp [integer_square_pole_series_term, norm_inv, norm_pow]
  have hsq : (‖(n : ℂ)‖ / 2) ^ 2 ≤ ‖z - (n : ℂ)‖ ^ 2 := by
    gcongr
  have hhalf_pos : 0 < (‖(n : ℂ)‖ / 2) ^ 2 := by
    have hnorm_pos : 0 < ‖(n : ℂ)‖ := by
      exact norm_pos_iff.mpr (by simpa using hnzero)
    positivity
  have hterm_pos : 0 < ‖z - (n : ℂ)‖ ^ 2 := by
    have hnorm_pos : 0 < ‖(n : ℂ)‖ := by
      exact norm_pos_iff.mpr (by simpa using hnzero)
    have : 0 < ‖z - (n : ℂ)‖ := lt_of_lt_of_le (by positivity : 0 < ‖(n : ℂ)‖ / 2) hlower
    positivity
  have hinv : (‖z - (n : ℂ)‖ ^ 2)⁻¹ ≤ ((‖(n : ℂ)‖ / 2) ^ 2)⁻¹ := by
    exact (inv_le_inv₀ hterm_pos hhalf_pos).2 hsq
  have hcalc : ((‖(n : ℂ)‖ / 2) ^ 2)⁻¹ = 4 * (((|n| : ℝ) ^ 2)⁻¹) := by
    have hnorm_pos : ‖(n : ℂ)‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (by simpa using hnzero)
    have habs_pos : (|(n : ℝ)|) ≠ 0 := by
      simpa [Complex.norm_intCast] using hnorm_pos
    rw [Complex.norm_intCast]
    field_simp [pow_two, habs_pos]
    ring
  calc
    ‖integer_square_pole_series_term n z‖ = (‖z - (n : ℂ)‖ ^ 2)⁻¹ := hterm
    _ ≤ ((‖(n : ℂ)‖ / 2) ^ 2)⁻¹ := hinv
    _ = 4 * (((|n| : ℝ) ^ 2)⁻¹) := hcalc

/-- Helper for Example 2: the square-pole family is pointwise summable for every `z : ℂ`. -/
private theorem summable_integer_square_pole_series_term (z : ℂ) :
    Summable (fun n : ℤ ↦ integer_square_pole_series_term n z) := by
  -- Reindex the canonical summable `z + n` family by negation.
  have hadd : Summable (fun n : ℤ ↦ 1 / (z + (n : ℂ)) ^ (2 : ℕ)) := by
    simpa using
      (EisensteinSeries.linear_right_summable z 1 (k := (2 : ℤ)) (by norm_num))
  have hneg : Summable (fun n : ℤ ↦ 1 / (z + ((Equiv.neg ℤ) n : ℂ)) ^ (2 : ℕ)) :=
    (Equiv.neg ℤ).summable_iff.mpr hadd
  simpa [integer_square_pole_series_term, sub_eq_add_neg] using hneg

/-- Example 2 (2): away from the integer points, the series
`∑ n : ℤ, 1 / (z - n)^2` is summable locally uniformly. -/
theorem integer_square_pole_series_summableLocallyUniformlyOn :
    SummableLocallyUniformlyOn integer_square_pole_series_term
      integerComplement := by
  -- Compact subsets of `integerComplement` are norm-bounded, so sufficiently far poles have a
  -- uniform `1 / |n|^2` majorant on the whole compact set.
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (by simpa [Complex.integerComplement] using Complex.isOpen_compl_range_intCast)
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  refine ⟨fun n : ℤ ↦ 4 * (((|n| : ℝ) ^ 2)⁻¹), summable_integer_square_majorant, ?_⟩
  have hlarge : ∀ᶠ n : ℤ in cofinite, 2 * R ≤ ‖(n : ℂ)‖ := by
    let M : ℤ := ⌈2 * R⌉
    refine Filter.eventually_cofinite.2 <|
      Set.Finite.subset (Set.finite_Icc (-M) M) ?_
    intro n hn
    have hlt : ‖(n : ℂ)‖ < 2 * R := lt_of_not_ge hn
    have hceil : 2 * R ≤ (M : ℝ) := Int.le_ceil (2 * R)
    have habs_real : ‖(n : ℂ)‖ ≤ (M : ℝ) := le_of_lt (lt_of_lt_of_le hlt hceil)
    have habs_int : |n| ≤ M := by
      exact_mod_cast habs_real
    exact abs_le.mp habs_int
  filter_upwards [hlarge] with n hn z hz
  exact integer_square_pole_series_term_norm_le_majorant (hR z hz) hn

/-- Example 2 (3): the sum of the integer square-pole series has period `1`. -/
theorem integer_square_pole_series_periodic :
    Function.Periodic integer_square_pole_series (1 : ℂ) := by
  intro z
  -- Reindex by the translation `n ↦ n + 1`.
  rw [integer_square_pole_series]
  conv_lhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [integer_square_pole_series_term, Equiv.coe_addRight]

/-- Helper for Example 2: the analytic tail obtained by deleting the `n`-th term. -/
private noncomputable def integer_square_pole_series_tail (n : ℤ) (z : ℂ) : ℂ :=
  ∑' m : ℤ, if m = n then 0 else integer_square_pole_series_term m z

/-- Helper for Example 2: translating the square-decay majorant preserves summability. -/
private theorem summable_integer_square_majorant_shift (n : ℤ) :
    Summable (fun m : ℤ ↦ 4 * (((|m - n| : ℝ) ^ 2)⁻¹)) := by
  -- This is just the base majorant reindexed by an integer translation.
  have hshift := (Equiv.addRight (-n : ℤ)).summable_iff.mpr summable_integer_square_majorant
  refine hshift.congr ?_
  intro m
  simp [sub_eq_add_neg]

/-- Helper for Example 2: the half-ball around `n` contains no point where `z - m = 0` for a
distinct integer `m`. -/
private theorem sub_ne_zero_of_mem_half_ball {n m : ℤ} {z : ℂ}
    (hz : z ∈ Metric.ball (n : ℂ) (1 / 2)) (hmn : m ≠ n) :
    z - (m : ℂ) ≠ 0 := by
  intro hzm
  have hz_eq : z = (m : ℂ) := sub_eq_zero.mp hzm
  have hball : ‖z - (n : ℂ)‖ < 1 / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have habs : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hdist : (1 : ℝ) ≤ ‖z - (n : ℂ)‖ := by
    have habs_real : (1 : ℝ) ≤ ‖((m - n : ℤ) : ℂ)‖ := by
      exact_mod_cast habs
    have hrewrite : ‖z - (n : ℂ)‖ = ‖(((m - n : ℤ) : ℂ))‖ := by
      simpa [hz_eq, sub_eq_add_neg]
    linarith
  nlinarith

/-- Helper for Example 2: deleting the singular term leaves a uniformly square-summable family on
the half-ball around that integer. -/
private theorem integer_square_pole_series_removed_term_summableLocallyUniformlyOn_ball (n : ℤ) :
    SummableLocallyUniformlyOn
      (fun m : ℤ ↦ fun z : ℂ ↦ if m = n then 0 else integer_square_pole_series_term m z)
      (Metric.ball (n : ℂ) (1 / 2)) := by
  -- On the half-ball, every remaining denominator is at least half the distance to the deleted
  -- integer index.
  apply SummableLocallyUniformlyOn_of_locally_bounded Metric.isOpen_ball
  intro K hK hKc
  refine ⟨fun m : ℤ ↦ 4 * (((|m - n| : ℝ) ^ 2)⁻¹),
    summable_integer_square_majorant_shift n, ?_⟩
  intro m z hz
  by_cases hmn : m = n
  · simp [hmn]
  · have hzball : ‖z - (n : ℂ)‖ ≤ 1 / 2 := by
      exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hK hz)
    have hunit : (1 : ℝ) ≤ ‖(((m - n : ℤ) : ℂ))‖ := by
      have habs : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hmn)
      exact_mod_cast habs
    have hcond : 2 * ‖z - (n : ℂ)‖ ≤ ‖(((m - n : ℤ) : ℂ))‖ := by
      nlinarith
    -- Shift the center to `0` so the previous majorant lemma applies directly.
    simpa [integer_square_pole_series_term, hmn, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using
      (integer_square_pole_series_term_norm_le_majorant (R := 1 / 2) (z := z - (n : ℂ))
        (n := m - n) hzball (by simpa using hunit))

/-- Helper for Example 2: the deleted-term tail is analytic at the deleted integer. -/
private theorem analyticAt_integer_square_pole_series_tail (n : ℤ) :
    AnalyticAt ℂ (integer_square_pole_series_tail n) (n : ℂ) := by
  have hdiff :
      DifferentiableOn ℂ (integer_square_pole_series_tail n) (Metric.ball (n : ℂ) (1 / 2)) := by
    -- The tail is locally uniformly summable, and every remaining summand is holomorphic on the
    -- half-ball.
    exact
      (integer_square_pole_series_removed_term_summableLocallyUniformlyOn_ball n).differentiableOn
        Metric.isOpen_ball
        (fun m z hz ↦ by
          by_cases hmn : m = n
          · simpa [integer_square_pole_series_tail, hmn] using
              (differentiableAt_const (c := (0 : ℂ)))
          · have hne : z - (m : ℂ) ≠ 0 := sub_ne_zero_of_mem_half_ball hz hmn
            have hdiff : DifferentiableAt ℂ (fun w : ℂ ↦ w - (m : ℂ)) z := by
              fun_prop
            simpa [integer_square_pole_series_tail, hmn, integer_square_pole_series_term] using
              (((hdiff.pow 2).inv
                (pow_ne_zero 2 hne))))
  -- The half-ball is a genuine neighborhood of `n`, so differentiability upgrades to analyticity.
  exact (hdiff.analyticOnNhd Metric.isOpen_ball) _ (by simp)

/-- Helper for Example 2: the Lean-defined sum splits into the principal term and the deleted
tail. -/
private theorem integer_square_pole_series_principal_part_eventuallyEq (n : ℤ) :
    integer_square_pole_series =ᶠ[𝓝[≠] (n : ℂ)]
      fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ) + integer_square_pole_series_tail n z := by
  -- The singled-out index separates by `tsum_eq_add_tsum_ite`.
  refine Filter.Eventually.of_forall fun z ↦ ?_
  simpa [integer_square_pole_series, integer_square_pole_series_tail, integer_square_pole_series_term]
    using (summable_integer_square_pole_series_term z).tsum_eq_add_tsum_ite n

/-- Helper for Example 2: the isolated principal term has meromorphic order `-2` at its pole. -/
private theorem integer_square_pole_series_term_order_at_self (n : ℤ) :
    meromorphicOrderAt (fun z ↦ integer_square_pole_series_term n z) (n : ℂ) = -2 := by
  -- This is the standard order computation for the inverse square of `z - n`.
  have hpow :
      meromorphicOrderAt (fun z : ℂ ↦ (z - (n : ℂ)) ^ (2 : ℕ)) (n : ℂ) = 2 := by
    exact meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := (n : ℂ)) (n := (2 : ℕ))
  calc
    meromorphicOrderAt (fun z ↦ integer_square_pole_series_term n z) (n : ℂ)
      = -meromorphicOrderAt (fun z : ℂ ↦ (z - (n : ℂ)) ^ (2 : ℕ)) (n : ℂ) := by
          simpa [integer_square_pole_series_term, one_div] using
            (meromorphicOrderAt_inv
              (f := fun z : ℂ ↦ (z - (n : ℂ)) ^ (2 : ℕ)) (x := (n : ℂ)))
    _ = -2 := by rw [hpow]

/-- Example 2 (4): the sum of the integer square-pole series is meromorphic on the complex
plane. -/
theorem integer_square_pole_series_meromorphic :
    Meromorphic integer_square_pole_series := by
  intro z
  by_cases hz : z ∈ integerComplement
  · -- Away from the integers, the locally uniformly convergent sum is analytic.
    have hanalytic : AnalyticOnNhd ℂ integer_square_pole_series integerComplement := by
      have hdiff : DifferentiableOn ℂ integer_square_pole_series integerComplement :=
        integer_square_pole_series_summableLocallyUniformlyOn.differentiableOn
          (by simpa [Complex.integerComplement] using Complex.isOpen_compl_range_intCast)
          (fun n r hr ↦ by
            have hne : r - (n : ℂ) ≠ 0 := by
              simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hr (-n)
            have hdiff : DifferentiableAt ℂ (fun z : ℂ ↦ z - (n : ℂ)) r := by
              fun_prop
            have htermDiff :
                DifferentiableAt ℂ (fun z : ℂ ↦ ((z - (n : ℂ)) ^ (2 : ℕ))⁻¹) r :=
              ((hdiff.pow 2).inv (pow_ne_zero 2 hne))
            show DifferentiableAt ℂ (fun z : ℂ ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ)) r
            simpa [one_div] using htermDiff)
      exact hdiff.analyticOnNhd
        (by simpa [Complex.integerComplement] using Complex.isOpen_compl_range_intCast)
    exact (hanalytic z hz).meromorphicAt
  · -- At an integer, use the principal-part decomposition proved below.
    have hzint : z ∈ Set.range ((↑) : ℤ → ℂ) := by
      simpa [Complex.integerComplement] using hz
    rcases hzint with ⟨n, rfl⟩
    let g := integer_square_pole_series_tail n
    have hg : AnalyticAt ℂ g (n : ℂ) := analyticAt_integer_square_pole_series_tail n
    have hEq := integer_square_pole_series_principal_part_eventuallyEq n
    have hprincipal : MeromorphicAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ)) (n : ℂ) := by
      have hpow : MeromorphicAt (fun z : ℂ ↦ (z - (n : ℂ)) ^ (2 : ℕ)) (n : ℂ) := by
        fun_prop
      have hprincipal' :
          MeromorphicAt (fun z : ℂ ↦ ((z - (n : ℂ)) ^ (2 : ℕ))⁻¹) (n : ℂ) := hpow.inv
      simpa [one_div] using hprincipal'
    have hmodel : MeromorphicAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ) + g z) (n : ℂ) := by
      exact hprincipal.add hg.meromorphicAt
    exact hmodel.congr hEq.symm

/-- Example 2 (5): every integer point is a pole of order `2` of the sum of the series. -/
theorem integer_square_pole_series_order_at_int (n : ℤ) :
    meromorphicOrderAt integer_square_pole_series (n : ℂ) = -2 := by
  let g := integer_square_pole_series_tail n
  have hg : AnalyticAt ℂ g (n : ℂ) := analyticAt_integer_square_pole_series_tail n
  have hEq := integer_square_pole_series_principal_part_eventuallyEq n
  have hprincipalOrder :
      meromorphicOrderAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ)) (n : ℂ) = -2 := by
    simpa [integer_square_pole_series_term, one_div] using
      integer_square_pole_series_term_order_at_self n
  have hmodel :
      meromorphicOrderAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ) + g z) (n : ℂ) = -2 := by
    -- The analytic tail has nonnegative order, so the pole order is controlled by the principal
    -- term alone.
    have hneg : ((-2 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ) := by
      exact_mod_cast (show (-2 : ℤ) < 0 by decide)
    have hpoleNeg :
        meromorphicOrderAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ)) (n : ℂ) < 0 := by
      rw [hprincipalOrder]
      exact hneg
    have hsame :
        meromorphicOrderAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ) + g z) (n : ℂ) =
          meromorphicOrderAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ)) (n : ℂ) := by
      exact meromorphicOrderAt_add_eq_left_of_lt
        (f₁ := fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ))
        (f₂ := g)
        hg.meromorphicAt
        (lt_of_lt_of_le hpoleNeg hg.meromorphicOrderAt_nonneg)
    exact hsame.trans hprincipalOrder
  calc
    meromorphicOrderAt integer_square_pole_series (n : ℂ) =
      meromorphicOrderAt (fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ) + g z) (n : ℂ) :=
        meromorphicOrderAt_congr hEq
    _ = -2 := hmodel

/-- Example 2 (6): near each integer `n`, the sum has principal part `1 / (z - n)^2`; this is the
source-form expansion used to read off that the residue is zero. -/
theorem integer_square_pole_series_principal_part_at_int (n : ℤ) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (n : ℂ) ∧
        integer_square_pole_series =ᶠ[𝓝[≠] (n : ℂ)]
          fun z ↦ 1 / (z - (n : ℂ)) ^ (2 : ℕ) + g z := by
  refine ⟨integer_square_pole_series_tail n, analyticAt_integer_square_pole_series_tail n,
    integer_square_pole_series_principal_part_eventuallyEq n⟩
