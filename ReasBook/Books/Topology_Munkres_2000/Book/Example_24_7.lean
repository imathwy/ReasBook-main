module

public import Topology_Munkres_2000.Book.Example_24_7.Connectedness

public section

open Filter Topology

namespace TopologistsSineCurve

/-- Helper for Example 24.7: `sin (1 / u)` attains either sign arbitrarily close to zero. -/
private lemma exists_pos_lt_sin_inv_eq_sign {ε z : ℝ} (hε : 0 < ε)
    (hz : z = 1 ∨ z = -1) :
    ∃ u, 0 < u ∧ u < ε ∧ Real.sin (1 / u) = z := by
  -- Large positive phases with the required quarter-period value have small reciprocals.
  rcases hz with rfl | rfl
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / (2 * Real.pi * ε))
    let a : ℝ := Real.pi / 2 + n * (2 * Real.pi)
    have ha_pos : 0 < a := by
      dsimp [a]
      positivity
    have ha_large : 1 / ε < a := by
      have hpi : 0 < 2 * Real.pi := by
        positivity
      have hn' : 1 / ε < (n : ℝ) * (2 * Real.pi) := by
        calc
          1 / ε = (1 / (2 * Real.pi * ε)) * (2 * Real.pi) := by field_simp
          _ < (n : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hn hpi
      dsimp [a]
      linarith [Real.pi_pos]
    refine ⟨1 / a, one_div_pos.mpr ha_pos, ?_, ?_⟩
    · apply (div_lt_iff₀ ha_pos).2
      have hscaled := (div_lt_iff₀ hε).1 ha_large
      nlinarith
    · simp only [one_div, inv_inv]
      exact Real.sin_add_nat_mul_two_pi _ _ |>.trans Real.sin_pi_div_two
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / (2 * Real.pi * ε))
    let a : ℝ := 3 * Real.pi / 2 + n * (2 * Real.pi)
    have ha_pos : 0 < a := by
      dsimp [a]
      positivity
    have ha_large : 1 / ε < a := by
      have hpi : 0 < 2 * Real.pi := by
        positivity
      have hn' : 1 / ε < (n : ℝ) * (2 * Real.pi) := by
        calc
          1 / ε = (1 / (2 * Real.pi * ε)) * (2 * Real.pi) := by field_simp
          _ < (n : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hn hpi
      dsimp [a]
      linarith [Real.pi_pos]
    refine ⟨1 / a, one_div_pos.mpr ha_pos, ?_, ?_⟩
    · apply (div_lt_iff₀ ha_pos).2
      have hscaled := (div_lt_iff₀ hε).1 ha_large
      nlinarith
    · simp only [one_div, inv_inv]
      dsimp [a]
      rw [Real.sin_add_nat_mul_two_pi]
      rw [show (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi by ring]
      rw [Real.sin_add_pi, Real.sin_pi_div_two]

/-- Helper for Example 24.7: a nonvertical point of `carrier` lies on `curve`. -/
private lemma mem_curve_of_mem_carrier_fst_ne_zero {p : ℝ × ℝ}
    (hp : p ∈ carrier) (hp_ne : p.1 ≠ 0) : p ∈ curve := by
  -- A convergent sequence of graph points preserves the graph equation away from zero.
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨v, hv_curve, hv_lim⟩ := hp
  have hx_lim : Filter.Tendsto (fun n ↦ (v n).1) Filter.atTop (𝓝 p.1) :=
    continuousAt_fst.tendsto.comp hv_lim
  have hy_lim : Filter.Tendsto (fun n ↦ (v n).2) Filter.atTop (𝓝 p.2) :=
    continuousAt_snd.tendsto.comp hv_lim
  have hpos : 0 ≤ p.1 := by
    apply ge_of_tendsto hx_lim
    filter_upwards with n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
    exact hx.1.le
  have hle : p.1 ≤ 1 := by
    apply le_of_tendsto hx_lim
    filter_upwards with n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
    exact hx.2
  have hpos' : 0 < p.1 := lt_of_le_of_ne hpos (Ne.symm hp_ne)
  have hsin_lim :
      Filter.Tendsto (fun n ↦ Real.sin (1 / (v n).1)) Filter.atTop
        (𝓝 (Real.sin (1 / p.1))) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ Real.sin (1 / x)) p.1 := by
      fun_prop
    exact hcont.tendsto.comp hx_lim
  have hy_eq : p.2 = Real.sin (1 / p.1) := by
    apply tendsto_nhds_unique hy_lim
    convert hsin_lim using 1
    funext n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
  exact ⟨p.1, ⟨hpos', hle⟩, Prod.ext rfl hy_eq.symm⟩

/-- Helper for Example 24.7: the origin belongs to the closure `carrier`. -/
private lemma origin_mem_carrier : (0, 0) ∈ carrier := by
  -- Graph points at reciprocal integer multiples of `π` converge to the origin.
  rw [mem_closure_iff_seq_limit]
  let v : ℕ → ℝ × ℝ := fun n ↦
    (1 / (((n + 1 : ℕ) : ℝ) * Real.pi), 0)
  refine ⟨v, ?_, ?_⟩
  · intro n
    refine ⟨1 / (((n + 1 : ℕ) : ℝ) * Real.pi), ?_, ?_⟩
    · constructor
      · positivity
      · have hden : 1 ≤ (((n + 1 : ℕ) : ℝ) * Real.pi) := by
          have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by
            exact_mod_cast Nat.succ_pos n
          have hpi : (2 : ℝ) ≤ Real.pi := by
            linarith [Real.one_le_pi_div_two]
          nlinarith
        apply (div_le_iff₀
          (show (0 : ℝ) < (((n + 1 : ℕ) : ℝ) * Real.pi) by positivity)).2
        simpa using hden
    · apply Prod.ext
      · rfl
      · dsimp [v]
        simp only [one_div, inv_inv]
        simpa only using Real.sin_nat_mul_pi (n + 1)
  · have hx :
        Filter.Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) * Real.pi))
          Filter.atTop (𝓝 0) := by
      have hbase : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      convert hbase.const_mul (1 / Real.pi) using 1
      · funext n
        simp only [Nat.cast_add, Nat.cast_one]
        field_simp
      · simp
    have hy : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds
    rw [nhds_prod_eq]
    exact hx.prodMk hy

/-- Helper for Example 24.7: points on `curve` have positive first coordinate. -/
private lemma curve_fst_pos {p : ℝ × ℝ} (hp : p ∈ curve) : 0 < p.1 := by
  -- Unpack the graph parameter, which belongs to `(0, 1]`.
  rcases hp with ⟨x, hx, rfl⟩
  exact hx.1

/-- Helper for Example 24.7: the second coordinate on `curve` is the oscillating function. -/
private lemma curve_snd_eq {p : ℝ × ℝ} (hp : p ∈ curve) :
    p.2 = Real.sin (1 / p.1) := by
  -- Unpack the defining image of the graph.
  rcases hp with ⟨x, hx, rfl⟩
  rfl

/-- Helper for Example 24.7: no path in `carrier` joins `vertical` to `curve`. -/
private lemma not_joinedIn_zero_curve {p q : ℝ × ℝ}
    (hp_zero : p.1 = 0) (hq : q ∈ curve) : ¬ JoinedIn carrier p q := by
  -- Choose a joining path and isolate the greatest parameter with zero first coordinate.
  intro hpq
  classical
  let γ : Path p q := hpq.somePath
  let zeroSet : Set unitInterval := {t | (γ t).1 = 0}
  have hx_cont : Continuous (fun t : unitInterval ↦ (γ t).1) :=
    continuous_fst.comp γ.continuous
  have hy_cont : Continuous (fun t : unitInterval ↦ (γ t).2) :=
    continuous_snd.comp γ.continuous
  have hzero_closed : IsClosed zeroSet := by
    exact isClosed_eq hx_cont continuous_const
  have hzero_nonempty : zeroSet.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [zeroSet, γ]
    rw [hpq.somePath.source]
    exact hp_zero
  obtain ⟨b, hb_mem, hb_greatest⟩ :=
    hzero_closed.isCompact.exists_isGreatest hzero_nonempty
  have hb_zero : (γ b).1 = 0 := hb_mem
  have hq_fst_pos : 0 < q.1 := curve_fst_pos hq
  have hb_lt_one : b < 1 := by
    rw [unitInterval.lt_one_iff_ne_one]
    intro hb_one
    subst b
    rw [γ.target] at hb_zero
    linarith
  -- Every later path point is nonvertical, hence lies on the oscillating graph.
  have hafter_curve {t : unitInterval} (hbt : b < t) : γ t ∈ curve := by
    apply mem_curve_of_mem_carrier_fst_ne_zero (hpq.somePath_mem t)
    intro ht_zero
    have ht_mem : t ∈ zeroSet := ht_zero
    exact (not_le_of_gt hbt) (hb_greatest ht_mem)
  have hafter_pos {t : unitInterval} (hbt : b < t) : 0 < (γ t).1 :=
    curve_fst_pos (hafter_curve hbt)
  have hafter_snd {t : unitInterval} (hbt : b < t) :
      (γ t).2 = Real.sin (1 / (γ t).1) :=
    curve_snd_eq (hafter_curve hbt)
  -- Choose the sign whose distance from the second coordinate at `b` is at least one.
  obtain ⟨z : ℝ, hz_sign, hz_far⟩ :
      ∃ z : ℝ, (z = 1 ∨ z = -1) ∧ 1 ≤ |z - (γ b).2| := by
    by_cases hnonneg : 0 ≤ (γ b).2
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_of_nonpos]
      · linarith
      · linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [abs_of_nonneg]
      · linarith
      · linarith
  have hy_at : ContinuousAt (fun t : unitInterval ↦ (γ t).2) b := hy_cont.continuousAt
  have hhalf : (0 : ℝ) < 1 / 2 := by
    norm_num
  obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.continuousAt_iff.mp hy_at) (1 / 2) hhalf
  let η : ℝ := min ((1 - (b : ℝ)) / 2) (δ / 2)
  have hb_real : (b : ℝ) < 1 := by
    exact_mod_cast hb_lt_one
  have hη_pos : 0 < η := by
    dsimp [η]
    have hleft : 0 < (1 - (b : ℝ)) / 2 := by
      linarith
    have hright : 0 < δ / 2 := by
      linarith
    exact lt_min hleft hright
  have hη_lt_one : (b : ℝ) + η < 1 := by
    have hη_le : η ≤ (1 - (b : ℝ)) / 2 := min_le_left _ _
    linarith
  have ht_mem : (b : ℝ) + η ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg b.property.1 hη_pos.le
    · exact hη_lt_one.le
  let t : unitInterval := ⟨(b : ℝ) + η, ht_mem⟩
  have hbt : b < t := by
    rw [← Subtype.coe_lt_coe]
    dsimp [t]
    linarith
  have ht_close : dist t b < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hη_le : η ≤ δ / 2 := min_le_right _ _
    dsimp [t]
    rw [abs_of_nonneg]
    · linarith
    · linarith
  -- Realize the distant sign below the first coordinate at `t`, then use the IVT.
  obtain ⟨u, hu_pos, hu_lt, hu_sin⟩ :=
    exists_pos_lt_sin_inv_eq_sign (hafter_pos hbt) hz_sign
  have hu_between : u ∈ Set.Icc ((γ b).1) ((γ t).1) := by
    rw [hb_zero]
    exact ⟨hu_pos.le, hu_lt.le⟩
  obtain ⟨s, hs_bounds, hs_x⟩ :=
    (intermediate_value_Icc hbt.le hx_cont.continuousOn) hu_between
  have hbs : b < s := by
    apply lt_of_not_ge
    intro hsb
    have hsb_eq : s = b := le_antisymm hsb hs_bounds.1
    subst s
    change (γ b).1 = u at hs_x
    rw [hb_zero] at hs_x
    linarith
  have hs_close : dist s b < δ := by
    calc
      dist s b = (s : ℝ) - b := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        exact sub_nonneg.mpr hs_bounds.1
      _ ≤ (t : ℝ) - b := by
        have hst : (s : ℝ) ≤ t := by
          exact_mod_cast hs_bounds.2
        exact sub_le_sub_right hst _
      _ = dist t b := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        exact sub_nonneg.mpr hbt.le
      _ < δ := ht_close
  have hy_close := hδ hs_close
  have hs_snd : (γ s).2 = z := by
    rw [hafter_snd hbs]
    change Real.sin (1 / (fun r : unitInterval ↦ (γ r).1) s) = z
    rw [hs_x, hu_sin]
  -- The oscillating value is simultaneously too close to and too far from the limit value.
  rw [hs_snd, Real.dist_eq] at hy_close
  linarith

/- Example 24.7 (1): The oscillating graph `curve` is connected. -/
#check curve_isConnected

/- Example 24.7 (2): The closure `carrier` of the oscillating graph is connected. -/
#check carrier_isConnected

/- Example 24.7 (3): The closure of the oscillating graph is the union of the
graph with the limiting vertical interval. -/
#check TopologistsSineCurve.carrier_eq_curve_union_vertical

/-- Example 24.7 (4): The topologist's sine curve is not path connected. -/
theorem carrier_not_isPathConnected : ¬ IsPathConnected carrier := by
  -- Explicit points in the two pieces would have to be joined under path connectedness.
  intro hpath
  let p : ℝ × ℝ := (0, 0)
  let q : ℝ × ℝ := (1, Real.sin 1)
  have hone_mem : (1 : ℝ) ∈ Set.Ioc 0 1 := ⟨by norm_num, le_rfl⟩
  have hq_curve : q ∈ curve := by
    refine ⟨1, hone_mem, ?_⟩
    dsimp [q]
    ring_nf
  have hp_carrier : p ∈ carrier := origin_mem_carrier
  have hq_carrier : q ∈ carrier := by
    rw [carrier_eq_curve_union_vertical]
    exact Or.inl hq_curve
  have hp_zero : p.1 = 0 := rfl
  exact not_joinedIn_zero_curve hp_zero hq_curve
    (hpath.joinedIn p hp_carrier q hq_carrier)

end TopologistsSineCurve
