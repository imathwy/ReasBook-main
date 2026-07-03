import Mathlib

open Filter Set
open scoped Topology ENNReal NNReal
open FormalMultilinearSeries
open ContinuousMultilinearMap

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Exercise 15: scalar one-variable analyticity is equivalent to admitting a scalar
power-series expansion. -/
theorem analyticAt_iff_exists_hasFPowerSeriesAt_ofScalars_local
    {f : ℝ → ℝ} {x₀ : ℝ} :
    AnalyticAt ℝ f x₀ ↔ ∃ a : ℕ → ℝ, HasFPowerSeriesAt f (ofScalars ℝ a) x₀ := by
  constructor
  · -- Extract the scalar coefficients of the given formal multilinear series.
    rintro ⟨p, hp⟩
    refine ⟨p.coeff, ?_⟩
    convert hp using 1
    ext n
    rw [← mkPiRing_coeff_eq p n, ← mkPiRing_coeff_eq (ofScalars ℝ p.coeff) n, coeff_ofScalars]
  · -- Any scalar power-series witness is already an analytic witness.
    rintro ⟨a, ha⟩
    exact ha.analyticAt

/-- Helper for Exercise 15: a real-valued real-analytic germ extends holomorphically to a small
complex ball. -/
lemma real_analyticAt_exists_complex_ball_extension {u : ℝ → ℝ} {x : ℝ}
    (hu : AnalyticAt ℝ u x) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball (Complex.ofReal x) r) ∧
        Set.EqOn (fun t : ℝ ↦ g (Complex.ofReal t)) (fun t ↦ (u t : ℂ)) (Metric.ball x r) := by
  rcases analyticAt_iff_exists_hasFPowerSeriesAt_ofScalars_local.mp hu with ⟨a, ha⟩
  let p : FormalMultilinearSeries ℝ ℝ ℝ := ofScalars ℝ a
  let q : FormalMultilinearSeries ℂ ℂ ℂ := ofScalars ℂ (fun n ↦ (a n : ℂ))
  have hp_pos : 0 < p.radius := by
    simpa [p] using ha.radius_pos
  rcases ha with ⟨rp, hpball⟩
  have hrp_pos : 0 < rp := hpball.r_pos
  have hq_radius : q.radius = p.radius := by
    -- The real and complex scalar series have identical coefficient norms, hence the same radius.
    rw [show q.radius = liminf (fun n => (1 / (‖q n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop by
      simpa using q.radius_eq_liminf]
    rw [show p.radius = liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop by
      simpa using p.radius_eq_liminf]
    congr with n
    have hnnnorm : ‖q n‖₊ = ‖p n‖₊ := by
      ext
      simp [p, q]
    rw [hnnnorm]
  have hq_pos : 0 < q.radius := by
    rw [hq_radius]
    exact hp_pos
  have hmin_pos : 0 < q.radius ⊓ rp := lt_min hq_pos hrp_pos
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hmin_pos with ⟨r, hr_pos, hr_lt⟩
  have hr_lt_q : (r : ℝ≥0∞) < q.radius := lt_of_lt_of_le hr_lt inf_le_left
  have hr_le_rp : (r : ℝ≥0∞) ≤ rp := le_of_lt <| lt_of_lt_of_le hr_lt inf_le_right
  let g : ℂ → ℂ := fun z ↦ q.sum (z - Complex.ofReal x)
  have hqball : HasFPowerSeriesOnBall g q (Complex.ofReal x) q.radius := by
    -- Translate the power series centered at `0` to a power series centered at `x`.
    simpa [g] using (q.hasFPowerSeriesOnBall hq_pos).comp_sub (Complex.ofReal x)
  have hqsmall : HasFPowerSeriesOnBall g q (Complex.ofReal x) (r : ℝ≥0∞) :=
    hqball.mono hr_pos hr_lt_q.le
  refine ⟨r, by exact_mod_cast hr_pos, g, ?_, ?_⟩
  · -- Holomorphicity on the smaller ball follows from the translated power-series expansion.
    simpa using hqsmall.analyticOnNhd.differentiableOn
  · intro t ht
    have hp_small : HasFPowerSeriesOnBall u p x (r : ℝ≥0∞) := hpball.mono hr_pos hr_le_rp
    have hu_sum : u t = p.sum (t - x) := by
      -- Evaluate the original real power series at the real displacement `t - x`.
      have ht0 : t - x ∈ Metric.eball (0 : ℝ) (r : ℝ≥0∞) := by
        simpa [Metric.mem_eball, Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using ht
      simpa [sub_eq_add_neg] using hp_small.sum ht0
    calc
      g (Complex.ofReal t) = q.sum (Complex.ofReal (t - x)) := by
        simp [g, Complex.ofReal_sub]
      _ = (p.sum (t - x) : ℂ) := by
        -- On real arguments, the complex scalar series is just the complexification of the real one.
        change
          FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ (a n : ℂ))
              (Complex.ofReal (t - x)) =
            ((FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (t - x)) : ℂ)
        rw [FormalMultilinearSeries.ofScalars_sum_eq, FormalMultilinearSeries.ofScalars_sum_eq]
        symm
        simpa [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow] using
          (Complex.ofReal_tsum (fun n : ℕ ↦ a n * (t - x) ^ n))
      _ = u t := by
        simp [hu_sum]

/-- Helper for Exercise 15: a real-analytic germ with values in `ℂ` admits a holomorphic extension
to a complex ball around the same real center. -/
lemma analyticAt_exists_complex_ball_extension {f : ℝ → ℂ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball (Complex.ofReal x) r) ∧
        Set.EqOn (fun t : ℝ ↦ g (Complex.ofReal t)) f (Metric.ball x r) := by
  have hre : AnalyticAt ℝ (fun t : ℝ ↦ (f t).re) x :=
    (Complex.reCLM.analyticAt (f x)).comp hf
  have him : AnalyticAt ℝ (fun t : ℝ ↦ (f t).im) x :=
    (Complex.imCLM.analyticAt (f x)).comp hf
  rcases real_analyticAt_exists_complex_ball_extension hre with ⟨rr, hrr_pos, gr, hgr_diff, hgr_eq⟩
  rcases real_analyticAt_exists_complex_ball_extension him with ⟨ri, hri_pos, gi, hgi_diff, hgi_eq⟩
  let r : ℝ := min rr ri
  let g : ℂ → ℂ := fun z ↦ gr z + Complex.I * gi z
  refine ⟨r, lt_min hrr_pos hri_pos, g, ?_, ?_⟩
  · -- Restrict both local charts to the common smaller radius and recombine them.
    have hgr_diff' : DifferentiableOn ℂ gr (Metric.ball (Complex.ofReal x) r) := by
      exact hgr_diff.mono (Metric.ball_subset_ball <| min_le_left _ _)
    have hgi_diff' : DifferentiableOn ℂ gi (Metric.ball (Complex.ofReal x) r) := by
      exact hgi_diff.mono (Metric.ball_subset_ball <| min_le_right _ _)
    simpa [g, mul_comm] using hgr_diff'.add (hgi_diff'.const_mul Complex.I)
  · intro t ht
    have htrr : t ∈ Metric.ball x rr := Metric.ball_subset_ball (min_le_left _ _) ht
    have htri : t ∈ Metric.ball x ri := Metric.ball_subset_ball (min_le_right _ _) ht
    calc
      g (Complex.ofReal t) = gr (Complex.ofReal t) + Complex.I * gi (Complex.ofReal t) := by
        rfl
      _ = ((f t).re : ℂ) + Complex.I * ((f t).im : ℂ) := by
        simp [hgr_eq htrr, hgi_eq htri]
      _ = f t := by
        simpa [mul_comm] using (Complex.re_add_im (f t))

/-- Helper for Exercise 15: if two complex balls centered on points of an interval overlap, then
one can choose a real point of the interval lying in both corresponding real balls. -/
lemma interval_overlap_contains_real_point {I : Set ℝ} (hI : Set.OrdConnected I)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) {rx ry : ℝ} {z : ℂ}
    (hzx : z ∈ Metric.ball (Complex.ofReal x) rx) (hzy : z ∈ Metric.ball (Complex.ofReal y) ry) :
    ∃ t ∈ I, t ∈ Metric.ball x rx ∧ t ∈ Metric.ball y ry := by
  have hrx : 0 < rx := lt_of_le_of_lt dist_nonneg hzx
  have hry : 0 < ry := lt_of_le_of_lt dist_nonneg hzy
  have hsum_pos : 0 < rx + ry := by
    linarith
  have hsum_ne : rx + ry ≠ 0 := ne_of_gt hsum_pos
  have hdist : |x - y| < rx + ry := by
    -- The overlap point forces the two real centers to be closer than the sum of the radii.
    have hdistC : dist (Complex.ofReal x) (Complex.ofReal y) < rx + ry := by
      calc
        dist (Complex.ofReal x) (Complex.ofReal y) ≤
            dist (Complex.ofReal x) z + dist z (Complex.ofReal y) := dist_triangle _ _ _
        _ < rx + ry := by
          have hx' : dist (Complex.ofReal x) z < rx := by
            simpa [dist_comm] using hzx
          exact add_lt_add hx' hzy
    have hdistR : dist x y < rx + ry := by
      simpa [Complex.isometry_ofReal.dist_eq x y] using hdistC
    simpa [Real.dist_eq] using hdistR
  let t : ℝ := (ry * x + rx * y) / (rx + ry)
  have ht_mem_I : t ∈ I := by
    -- The weighted average lies between `x` and `y`, hence remains in the order-connected interval.
    by_cases hxy : x ≤ y
    · have hx_le_t : x ≤ t := by
        dsimp [t]
        exact (le_div_iff₀ hsum_pos).2 (by nlinarith)
      have ht_le_y : t ≤ y := by
        dsimp [t]
        exact (div_le_iff₀ hsum_pos).2 (by nlinarith)
      exact (hI.out hx hy) ⟨hx_le_t, ht_le_y⟩
    · have hy_le_t : y ≤ t := by
        dsimp [t]
        exact (le_div_iff₀ hsum_pos).2 (by nlinarith)
      have ht_le_x : t ≤ x := by
        dsimp [t]
        exact (div_le_iff₀ hsum_pos).2 (by nlinarith)
      exact (hI.out hy hx) ⟨hy_le_t, ht_le_x⟩
  have ht_ball_x : t ∈ Metric.ball x rx := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |t - x| = rx * |y - x| / (rx + ry) := by
      dsimp [t]
      rw [show (ry * x + rx * y) / (rx + ry) - x = rx * (y - x) / (rx + ry) by
        field_simp [hsum_ne]
        ring_nf]
      rw [abs_div, abs_mul, abs_of_pos hrx, abs_of_pos hsum_pos]
    have hmul : rx * |y - x| < rx * (rx + ry) := by
      exact mul_lt_mul_of_pos_left (by simpa [abs_sub_comm] using hdist) hrx
    have hlt : rx * |y - x| / (rx + ry) < rx :=
      (div_lt_iff₀ hsum_pos).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact habs.trans_lt hlt
  have ht_ball_y : t ∈ Metric.ball y ry := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |t - y| = ry * |y - x| / (rx + ry) := by
      dsimp [t]
      rw [show (ry * x + rx * y) / (rx + ry) - y = ry * (x - y) / (rx + ry) by
        field_simp [hsum_ne]
        ring_nf]
      rw [abs_div, abs_mul, abs_of_pos hry, abs_of_pos hsum_pos, abs_sub_comm]
    have hmul : ry * |y - x| < ry * (rx + ry) := by
      exact mul_lt_mul_of_pos_left (by simpa [abs_sub_comm] using hdist) hry
    have hlt : ry * |y - x| / (rx + ry) < ry :=
      (div_lt_iff₀ hsum_pos).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact habs.trans_lt hlt
  exact ⟨t, ht_mem_I, ht_ball_x, ht_ball_y⟩

/-- Helper for Exercise 15: if two local complex extensions agree with the same real function on
overlapping real balls, then they coincide frequently at the corresponding punctured complex
neighborhood of any common real point. -/
private lemma complex_extensions_frequently_eq_at_real_point
    {f : ℝ → ℂ} {gx gy : ℂ → ℂ} {x y t rx ry : ℝ}
    (htx : t ∈ Metric.ball x rx) (hty : t ∈ Metric.ball y ry)
    (hx : Set.EqOn (fun s : ℝ ↦ gx (Complex.ofReal s)) f (Metric.ball x rx))
    (hy : Set.EqOn (fun s : ℝ ↦ gy (Complex.ofReal s)) f (Metric.ball y ry)) :
    ∃ᶠ z in 𝓝[≠] Complex.ofReal t, gx z = gy z := by
  have htx' : dist t x < rx := htx
  have hty' : dist t y < ry := hty
  let εx : ℝ := rx - dist t x
  let εy : ℝ := ry - dist t y
  let ε : ℝ := min εx εy
  have hεx_pos : 0 < εx := by
    dsimp [εx]
    linarith
  have hεy_pos : 0 < εy := by
    dsimp [εy]
    linarith
  have hε_pos : 0 < ε := lt_min hεx_pos hεy_pos
  have hreal_eq :
      ∀ᶠ s in 𝓝[≠] t, gx (Complex.ofReal s) = gy (Complex.ofReal s) := by
    -- Restrict to a small punctured real ball that stays inside both extension intervals.
    refine (inter_mem_nhdsWithin {t}ᶜ (Metric.ball_mem_nhds t hε_pos)).mono ?_
    intro s hs
    have hsx : s ∈ Metric.ball x rx := by
      rw [Metric.mem_ball] at hs ⊢
      calc
        dist s x ≤ dist s t + dist t x := dist_triangle _ _ _
        _ < ε + dist t x := add_lt_add_right hs.2 _
        _ ≤ rx := by
          have hε_le : ε ≤ εx := min_le_left _ _
          dsimp [εx] at hε_le
          linarith
    have hsy : s ∈ Metric.ball y ry := by
      rw [Metric.mem_ball] at hs ⊢
      calc
        dist s y ≤ dist s t + dist t y := dist_triangle _ _ _
        _ < ε + dist t y := add_lt_add_right hs.2 _
        _ ≤ ry := by
          have hε_le : ε ≤ εy := min_le_right _ _
          dsimp [εy] at hε_le
          linarith
    rw [hx hsx, hy hsy]
  -- Move the punctured-real frequent equality through the real embedding into `ℂ`.
  rw [← Complex.isometry_ofReal.isEmbedding.map_nhdsWithin_eq ({t}ᶜ) t, Filter.frequently_map]
  exact hreal_eq.frequently

/-- Helper for Exercise 15: the local holomorphic extensions associated to two points of the
interval agree on the overlap of their complex balls. -/
private lemma complex_ball_extensions_eqOn_inter {I : Set ℝ} (hI : Set.OrdConnected I)
    {f : ℝ → ℂ} {ρ : I → ℝ} {G : I → ℂ → ℂ}
    (hGdiff : ∀ x, DifferentiableOn ℂ (G x) (Metric.ball (Complex.ofReal x.1) (ρ x)))
    (hGeq : ∀ x, Set.EqOn (fun t : ℝ ↦ G x (Complex.ofReal t)) f (Metric.ball x.1 (ρ x)))
    (x y : I) :
    Set.EqOn (G x) (G y)
      (Metric.ball (Complex.ofReal x.1) (ρ x) ∩ Metric.ball (Complex.ofReal y.1) (ρ y)) := by
  let Ux : Set ℂ := Metric.ball (Complex.ofReal x.1) (ρ x)
  let Uy : Set ℂ := Metric.ball (Complex.ofReal y.1) (ρ y)
  by_cases hU : (Ux ∩ Uy).Nonempty
  · rcases hU with ⟨z, hz⟩
    rcases interval_overlap_contains_real_point hI x.2 y.2 hz.1 hz.2 with ⟨t, htI, htx, hty⟩
    have hAx : AnalyticOnNhd ℂ (G x) (Ux ∩ Uy) := by
      -- Restrict the analyticity of `G x` to the common overlap.
      exact ((hGdiff x).analyticOnNhd isOpen_ball).mono inter_subset_left
    have hAy : AnalyticOnNhd ℂ (G y) (Ux ∩ Uy) := by
      -- Restrict the analyticity of `G y` to the common overlap.
      exact ((hGdiff y).analyticOnNhd isOpen_ball).mono inter_subset_right
    have hOverlap : IsPreconnected (Ux ∩ Uy) := by
      -- Intersections of convex balls in `ℂ` remain preconnected.
      simpa [Ux, Uy] using
        ((convex_ball (Complex.ofReal x.1) (ρ x)).inter
          (convex_ball (Complex.ofReal y.1) (ρ y))).isPreconnected
    have hfreq :
        ∃ᶠ w in 𝓝[≠] Complex.ofReal t, G x w = G y w :=
      complex_extensions_frequently_eq_at_real_point htx hty (hGeq x) (hGeq y)
    have ht_mem : Complex.ofReal t ∈ Ux ∩ Uy := by
      exact ⟨htx, hty⟩
    -- The one-variable identity theorem upgrades equality near the real overlap point to the whole
    -- complex overlap.
    exact hAx.eqOn_of_preconnected_of_frequently_eq hAy hOverlap ht_mem hfreq
  · intro z hz
    exact False.elim (hU ⟨z, hz⟩)

/-- Helper for Exercise 15: the union of the local extension balls is connected because every ball
meets the common real core `Complex.ofReal '' I`. -/
private lemma extension_domain_is_connected {I : Set ℝ} (hI : Set.OrdConnected I)
    (hI_nonempty : I.Nonempty) {ρ : I → ℝ} (hρpos : ∀ x, 0 < ρ x) :
    IsConnected (⋃ x : I, Metric.ball (Complex.ofReal x.1) (ρ x)) := by
  let S : Set ℂ := Complex.ofReal '' I
  let U : I → Set ℂ := fun x ↦ Metric.ball (Complex.ofReal x.1) (ρ x)
  let V : I → Set ℂ := fun x ↦ S ∪ U x
  have hS_pre : IsPreconnected S := by
    -- The real core is the continuous image of the order-connected interval.
    simpa [S] using hI.isPreconnected.image Complex.ofReal Complex.continuous_ofReal.continuousOn
  have hV_pre : ∀ x, IsPreconnected (V x) := by
    intro x
    have hinter : (S ∩ U x).Nonempty := by
      refine ⟨Complex.ofReal x.1, ?_⟩
      exact ⟨⟨x.1, x.2, rfl⟩, by simpa [U] using Metric.mem_ball_self (hρpos x)⟩
    -- Each enlarged set is a union of two preconnected pieces with a common point.
    exact hS_pre.union' hinter isPreconnected_ball
  have hcommon : (⋂ x, V x).Nonempty := by
    rcases hI_nonempty with ⟨x, hx⟩
    refine ⟨Complex.ofReal x, ?_⟩
    intro y
    exact Or.inl ⟨x, hx, rfl⟩
  have hUnion_pre : IsPreconnected (⋃ x, V x) := isPreconnected_iUnion hcommon hV_pre
  have hS_subset_D : S ⊆ ⋃ x : I, U x := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa [U] using Metric.mem_ball_self (hρpos ⟨x, hx⟩)⟩
  have hUnion_eq :
      (⋃ x, V x) = ⋃ x : I, U x := by
    ext z
    constructor
    · intro hz
      rcases mem_iUnion.mp hz with ⟨x, hz⟩
      rcases hz with hz | hz
      · exact hS_subset_D hz
      · exact mem_iUnion.mpr ⟨x, hz⟩
    · intro hz
      rcases mem_iUnion.mp hz with ⟨x, hz⟩
      exact mem_iUnion.mpr ⟨x, Or.inr hz⟩
  have hD_nonempty : (⋃ x : I, U x).Nonempty := by
    rcases hI_nonempty with ⟨x, hx⟩
    refine ⟨Complex.ofReal x, mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩⟩
    simpa [U] using Metric.mem_ball_self (hρpos ⟨x, hx⟩)
  exact ⟨hD_nonempty, hUnion_eq ▸ hUnion_pre⟩

/-- Helper for Exercise 15: the function obtained by choosing any local chart on the union agrees
with each prescribed chart on that chart's own ball. -/
private lemma glued_extension_eqOn_chart
    {I : Set ℝ} {U : I → Set ℂ} {G : I → ℂ → ℂ}
    (hoverlap : ∀ x y, Set.EqOn (G x) (G y) (U x ∩ U y)) :
    let D : Set ℂ := ⋃ x : I, U x
    let g : ℂ → ℂ := fun z ↦ if hz : z ∈ D then G (Classical.choose (mem_iUnion.mp hz)) z else 0
    ∀ x : I, Set.EqOn g (G x) (U x) := by
  intro D g x z hz
  have hzD : z ∈ D := mem_iUnion.mpr ⟨x, hz⟩
  have hchosen : z ∈ U (Classical.choose (mem_iUnion.mp hzD)) :=
    Classical.choose_spec (mem_iUnion.mp hzD)
  -- At any point of `U x`, the chosen chart overlaps with `x`, so the overlap lemma identifies
  -- the chosen value with `G x`.
  rw [show g z = G (Classical.choose (mem_iUnion.mp hzD)) z by simp [g, hzD]]
  exact hoverlap _ _ ⟨hchosen, hz⟩

/-- Exercise 15: a complex-valued real-analytic function on an interval of `ℝ` extends to a
holomorphic function on a connected open subset of `ℂ` containing that interval. -/
-- Proof sketch: for each `x ∈ I`, use the real-analytic power series of `f` at `x` to obtain a
-- holomorphic function on a small complex neighborhood of `x`; uniqueness of analytic continuation
-- on overlaps along the interval lets one glue these local extensions, and the union of the local
-- neighborhoods gives the required connected open set; on an open subset of `ℂ`, holomorphicity is
-- expressed canonically by `DifferentiableOn`.
theorem real_analyticOnNhd_exists_complex_extension_on_interval
    {I : Set ℝ} {f : ℝ → ℂ} (hI : Set.OrdConnected I) (hf : AnalyticOnNhd ℝ f I) :
    ∃ D : Set ℂ, ∃ g : ℂ → ℂ,
      IsOpen D ∧ IsConnected D ∧ Complex.ofReal '' I ⊆ D ∧ DifferentiableOn ℂ g D ∧
        Set.EqOn (g ∘ Complex.ofReal) f I := by
  by_cases hI_empty : I = ∅
  · refine ⟨Set.univ, 0, isOpen_univ, isConnected_univ, ?_, ?_, ?_⟩
    · simp [hI_empty]
    · simpa [differentiableOn_univ] using
        (differentiable_const : Differentiable ℂ (fun _ : ℂ ↦ (0 : ℂ)))
  · simpa [hI_empty]
  · -- Route correction: the local chart construction is in place; the remaining work is the
    -- source-faithful gluing of those local holomorphic charts on the union of their balls.
    classical
    have hI_nonempty : I.Nonempty := Set.nonempty_iff_ne_empty.mpr hI_empty
    have hlocal :
        ∀ x : I, ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g (Metric.ball (Complex.ofReal x.1) r) ∧
            Set.EqOn (fun t : ℝ ↦ g (Complex.ofReal t)) f (Metric.ball x.1 r) := by
      intro x
      exact analyticAt_exists_complex_ball_extension (hf x.1 x.2)
    choose ρ hρpos G hGdiff hGeq using hlocal
    let U : I → Set ℂ := fun x ↦ Metric.ball (Complex.ofReal x.1) (ρ x)
    let D : Set ℂ := ⋃ x : I, U x
    have hoverlap : ∀ x y, Set.EqOn (G x) (G y) (U x ∩ U y) := by
      intro x y
      -- The identity theorem turns the overlap geometry into a genuine gluing relation.
      simpa [U] using complex_ball_extensions_eqOn_inter hI hGdiff hGeq x y
    have hD_open : IsOpen D := by
      -- The extension domain is the union of the local complex balls.
      simpa [D, U] using isOpen_iUnion (fun x : I ↦ isOpen_ball)
    have hD_connected : IsConnected D := by
      -- The common real core keeps the union of local balls connected.
      simpa [D, U] using extension_domain_is_connected hI hI_nonempty hρpos
    let g : ℂ → ℂ := fun z ↦ if hz : z ∈ D then G (Classical.choose (mem_iUnion.mp hz)) z else 0
    have hg_chart : ∀ x : I, Set.EqOn g (G x) (U x) := by
      -- On each local ball, the chosen-value definition collapses to that chart.
      simpa [D, g] using glued_extension_eqOn_chart (U := U) (G := G) hoverlap
    have hcore : Complex.ofReal '' I ⊆ D := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa [U] using Metric.mem_ball_self (hρpos ⟨x, hx⟩)⟩
    have hg_diff : DifferentiableOn ℂ g D := by
      -- Differentiability is local, so it suffices to compare `g` with one chart around each point.
      refine differentiableOn_of_locally_differentiableOn ?_
      intro z hz
      rcases mem_iUnion.mp hz with ⟨x, hzU⟩
      refine ⟨U x, isOpen_ball, hzU, ?_⟩
      exact (hGdiff x).congr_mono (fun w hw ↦ hg_chart x hw.2) inter_subset_right
    refine ⟨D, g, hD_open, hD_connected, hcore, hg_diff, ?_⟩
    intro x hx
    let ix : I := ⟨x, hx⟩
    have hxU : Complex.ofReal x ∈ U ix := by
      simpa [U] using Metric.mem_ball_self (hρpos ix)
    -- Evaluate the glued chart on the real axis using the chart centered at the same real point.
    calc
      g (Complex.ofReal x) = G ix (Complex.ofReal x) := hg_chart ix hxU
      _ = f x := by
        simpa using hGeq ix (Metric.mem_ball_self (hρpos ix))
