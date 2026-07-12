import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no `lean_leansearch` MCP tool was exposed in this runner, so the
-- statement surface is phrased directly in terms of the nearby fiber set, using mathlib's
-- canonical `analyticOrderAt` and `Set.encard` APIs rather than a local root-enumeration wrapper.

/-- Helper for Proposition 4.2: the order hypothesis gives the standard local factorization
`f z - a = (z - z₀)^k * g z` with a nonvanishing analytic unit `g`. -/
lemma extract_pow_factor_at_root
    {f : ℂ → ℂ} {z₀ a : ℂ} {k : ℕ}
    (hk : 0 < k)
    (horder : analyticOrderAt (f · - a) z₀ = k) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in nhds z₀, f z - a = (z - z₀) ^ k * g z := by
  -- A positive analytic order forces analyticity and vanishing at the center.
  have hne0 : analyticOrderAt (f · - a) z₀ ≠ 0 := by
    rw [horder]
    exact_mod_cast hk.ne'
  have han : AnalyticAt ℂ (f · - a) z₀ := (analyticOrderAt_ne_zero.1 hne0).1
  -- The order characterization immediately produces the required unit factor.
  simpa [smul_eq_mul] using (han.analyticOrderAt_eq_natCast (n := k)).1 horder

/-- Helper for Proposition 4.2: after choosing an analytic branch of a `k`th root of the unit
factor, one gets a local coordinate `h` with `f z - a = h z ^ k` near `z₀` and `deriv h z₀ ≠ 0`. -/
lemma build_local_power_coordinate
    {f : ℂ → ℂ} {z₀ a : ℂ} {k : ℕ}
    (hk : 0 < k)
    (horder : analyticOrderAt (f · - a) z₀ = k) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ h z₀ = 0 ∧ deriv h z₀ ≠ 0 ∧
      ∀ᶠ z in nhds z₀, f z - a = h z ^ k := by
  classical
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := extract_pow_factor_at_root hk horder
  let σ : ℂ := if g z₀ ∈ Complex.slitPlane then 1 else -1
  have hσ_ne : σ ≠ 0 := by
    by_cases hslit : g z₀ ∈ Complex.slitPlane
    · simp [σ, hslit]
    · simp [σ, hslit]
  have hσ_slit : σ * g z₀ ∈ Complex.slitPlane := by
    by_cases hslit : g z₀ ∈ Complex.slitPlane
    · simpa [σ, hslit] using hslit
    · have hgslit : -g z₀ ∈ Complex.slitPlane := by
        exact (Complex.mem_slitPlane_or_neg_mem_slitPlane hg_ne).resolve_left hslit
      simpa [σ, hslit, neg_mul] using hgslit
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (σ⁻¹) hk
  let r : ℂ → ℂ := fun z ↦ (σ * g z) ^ ((k : ℂ)⁻¹)
  have hr_an : AnalyticAt ℂ r z₀ := by
    -- The chosen sign puts the unit factor in the slit plane, so `cpow` gives a local analytic root.
    have hsg_an : AnalyticAt ℂ ((σ : ℂ) • g) z₀ := hg_an.const_smul
    have hsg_an' : AnalyticAt ℂ (fun z ↦ σ * g z) z₀ := by
      simpa [smul_eq_mul]
        using hsg_an
    simpa [r] using hsg_an'.cpow analyticAt_const hσ_slit
  let h : ℂ → ℂ := fun z ↦ (z - z₀) * (c * r z)
  have hh_an : AnalyticAt ℂ h z₀ := by
    -- The coordinate is the centered variable times the analytic root of the unit factor.
    dsimp [h]
    fun_prop
  have hh_zero : h z₀ = 0 := by
    simp [h]
  have hrz0_ne : r z₀ ≠ 0 := by
    have hbase_ne : σ * g z₀ ≠ 0 := mul_ne_zero hσ_ne hg_ne
    intro hr0
    have : σ * g z₀ = 0 := by
      calc
        σ * g z₀ = (r z₀) ^ k := by
          symm
          simp [r, hk.ne']
        _ = 0 := by simp [hr0, hk.ne']
    exact hbase_ne this
  have hc_ne : c ≠ 0 := by
    have hpow_ne : c ^ k ≠ 0 := by
      simpa [hc] using inv_ne_zero hσ_ne
    intro hc0
    exact hpow_ne (by simp [hc0, hk.ne'])
  have hh_deriv : deriv h z₀ ≠ 0 := by
    -- The linear term of `h` at `z₀` is exactly `c * r z₀`.
    have hsub : HasDerivAt (fun z : ℂ ↦ z - z₀) 1 z₀ := by
      simpa using (hasDerivAt_id z₀).sub_const z₀
    have hcr : HasDerivAt (fun z : ℂ ↦ c * r z) (c * deriv r z₀) z₀ := by
      simpa using (hr_an.differentiableAt.hasDerivAt.const_mul c)
    have hh_hasDeriv :
        HasDerivAt h (1 * (c * r z₀) + (z₀ - z₀) * (c * deriv r z₀)) z₀ := by
      simpa [h] using hsub.mul hcr
    have hderiv_eq : deriv h z₀ = c * r z₀ := by
      simpa using hh_hasDeriv.deriv
    rw [hderiv_eq]
    exact mul_ne_zero hc_ne hrz0_ne
  have hh_pow : ∀ᶠ z in nhds z₀, f z - a = h z ^ k := by
    -- The chosen root branch turns the factorization into an exact `k`th-power identity.
    filter_upwards [hfg] with z hz
    have hz' : h z ^ k = f z - a := by
      calc
        h z ^ k = ((z - z₀) * (c * r z)) ^ k := by simp [h]
        _ = (z - z₀) ^ k * ((c * r z) ^ k) := by rw [mul_pow]
        _ = (z - z₀) ^ k * (c ^ k * (r z) ^ k) := by rw [mul_pow]
        _ = (z - z₀) ^ k * (σ⁻¹ * (σ * g z)) := by rw [hc]; simp [r, hk.ne']
        _ = (z - z₀) ^ k * g z := by simpa [mul_assoc, hσ_ne]
        _ = f z - a := hz.symm
    exact hz'.symm
  exact ⟨h, hh_an, hh_zero, hh_deriv, hh_pow⟩

/-- Helper for Proposition 4.2: once `b - a` is small and nonzero, the equation `w ^ k = b - a`
has exactly `k` distinct solutions in any prescribed small ball around `0`. -/
lemma small_nth_root_set_encard
    {a : ℂ} {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b : ℂ, ‖b - a‖ < δ → b ≠ a →
      {w : ℂ | w ∈ Metric.ball 0 ε ∧ w ^ k = b - a}.encard = k := by
  refine ⟨ε ^ k, by positivity, ?_⟩
  intro b hb hba
  let c : ℂ := b - a
  have hc_ne : c ≠ 0 := sub_ne_zero.mpr hba
  have hball_eq : {w : ℂ | w ∈ Metric.ball 0 ε ∧ w ^ k = c} = {w : ℂ | w ^ k = c} := by
    ext w
    constructor
    · intro hw
      exact hw.2
    · intro hw
      have hw_ball : w ∈ Metric.ball 0 ε := by
        -- A root of a sufficiently small value must itself be small.
        have hw_norm : ‖w‖ ^ k = ‖c‖ := by
          simpa [c, norm_pow] using congrArg norm hw
        have hpow_lt : ‖w‖ ^ k < ε ^ k := by
          rw [hw_norm]
          simpa [c] using hb
        have hnorm_lt : ‖w‖ < ε := by
          exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le hk.ne').mp hpow_lt
        simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt
      exact ⟨hw_ball, hw⟩
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / k)) k :=
    Complex.isPrimitiveRoot_exp k hk.ne'
  have hroot : ∃ α : ℂ, α ^ k = c := IsAlgClosed.exists_pow_nat_eq c hk
  have hcard_finset : (Polynomial.nthRootsFinset k c).card = k := by
    calc
      (Polynomial.nthRootsFinset k c).card = Multiset.card (Polynomial.nthRoots k c) := by
        rw [Polynomial.nthRootsFinset_def, Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hc_ne)]
      _ = k := by
        simpa [if_pos hroot] using IsPrimitiveRoot.card_nthRoots hζ c
  calc
    {w : ℂ | w ∈ Metric.ball 0 ε ∧ w ^ k = c}.encard = {w : ℂ | w ^ k = c}.encard := by
      rw [hball_eq]
    _ = ((Polynomial.nthRootsFinset k c : Finset ℂ) : Set ℂ).encard := by
      rw [Polynomial.nthRootsFinset_toSet hk c]
    _ = k := by
      rw [Set.Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet _)]
      simpa using hcard_finset

/-- Helper for Proposition 4.2: a nonzero solution of the local power-coordinate equation is a
simple root of `f - b`. -/
lemma simple_of_power_coordinate_solution
    {f h : ℂ → ℂ} {z a b : ℂ} {k : ℕ}
    (hk : 0 < k)
    (hf : AnalyticAt ℂ f z)
    (hh : AnalyticAt ℂ h z)
    (heq : ∀ᶠ w in nhds z, f w - a = h w ^ k)
    (hfb : f z = b)
    (hba : b ≠ a)
    (hderivh : deriv h z ≠ 0) :
    analyticOrderAt (f · - b) z = 1 := by
  -- Evaluating the local identity at the point shows that the power-coordinate value is nonzero.
  have hzpow : h z ^ k = b - a := by
    have hself : f z - a = h z ^ k := heq.self_of_nhds
    rw [hfb] at hself
    exact hself.symm
  have hz_ne : h z ≠ 0 := by
    intro hz0
    have hpow_ne : h z ^ k ≠ 0 := by
      simpa [hzpow] using sub_ne_zero.mpr hba
    exact hpow_ne (by simp [hz0, hk.ne'])
  have hf_deriv_ne : deriv f z ≠ 0 := by
    -- Differentiating the power-coordinate identity gives the derivative of `f`.
    have hderiv_eq : deriv f z = (k : ℂ) * h z ^ (k - 1) * deriv h z := by
      calc
        deriv f z = deriv (fun w ↦ f w - a) z := by simp
        _ = deriv (fun w ↦ h w ^ k) z := by rw [Filter.EventuallyEq.deriv_eq heq]
        _ = (k : ℂ) * h z ^ (k - 1) * deriv h z := by
          simpa using deriv_pow hh.differentiableAt k
    rw [hderiv_eq]
    exact mul_ne_zero
      (mul_ne_zero (Nat.cast_ne_zero.mpr hk.ne') (pow_ne_zero _ hz_ne))
      hderivh
  -- A nonvanishing derivative characterizes a simple zero.
  simpa [hfb] using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf_deriv_ne

/-- Helper for Proposition 4.2: a predicate holding on a whole metric ball holds eventually near
each point of that ball. -/
lemma eventually_eq_of_forall_mem_ball
    {α : Type*} [PseudoMetricSpace α] {P : α → Prop} {x y : α} {r : ℝ}
    (hx : x ∈ Metric.ball y r)
    (hP : ∀ z ∈ Metric.ball y r, P z) :
    ∀ᶠ z in nhds x, P z := by
  -- The ambient ball is itself a neighborhood of each of its points.
  exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) fun z hz ↦ hP z hz

/-- Helper for Proposition 4.2: shrink the local inverse and power-coordinate identities to explicit
balls around `z₀` and `0`. -/
lemma shrink_to_local_inverse_ball
    {f h L : ℂ → ℂ} {z₀ a : ℂ} {k : ℕ}
    (hh_pow : ∀ᶠ z in nhds z₀, f z - a = h z ^ k)
    (hleft : ∀ᶠ z in nhds z₀, L (h z) = z)
    (hderiv_ev : ∀ᶠ z in nhds z₀, deriv h z ≠ 0)
    (hh_an_ev : ∀ᶠ z in nhds z₀, AnalyticAt ℂ h z)
    (hLt : Filter.Tendsto L (nhds 0) (nhds z₀))
    (hright : ∀ᶠ w in nhds 0, h (L w) = w) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ ε > 0,
        (∀ z ∈ Metric.ball z₀ r, f z - a = h z ^ k) ∧
        (∀ z ∈ Metric.ball z₀ r, L (h z) = z) ∧
        (∀ z ∈ Metric.ball z₀ r, deriv h z ≠ 0) ∧
        (∀ z ∈ Metric.ball z₀ r, AnalyticAt ℂ h z) ∧
        (∀ w ∈ Metric.ball 0 ε, L w ∈ Metric.ball z₀ r) ∧
        (∀ w ∈ Metric.ball 0 ε, h (L w) = w) := by
  -- Intersect all `z₀`-side eventual facts once and extract a single working radius.
  have hzpack :
      ∀ᶠ z in nhds z₀,
        f z - a = h z ^ k ∧
          L (h z) = z ∧
            deriv h z ≠ 0 ∧
              AnalyticAt ℂ h z := by
    filter_upwards [hh_pow, hleft, hderiv_ev, hh_an_ev] with z hzpow hzleft hzderiv hzan
    exact ⟨hzpow, hzleft, hzderiv, hzan⟩
  rcases Metric.eventually_nhds_iff_ball.mp hzpack with ⟨r₀, hr₀pos, hzball⟩
  refine ⟨r₀, hr₀pos, ?_⟩
  intro r hrpos hrr₀
  -- For the chosen `r`, use the inverse map's continuity and right-inverse identity near `0`.
  have hwpack : ∀ᶠ w in nhds (0 : ℂ), L w ∈ Metric.ball z₀ r ∧ h (L w) = w := by
    have hLball : ∀ᶠ w in nhds (0 : ℂ), L w ∈ Metric.ball z₀ r := by
      exact hLt (Metric.ball_mem_nhds z₀ hrpos)
    exact hLball.and hright
  rcases Metric.eventually_nhds_iff_ball.mp hwpack with ⟨ε, hεpos, hεball⟩
  refine ⟨ε, hεpos, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hzball z (lt_of_lt_of_le hz hrr₀)).1
  · intro z hz
    exact (hzball z (lt_of_lt_of_le hz hrr₀)).2.1
  · intro z hz
    exact (hzball z (lt_of_lt_of_le hz hrr₀)).2.2.1
  · intro z hz
    exact (hzball z (lt_of_lt_of_le hz hrr₀)).2.2.2
  · intro w hw
    exact (hεball w hw).1
  · intro w hw
    exact (hεball w hw).2

/-- Helper for Proposition 4.2: on sufficiently small balls, the fiber of `f` over `b` is in
bijection with the fiber of `w ↦ w ^ k` over `b - a`. -/
lemma fiber_model_bijOn
    {f h L : ℂ → ℂ} {z₀ a b : ℂ} {k : ℕ} {r ε : ℝ}
    (hk : 0 < k)
    (hpow_ball : ∀ z ∈ Metric.ball z₀ r, f z - a = h z ^ k)
    (hleft_ball : ∀ z ∈ Metric.ball z₀ r, L (h z) = z)
    (hL_ball : ∀ w ∈ Metric.ball 0 ε, L w ∈ Metric.ball z₀ r)
    (hright_ball : ∀ w ∈ Metric.ball 0 ε, h (L w) = w)
    (hε : 0 < ε)
    (hb : ‖b - a‖ < ε ^ k) :
    Set.BijOn h
      {z | z ∈ Metric.ball z₀ r ∧ f z = b}
      {w | w ∈ Metric.ball 0 ε ∧ w ^ k = b - a} := by
  -- The local inverse data gives the bijection once the forward image is shown to stay in the ball.
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro z hz
    have hzpow : h z ^ k = b - a := by
      rw [← hpow_ball z hz.1, hz.2]
    have hpow_norm : ‖h z‖ ^ k = ‖b - a‖ := by
      simpa [norm_pow] using congrArg norm hzpow
    have hhz_ball : h z ∈ Metric.ball 0 ε := by
      have hlt : ‖h z‖ ^ k < ε ^ k := by
        rw [hpow_norm]
        exact hb
      have hnorm_lt : ‖h z‖ < ε := by
        exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le hk.ne').mp hlt
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt
    exact ⟨hhz_ball, hzpow⟩
  · intro z₁ hz₁ z₂ hz₂ hEq
    calc
      z₁ = L (h z₁) := (hleft_ball z₁ hz₁.1).symm
      _ = L (h z₂) := by rw [hEq]
      _ = z₂ := hleft_ball z₂ hz₂.1
  · intro w hw
    refine ⟨L w, ?_, ?_⟩
    · refine ⟨hL_ball w hw.1, ?_⟩
      have hsub : f (L w) - a = b - a := by
        calc
          f (L w) - a = h (L w) ^ k := hpow_ball (L w) (hL_ball w hw.1)
          _ = w ^ k := by rw [hright_ball w hw.1]
          _ = b - a := hw.2
      have hEq := congrArg (fun u : ℂ ↦ u + a) hsub
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq
    · exact hright_ball w hw.1

/-- Proposition 4.2: if `z₀` is a zero of order `k` of `f - a`, then every sufficiently small ball
centered at `z₀` contains exactly `k` solutions of `f z = b` for every sufficiently near value
`b ≠ a`, and each of those solutions is simple. -/
theorem nearby_level_set_has_k_simple_roots
    {f : ℂ → ℂ} {z₀ a : ℂ} {k : ℕ}
    (hk : 0 < k)
    (horder : analyticOrderAt (f · - a) z₀ = k) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ δ > 0, ∀ b : ℂ, ‖b - a‖ < δ → b ≠ a →
        {z | z ∈ Metric.ball z₀ r ∧ f z = b}.encard = k ∧
          ∀ z ∈ Metric.ball z₀ r, f z = b →
            analyticOrderAt (f · - b) z = 1 := by
  -- Route correction: first construct the local power coordinate promised by the source proof.
  -- The remaining work is to shrink to a ball where the local inverse and the model root count
  -- match the fiber of `f`.
  obtain ⟨h, hh_an, hh_zero, hh_deriv, hh_pow⟩ := build_local_power_coordinate hk horder
  let L : ℂ → ℂ := hh_an.hasStrictDerivAt.localInverse h (deriv h z₀) z₀ hh_deriv
  have hleft : ∀ᶠ z in nhds z₀, L (h z) = z := by
    simpa [L] using HasStrictDerivAt.eventually_left_inverse (f := h) (f' := deriv h z₀)
      (a := z₀) hh_an.hasStrictDerivAt hh_deriv
  have hright : ∀ᶠ w in nhds 0, h (L w) = w := by
    simpa [L, hh_zero] using HasStrictDerivAt.eventually_right_inverse (f := h)
      (f' := deriv h z₀) (a := z₀) hh_an.hasStrictDerivAt hh_deriv
  have hLstrict : HasStrictDerivAt L (deriv h z₀)⁻¹ (h z₀) := by
    -- The inverse function theorem gives differentiability, hence continuity, of the local inverse.
    simpa [L] using (HasStrictDerivAt.to_localInverse
      (f := h) (f' := deriv h z₀) (a := z₀) (hf := hh_an.hasStrictDerivAt) (hf' := hh_deriv))
  have hL_zero : L 0 = z₀ := by
    -- Evaluating the left-inverse identity at the center identifies the inverse base point.
    simpa [hh_zero] using hleft.self_of_nhds
  have hLt : Filter.Tendsto L (nhds 0) (nhds z₀) := by
    -- Recenter the local inverse continuity at `0 = h z₀`.
    simpa [hh_zero, hL_zero] using hLstrict.hasDerivAt.continuousAt.tendsto
  have hderiv_ev : ∀ᶠ z in nhds z₀, deriv h z ≠ 0 := by
    -- Analyticity keeps the derivative away from `0` on a punctured neighborhood of the center.
    exact (hh_an.deriv.continuousAt.eventually_ne hh_deriv)
  have hh_an_ev : ∀ᶠ z in nhds z₀, AnalyticAt ℂ h z := hh_an.eventually_analyticAt
  obtain ⟨r₀, hr₀pos, hr₀⟩ :=
    shrink_to_local_inverse_ball hh_pow hleft hderiv_ev hh_an_ev hLt hright
  refine ⟨r₀, hr₀pos, ?_⟩
  intro r hrpos hrr₀
  obtain ⟨ε, hεpos, hpow_ball, hleft_ball, hderiv_ball, hh_an_ball, hL_ball, hright_ball⟩ :=
    hr₀ r hrpos hrr₀
  obtain ⟨δcount, hδcount_pos, hcount⟩ :=
    small_nth_root_set_encard (a := a) (k := k) hk hεpos
  let δ : ℝ := min δcount (ε ^ k)
  refine ⟨δ, by
    dsimp [δ]
    exact lt_min hδcount_pos (by positivity), ?_⟩
  intro b hb hba
  have hb_count : ‖b - a‖ < δcount := lt_of_lt_of_le hb (min_le_left _ _)
  have hb_model : ‖b - a‖ < ε ^ k := lt_of_lt_of_le hb (min_le_right _ _)
  have hbij :=
    fiber_model_bijOn hk hpow_ball hleft_ball hL_ball hright_ball hεpos hb_model
  have hmodel_count :
      {w : ℂ | w ∈ Metric.ball 0 ε ∧ w ^ k = b - a}.encard = k :=
    hcount b hb_count hba
  refine ⟨?_, ?_⟩
  · -- Transport the exact model count back through the local coordinate bijection.
    calc
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ f z = b}.encard
          = {w : ℂ | w ∈ Metric.ball 0 ε ∧ w ^ k = b - a}.encard := by
              exact Set.encard_congr (Set.BijOn.equiv h hbij)
      _ = k := hmodel_count
  · intro z hz hfb
    have hhz : AnalyticAt ℂ h z := hh_an_ball z hz
    have heqz : ∀ᶠ w in nhds z, f w - a = h w ^ k :=
      eventually_eq_of_forall_mem_ball hz hpow_ball
    have hf_model : AnalyticAt ℂ (fun w ↦ h w ^ k + a) z := by
      exact (hhz.pow k).add analyticAt_const
    have hfz : AnalyticAt ℂ f z := by
      -- On the chosen ball, `f` agrees with the analytic model `h^k + a`.
      have hEq : (fun w ↦ h w ^ k + a) =ᶠ[nhds z] f := by
        filter_upwards [heqz] with w hw
        exact (eq_add_of_sub_eq hw).symm
      exact hf_model.congr hEq
    exact simple_of_power_coordinate_solution hk hfz hhz heqz hfb hba (hderiv_ball z hz)
