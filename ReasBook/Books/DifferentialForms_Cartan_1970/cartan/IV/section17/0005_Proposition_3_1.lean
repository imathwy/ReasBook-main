import DifferentialForms_Cartan_1970.IV.section17.«0003_Proposition_2_1»
import DifferentialForms_Cartan_1970.I.section02.«0015_Proposition_I_2_extra_8»
import DifferentialForms_Cartan_1970.IV.section13.«0005_Proposition_2_2»
import DifferentialForms_Cartan_1970.IV.section13.«0006_Lemma_IV_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

-- Domain sampling: Proposition 3.1 is the immediate bidisc sequel to Proposition 2.1, so its
-- main hypothesis should reuse the same owner abstraction `DifferentiableOn ℂ` on `bidisc ρ₁ ρ₂`
-- rather than restating a separate continuity-plus-slices package.

/-- Helper for Proposition 3.1: each scalar Cauchy-kernel coefficient is a fixed inverse times
the corresponding geometric term. -/
lemma cauchy_kernel_term_eq_inv_mul_geometric (z ζ : ℂ) (n : ℕ) :
    z ^ n / ζ ^ (n + 1) = ζ⁻¹ * (z / ζ) ^ n := by
  -- Rewrite both sides as powers of `ζ⁻¹`; this is the scalar algebra behind formula `(3.2)`.
  calc
    z ^ n / ζ ^ (n + 1) = z ^ n * (ζ⁻¹) ^ (n + 1) := by
      simp [div_eq_mul_inv, inv_pow]
    _ = z ^ n * ((ζ⁻¹) ^ n * ζ⁻¹) := by
      rw [pow_succ']
      ac_rfl
    _ = ζ⁻¹ * (z / ζ) ^ n := by
      rw [div_eq_mul_inv, mul_pow]
      ac_rfl

/-- Helper for Proposition 3.1: on a smaller one-variable disc, the scalar Cauchy kernel has the
expected geometric-series expansion. -/
lemma geometric_cauchy_kernel_tsum_of_norm_lt {z ζ : ℂ} (h : ‖z‖ < ‖ζ‖) :
    Summable (fun n : ℕ ↦ z ^ n / ζ ^ (n + 1)) ∧
      (∑' n : ℕ, z ^ n / ζ ^ (n + 1)) = (ζ - z)⁻¹ := by
  have hζ_norm_pos : 0 < ‖ζ‖ := lt_of_le_of_lt (norm_nonneg z) h
  have hζ : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζ_norm_pos)
  have hsub : ζ - z ≠ 0 := sub_ne_zero.mpr <| by
    intro hEq
    apply (ne_of_gt h)
    simp [hEq]
  have hratio : ‖z / ζ‖ < 1 := by
    simpa [norm_div] using (div_lt_one hζ_norm_pos).2 h
  have hgeom :
      HasSum (fun n : ℕ ↦ ζ⁻¹ * (z / ζ) ^ n) (ζ⁻¹ * (1 - z / ζ)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hratio).mul_left (ζ⁻¹)
  have hclosed_form : ζ⁻¹ * (1 - z / ζ)⁻¹ = (ζ - z)⁻¹ := by
    field_simp [hζ, hsub, div_eq_mul_inv]
  have hsum :
      HasSum (fun n : ℕ ↦ z ^ n / ζ ^ (n + 1)) (ζ⁻¹ * (1 - z / ζ)⁻¹) := by
    -- Transport the geometric series back to the Cauchy-kernel coefficients.
    convert hgeom using 1
    · ext n
      exact cauchy_kernel_term_eq_inv_mul_geometric z ζ n
  refine ⟨hsum.summable, ?_⟩
  calc
    (∑' n : ℕ, z ^ n / ζ ^ (n + 1)) = ζ⁻¹ * (1 - z / ζ)⁻¹ := hsum.tsum_eq
    _ = (ζ - z)⁻¹ := hclosed_form

/-- Helper for Proposition 3.1: the norms of the scalar Cauchy-kernel coefficients are summable on
every smaller disc. This is the absolute-convergence input for the double series. -/
lemma summable_norm_geometric_cauchy_kernel_of_norm_lt {z ζ : ℂ} (h : ‖z‖ < ‖ζ‖) :
    Summable (fun n : ℕ ↦ ‖z ^ n / ζ ^ (n + 1)‖) := by
  have hζ_norm_pos : 0 < ‖ζ‖ := lt_of_le_of_lt (norm_nonneg z) h
  have hratio : ‖z / ζ‖ < 1 := by
    simpa [norm_div] using (div_lt_one hζ_norm_pos).2 h
  -- Compare the norm series to the geometric series for `‖z / ζ‖`.
  convert (summable_geometric_of_lt_one (norm_nonneg (z / ζ)) hratio).mul_left ‖ζ⁻¹‖ using 1
  ext n
  rw [cauchy_kernel_term_eq_inv_mul_geometric, norm_mul, norm_pow]

/-- Helper for Proposition 3.1: the `(p,q)` term in the bidisc Cauchy-kernel expansion `(3.2)`. -/
noncomputable def bidisc_cauchy_kernel_term (z₁ z₂ ζ₁ ζ₂ : ℂ) : ℕ × ℕ → ℂ :=
  fun n ↦ z₁ ^ n.1 * z₂ ^ n.2 / (ζ₁ ^ (n.1 + 1) * ζ₂ ^ (n.2 + 1))

/-- Helper for Proposition 3.1: the paired bidisc kernel term is the product of the two scalar
geometric-kernel coefficients. -/
lemma bidisc_cauchy_kernel_term_eq_prod (z₁ z₂ ζ₁ ζ₂ : ℂ) (n : ℕ × ℕ) :
    bidisc_cauchy_kernel_term z₁ z₂ ζ₁ ζ₂ n =
      (z₁ ^ n.1 / ζ₁ ^ (n.1 + 1)) * (z₂ ^ n.2 / ζ₂ ^ (n.2 + 1)) := by
  -- Separate the denominator so the double series becomes a product of scalar series.
  simp [bidisc_cauchy_kernel_term, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 3.1: absolutely summable scalar coefficient families multiply to the
expected double `tsum` indexed by `ℕ × ℕ`. -/
lemma tsum_prod_mk_of_summable_norm {f g : ℕ → ℂ}
    (hf : Summable (fun p : ℕ ↦ ‖f p‖)) (hg : Summable (fun q : ℕ ↦ ‖g q‖)) :
    (∑' n : ℕ × ℕ, f n.1 * g n.2) = (∑' p : ℕ, f p) * (∑' q : ℕ, g q) := by
  -- This is the standard absolutely convergent product formula, rewritten in the target order.
  symm
  exact tsum_mul_tsum_of_summable_norm hf hg

/-- Helper for Proposition 3.1: the bidisc Cauchy kernel factors as the product of the two scalar
geometric kernels, giving the pointwise form of textbook formula `(3.2)`. -/
lemma bidisc_cauchy_kernel_tsum_of_norm_lt
    {z₁ z₂ ζ₁ ζ₂ : ℂ} (h₁ : ‖z₁‖ < ‖ζ₁‖) (h₂ : ‖z₂‖ < ‖ζ₂‖) :
    Summable (bidisc_cauchy_kernel_term z₁ z₂ ζ₁ ζ₂) ∧
      (∑' n : ℕ × ℕ, bidisc_cauchy_kernel_term z₁ z₂ ζ₁ ζ₂ n) =
        ((ζ₁ - z₁) * (ζ₂ - z₂))⁻¹ := by
  let f₁ : ℕ → ℂ := fun p ↦ z₁ ^ p / ζ₁ ^ (p + 1)
  let f₂ : ℕ → ℂ := fun q ↦ z₂ ^ q / ζ₂ ^ (q + 1)
  have htsum₁ : (∑' p : ℕ, f₁ p) = (ζ₁ - z₁)⁻¹ := by
    simpa [f₁] using (geometric_cauchy_kernel_tsum_of_norm_lt h₁).2
  have htsum₂ : (∑' q : ℕ, f₂ q) = (ζ₂ - z₂)⁻¹ := by
    simpa [f₂] using (geometric_cauchy_kernel_tsum_of_norm_lt h₂).2
  have hnorm₁ : Summable (fun p : ℕ ↦ ‖f₁ p‖) := by
    simpa [f₁] using summable_norm_geometric_cauchy_kernel_of_norm_lt h₁
  have hnorm₂ : Summable (fun q : ℕ ↦ ‖f₂ q‖) := by
    simpa [f₂] using summable_norm_geometric_cauchy_kernel_of_norm_lt h₂
  have hfactor :
      bidisc_cauchy_kernel_term z₁ z₂ ζ₁ ζ₂ =
        (fun n : ℕ × ℕ ↦ f₁ n.1 * f₂ n.2) := by
    funext n
    simp [f₁, f₂, bidisc_cauchy_kernel_term_eq_prod]
  have hprod_summable : Summable (fun n : ℕ × ℕ ↦ f₁ n.1 * f₂ n.2) :=
    summable_mul_of_summable_norm hnorm₁ hnorm₂
  constructor
  · -- The pointwise factorization turns bidisc summability into the product summability.
    rw [hfactor]
    exact hprod_summable
  · -- Evaluate the double `tsum` by the scalar Cauchy-kernel sums in each variable.
    calc
      (∑' n : ℕ × ℕ, bidisc_cauchy_kernel_term z₁ z₂ ζ₁ ζ₂ n)
          = ∑' n : ℕ × ℕ, f₁ n.1 * f₂ n.2 := by rw [hfactor]
      _ = (∑' p : ℕ, f₁ p) * (∑' q : ℕ, f₂ q) := by
            exact tsum_prod_mk_of_summable_norm hnorm₁ hnorm₂
      _ = (ζ₁ - z₁)⁻¹ * (ζ₂ - z₂)⁻¹ := by rw [htsum₁, htsum₂]
      _ = ((ζ₁ - z₁) * (ζ₂ - z₂))⁻¹ := by
            rw [mul_inv_rev]
            ac_rfl

/-- Helper for Proposition 3.1: uniform convergence of a Nat-indexed family on a circle allows
termwise circle integration. This is the one-variable exchange step used twice in the source proof
when commuting the `q`-sum through the inner integral and the `p`-sum through the outer integral. -/
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere
    {ι : Type*} [Countable ι] {F : ι → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ i, ContinuousOn (F i) (Metric.sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (Metric.sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' i : ι, F i z) = ∑' i : ι, ∮ z in C(0, (R : ℝ)), F i z := by
  classical
  have hhas :
      HasSumUniformlyOn F (fun z ↦ ∑' i : ι, F i z) (Metric.sphere (0 : ℂ) (R : ℝ)) :=
    hsum.hasSumUniformlyOn
  have hcont_partial :
      ∀ s : Finset ι,
        ContinuousOn (fun z : ℂ ↦ ∑ i ∈ s, F i z) (Metric.sphere (0 : ℂ) (R : ℝ)) := by
    -- Finite partial sums preserve continuity on the boundary circle.
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
    · intro i s hi hs
      simpa [Finset.sum_insert, hi] using (hcont i).add hs
  have htendsto :
      Filter.Tendsto (fun s : Finset ι ↦ ∮ z in C(0, (R : ℝ)), ∑ i ∈ s, F i z) Filter.atTop
        (𝓝 (∮ z in C(0, (R : ℝ)), ∑' i : ι, F i z)) :=
    hhas.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn R.2
      (Filter.Eventually.of_forall hcont_partial)
  have hsum_int :
      HasSum (fun i : ι ↦ ∮ z in C(0, (R : ℝ)), F i z)
        (∮ z in C(0, (R : ℝ)), ∑' i : ι, F i z) := by
    rw [HasSum]
    convert htendsto using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun i _ ↦ (hcont i).circleIntegrable R.2
  exact hsum_int.tsum_eq.symm

/-- Helper for Proposition 3.1: uniform convergence of a Nat-indexed family on a circle allows
termwise circle integration. This is the one-variable exchange step used twice in the source proof
when commuting the `q`-sum through the inner integral and the `p`-sum through the outer integral. -/
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere_nat
    {F : ℕ → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ n, ContinuousOn (F n) (Metric.sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (Metric.sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' n : ℕ, F n z) = ∑' n : ℕ, ∮ z in C(0, (R : ℝ)), F n z := by
  exact circleIntegral_tsum_of_summableUniformlyOn_sphere hcont hsum

/-- Helper for Proposition 3.1: the double Cauchy integral formula `(3.3)` attached to an
admissible pair of radii. -/
noncomputable def bidisc_cauchy_coefficient
    (f : ℂ × ℂ → ℂ) (R₁ R₂ : ℝ) (p q : ℕ) : ℂ :=
  (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
    ∮ ζ₁ in C(0, R₁), ∮ ζ₂ in C(0, R₂),
      f (ζ₁, ζ₂) / (ζ₁ ^ (p + 1) * ζ₂ ^ (q + 1)))

/-- Helper for Proposition 3.1: the bidisc Cauchy coefficient is an outer normalized circle
integral of the inner normalized circle integrals. -/
lemma bidisc_cauchy_coefficient_eq_iterated_normalized
    (f : ℂ × ℂ → ℂ) (R₁ R₂ : ℝ) (p q : ℕ) :
    bidisc_cauchy_coefficient f R₁ R₂ p q =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ₁ in C(0, R₁),
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ₂ in C(0, R₂), f (ζ₁, ζ₂) / (ζ₁ ^ (p + 1) * ζ₂ ^ (q + 1))) := by
  -- Pull one copy of `(2π i)⁻¹` through the outer circle integral so the coefficient becomes
  -- two successive normalized one-variable Cauchy transforms.
  simp only [bidisc_cauchy_coefficient, pow_two, smul_eq_mul]
  rw [circleIntegral.integral_const_mul]
  ring_nf

/-- Helper for Proposition 3.1: each concrete double-series term is bounded by its normal-majorant
term. -/
lemma norm_double_power_series_term_le_normal_majorant
    (a : ℕ → ℕ → ℂ) (n : ℕ × ℕ) (z₁ z₂ : ℂ) :
    ‖a n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2‖ ≤
      ‖a n.1 n.2‖ * ‖z₁‖ ^ n.1 * ‖z₂‖ ^ n.2 := by
  -- Expand the norm of the product and rewrite the powers by their scalar norms.
  rw [norm_mul, norm_mul, norm_pow, norm_pow]

/-- Helper for Proposition 3.1: summability of the normal majorant implies summability of the
double power series itself at the same point. -/
lemma summable_double_power_series_of_summable_normal_majorant
    {a : ℕ → ℕ → ℂ} {z₁ z₂ : ℂ}
    (h :
      Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * ‖z₁‖ ^ n.1 * ‖z₂‖ ^ n.2)) :
    Summable (fun n : ℕ × ℕ ↦ a n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2) := by
  -- The usual comparison test upgrades the norm-majorant summability to the complex series.
  refine Summable.of_norm_bounded h ?_
  intro n
  exact norm_double_power_series_term_le_normal_majorant a n z₁ z₂

/-- Helper for Proposition 3.1: if a scalar function agrees on a disc with the convergent scalar
owner series `∑ a n z^n`, then it has the corresponding power-series expansion at `0`. -/
lemma hasFPowerSeriesAtZeroOfEqTsumOnBall
    {g : ℂ → ℂ} {a : ℕ → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hs : Summable (fun n : ℕ ↦ ‖a n‖ * r ^ n))
    (hEq :
      Set.EqOn g (fun z : ℂ ↦ ∑' n : ℕ, a n * z ^ n) (Metric.ball (0 : ℂ) r)) :
    HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
  let rnn : NNReal := ⟨r, hr.le⟩
  have hradius : ENNReal.ofReal r ≤ p.radius := by
    -- Weighted norm summability at radius `r` gives the standard lower bound on the owner radius.
    have howner :
        Summable (fun n : ℕ ↦ ‖p n‖ * (rnn : ℝ) ^ n) := by
      simpa [p, rnn, FormalMultilinearSeries.ofScalars_norm] using hs
    simpa [rnn, ENNReal.ofReal_eq_coe_nnreal hr.le] using
      (p.le_radius_of_summable_norm (r := rnn) howner)
  have hp_radius_pos : 0 < p.radius := by
    exact lt_of_lt_of_le (by simpa using ENNReal.ofReal_pos.mpr hr) hradius
  have hseries_full :
      HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum a) p 0 p.radius := by
    -- The canonical owner series always realizes its own power series on its full convergence ball.
    simpa [p] using p.hasFPowerSeriesOnBall hp_radius_pos
  have hseries_r :
      HasFPowerSeriesOnBall
        (FormalMultilinearSeries.ofScalarsSum a) p 0 (ENNReal.ofReal r) := by
    -- Restrict the owner expansion from the full radius to the concrete real disc `r`.
    exact hseries_full.mono (by simpa using ENNReal.ofReal_pos.mpr hr) hradius
  have hEqOn :
      Set.EqOn
        (FormalMultilinearSeries.ofScalarsSum a) g
        (Metric.eball (0 : ℂ) (ENNReal.ofReal r)) := by
    -- Translate the given pointwise `tsum` identity from the real ball to the owner `eball`.
    intro z hz
    symm
    calc
      g z = ∑' n : ℕ, a n * z ^ n := hEq (by
        simpa [Metric.mem_ball, Metric.mem_eball, edist_dist, hr] using hz)
      _ = FormalMultilinearSeries.ofScalarsSum a z := by
        rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
        exact tsum_congr fun n ↦ by simp [smul_eq_mul]
  exact (hseries_r.congr hEqOn).hasFPowerSeriesAt

/-- Helper for Proposition 3.1: if the circle-integrand kernel is jointly continuous in a
parameter and the angular variable, then the resulting circle integral depends continuously on the
parameter. -/
lemma continuous_parametric_circleIntegral
    {S : Type*} [TopologicalSpace S] {c : ℂ} {R : ℝ} {K : S → ℂ → ℂ}
    (hK : Continuous fun p : S × ℝ ↦ deriv (circleMap c R) p.2 * K p.1 (circleMap c R p.2)) :
    Continuous fun x : S ↦ ∮ z in C(c, R), K x z := by
  let K' : S → ℝ → ℂ := fun x θ ↦ deriv (circleMap c R) θ * K x (circleMap c R θ)
  have hK' : Continuous (Function.uncurry K') := by
    simpa [K'] using hK
  simpa [circleIntegral, K'] using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hK' (0 : ℝ) (2 * Real.pi))

/-- Helper for Proposition 3.1: integrating a torus-continuous kernel over the second boundary
circle yields a continuous function of the first boundary variable. -/
lemma continuousOn_second_circleIntegral_of_continuousOn_torus
    {R₁ R₂ : ℝ} (hR₂ : 0 ≤ R₂) {Φ : ℂ × ℂ → ℂ}
    (hΦ :
      ContinuousOn Φ (Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂)) :
    ContinuousOn (fun ζ₁ : ℂ ↦ ∮ ζ₂ in C(0, R₂), Φ (ζ₁, ζ₂)) (Metric.sphere (0 : ℂ) R₁) := by
  rw [continuousOn_iff_continuous_restrict]
  let S : Set ℂ := Metric.sphere (0 : ℂ) R₁
  let ΦS : S → ℂ → ℂ := fun x ζ₂ ↦ Φ (x.1, ζ₂)
  have hparam :
      Continuous fun p : S × ℝ ↦
        deriv (circleMap 0 R₂) p.2 * ΦS p.1 (circleMap 0 R₂ p.2) := by
    have hfst : Continuous fun p : S × ℝ ↦ (p.1 : ℂ) :=
      continuous_subtype_val.comp continuous_fst
    have hsnd : Continuous fun p : S × ℝ ↦ circleMap 0 R₂ p.2 :=
      (continuous_circleMap 0 R₂).comp continuous_snd
    have hpair :
        Continuous fun p : S × ℝ ↦ ((p.1 : ℂ), circleMap 0 R₂ p.2) :=
      hfst.prodMk hsnd
    have hpair_mem :
        ∀ p : S × ℝ,
          ((p.1 : ℂ), circleMap 0 R₂ p.2) ∈
            Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂ := by
      intro p
      exact ⟨p.1.2, circleMap_mem_sphere (0 : ℂ) hR₂ p.2⟩
    have hcomp :
        Continuous fun p : S × ℝ ↦ Φ ((p.1 : ℂ), circleMap 0 R₂ p.2) :=
      hΦ.comp_continuous hpair hpair_mem
    have hderiv :
        Continuous fun p : S × ℝ ↦ deriv (circleMap 0 R₂) p.2 := by
      simpa [deriv_circleMap] using
        (((continuous_circleMap 0 R₂).comp continuous_snd).mul continuous_const)
    simpa [ΦS] using hderiv.mul hcomp
  simpa [S, ΦS] using continuous_parametric_circleIntegral (S := S) hparam

/-- Helper for Proposition 3.1: the inner normalized Cauchy transform in the second variable. -/
noncomputable def outerNormalizedCauchyInner
    (f : ℂ × ℂ → ℂ) (R₂ : ℝ) (z₂ : ℂ) (ζ₁ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ ζ₂ in C(0, R₂), (ζ₂ - z₂)⁻¹ * f (ζ₁, ζ₂)

/-- Helper for Proposition 3.1: the `q`-th inner term in the outer normalized Cauchy expansion. -/
noncomputable def outerNormalizedCauchyFamily
    (f : ℂ × ℂ → ℂ) (R₂ : ℝ) (z : ℂ × ℂ) (p : ℕ) (q : ℕ) (ζ₁ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ ζ₂ in C(0, R₂),
      (f (ζ₁, ζ₂) * (z.1 ^ p * z.2 ^ q)) *
        ((ζ₁ ^ (p + 1))⁻¹ * (ζ₂ ^ (q + 1))⁻¹)

/-- Helper for Proposition 3.1: the normalized outer Cauchy integral whose coefficient row is
being identified. -/
noncomputable def outerNormalizedCauchyOuterValue
    (f : ℂ × ℂ → ℂ) (R₁ R₂ : ℝ) (z : ℂ × ℂ) (p : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ ζ₁ in C(0, R₁), (z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁

/-- Helper for Proposition 3.1: the termwise-integrated outer normalized Cauchy family sum. -/
noncomputable def outerNormalizedCauchyIntegratedFamilyValue
    (f : ℂ × ℂ → ℂ) (R₁ R₂ : ℝ) (z : ℂ × ℂ) (p : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∑' q : ℕ, ∮ ζ₁ in C(0, R₁), outerNormalizedCauchyFamily f R₂ z p q ζ₁

/-- Helper for Proposition 3.1: the outer circle integral of the `q`-series before commuting the
sum and the integral. -/
noncomputable def outerNormalizedCauchyCircleIntegralTsumValue
    (f : ℂ × ℂ → ℂ) (R₁ R₂ : ℝ) (z : ℂ × ℂ) (p : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ ζ₁ in C(0, R₁), ∑' q : ℕ, outerNormalizedCauchyFamily f R₂ z p q ζ₁

/-- Helper for Proposition 3.1: the coefficient-row series attached to the bidisc Cauchy
coefficients. -/
noncomputable def outerNormalizedCauchyCoefficientRowValue
    (f : ℂ × ℂ → ℂ) (R₁ R₂ : ℝ) (z : ℂ × ℂ) (p : ℕ) : ℂ :=
  ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q

/-- Helper for Proposition 3.1: each outer normalized Cauchy family term is continuous on the
outer boundary circle. -/
lemma continuousOn_outerNormalizedCauchyFamily
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ R₁ R₂ : ℝ} {z : ℂ × ℂ}
    (hR₁_pos : 0 < R₁) (hR₁ρ₁ : R₁ < ρ₁) (hR₂_pos : 0 < R₂) (hR₂ρ₂ : R₂ < ρ₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂))
    (p q : ℕ) :
    ContinuousOn (outerNormalizedCauchyFamily f R₂ z p q) (Metric.sphere (0 : ℂ) R₁) := by
  let K : Set (ℂ × ℂ) :=
    Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂
  have hK_subset : K ⊆ bidisc ρ₁ ρ₂ := by
    intro w hw
    rcases hw with ⟨hw₁, hw₂⟩
    rw [mem_bidisc]
    constructor
    · have hw₁_norm : ‖w.1‖ = R₁ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw₁
      simpa [hw₁_norm] using hR₁ρ₁
    · have hw₂_norm : ‖w.2‖ = R₂ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw₂
      simpa [hw₂_norm] using hR₂ρ₂
  have hcontK : ContinuousOn f K := hf.continuousOn.mono hK_subset
  let Φq : ℂ × ℂ → ℂ := fun ζ ↦
    (f ζ * (z.1 ^ p * z.2 ^ q)) *
      ((ζ.1 ^ (p + 1))⁻¹ * (ζ.2 ^ (q + 1))⁻¹)
  have hΦ : ContinuousOn Φq K := by
    have hζ₁_inv :
        ContinuousOn (fun ζ : ℂ × ℂ ↦ (ζ.1 ^ (p + 1))⁻¹) K := by
      refine (continuous_fst.pow _).continuousOn.inv₀ ?_
      intro w hw
      have hw1 : w.1 ≠ 0 := by
        intro h0
        have hnorm : ‖w.1‖ = R₁ := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hw.1
        exact hR₁_pos.ne' (by simpa [h0] using hnorm.symm)
      exact pow_ne_zero _ hw1
    have hζ₂_inv :
        ContinuousOn (fun ζ : ℂ × ℂ ↦ (ζ.2 ^ (q + 1))⁻¹) K := by
      refine (continuous_snd.pow _).continuousOn.inv₀ ?_
      intro w hw
      have hw2 : w.2 ≠ 0 := by
        intro h0
        have hnorm : ‖w.2‖ = R₂ := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hw.2
        exact hR₂_pos.ne' (by simpa [h0] using hnorm.symm)
      exact pow_ne_zero _ hw2
    have hden :
        ContinuousOn (fun ζ : ℂ × ℂ ↦ (ζ.1 ^ (p + 1))⁻¹ * (ζ.2 ^ (q + 1))⁻¹) K :=
      hζ₁_inv.mul hζ₂_inv
    have hnum :
        ContinuousOn (fun ζ : ℂ × ℂ ↦ f ζ * (z.1 ^ p * z.2 ^ q)) K :=
      hcontK.mul continuousOn_const
    simpa [Φq] using hnum.mul hden
  have hplain :
      ContinuousOn
        (fun ζ₁ : ℂ ↦
          ∮ ζ₂ in C(0, R₂),
            (f (ζ₁, ζ₂) * (z.1 ^ p * z.2 ^ q)) *
              ((ζ₁ ^ (p + 1))⁻¹ * (ζ₂ ^ (q + 1))⁻¹))
        (Metric.sphere (0 : ℂ) R₁) := by
    simpa [Φq] using
      (continuousOn_second_circleIntegral_of_continuousOn_torus
        (R₁ := R₁) (R₂ := R₂) (Φ := Φq) hR₂_pos.le hΦ)
  intro ζ₁ hζ₁
  have hFdef :
      outerNormalizedCauchyFamily f R₂ z p q =
        fun ζ : ℂ ↦
          (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₂ in C(0, R₂),
              (f (ζ, ζ₂) * (z.1 ^ p * z.2 ^ q)) *
                ((ζ ^ (p + 1))⁻¹ * (ζ₂ ^ (q + 1))⁻¹) := by
    funext ζ
    simp [outerNormalizedCauchyFamily]
  rw [hFdef]
  exact (hplain.continuousWithinAt hζ₁).const_mul ((2 * Real.pi * Complex.I : ℂ)⁻¹)

/-- Helper for Proposition 3.1: the outer normalized Cauchy family is uniformly summable on the
outer boundary circle. -/
lemma summableUniformlyOn_outerNormalizedCauchyFamily
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ} {M : ℝ}
    (hR₁_pos : 0 < R₁) (hR₂_pos : 0 < R₂) (hz₂R₂ : ‖z.2‖ < R₂)
    (hM :
      ∀ w ∈ Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂, ‖f w‖ ≤ M)
    (p : ℕ) :
    SummableUniformlyOn (outerNormalizedCauchyFamily f R₂ z p) (Metric.sphere (0 : ℂ) R₁) := by
  have hF_majorant :
      Summable
        (fun q : ℕ ↦
          R₂ * (M * (‖z.1‖ ^ p / R₁ ^ (p + 1) * (‖z.2‖ ^ q / R₂ ^ (q + 1))))) := by
    have hgeom : Summable (fun q : ℕ ↦ ‖z.2‖ ^ q / R₂ ^ (q + 1)) := by
      have hratio : ‖z.2‖ < ‖(R₂ : ℂ)‖ := by
        simpa [Complex.norm_real, abs_of_pos hR₂_pos] using hz₂R₂
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR₂_pos, div_eq_mul_inv] using
        summable_norm_geometric_cauchy_kernel_of_norm_lt (z := z.2) (ζ := (R₂ : ℂ)) hratio
    simpa [mul_assoc] using
      (hgeom.mul_left (M * (‖z.1‖ ^ p / R₁ ^ (p + 1)))).mul_left R₂
  refine
    (HasSumUniformlyOn.of_norm_le_summable hF_majorant fun q ζ₁ hζ₁ ↦ ?_).summableUniformlyOn
  have hζ₁_norm : ‖ζ₁‖ = R₁ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁
  let gq : ℂ → ℂ := fun ζ₂ ↦
    (f (ζ₁, ζ₂) * (z.1 ^ p * z.2 ^ q)) *
      ((ζ₁ ^ (p + 1))⁻¹ * (ζ₂ ^ (q + 1))⁻¹)
  have hgq_bound :
      ∀ ζ₂ ∈ Metric.sphere (0 : ℂ) R₂,
        ‖gq ζ₂‖ ≤ M * (‖z.1‖ ^ p / R₁ ^ (p + 1) * (‖z.2‖ ^ q / R₂ ^ (q + 1))) := by
    intro ζ₂ hζ₂
    have hζ₂_norm : ‖ζ₂‖ = R₂ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₂
    have hw :
        ((ζ₁, ζ₂) : ℂ × ℂ) ∈ Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂ :=
      ⟨hζ₁, hζ₂⟩
    calc
      ‖gq ζ₂‖
          = ‖f (ζ₁, ζ₂)‖ * (‖z.1‖ ^ p / R₁ ^ (p + 1) * (‖z.2‖ ^ q / R₂ ^ (q + 1))) := by
              simp [gq, hζ₁_norm, hζ₂_norm, norm_pow, div_eq_mul_inv, mul_assoc,
                mul_left_comm, mul_comm]
      _ ≤ M * (‖z.1‖ ^ p / R₁ ^ (p + 1) * (‖z.2‖ ^ q / R₂ ^ (q + 1))) := by
            gcongr
            exact hM (ζ₁, ζ₂) hw
  have hbound :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR₂_pos.le hgq_bound
  simpa [outerNormalizedCauchyFamily, gq] using hbound

/-- Helper for Proposition 3.1: on the outer boundary circle, the normalized Cauchy kernel agrees
pointwise with the `q`-series of outer normalized Cauchy family terms. -/
lemma outerNormalizedCauchyTerm_eq_tsum_on_outerSphere
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ}
    (_hR₁_pos : 0 < R₁) (hR₂_pos : 0 < R₂) (hz₂R₂ : ‖z.2‖ < R₂)
    (hcontK :
      ContinuousOn f (Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂))
    (p : ℕ) :
    Set.EqOn
      (fun ζ₁ : ℂ ↦ (z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁)
      (fun ζ₁ : ℂ ↦ ∑' q : ℕ, outerNormalizedCauchyFamily f R₂ z p q ζ₁)
      (Metric.sphere (0 : ℂ) R₁) := by
  intro ζ₁ hζ₁
  have hslice_cont :
      ContinuousOn (fun ζ₂ : ℂ ↦ f (ζ₁, ζ₂)) (Metric.sphere (0 : ℂ) R₂) := by
    exact hcontK.comp
      ((continuous_const.prodMk continuous_id).continuousOn)
      (fun ζ₂ hζ₂ ↦ ⟨hζ₁, hζ₂⟩)
  have hslice_circle :
      CircleIntegrable (fun ζ₂ : ℂ ↦ f (ζ₁, ζ₂)) 0 R₂ :=
    hslice_cont.circleIntegrable hR₂_pos.le
  have hinner :
      HasSum
        (fun q : ℕ ↦
          (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₂ in C(0, R₂), (z.2 / ζ₂) ^ q * ζ₂⁻¹ * f (ζ₁, ζ₂))
        (outerNormalizedCauchyInner f R₂ z.2 ζ₁) := by
    have hsum :=
      (hasSum_two_pi_I_cauchyPowerSeries_integral
        (f := fun ζ₂ : ℂ ↦ f (ζ₁, ζ₂)) hslice_circle hz₂R₂).mul_left
          ((2 * Real.pi * Complex.I : ℂ)⁻¹)
    simpa [outerNormalizedCauchyInner, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hsum
  have hscaled :
      HasSum
        (fun q : ℕ ↦
          ((z.1 / ζ₁) ^ p * ζ₁⁻¹) *
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ₂ in C(0, R₂), (z.2 / ζ₂) ^ q * ζ₂⁻¹ * f (ζ₁, ζ₂)))
        ((z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁) :=
    hinner.mul_left ((z.1 / ζ₁) ^ p * ζ₁⁻¹)
  calc
    (z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁
        = ∑' q : ℕ,
            ((z.1 / ζ₁) ^ p * ζ₁⁻¹) *
              ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                ∮ ζ₂ in C(0, R₂), (z.2 / ζ₂) ^ q * ζ₂⁻¹ * f (ζ₁, ζ₂)) := by
                  exact hscaled.tsum_eq.symm
    _ = ∑' q : ℕ, outerNormalizedCauchyFamily f R₂ z p q ζ₁ := by
          refine tsum_congr fun q ↦ ?_
          have hkernel₁ :
              (z.1 / ζ₁) ^ p * ζ₁⁻¹ = z.1 ^ p / ζ₁ ^ (p + 1) := by
            simpa [mul_comm] using (cauchy_kernel_term_eq_inv_mul_geometric z.1 ζ₁ p).symm
          have hrow :
              ∮ ζ₂ in C(0, R₂), (z.2 / ζ₂) ^ q * ζ₂⁻¹ * f (ζ₁, ζ₂) =
                ∮ ζ₂ in C(0, R₂), f (ζ₁, ζ₂) * z.2 ^ q / ζ₂ ^ (q + 1) := by
                  apply circleIntegral.integral_congr hR₂_pos.le
                  intro ζ₂ hζ₂
                  calc
                    (z.2 / ζ₂) ^ q * ζ₂⁻¹ * f (ζ₁, ζ₂)
                        = (z.2 ^ q / ζ₂ ^ (q + 1)) * f (ζ₁, ζ₂) := by
                            rw [cauchy_kernel_term_eq_inv_mul_geometric z.2 ζ₂ q]
                            ring
                    _ = f (ζ₁, ζ₂) * z.2 ^ q / ζ₂ ^ (q + 1) := by
                          ring
          rw [hrow]
          calc
            ((z.1 / ζ₁) ^ p * ζ₁⁻¹) *
                ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                  ∮ ζ₂ in C(0, R₂), f (ζ₁, ζ₂) * z.2 ^ q / ζ₂ ^ (q + 1))
                = (((z.1 / ζ₁) ^ p * ζ₁⁻¹) * (2 * Real.pi * Complex.I : ℂ)⁻¹) *
                    ∮ ζ₂ in C(0, R₂), f (ζ₁, ζ₂) * z.2 ^ q / ζ₂ ^ (q + 1) := by
                      ring
            _
                = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
                    ((z.1 ^ p / ζ₁ ^ (p + 1)) *
                      ∮ ζ₂ in C(0, R₂), f (ζ₁, ζ₂) * z.2 ^ q / ζ₂ ^ (q + 1)) := by
                        rw [hkernel₁]
                        ring
            _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
                  ∮ ζ₂ in C(0, R₂),
                    (z.1 ^ p / ζ₁ ^ (p + 1)) * (f (ζ₁, ζ₂) * z.2 ^ q / ζ₂ ^ (q + 1)) := by
                      rw [← circleIntegral.integral_const_mul]
            _ = outerNormalizedCauchyFamily f R₂ z p q ζ₁ := by
                  simp [outerNormalizedCauchyFamily, div_eq_mul_inv, mul_assoc, mul_left_comm,
                    mul_comm]

/-- Helper for Proposition 3.1: each outer normalized Cauchy family integral is exactly the
corresponding bidisc Cauchy coefficient term. -/
lemma outerNormalizedCauchyFamily_integral_eq_coefficientTerm
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ} {p q : ℕ}
    (hR₁_pos : 0 < R₁) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₁ in C(0, R₁), outerNormalizedCauchyFamily f R₂ z p q ζ₁ =
      bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
  have hFq :
      ∮ ζ₁ in C(0, R₁), outerNormalizedCauchyFamily f R₂ z p q ζ₁ =
        ∮ ζ₁ in C(0, R₁),
          (z.1 ^ p * z.2 ^ q) *
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ₂ in C(0, R₂), f (ζ₁, ζ₂) / (ζ₁ ^ (p + 1) * ζ₂ ^ (q + 1))) := by
    apply circleIntegral.integral_congr hR₁_pos.le
    intro ζ₁ hζ₁
    simp [outerNormalizedCauchyFamily, circleIntegral.integral_const_mul, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  rw [hFq, circleIntegral.integral_const_mul, bidisc_cauchy_coefficient_eq_iterated_normalized]
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 3.1: continuity, uniform summability, and the pointwise boundary
identity together yield the outer normalized coefficient row formula. -/
lemma outerNormalizedCauchyOuterValue_eq_circleIntegralTsum
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ} (p : ℕ)
    (hR₁_pos : 0 < R₁)
    (hpoint :
      Set.EqOn
        (fun ζ₁ : ℂ ↦ (z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁)
        (fun ζ₁ : ℂ ↦ ∑' q : ℕ, outerNormalizedCauchyFamily f R₂ z p q ζ₁)
        (Metric.sphere (0 : ℂ) R₁)) :
    outerNormalizedCauchyOuterValue f R₁ R₂ z p =
      outerNormalizedCauchyCircleIntegralTsumValue f R₁ R₂ z p := by
  calc
    outerNormalizedCauchyOuterValue f R₁ R₂ z p
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₁ in C(0, R₁), (z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁ := by
              rfl
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ₁ in C(0, R₁), ∑' q : ℕ, outerNormalizedCauchyFamily f R₂ z p q ζ₁ := by
            congr 1
            apply circleIntegral.integral_congr hR₁_pos.le
            exact hpoint
    _ = outerNormalizedCauchyCircleIntegralTsumValue f R₁ R₂ z p := by rfl

/-- Helper for Proposition 3.1: commuting the outer `q`-sum through the outer circle integral
produces the integrated-family value. -/
lemma outerNormalizedCauchyCircleIntegralTsum_eq_integratedFamilyValue
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ} (p : ℕ) (hR₁_pos : 0 < R₁)
    (hF_cont :
      ∀ q, ContinuousOn (outerNormalizedCauchyFamily f R₂ z p q) (Metric.sphere (0 : ℂ) R₁))
    (hF_uniform :
      SummableUniformlyOn (outerNormalizedCauchyFamily f R₂ z p) (Metric.sphere (0 : ℂ) R₁)) :
    outerNormalizedCauchyCircleIntegralTsumValue f R₁ R₂ z p =
      outerNormalizedCauchyIntegratedFamilyValue f R₁ R₂ z p := by
  let F : ℕ → ℂ → ℂ := outerNormalizedCauchyFamily f R₂ z p
  let R : NNReal := ⟨R₁, hR₁_pos.le⟩
  have hF_cont' : ∀ q, ContinuousOn (F q) (Metric.sphere (0 : ℂ) R₁) := by
    intro q
    simpa [F] using hF_cont q
  have hF_uniform' : SummableUniformlyOn F (Metric.sphere (0 : ℂ) R₁) := by
    simpa [F] using hF_uniform
  have hswap :
      (∮ ζ₁ in C(0, R₁), ∑' q : ℕ, F q ζ₁) =
        ∑' q : ℕ, ∮ ζ₁ in C(0, R₁), F q ζ₁ :=
    circleIntegral_tsum_of_summableUniformlyOn_sphere_nat (R := R) (F := F) hF_cont' hF_uniform'
  calc
    outerNormalizedCauchyCircleIntegralTsumValue f R₁ R₂ z p
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₁ in C(0, R₁), ∑' q : ℕ, outerNormalizedCauchyFamily f R₂ z p q ζ₁ := by
              rfl
    _
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∑' q : ℕ, ∮ ζ₁ in C(0, R₁), F q ζ₁ := by
              simp [F, hswap]
    _ = outerNormalizedCauchyIntegratedFamilyValue f R₁ R₂ z p := by
          rfl

/-- Helper for Proposition 3.1: continuity, uniform summability, and the pointwise boundary
identity together yield the outer normalized coefficient row formula. -/
lemma outerNormalizedCauchyTerm_eq_integratedFamilyTsum_of_boundaryData
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ} (p : ℕ)
    (hR₁_pos : 0 < R₁) (hR₂_pos : 0 < R₂) (hz₂R₂ : ‖z.2‖ < R₂)
    (hcontK :
      ContinuousOn f (Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂))
    (hF_cont :
      ∀ q, ContinuousOn (outerNormalizedCauchyFamily f R₂ z p q) (Metric.sphere (0 : ℂ) R₁))
    (hF_uniform :
      SummableUniformlyOn (outerNormalizedCauchyFamily f R₂ z p) (Metric.sphere (0 : ℂ) R₁)) :
    outerNormalizedCauchyOuterValue f R₁ R₂ z p =
      outerNormalizedCauchyIntegratedFamilyValue f R₁ R₂ z p := by
  have hpoint :
      Set.EqOn
        (fun ζ₁ : ℂ ↦ (z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁)
        (fun ζ₁ : ℂ ↦ ∑' q : ℕ, outerNormalizedCauchyFamily f R₂ z p q ζ₁)
        (Metric.sphere (0 : ℂ) R₁) :=
    outerNormalizedCauchyTerm_eq_tsum_on_outerSphere
      (f := f) (R₁ := R₁) (R₂ := R₂) (z := z)
      hR₁_pos hR₂_pos hz₂R₂ hcontK p
  calc
    outerNormalizedCauchyOuterValue f R₁ R₂ z p
        = outerNormalizedCauchyCircleIntegralTsumValue f R₁ R₂ z p := by
              exact
                outerNormalizedCauchyOuterValue_eq_circleIntegralTsum
                  (f := f) (R₁ := R₁) (R₂ := R₂) (z := z) p hR₁_pos hpoint
    _ = outerNormalizedCauchyIntegratedFamilyValue f R₁ R₂ z p := by
          exact
            outerNormalizedCauchyCircleIntegralTsum_eq_integratedFamilyValue
              (f := f) (R₁ := R₁) (R₂ := R₂) (z := z) p hR₁_pos hF_cont hF_uniform

/-- Helper for Proposition 3.1: the termwise-integrated outer normalized family sum is exactly the
coefficient-row series. -/
lemma outerNormalizedCauchyIntegratedFamilyValue_eq_coefficientRowValue
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ} (p : ℕ) (hR₁_pos : 0 < R₁) :
    outerNormalizedCauchyIntegratedFamilyValue f R₁ R₂ z p =
      outerNormalizedCauchyCoefficientRowValue f R₁ R₂ z p := by
  calc
    outerNormalizedCauchyIntegratedFamilyValue f R₁ R₂ z p
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∑' q : ℕ, ∮ ζ₁ in C(0, R₁), outerNormalizedCauchyFamily f R₂ z p q ζ₁
          := by rfl
    _
        =
          ∑' q : ℕ,
            (2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ₁ in C(0, R₁), outerNormalizedCauchyFamily f R₂ z p q ζ₁ := by
                symm
                exact tsum_mul_left
    _ = ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
          refine tsum_congr fun q ↦ ?_
          exact
            outerNormalizedCauchyFamily_integral_eq_coefficientTerm
              (f := f) (R₁ := R₁) (R₂ := R₂) (z := z) (p := p) (q := q) hR₁_pos
    _ = outerNormalizedCauchyCoefficientRowValue f R₁ R₂ z p := by rfl

/-- Helper for Proposition 3.1: continuity, uniform summability, and the pointwise boundary
identity together yield the outer normalized coefficient row formula. -/
lemma outerNormalizedCauchyTerm_eq_bidiscCoefficientRow_of_boundaryData
    {f : ℂ × ℂ → ℂ} {R₁ R₂ : ℝ} {z : ℂ × ℂ} (p : ℕ)
    (hR₁_pos : 0 < R₁) (hR₂_pos : 0 < R₂) (hz₂R₂ : ‖z.2‖ < R₂)
    (hcontK :
      ContinuousOn f (Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂))
    (hF_cont :
      ∀ q, ContinuousOn (outerNormalizedCauchyFamily f R₂ z p q) (Metric.sphere (0 : ℂ) R₁))
    (hF_uniform :
      SummableUniformlyOn (outerNormalizedCauchyFamily f R₂ z p) (Metric.sphere (0 : ℂ) R₁)) :
    outerNormalizedCauchyOuterValue f R₁ R₂ z p =
      outerNormalizedCauchyCoefficientRowValue f R₁ R₂ z p := by
  calc
    outerNormalizedCauchyOuterValue f R₁ R₂ z p
        = outerNormalizedCauchyIntegratedFamilyValue f R₁ R₂ z p := by
            exact
              outerNormalizedCauchyTerm_eq_integratedFamilyTsum_of_boundaryData
                (f := f) (R₁ := R₁) (R₂ := R₂) (z := z) p
                hR₁_pos hR₂_pos hz₂R₂ hcontK hF_cont hF_uniform
    _ = outerNormalizedCauchyCoefficientRowValue f R₁ R₂ z p := by
          exact outerNormalizedCauchyIntegratedFamilyValue_eq_coefficientRowValue
            (f := f) (R₁ := R₁) (R₂ := R₂) (z := z) p hR₁_pos

/-- Helper for Proposition 3.1: the `p`-th normalized outer Cauchy term expands as the
corresponding inner coefficient series in `z₂`. -/
lemma outerNormalizedCauchyTerm_eq_bidiscCoefficientRow_explicit
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ R₁ R₂ : ℝ} {z : ℂ × ℂ}
    (hR₁_pos : 0 < R₁) (hR₁ρ₁ : R₁ < ρ₁) (hR₂_pos : 0 < R₂) (hR₂ρ₂ : R₂ < ρ₂)
    (_hz₁R₁ : ‖z.1‖ < R₁) (hz₂R₂ : ‖z.2‖ < R₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂))
    (p : ℕ) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₁ in C(0, R₁), (z.1 / ζ₁) ^ p * ζ₁⁻¹ * outerNormalizedCauchyInner f R₂ z.2 ζ₁ =
      ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
  let K : Set (ℂ × ℂ) :=
    Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂
  have hK_subset : K ⊆ bidisc ρ₁ ρ₂ := by
    intro w hw
    rcases hw with ⟨hw₁, hw₂⟩
    rw [mem_bidisc]
    constructor
    · have hw₁_norm : ‖w.1‖ = R₁ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw₁
      simpa [hw₁_norm] using hR₁ρ₁
    · have hw₂_norm : ‖w.2‖ = R₂ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw₂
      simpa [hw₂_norm] using hR₂ρ₂
  have hcontK : ContinuousOn f K := hf.continuousOn.mono hK_subset
  have hK_compact : IsCompact K :=
    (isCompact_sphere (0 : ℂ) R₁).prod (isCompact_sphere (0 : ℂ) R₂)
  obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn hcontK
  have hF_cont :
      ∀ q, ContinuousOn (outerNormalizedCauchyFamily f R₂ z p q) (Metric.sphere (0 : ℂ) R₁) := by
    intro q
    exact
      continuousOn_outerNormalizedCauchyFamily
        (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (R₁ := R₁) (R₂ := R₂) (z := z)
        hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂ hf p q
  have hF_uniform :
      SummableUniformlyOn (outerNormalizedCauchyFamily f R₂ z p) (Metric.sphere (0 : ℂ) R₁) := by
    exact
      summableUniformlyOn_outerNormalizedCauchyFamily
        (f := f) (R₁ := R₁) (R₂ := R₂) (z := z) (M := M)
        hR₁_pos hR₂_pos hz₂R₂ hM p
  exact
    outerNormalizedCauchyTerm_eq_bidiscCoefficientRow_of_boundaryData
      (f := f) (R₁ := R₁) (R₂ := R₂) (z := z) p
      hR₁_pos hR₂_pos hz₂R₂ hcontK hF_cont hF_uniform

/-- Helper for Proposition 3.1: this packages the explicit outer normalized row identity back into
the original `let`-bound formulation used downstream. -/
lemma outerNormalizedCauchyTerm_eq_bidiscCoefficientRow
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ R₁ R₂ : ℝ} {z : ℂ × ℂ}
    (hR₁_pos : 0 < R₁) (hR₁ρ₁ : R₁ < ρ₁) (hR₂_pos : 0 < R₂) (hR₂ρ₂ : R₂ < ρ₂)
    (hz₁R₁ : ‖z.1‖ < R₁) (hz₂R₂ : ‖z.2‖ < R₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂))
    (p : ℕ) :
    let J : ℂ → ℂ := fun ζ₁ ↦
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₂ in C(0, R₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂)
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₁ in C(0, R₁), (z.1 / ζ₁) ^ p * ζ₁⁻¹ * J ζ₁ =
      ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
  simpa [outerNormalizedCauchyInner] using
    outerNormalizedCauchyTerm_eq_bidiscCoefficientRow_explicit
      (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (R₁ := R₁) (R₂ := R₂) (z := z)
      hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂ hz₁R₁ hz₂R₂ hf p

/-- Helper for Proposition 3.1: on every smaller closed bidisc, the iterated Cauchy formula from
Proposition 2.1 expands into the nested series of Cauchy coefficients `(3.3)`. -/
lemma cauchy_local_double_series_eq_on_closed_bidisc
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ R₁ R₂ r₁ r₂ : ℝ} {z : ℂ × ℂ}
    (hR₁_pos : 0 < R₁) (hR₁ρ₁ : R₁ < ρ₁) (hR₂_pos : 0 < R₂) (hR₂ρ₂ : R₂ < ρ₂)
    (_hr₁_nonneg : 0 ≤ r₁) (hr₁R₁ : r₁ < R₁) (_hr₂_nonneg : 0 ≤ r₂) (hr₂R₂ : r₂ < R₂)
    (hz₁ : ‖z.1‖ ≤ r₁) (hz₂ : ‖z.2‖ ≤ r₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    f z = ∑' p : ℕ, ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
  let K : Set (ℂ × ℂ) :=
    Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂
  have hz₁R₁ : ‖z.1‖ < R₁ := lt_of_le_of_lt hz₁ hr₁R₁
  have hz₂R₂ : ‖z.2‖ < R₂ := lt_of_le_of_lt hz₂ hr₂R₂
  have hK_subset : K ⊆ bidisc ρ₁ ρ₂ := by
    -- Each boundary point still lies in the open bidisc because the chosen radii are admissible.
    intro w hw
    rcases hw with ⟨hw₁, hw₂⟩
    rw [mem_bidisc]
    constructor
    · have hw₁_norm : ‖w.1‖ = R₁ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw₁
      simpa [hw₁_norm] using hR₁ρ₁
    · have hw₂_norm : ‖w.2‖ = R₂ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw₂
      simpa [hw₂_norm] using hR₂ρ₂
  have hcontK : ContinuousOn f K := hf.continuousOn.mono hK_subset
  have hK_compact : IsCompact K :=
    (isCompact_sphere (0 : ℂ) R₁).prod (isCompact_sphere (0 : ℂ) R₂)
  obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn hcontK
  let J : ℂ → ℂ := fun ζ₁ ↦
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ ζ₂ in C(0, R₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂)
  have hinnerKernel_cont :
      ContinuousOn
        (fun ζ : ℂ × ℂ ↦ (ζ.2 - z.2)⁻¹ * f ζ)
        K := by
    have hker :
        ContinuousOn (fun ζ : ℂ × ℂ ↦ (ζ.2 - z.2)⁻¹) K := by
      refine (continuous_snd.sub continuous_const).continuousOn.inv₀ ?_
      intro w hw
      exact sub_ne_zero.mpr fun hEq ↦ by
        apply ne_of_gt hz₂R₂
        simpa [hEq, Metric.mem_sphere, dist_eq_norm] using hw.2.symm
    exact hker.mul hcontK
  have hJ_cont :
      ContinuousOn J (Metric.sphere (0 : ℂ) R₁) := by
    have hplain :
        ContinuousOn
          (fun ζ₁ : ℂ ↦ ∮ ζ₂ in C(0, R₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂))
          (Metric.sphere (0 : ℂ) R₁) := by
      exact continuousOn_second_circleIntegral_of_continuousOn_torus
        (R₁ := R₁) (R₂ := R₂) hR₂_pos.le hinnerKernel_cont
    intro ζ₁ hζ₁
    simpa [J] using
      (hplain.continuousWithinAt hζ₁).const_mul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  have hJ_circle : CircleIntegrable J 0 R₁ := hJ_cont.circleIntegrable hR₁_pos.le
  have hcauchy :
      f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₁ in C(0, R₁), (ζ₁ - z.1)⁻¹ * J ζ₁ := by
    calc
      f z =
          (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
            ∮ ζ₁ in C(0, R₁), ∮ ζ₂ in C(0, R₂),
              f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) := by
            exact
              cauchy_integral_formula_two_variables_on_bidisc
                (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (r₁ := R₁) (r₂ := R₂) (z := z)
                hR₁ρ₁ hR₂ρ₂ hz₁R₁ hz₂R₂ hf
      _ =
          (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
            ∮ ζ₁ in C(0, R₁),
              (ζ₁ - z.1)⁻¹ *
                ∮ ζ₂ in C(0, R₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂)) := by
            congr 1
            apply circleIntegral.integral_congr hR₁_pos.le
            intro ζ₁ hζ₁
            calc
              ∮ ζ₂ in C(0, R₂), f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))
                  = ∮ ζ₂ in C(0, R₂),
                      (ζ₁ - z.1)⁻¹ * ((ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂)) := by
                        apply circleIntegral.integral_congr hR₂_pos.le
                        intro ζ₂ hζ₂
                        simp [div_eq_mul_inv, mul_assoc, mul_comm]
              _ = (ζ₁ - z.1)⁻¹ * ∮ ζ₂ in C(0, R₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂) := by
                    rw [circleIntegral.integral_const_mul]
      _ =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₁ in C(0, R₁), (ζ₁ - z.1)⁻¹ * J ζ₁ := by
            simp_rw [J]
            have hconst :
                (∮ ζ₁ in C(0, R₁),
                  (ζ₁ - z.1)⁻¹ *
                    ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                      ∮ ζ₂ in C(0, R₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂))) =
                  ∮ ζ₁ in C(0, R₁),
                    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
                      ((ζ₁ - z.1)⁻¹ *
                        ∮ ζ₂ in C(0, R₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂)) := by
              apply circleIntegral.integral_congr hR₁_pos.le
              intro ζ₁ hζ₁
              ring
            rw [hconst, circleIntegral.integral_const_mul, pow_two]
            ring
  have houter :
      HasSum
        (fun p : ℕ ↦
          (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₁ in C(0, R₁), (z.1 / ζ₁) ^ p * ζ₁⁻¹ * J ζ₁)
        (f z) := by
    have hsum :=
      (hasSum_two_pi_I_cauchyPowerSeries_integral
        (f := J) hJ_circle hz₁R₁).mul_left ((2 * Real.pi * Complex.I : ℂ)⁻¹)
    simpa [hcauchy, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum
  have houter_term :
      ∀ p : ℕ,
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₁ in C(0, R₁), (z.1 / ζ₁) ^ p * ζ₁⁻¹ * J ζ₁ =
          ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
    intro p
    simpa [J] using
      outerNormalizedCauchyTerm_eq_bidiscCoefficientRow
        (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (R₁ := R₁) (R₂ := R₂) (z := z)
        hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂ hz₁R₁ hz₂R₂ hf p
  calc
    f z = ∑' p : ℕ,
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ₁ in C(0, R₁), (z.1 / ζ₁) ^ p * ζ₁⁻¹ * J ζ₁ := houter.tsum_eq.symm
    _ = ∑' p : ℕ, ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
          refine tsum_congr houter_term

/-- Helper for Proposition 3.1: the Cauchy coefficients satisfy the textbook weighted bound, hence
their normal majorant is summable on every smaller closed bidisc. -/
lemma cauchy_coefficients_bound_and_mem_domain
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ R₁ R₂ : ℝ}
    (hR₁_pos : 0 < R₁) (hR₁ρ₁ : R₁ < ρ₁) (hR₂_pos : 0 < R₂) (hR₂ρ₂ : R₂ < ρ₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ p q : ℕ,
        ‖bidisc_cauchy_coefficient f R₁ R₂ p q‖ * R₁ ^ p * R₂ ^ q ≤ M) ∧
      ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ < R₁ → 0 ≤ r₂ → r₂ < R₂ →
        Summable (fun n : ℕ × ℕ ↦
          ‖bidisc_cauchy_coefficient f R₁ R₂ n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2) := by
  let K : Set (ℂ × ℂ) :=
    Metric.sphere (0 : ℂ) R₁ ×ˢ Metric.sphere (0 : ℂ) R₂
  have hK_nonempty : K.Nonempty := by
    -- The boundary torus is nonempty because both radii are positive.
    have hζ₁ : (R₁ : ℂ) ∈ Metric.sphere (0 : ℂ) R₁ := by
      simp [hR₁_pos.le]
    have hζ₂ : (R₂ : ℂ) ∈ Metric.sphere (0 : ℂ) R₂ := by
      simp [hR₂_pos.le]
    exact ⟨((R₁ : ℂ), (R₂ : ℂ)), ⟨hζ₁, hζ₂⟩⟩
  have hK_subset : K ⊆ bidisc ρ₁ ρ₂ := by
    -- Each boundary point still lies in the open bidisc because the chosen radii are admissible.
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    rw [mem_bidisc]
    constructor
    · have hz₁_norm : ‖z.1‖ = R₁ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz₁
      simpa [hz₁_norm] using hR₁ρ₁
    · have hz₂_norm : ‖z.2‖ = R₂ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz₂
      simpa [hz₂_norm] using hR₂ρ₂
  have hK_compact : IsCompact K :=
    (isCompact_sphere (0 : ℂ) R₁).prod (isCompact_sphere (0 : ℂ) R₂)
  have hcontK : ContinuousOn f K := hf.continuousOn.mono hK_subset
  have hnorm_cont : ContinuousOn (fun z : ℂ × ℂ ↦ ‖f z‖) K :=
    continuous_norm.comp_continuousOn hcontK
  obtain ⟨w, hwK, hwMax⟩ := hK_compact.exists_isMaxOn hK_nonempty hnorm_cont
  let M : ℝ := ‖f w‖
  have hM_nonneg : 0 ≤ M := by
    -- The torus supremum bound is a norm, hence nonnegative.
    dsimp [M]
    exact norm_nonneg _
  have htorus_bound : ∀ z ∈ K, ‖f z‖ ≤ M := by
    -- The chosen point `w` realizes the maximum of `‖f‖` on the compact boundary torus.
    intro z hz
    simpa [M] using hwMax hz
  have hweighted_bound :
      ∀ p q : ℕ, ‖bidisc_cauchy_coefficient f R₁ R₂ p q‖ * R₁ ^ p * R₂ ^ q ≤ M := by
    intro p q
    have hcoeff_norm :
        ‖bidisc_cauchy_coefficient f R₁ R₂ p q‖ ≤
          R₁ * (R₂ * (M / (R₁ ^ (p + 1) * R₂ ^ (q + 1)))) := by
      -- Apply the normalized circle-integral bound first in `ζ₂`, then in `ζ₁`.
      rw [bidisc_cauchy_coefficient_eq_iterated_normalized]
      refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR₁_pos.le ?_
      intro ζ₁ hζ₁
      refine
        (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR₂_pos.le ?_).trans
          le_rfl
      intro ζ₂ hζ₂
      have hζ₁_norm : ‖ζ₁‖ = R₁ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁
      have hζ₂_norm : ‖ζ₂‖ = R₂ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hζ₂
      have hpoint :
          ‖f (ζ₁, ζ₂)‖ ≤ M := by
        exact htorus_bound (ζ₁, ζ₂) ⟨hζ₁, hζ₂⟩
      have hdenom_pos : 0 < R₁ ^ (p + 1) * R₂ ^ (q + 1) := by
        positivity
      -- On the boundary torus the denominator has fixed norm `R₁^(p+1) R₂^(q+1)`.
      rw [norm_div, norm_mul, norm_pow, norm_pow, hζ₁_norm, hζ₂_norm]
      exact div_le_div_of_nonneg_right hpoint hdenom_pos.le
    have hweight_nonneg : 0 ≤ R₁ ^ p * R₂ ^ q := by
      positivity
    have hscaled :=
      mul_le_mul_of_nonneg_right hcoeff_norm hweight_nonneg
    -- The two circle-radius factors cancel exactly against the denominator powers.
    calc
      ‖bidisc_cauchy_coefficient f R₁ R₂ p q‖ * R₁ ^ p * R₂ ^ q
          ≤ (R₁ * (R₂ * (M / (R₁ ^ (p + 1) * R₂ ^ (q + 1))))) * (R₁ ^ p * R₂ ^ q) := by
            simpa [mul_assoc] using hscaled
      _ = M := by
        rw [pow_succ', pow_succ', div_eq_mul_inv]
        field_simp [hR₁_pos.ne', hR₂_pos.ne']
  refine ⟨M, hM_nonneg, hweighted_bound, ?_⟩
  intro r₁ r₂ hr₁_nonneg hr₁R₁ hr₂_nonneg hr₂R₂
  have hlocus :
      (r₁, r₂) ∈
        formalSeriesConvergenceLocus (fun p q ↦ bidisc_cauchy_coefficient f R₁ R₂ p q) := by
    -- The weighted Cauchy bound gives the usual double geometric majorant on every smaller bidisc.
    exact formalSeriesConvergenceLocus_of_bounded_coefficients
      (a := fun p q ↦ bidisc_cauchy_coefficient f R₁ R₂ p q)
      hr₁_nonneg hr₂_nonneg hweighted_bound hr₁R₁ hr₂R₂
  -- Unfold the convergence locus to recover the desired summability statement.
  rw [mem_formalSeriesConvergenceLocus_iff] at hlocus
  exact hlocus.2.2

/-- Helper for Proposition 3.1: the double Cauchy coefficients do not depend on which admissible
radius pair inside the bidisc is used to compute them. -/
lemma cauchy_coefficients_eq_of_two_admissible_pairs
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ R₁ R₂ S₁ S₂ : ℝ}
    (hR₁_pos : 0 < R₁) (hR₁ρ₁ : R₁ < ρ₁) (hR₂_pos : 0 < R₂) (hR₂ρ₂ : R₂ < ρ₂)
    (hS₁_pos : 0 < S₁) (hS₁ρ₁ : S₁ < ρ₁) (hS₂_pos : 0 < S₂) (hS₂ρ₂ : S₂ < ρ₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    ∀ p q : ℕ,
      bidisc_cauchy_coefficient f R₁ R₂ p q = bidisc_cauchy_coefficient f S₁ S₂ p q := by
  let T₁ : ℝ := min R₁ S₁ / 2
  let T₂ : ℝ := min R₂ S₂ / 2
  let coeffR : ℕ → ℕ → ℂ := fun p q ↦ bidisc_cauchy_coefficient f R₁ R₂ p q
  let coeffS : ℕ → ℕ → ℂ := fun p q ↦ bidisc_cauchy_coefficient f S₁ S₂ p q
  let rowR : ℂ → ℕ → ℂ := fun z₂ p ↦ ∑' q, coeffR p q * z₂ ^ q
  let rowS : ℂ → ℕ → ℂ := fun z₂ p ↦ ∑' q, coeffS p q * z₂ ^ q
  let xMajorantR : ℕ → ℝ := fun p ↦ ∑' q, ‖coeffR p q‖ * T₂ ^ q
  let xMajorantS : ℕ → ℝ := fun p ↦ ∑' q, ‖coeffS p q‖ * T₂ ^ q
  have hT₁_pos : 0 < T₁ := by
    dsimp [T₁]
    positivity
  have hT₂_pos : 0 < T₂ := by
    dsimp [T₂]
    positivity
  have hT₁R₁ : T₁ < R₁ := by
    dsimp [T₁]
    have hhalf : min R₁ S₁ / 2 < min R₁ S₁ := by
      exact half_lt_self (lt_min hR₁_pos hS₁_pos)
    exact lt_of_lt_of_le hhalf (min_le_left _ _)
  have hT₁S₁ : T₁ < S₁ := by
    dsimp [T₁]
    have hhalf : min R₁ S₁ / 2 < min R₁ S₁ := by
      exact half_lt_self (lt_min hR₁_pos hS₁_pos)
    exact lt_of_lt_of_le hhalf (min_le_right _ _)
  have hT₂R₂ : T₂ < R₂ := by
    dsimp [T₂]
    have hhalf : min R₂ S₂ / 2 < min R₂ S₂ := by
      exact half_lt_self (lt_min hR₂_pos hS₂_pos)
    exact lt_of_lt_of_le hhalf (min_le_left _ _)
  have hT₂S₂ : T₂ < S₂ := by
    dsimp [T₂]
    have hhalf : min R₂ S₂ / 2 < min R₂ S₂ := by
      exact half_lt_self (lt_min hR₂_pos hS₂_pos)
    exact lt_of_lt_of_le hhalf (min_le_right _ _)
  have hsumR :
      Summable (fun n : ℕ × ℕ ↦ ‖coeffR n.1 n.2‖ * T₁ ^ n.1 * T₂ ^ n.2) := by
    rcases
        cauchy_coefficients_bound_and_mem_domain
          (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂ hf with
      ⟨_, _, _, hsummable⟩
    simpa [coeffR] using hsummable T₁ T₂ hT₁_pos.le hT₁R₁ hT₂_pos.le hT₂R₂
  have hsumS :
      Summable (fun n : ℕ × ℕ ↦ ‖coeffS n.1 n.2‖ * T₁ ^ n.1 * T₂ ^ n.2) := by
    rcases
        cauchy_coefficients_bound_and_mem_domain
          (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) hS₁_pos hS₁ρ₁ hS₂_pos hS₂ρ₂ hf with
      ⟨_, _, _, hsummable⟩
    simpa [coeffS] using hsummable T₁ T₂ hT₁_pos.le hT₁S₁ hT₂_pos.le hT₂S₂
  have hnonnegR :
      0 ≤ fun n : ℕ × ℕ ↦ ‖coeffR n.1 n.2‖ * T₁ ^ n.1 * T₂ ^ n.2 := by
    intro n
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (pow_nonneg hT₁_pos.le _))
      (pow_nonneg hT₂_pos.le _)
  have hnonnegS :
      0 ≤ fun n : ℕ × ℕ ↦ ‖coeffS n.1 n.2‖ * T₁ ^ n.1 * T₂ ^ n.2 := by
    intro n
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (pow_nonneg hT₁_pos.le _))
      (pow_nonneg hT₂_pos.le _)
  have hsplitsR := (summable_prod_of_nonneg hnonnegR).1 hsumR
  have hsplitsS := (summable_prod_of_nonneg hnonnegS).1 hsumS
  have hrowBaseR :
      ∀ p, Summable (fun q ↦ ‖coeffR p q‖ * T₂ ^ q) := by
    intro p
    have hp :
        Summable (fun q ↦ ‖coeffR p q‖ * T₁ ^ p * T₂ ^ q) := hsplitsR.1 p
    have hp' :
        Summable (fun q ↦ (‖coeffR p q‖ * T₂ ^ q) * T₁ ^ p) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hp
    exact (summable_mul_right_iff (pow_ne_zero _ hT₁_pos.ne')).1 hp'
  have hrowBaseS :
      ∀ p, Summable (fun q ↦ ‖coeffS p q‖ * T₂ ^ q) := by
    intro p
    have hp :
        Summable (fun q ↦ ‖coeffS p q‖ * T₁ ^ p * T₂ ^ q) := hsplitsS.1 p
    have hp' :
        Summable (fun q ↦ (‖coeffS p q‖ * T₂ ^ q) * T₁ ^ p) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hp
    exact (summable_mul_right_iff (pow_ne_zero _ hT₁_pos.ne')).1 hp'
  have houterR : Summable (fun p ↦ xMajorantR p * T₁ ^ p) := by
    refine hsplitsR.2.congr ?_
    intro p
    simpa [xMajorantR, mul_assoc, mul_left_comm, mul_comm] using
      (hrowBaseR p).tsum_mul_right (T₁ ^ p)
  have houterS : Summable (fun p ↦ xMajorantS p * T₁ ^ p) := by
    refine hsplitsS.2.congr ?_
    intro p
    simpa [xMajorantS, mul_assoc, mul_left_comm, mul_comm] using
      (hrowBaseS p).tsum_mul_right (T₁ ^ p)
  have hrowNormLeR :
      ∀ {z₂ : ℂ}, ‖z₂‖ < T₂ → ∀ p, ‖rowR z₂ p‖ ≤ xMajorantR p := by
    intro z₂ hz₂ p
    have hnorm :
        Summable (fun q ↦ ‖coeffR p q * z₂ ^ q‖) := by
      refine (hrowBaseR p).of_nonneg_of_le (fun q ↦ norm_nonneg _) ?_
      intro q
      calc
        ‖coeffR p q * z₂ ^ q‖ = ‖coeffR p q‖ * ‖z₂‖ ^ q := by
          simp [norm_pow]
        _ ≤ ‖coeffR p q‖ * T₂ ^ q := by
          gcongr
    have hnorm' : Summable (fun q ↦ ‖coeffR p q‖ * ‖z₂‖ ^ q) := by
      simpa [norm_pow] using hnorm
    calc
      ‖rowR z₂ p‖ = ‖∑' q, coeffR p q * z₂ ^ q‖ := by simp [rowR]
      _ ≤ ∑' q, ‖coeffR p q * z₂ ^ q‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' q, ‖coeffR p q‖ * ‖z₂‖ ^ q := by
            simp [norm_pow]
      _ ≤ ∑' q, ‖coeffR p q‖ * T₂ ^ q := by
            exact hnorm'.tsum_le_tsum (fun q ↦ by gcongr) (hrowBaseR p)
      _ = xMajorantR p := by simp [xMajorantR]
  have hrowNormLeS :
      ∀ {z₂ : ℂ}, ‖z₂‖ < T₂ → ∀ p, ‖rowS z₂ p‖ ≤ xMajorantS p := by
    intro z₂ hz₂ p
    have hnorm :
        Summable (fun q ↦ ‖coeffS p q * z₂ ^ q‖) := by
      refine (hrowBaseS p).of_nonneg_of_le (fun q ↦ norm_nonneg _) ?_
      intro q
      calc
        ‖coeffS p q * z₂ ^ q‖ = ‖coeffS p q‖ * ‖z₂‖ ^ q := by
          simp [norm_pow]
        _ ≤ ‖coeffS p q‖ * T₂ ^ q := by
          gcongr
    have hnorm' : Summable (fun q ↦ ‖coeffS p q‖ * ‖z₂‖ ^ q) := by
      simpa [norm_pow] using hnorm
    calc
      ‖rowS z₂ p‖ = ‖∑' q, coeffS p q * z₂ ^ q‖ := by simp [rowS]
      _ ≤ ∑' q, ‖coeffS p q * z₂ ^ q‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' q, ‖coeffS p q‖ * ‖z₂‖ ^ q := by
            simp [norm_pow]
      _ ≤ ∑' q, ‖coeffS p q‖ * T₂ ^ q := by
            exact hnorm'.tsum_le_tsum (fun q ↦ by gcongr) (hrowBaseS p)
      _ = xMajorantS p := by simp [xMajorantS]
  have hrow_eq :
      Set.EqOn
        rowR
        rowS
        (Metric.ball (0 : ℂ) T₂) := by
    intro z₂ hz₂
    have hz₂_norm : ‖z₂‖ < T₂ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz₂
    have hseriesR :
        HasFPowerSeriesAt
          (fun w : ℂ ↦ f (w, z₂))
          (FormalMultilinearSeries.ofScalars ℂ (rowR z₂))
          0 := by
      refine hasFPowerSeriesAtZeroOfEqTsumOnBall
        (g := fun w : ℂ ↦ f (w, z₂))
        (a := rowR z₂)
        (r := T₁)
        hT₁_pos
        ?_
        ?_
      · refine Summable.of_nonneg_of_le
          (fun p ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hT₁_pos.le _))
          ?_
          houterR
        intro p
        exact mul_le_mul_of_nonneg_right (hrowNormLeR hz₂_norm p) (pow_nonneg hT₁_pos.le _)
      · intro w hw
        have hw_norm : ‖w‖ < T₁ := by
          simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hlocal :=
          cauchy_local_double_series_eq_on_closed_bidisc
            (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (R₁ := R₁) (R₂ := R₂)
            (r₁ := ‖w‖) (r₂ := ‖z₂‖) (z := (w, z₂))
            hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂
            (norm_nonneg _) (lt_trans hw_norm hT₁R₁) (norm_nonneg _) (lt_trans hz₂_norm hT₂R₂)
            le_rfl le_rfl hf
        calc
          f (w, z₂)
              = ∑' p : ℕ, ∑' q : ℕ,
                  bidisc_cauchy_coefficient f R₁ R₂ p q * w ^ p * z₂ ^ q := hlocal
          _ = ∑' p : ℕ, rowR z₂ p * w ^ p := by
                refine tsum_congr fun p ↦ ?_
                have hnorm :
                    Summable (fun q ↦ ‖coeffR p q * z₂ ^ q‖) := by
                  refine (hrowBaseR p).of_nonneg_of_le (fun q ↦ norm_nonneg _) ?_
                  intro q
                  calc
                    ‖coeffR p q * z₂ ^ q‖ = ‖coeffR p q‖ * ‖z₂‖ ^ q := by
                      simp [norm_pow]
                    _ ≤ ‖coeffR p q‖ * T₂ ^ q := by
                      gcongr
                have hrowSeries : Summable (fun q ↦ coeffR p q * z₂ ^ q) := hnorm.of_norm
                simpa [rowR, coeffR, mul_assoc, mul_left_comm, mul_comm] using
                  (hrowSeries.tsum_mul_right (w ^ p))
    have hseriesS :
        HasFPowerSeriesAt
          (fun w : ℂ ↦ f (w, z₂))
          (FormalMultilinearSeries.ofScalars ℂ (rowS z₂))
          0 := by
      refine hasFPowerSeriesAtZeroOfEqTsumOnBall
        (g := fun w : ℂ ↦ f (w, z₂))
        (a := rowS z₂)
        (r := T₁)
        hT₁_pos
        ?_
        ?_
      · refine Summable.of_nonneg_of_le
          (fun p ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hT₁_pos.le _))
          ?_
          houterS
        intro p
        exact mul_le_mul_of_nonneg_right (hrowNormLeS hz₂_norm p) (pow_nonneg hT₁_pos.le _)
      · intro w hw
        have hw_norm : ‖w‖ < T₁ := by
          simpa [Metric.mem_ball, dist_eq_norm] using hw
        have hlocal :=
          cauchy_local_double_series_eq_on_closed_bidisc
            (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (R₁ := S₁) (R₂ := S₂)
            (r₁ := ‖w‖) (r₂ := ‖z₂‖) (z := (w, z₂))
            hS₁_pos hS₁ρ₁ hS₂_pos hS₂ρ₂
            (norm_nonneg _) (lt_trans hw_norm hT₁S₁) (norm_nonneg _) (lt_trans hz₂_norm hT₂S₂)
            le_rfl le_rfl hf
        calc
          f (w, z₂)
              = ∑' p : ℕ, ∑' q : ℕ,
                  bidisc_cauchy_coefficient f S₁ S₂ p q * w ^ p * z₂ ^ q := hlocal
          _ = ∑' p : ℕ, rowS z₂ p * w ^ p := by
                refine tsum_congr fun p ↦ ?_
                have hnorm :
                    Summable (fun q ↦ ‖coeffS p q * z₂ ^ q‖) := by
                  refine (hrowBaseS p).of_nonneg_of_le (fun q ↦ norm_nonneg _) ?_
                  intro q
                  calc
                    ‖coeffS p q * z₂ ^ q‖ = ‖coeffS p q‖ * ‖z₂‖ ^ q := by
                      simp [norm_pow]
                    _ ≤ ‖coeffS p q‖ * T₂ ^ q := by
                      gcongr
                have hrowSeries : Summable (fun q ↦ coeffS p q * z₂ ^ q) := hnorm.of_norm
                simpa [rowS, coeffS, mul_assoc, mul_left_comm, mul_comm] using
                  (hrowSeries.tsum_mul_right (w ^ p))
    exact funext fun p ↦ by
      simpa [FormalMultilinearSeries.coeff_ofScalars] using
        congrArg (fun P : FormalMultilinearSeries ℂ ℂ ℂ ↦ P.coeff p)
          (hseriesR.eq_formalMultilinearSeries hseriesS)
  intro p q
  have hseriesR :
      HasFPowerSeriesAt
        (fun z₂ : ℂ ↦ rowR z₂ p)
        (FormalMultilinearSeries.ofScalars ℂ (coeffR p))
        0 := by
    refine hasFPowerSeriesAtZeroOfEqTsumOnBall
      (g := fun z₂ : ℂ ↦ rowR z₂ p)
      (a := coeffR p)
      (r := T₂)
      hT₂_pos
      ?_
      ?_
    · simpa [coeffR] using hrowBaseR p
    · intro z₂ hz₂
      simp [rowR]
  have hseriesS :
      HasFPowerSeriesAt
        (fun z₂ : ℂ ↦ rowR z₂ p)
        (FormalMultilinearSeries.ofScalars ℂ (coeffS p))
        0 := by
    refine hasFPowerSeriesAtZeroOfEqTsumOnBall
      (g := fun z₂ : ℂ ↦ rowR z₂ p)
      (a := coeffS p)
      (r := T₂)
      hT₂_pos
      ?_
      ?_
    · simpa [coeffS] using hrowBaseS p
    · intro z₂ hz₂
      have hrow_val := congrArg (fun a : ℕ → ℂ ↦ a p) (hrow_eq hz₂)
      simpa [rowS] using hrow_val
  simpa [FormalMultilinearSeries.coeff_ofScalars, coeffR, coeffS] using
    congrArg (fun P : FormalMultilinearSeries ℂ ℂ ℂ ↦ P.coeff q)
      (hseriesR.eq_formalMultilinearSeries hseriesS)

/-- Cartan section17 0005_Proposition_3_1: Proposition 3.1 says that if `f` is holomorphic on the
bidisc `‖z₁‖ < ρ₁`, `‖z₂‖ < ρ₂`, equivalently
under the separate-slice hypotheses of Proposition 2.1, then `f` admits a double power series
expansion there; equivalently, there are
coefficients `a p q` whose scalar double series converges on every smaller closed bidisc and sums
to `f z₁ z₂` throughout the open bidisc. -/
theorem holomorphic_on_bidisc_has_double_power_series
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ : ℝ} (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    ∃ a : ℕ → ℕ → ℂ,
      (∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ < ρ₁ → 0 ≤ r₂ → r₂ < ρ₂ →
        Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2)) ∧
      ∀ z : ℂ × ℂ, ‖z.1‖ < ρ₁ → ‖z.2‖ < ρ₂ →
        f z = ∑' n : ℕ × ℕ, a n.1 n.2 * z.1 ^ n.1 * z.2 ^ n.2 := by
  by_cases hpos : 0 < ρ₁ ∧ 0 < ρ₂
  · -- Route correction: the remaining case is the genuine textbook argument, using Proposition 2.1
    -- plus the local Cauchy-series lemma, radius-independence of the coefficients, and the
    -- resulting Cauchy majorant bound on smaller closed bidiscs.
    rcases hpos with ⟨hρ₁_pos, hρ₂_pos⟩
    let R₁₀ : ℝ := ρ₁ / 2
    let R₂₀ : ℝ := ρ₂ / 2
    have hR₁₀_pos : 0 < R₁₀ := by
      dsimp [R₁₀]
      linarith
    have hR₁₀ρ₁ : R₁₀ < ρ₁ := by
      dsimp [R₁₀]
      linarith
    have hR₂₀_pos : 0 < R₂₀ := by
      dsimp [R₂₀]
      linarith
    have hR₂₀ρ₂ : R₂₀ < ρ₂ := by
      dsimp [R₂₀]
      linarith
    let a : ℕ → ℕ → ℂ := fun p q ↦ bidisc_cauchy_coefficient f R₁₀ R₂₀ p q
    refine ⟨a, ?_, ?_⟩
    · -- For any smaller closed bidisc, enlarge its radii slightly and compare with the reference
      -- Cauchy coefficients computed at the fixed pair `(R₁₀,R₂₀)`.
      intro r₁ r₂ hr₁_nonneg hr₁ρ₁ hr₂_nonneg hr₂ρ₂
      rcases exists_between hr₁ρ₁ with ⟨R₁, hr₁R₁, hR₁ρ₁⟩
      rcases exists_between hr₂ρ₂ with ⟨R₂, hr₂R₂, hR₂ρ₂⟩
      have hR₁_pos : 0 < R₁ := lt_of_le_of_lt hr₁_nonneg hr₁R₁
      have hR₂_pos : 0 < R₂ := lt_of_le_of_lt hr₂_nonneg hr₂R₂
      have hcoeff_eq :
          ∀ p q : ℕ, a p q = bidisc_cauchy_coefficient f R₁ R₂ p q := by
        intro p q
        simpa [a] using
          (cauchy_coefficients_eq_of_two_admissible_pairs
            (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
            hR₁₀_pos hR₁₀ρ₁ hR₂₀_pos hR₂₀ρ₂
            hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂ hf p q)
      rcases
          cauchy_coefficients_bound_and_mem_domain
            (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
            hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂ hf with
        ⟨M, hM_nonneg, hbound, hsummable⟩
      -- The local bound gives summability for the chosen larger radii, and coefficient
      -- independence transfers it back to the global array `a`.
      have hsum_local : Summable (fun n : ℕ × ℕ ↦
          ‖bidisc_cauchy_coefficient f R₁ R₂ n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2) :=
        hsummable r₁ r₂ hr₁_nonneg hr₁R₁ hr₂_nonneg hr₂R₂
      simpa [a, hcoeff_eq] using hsum_local
    · -- At each interior point, choose intermediate radii, use the local nested Cauchy series,
      -- replace its coefficients by the fixed global coefficients, and flatten the nested sum.
      intro z hz₁ hz₂
      rcases exists_between hz₁ with ⟨R₁, hz₁R₁, hR₁ρ₁⟩
      rcases exists_between hz₂ with ⟨R₂, hz₂R₂, hR₂ρ₂⟩
      have hR₁_pos : 0 < R₁ := lt_of_le_of_lt (norm_nonneg z.1) hz₁R₁
      have hR₂_pos : 0 < R₂ := lt_of_le_of_lt (norm_nonneg z.2) hz₂R₂
      have hlocal :
          f z = ∑' p : ℕ, ∑' q : ℕ,
            bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
        -- Apply the local Cauchy expansion on the closed bidisc with radii `‖z₁‖, ‖z₂‖`.
        exact cauchy_local_double_series_eq_on_closed_bidisc
          (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (R₁ := R₁) (R₂ := R₂)
          (r₁ := ‖z.1‖) (r₂ := ‖z.2‖) (z := z)
          hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂
          (norm_nonneg _) hz₁R₁ (norm_nonneg _) hz₂R₂
          le_rfl le_rfl hf
      have hcoeff_eq :
          ∀ p q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q = a p q := by
        intro p q
        simpa [a] using
          (cauchy_coefficients_eq_of_two_admissible_pairs
            (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
            hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂
            hR₁₀_pos hR₁₀ρ₁ hR₂₀_pos hR₂₀ρ₂ hf p q)
      rcases
          cauchy_coefficients_bound_and_mem_domain
            (f := f) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
            hR₁_pos hR₁ρ₁ hR₂_pos hR₂ρ₂ hf with
        ⟨M, hM_nonneg, hbound, hsummable⟩
      have hmajorant :
          Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * ‖z.1‖ ^ n.1 * ‖z.2‖ ^ n.2) := by
        have hsum_local : Summable (fun n : ℕ × ℕ ↦
            ‖bidisc_cauchy_coefficient f R₁ R₂ n.1 n.2‖ * ‖z.1‖ ^ n.1 * ‖z.2‖ ^ n.2) :=
          hsummable ‖z.1‖ ‖z.2‖ (norm_nonneg _) hz₁R₁ (norm_nonneg _) hz₂R₂
        simpa [a, hcoeff_eq] using hsum_local
      have hseries :
          Summable (fun n : ℕ × ℕ ↦ a n.1 n.2 * z.1 ^ n.1 * z.2 ^ n.2) :=
        summable_double_power_series_of_summable_normal_majorant hmajorant
      have hrows :
          ∀ p : ℕ, Summable (fun q : ℕ ↦ a p q * z.1 ^ p * z.2 ^ q) := by
        intro p
        simpa using hseries.prod_factor p
      calc
        f z = ∑' p : ℕ, ∑' q : ℕ,
            bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := hlocal
        _ = ∑' p : ℕ, ∑' q : ℕ, a p q * z.1 ^ p * z.2 ^ q := by
              refine tsum_congr fun p ↦ ?_
              refine tsum_congr fun q ↦ ?_
              rw [hcoeff_eq p q]
        _ = ∑' n : ℕ × ℕ, a n.1 n.2 * z.1 ^ n.1 * z.2 ^ n.2 := by
              symm
              exact hseries.tsum_prod' hrows
  · refine ⟨fun _ _ ↦ 0, ?_, ?_⟩
    · -- For the zero coefficient array, the normal-majorant series is identically zero.
      intro r₁ r₂ hr₁ hrρ₁ hr₂ hrρ₂
      simp
    · -- If one bidisc radius is nonpositive, there are no points satisfying
      -- both strict norm bounds.
      intro z hz₁ hz₂
      have hρ₁_pos : 0 < ρ₁ := lt_of_le_of_lt (norm_nonneg z.1) hz₁
      have hρ₂_pos : 0 < ρ₂ := lt_of_le_of_lt (norm_nonneg z.2) hz₂
      exact (hpos ⟨hρ₁_pos, hρ₂_pos⟩).elim

/-- Source-facing bridge/view of Proposition 3.1 with the separate-slice hypotheses from
Proposition 2.1. -/
theorem separately_holomorphic_has_double_power_series_on_bidisc
    {f : ℂ → ℂ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ρ₂ →
        DifferentiableOn ℂ (fun z ↦ f z w) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f w z) (Metric.ball (0 : ℂ) ρ₂)) :
    ∃ a : ℕ → ℕ → ℂ,
      (∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ < ρ₁ → 0 ≤ r₂ → r₂ < ρ₂ →
        Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2)) ∧
      ∀ z₁ z₂ : ℂ, ‖z₁‖ < ρ₁ → ‖z₂‖ < ρ₂ →
        f z₁ z₂ = ∑' n : ℕ × ℕ, a n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2 := by
  have huncurry : DifferentiableOn ℂ (Function.uncurry f) (bidisc ρ₁ ρ₂) := by
    -- Proposition 2.1 already upgrades the slice hypotheses to the canonical bidisc owner.
    exact separately_holomorphic_uncurry_differentiableOn_bidisc hhol₁ hhol₂
  rcases holomorphic_on_bidisc_has_double_power_series huncurry with ⟨a, haSummable, haEq⟩
  refine ⟨a, haSummable, ?_⟩
  intro z₁ z₂ hz₁ hz₂
  exact haEq (z₁, z₂) hz₁ hz₂
