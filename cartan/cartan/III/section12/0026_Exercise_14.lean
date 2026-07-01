import Mathlib
import cartan.III.section10.«0001_Definition_III_4_extra_1»
import cartan.III.section10.«0003_Theorem_III_4_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement shape was checked against mathlib's `Function.Periodic.cuspFunction` /
-- `UpperHalfPlane.qExpansion` API and the local Laurent-series precedent.

open scoped Topology Manifold
open Function.Periodic

noncomputable section

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet
local notation "π" => (Real.pi : ℂ)

/-- Helper for Exercise 14: a nonzero point of the open unit ball has `invQParam` in the upper
half-plane. -/
lemma invQParam_mem_upper_half_plane_of_mem_punctured_unit_ball
    {q : ℂ} (hq : q ∈ Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) :
    0 < Complex.im (invQParam (1 : ℝ) q) := by
  have hqball : ‖q‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq.1
  -- The punctured unit-disc hypothesis is exactly the owner criterion for `invQParam`.
  exact Function.Periodic.im_invQParam_pos_of_norm_lt_one Real.zero_lt_one hqball hq.2

/-- Helper for Exercise 14: the punctured open unit disc is exactly the annulus `0 < ‖q‖ < 1`. -/
lemma punctured_unit_ball_eq_complexOpenAnnulus_zero_one :
    Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ) = complexOpenAnnulus 0 1 := by
  ext q
  constructor
  · intro hq
    have hqball : ‖q‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq.1
    -- The puncture excludes the origin, so the annulus inner inequality becomes strict.
    have hqnorm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq.2
    change (0 : ENNReal) < ‖q‖₊ ∧ ‖q‖₊ < (1 : ENNReal)
    exact ⟨by exact_mod_cast hqnorm_pos, by exact_mod_cast hqball⟩
  · intro hq
    have hqball : q ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq.2
    have hq0 : q ≠ 0 := by
      intro hq0
      have : ¬ (0 : ENNReal) < (0 : ENNReal) := by simp
      exact this (by simpa [hq0] using hq.1)
    -- Translating the annulus inequalities back gives the punctured metric ball.
    exact ⟨hqball, hq0⟩

/-- Helper for Exercise 14: `qParam` sends the upper half-plane into the annulus `0 < ‖q‖ < 1`. -/
lemma qParam_mem_complexOpenAnnulus_zero_one_of_mem_upper_half_plane
    {z : ℂ} (hz : z ∈ ℍₒ) :
    qParam (1 : ℝ) z ∈ complexOpenAnnulus 0 1 := by
  have hqball : ‖qParam (1 : ℝ) z‖ < 1 := by
    simpa using
      (Function.Periodic.norm_qParam_lt_iff (h := (1 : ℝ)) Real.zero_lt_one 0 z).2 hz
  -- The `q`-parameter never vanishes, so only the outer radius requires work.
  have hqnorm_pos : 0 < ‖qParam (1 : ℝ) z‖ :=
    norm_pos_iff.mpr (Function.Periodic.qParam_ne_zero (h := (1 : ℝ)) z)
  change (0 : ENNReal) < ‖qParam (1 : ℝ) z‖₊ ∧ ‖qParam (1 : ℝ) z‖₊ < (1 : ENNReal)
  exact ⟨by exact_mod_cast hqnorm_pos, by exact_mod_cast hqball⟩

/-- Helper for Exercise 14: composing an annulus Laurent expansion with `qParam` gives the
corresponding locally uniformly summable Fourier-Laurent family on the upper half-plane. -/
lemma hasSumLocallyUniformlyOn_qParam_pullback
    {a : ℤ → ℂ} (ha : IsLaurentSeriesOnAnnulus a 0 1) :
    HasSumLocallyUniformlyOn
      (fun n z ↦ a n * qParam (1 : ℝ) z ^ n)
      (fun z ↦ ∑' n : ℤ, a n * qParam (1 : ℝ) z ^ n)
      ℍₒ := by
  -- Pull back the annulus Laurent family along the continuous map
  -- `qParam : ℍₒ → complexOpenAnnulus 0 1`.
  exact (ha.hasSumLocallyUniformlyOn.comp (qParam (1 : ℝ))
    (fun z hz ↦ qParam_mem_complexOpenAnnulus_zero_one_of_mem_upper_half_plane hz)
    (Function.Periodic.continuous_qParam.continuousOn))

/-- Helper for Exercise 14: multiplying a `qParam` Laurent monomial by the `n`th Fourier weight
shifts the frequency from `m` to `m - n`. -/
lemma exercise14_qParam_zpow_mul_fourier_weight
    (m n : ℤ) (z : ℂ) :
    qParam (1 : ℝ) z ^ m * Complex.exp (-2 * π * Complex.I * (n : ℂ) * z) =
      Complex.exp (2 * π * Complex.I * ((m - n : ℤ) : ℂ) * z) := by
  have hqParam :
      qParam (1 : ℝ) z = Complex.exp (2 * π * Complex.I * z / (1 : ℂ)) := by
    norm_num [Function.Periodic.qParam]
  -- Rewrite the `qParam` power as a single exponential with integer frequency `m`.
  calc
    qParam (1 : ℝ) z ^ m * Complex.exp (-2 * π * Complex.I * (n : ℂ) * z)
        = Complex.exp ((m : ℂ) * (2 * π * Complex.I * z)) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * z) := by
            rw [hqParam, div_one, ← Complex.exp_int_mul]
    -- Combine the two exponentials into one.
    _ = Complex.exp (((m : ℂ) * (2 * π * Complex.I * z)) +
          (-2 * π * Complex.I * (n : ℂ) * z)) := by
          rw [← Complex.exp_add]
    -- Normalize the frequency to `m - n`.
    _ = Complex.exp (2 * π * Complex.I * ((m - n : ℤ) : ℂ) * z) := by
          congr 1
          rw [Int.cast_sub]
          ring

/-- Helper for Exercise 14: the `n`th Fourier weight is the `(-n)`th power of `qParam`. -/
lemma exercise14_fourier_weight_eq_qParam_zpow
    (n : ℤ) (z : ℂ) :
    Complex.exp (-2 * π * Complex.I * (n : ℂ) * z) =
      qParam (1 : ℝ) z ^ (-n) := by
  have hqParam :
      qParam (1 : ℝ) z = Complex.exp (2 * π * Complex.I * z / (1 : ℂ)) := by
    norm_num [Function.Periodic.qParam]
  -- First identify the Fourier weight with the `(-n)` frequency exponential.
  calc
    Complex.exp (-2 * π * Complex.I * (n : ℂ) * z)
        = Complex.exp (2 * π * Complex.I * ((-n : ℤ) : ℂ) * z) := by
            simpa using (exercise14_qParam_zpow_mul_fourier_weight 0 n z)
    -- Then rewrite that exponential back as the corresponding `qParam` power.
    _ = qParam (1 : ℝ) z ^ (-n) := by
          symm
          calc
            qParam (1 : ℝ) z ^ (-n) = Complex.exp (((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * z)) := by
              rw [hqParam, div_one, ← Complex.exp_int_mul]
            _ = Complex.exp (2 * π * Complex.I * ((-n : ℤ) : ℂ) * z) := by
              congr 1
              ring

/-- Helper for Exercise 14: the horizontal integral of a single exponential frequency detects only
the zero frequency. -/
lemma exercise14_intervalIntegral_exp_frequency
    (a : ℂ) (k : ℤ) (y : ℝ) :
    ∫ x in (0 : ℝ)..1,
      a * Complex.exp (2 * π * Complex.I * (k : ℂ) * (x + y * Complex.I)) =
        if k = 0 then a else 0 := by
  by_cases hk : k = 0
  · subst hk
    -- The zero frequency leaves a constant integrand on the unit interval.
    simp
  · let c : ℂ := 2 * π * Complex.I * (k : ℂ)
    have hkC : (k : ℂ) ≠ 0 := by
      exact_mod_cast hk
    have hpi : (π : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have htwoPiI : (2 * π * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero htwoPiI hkC
    have hrewrite :
        (fun x : ℝ ↦ a * Complex.exp (2 * π * Complex.I * (k : ℂ) * (x + y * Complex.I))) =
          fun x : ℝ ↦ (a * Complex.exp (c * (y * Complex.I))) * Complex.exp (c * x) := by
      funext x
      dsimp [c]
      calc
        a * Complex.exp (2 * π * Complex.I * (k : ℂ) * (x + y * Complex.I))
            = a * (Complex.exp (c * x) * Complex.exp (c * (y * Complex.I))) := by
                rw [show 2 * π * Complex.I * (k : ℂ) * (x + y * Complex.I) =
                  c * x + c * (y * Complex.I) by
                    dsimp [c]
                    ring, Complex.exp_add]
        _ = (a * Complex.exp (c * (y * Complex.I))) * Complex.exp (c * x) := by
              ring
    rw [hrewrite, intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    have hexp : Complex.exp c = 1 := by
      dsimp [c]
      rw [show 2 * π * Complex.I * (k : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        ring]
      simpa using
        (Complex.exp_int_mul_two_pi_mul_I k :
          Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1)
    have hexp1 : Complex.exp (c * (1 : ℂ)) = 1 := by
      simpa using hexp
    have hzero :
        ((Complex.exp (c * ((1 : ℝ) : ℂ)) - Complex.exp (c * ((0 : ℝ) : ℂ))) / c : ℂ) = 0 := by
      rw [show (((1 : ℝ) : ℂ)) = (1 : ℂ) by norm_num, show (((0 : ℝ) : ℂ)) = (0 : ℂ) by norm_num,
        hexp1]
      simp [hc]
    -- The nonzero frequencies integrate to zero over one full period.
    rw [if_neg hk, hzero]
    ring

/-- Helper for Exercise 14: after weighting by the `n`th Fourier kernel, integrating the `m`th
Laurent term over one horizontal period picks out exactly the diagonal term `m = n`. -/
lemma exercise14_intervalIntegral_weighted_laurent_term
    (a : ℂ) (m n : ℤ) (y : ℝ) :
    ∫ x in (0 : ℝ)..1,
      a * qParam (1 : ℝ) (x + y * Complex.I) ^ m *
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) =
          if m = n then a else 0 := by
  -- Rewrite the weighted Laurent term as a single exponential at frequency `m - n`.
  calc
    ∫ x in (0 : ℝ)..1,
      a * qParam (1 : ℝ) (x + y * Complex.I) ^ m *
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))
        = ∫ x in (0 : ℝ)..1,
            a * Complex.exp (2 * π * Complex.I * ((m - n : ℤ) : ℂ) *
              (x + y * Complex.I)) := by
              congr with x
              simpa [mul_assoc] using congrArg
                (fun t : ℂ ↦ a * t)
                (exercise14_qParam_zpow_mul_fourier_weight m n (x + y * Complex.I))
    -- One-period integration kills every non-diagonal frequency.
    _ = if m - n = 0 then a else 0 :=
          exercise14_intervalIntegral_exp_frequency a (m - n) y
    -- The diagonal condition `m - n = 0` is equivalent to `m = n`.
    _ = if m = n then a else 0 := by
          simp [sub_eq_zero]

/-- Helper for Exercise 14: each weighted Laurent term on a fixed horizontal line is continuous in
the horizontal parameter. -/
lemma exercise14_continuous_weighted_term
    (a : ℂ) (m n : ℤ) (y : ℝ) :
    Continuous (fun x : ℝ ↦
      a * qParam (1 : ℝ) (x + y * Complex.I) ^ m *
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))) := by
  have hrewrite :
      (fun x : ℝ ↦
        a * qParam (1 : ℝ) (x + y * Complex.I) ^ m *
          Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))) =
        fun x : ℝ ↦
          a * Complex.exp (2 * π * Complex.I * ((m - n : ℤ) : ℂ) * (x + y * Complex.I)) := by
    funext x
    -- Collapse the weighted Laurent monomial to a single exponential factor.
    simpa [mul_assoc] using congrArg
      (fun t : ℂ ↦ a * t)
      (exercise14_qParam_zpow_mul_fourier_weight m n (x + y * Complex.I))
  -- Continuity is now just continuity of an affine map followed by `Complex.exp`.
  rw [hrewrite]
  fun_prop

/-- Helper for Exercise 14: each pulled-back Laurent monomial along a horizontal line is
continuous in the horizontal parameter. -/
lemma exercise14_continuous_pullback_term
    (a : ℂ) (m : ℤ) (y : ℝ) :
    Continuous (fun x : ℝ ↦ a * qParam (1 : ℝ) (x + y * Complex.I) ^ m) := by
  -- This is the `n = 0` case of the weighted continuity lemma, so the extra Fourier factor drops
  -- out.
  simpa using (exercise14_continuous_weighted_term a m 0 y)

/-- Helper for Exercise 14: multiplying a locally uniformly summable family by a fixed continuous
weight preserves local uniform summability on the same set. -/
lemma exercise14_hasSumLocallyUniformlyOn_mul_fixed
    {X ι : Type*} [TopologicalSpace X] {s : Set X} {F : ι → X → ℂ} {G g : X → ℂ}
    (h : HasSumLocallyUniformlyOn F G s) (hg : ContinuousOn g s) (hG : ContinuousOn G s) :
    HasSumLocallyUniformlyOn (fun i x ↦ g x * F i x) (fun x ↦ g x * G x) s := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h ⊢
  have hconst : TendstoLocallyUniformlyOn (fun _ : Finset ι ↦ g) g Filter.atTop s := by
    -- The constant family already converges locally uniformly to itself.
    intro u hu x hx
    refine ⟨s, self_mem_nhdsWithin, ?_⟩
    filter_upwards with n y hy
    exact refl_mem_uniformity hu
  -- Multiply the partial sums by the fixed factor before rewriting the finite sums.
  refine (hconst.mul₀ h hg hG).congr ?_
  intro t
  intro x hx
  simp [Finset.mul_sum, mul_assoc]

/-- Helper for Exercise 14: on a compact set, local uniform summability upgrades to uniform
summability. -/
lemma exercise14_hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact
    {X ι : Type*} [TopologicalSpace X] {s : Set X} {F : ι → X → ℂ} {G : X → ℂ}
    (hs : IsCompact s) (h : HasSumLocallyUniformlyOn F G s) :
    HasSumUniformlyOn F G s := by
  -- Compactness identifies local uniform convergence with uniform convergence on `s`.
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]
  exact hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp h

/-- Helper for Exercise 14: after pulling the Laurent series back along `x ↦ x + y * I` and
weighting by the fixed `n`th Fourier kernel, the resulting family converges uniformly on the
compact unit interval. -/
lemma exercise14_weighted_pullback_hasSumUniformlyOn_unitInterval
    {a : ℤ → ℂ} (ha : IsLaurentSeriesOnAnnulus a 0 1)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasSumUniformlyOn
      (fun m (x : ℝ) ↦
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) *
          (a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m))
      (fun x : ℝ ↦
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) *
          (∑' m : ℤ, a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m))
      (Set.Icc (0 : ℝ) 1) := by
  have hbase :
      HasSumLocallyUniformlyOn
        (fun m (x : ℝ) ↦ a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m)
        (fun x : ℝ ↦ ∑' m : ℤ, a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m)
        (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the upper-half-plane pullback series to the horizontal segment `x ↦ x + y * I`.
    refine (hasSumLocallyUniformlyOn_qParam_pullback ha).comp
      (fun x : ℝ ↦ x + y * Complex.I) ?_ ?_
    · intro x hx
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hy
    · have hline : Continuous (fun x : ℝ ↦ x + y * Complex.I) := by
        fun_prop
      exact hline.continuousOn
  have hsum_cont :
      ContinuousOn
        (fun x : ℝ ↦ ∑' m : ℤ, a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m)
        (Set.Icc (0 : ℝ) 1) := by
    -- The compact interval sees a locally uniform limit of continuous finite partial sums.
    have hpartial_cont :
        ∀ s : Finset ℤ,
          Continuous
            (fun x : ℝ ↦ ∑ m ∈ s, a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m) := by
      intro s
      exact continuous_finsetSum s (fun m _ ↦ exercise14_continuous_pullback_term (a m) m y)
    exact
      (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hbase).continuousOn
        (Filter.Frequently.of_forall fun s : Finset ℤ ↦
          show ContinuousOn
              (fun x : ℝ ↦ ∑ m ∈ s, a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m)
              (Set.Icc (0 : ℝ) 1) from
            (hpartial_cont s).continuousOn)
  have hweight_cont :
      ContinuousOn
        (fun x : ℝ ↦ Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)))
        (Set.Icc (0 : ℝ) 1) := by
    have hweight :
        Continuous
          (fun x : ℝ ↦ Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))) := by
      fun_prop
    exact hweight.continuousOn
  have hweighted :
      HasSumLocallyUniformlyOn
        (fun m (x : ℝ) ↦
          Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) *
            (a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m))
        (fun x : ℝ ↦
          Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) *
            (∑' m : ℤ, a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m))
        (Set.Icc (0 : ℝ) 1) :=
    exercise14_hasSumLocallyUniformlyOn_mul_fixed hbase hweight_cont hsum_cont
  -- Compactness upgrades the locally uniform convergence on `[0,1]` to uniform convergence.
  exact
    exercise14_hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact isCompact_Icc hweighted

/-- Helper for Exercise 14: the Laurent coefficient of the descended punctured-disc expansion is
the textbook horizontal integral along any line `Im z = y > 0`. -/
lemma exercise14_coeff_eq_horizontal_integral_of_descended_annulus_expansion
    {f g : ℂ → ℂ} {a : ℤ → ℂ}
    (ha : IsLaurentSeriesOnAnnulus a 0 1)
    (hgLaurent : Set.EqOn g (fun q ↦ ∑' m : ℤ, a m * q ^ m) (complexOpenAnnulus 0 1))
    (hgq : Set.EqOn (fun z ↦ g (qParam (1 : ℝ) z)) f ℍₒ) :
    ∀ n : ℤ, ∀ y : ℝ, 0 < y →
      a n =
        ∫ x in (0 : ℝ)..1,
          f (x + y * Complex.I) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) := by
  intro n y hy
  let term : ℤ → ℝ → ℂ := fun m x ↦
    a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m *
      Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))
  let summed : ℝ → ℂ := fun x ↦
    (∑' m : ℤ, a m * qParam (1 : ℝ) (x + y * Complex.I) ^ m) *
      Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))
  have huniform :
      HasSumUniformlyOn term summed (Set.Icc 0 1) := by
    -- This is the source-controlled object: the weighted pullback Laurent series on one period.
    simpa [term, summed, mul_assoc, mul_left_comm, mul_comm] using
      exercise14_weighted_pullback_hasSumUniformlyOn_unitInterval (a := a) ha n hy
  have hpartial_cont :
      ∀ s : Finset ℤ, ContinuousOn (fun x : ℝ ↦ ∑ m ∈ s, term m x) (Set.uIcc 0 1) := by
    intro s
    -- Every finite partial sum is continuous because each weighted term is continuous.
    have hcont :
        Continuous (fun x : ℝ ↦ ∑ m ∈ s, term m x) := by
      exact continuous_finsetSum s (fun m _ ↦ exercise14_continuous_weighted_term (a m) m n y)
    exact hcont.continuousOn
  have hpartial_tendsto :
      Filter.Tendsto
        (fun s : Finset ℤ ↦ ∫ x in (0 : ℝ)..1, ∑ m ∈ s, term m x)
        Filter.atTop
        (𝓝 (∫ x in (0 : ℝ)..1, summed x)) := by
    -- Uniform convergence on `[0,1]` allows the interval integral to pass to the limit.
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · exact Filter.Eventually.of_forall fun s ↦ by
        simpa [Set.uIcc_of_le zero_le_one] using hpartial_cont s
    · simpa [hasSumUniformlyOn_iff_tendstoUniformlyOn] using huniform.tendstoUniformlyOn
  have hterm_integrable :
      ∀ m : ℤ, IntervalIntegrable (term m) MeasureTheory.volume (0 : ℝ) 1 := by
    intro m
    exact
      (exercise14_continuous_weighted_term (a m) m n y).continuousOn.intervalIntegrable_of_Icc
        zero_le_one
  have hterm_eval :
      ∀ m : ℤ,
        ∫ x in (0 : ℝ)..1, term m x = if m = n then a m else 0 := by
    intro m
    -- Orthogonality of the frequencies `m - n` kills every off-diagonal term.
    simpa [term] using exercise14_intervalIntegral_weighted_laurent_term (a m) m n y
  have hpartial_eval :
      ∀ s : Finset ℤ,
        (∫ x in (0 : ℝ)..1, ∑ m ∈ s, term m x) = if n ∈ s then a n else 0 := by
    intro s
    -- After termwise integration, a finite partial sum collapses to its diagonal contribution.
    rw [intervalIntegral.integral_finsetSum fun m _ ↦ hterm_integrable m]
    simp [hterm_eval]
  have hpartial_tendsto_coeff :
      Filter.Tendsto
        (fun s : Finset ℤ ↦ ∫ x in (0 : ℝ)..1, ∑ m ∈ s, term m x)
        Filter.atTop
        (𝓝 (a n)) := by
    -- Eventually every large enough finite set contains `n`, so the partial integrals stabilize
    -- at the coefficient `a n`.
    have hevent :
        (fun _ : Finset ℤ ↦ a n) =ᶠ[Filter.atTop]
          (fun s : Finset ℤ ↦ if n ∈ s then a n else 0) := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨{n}, fun s hs ↦ ?_⟩
      have hn : n ∈ s := by
        simpa using hs
      simp [hn]
    have heval :
        (fun s : Finset ℤ ↦ if n ∈ s then a n else 0) =ᶠ[Filter.atTop]
          (fun s : Finset ℤ ↦ ∫ x in (0 : ℝ)..1, ∑ m ∈ s, term m x) :=
      Filter.Eventually.of_forall fun s ↦ (hpartial_eval s).symm
    exact (tendsto_const_nhds.congr' hevent).congr' heval
  have hsummed_eq :
      Set.EqOn
        summed
        (fun x : ℝ ↦
          f (x + y * Complex.I) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)))
        (Set.Icc 0 1) := by
    intro x hx
    have hz : x + y * Complex.I ∈ ℍₒ := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hy
    have hzAnn :
        qParam (1 : ℝ) (x + y * Complex.I) ∈ complexOpenAnnulus 0 1 :=
      qParam_mem_complexOpenAnnulus_zero_one_of_mem_upper_half_plane hz
    -- Rewrite the pulled-back Laurent sum through the descended annulus expansion and then back to
    -- the original periodic function.
    calc
      summed x
        = g (qParam (1 : ℝ) (x + y * Complex.I)) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) := by
            simpa [summed, mul_assoc, mul_left_comm, mul_comm] using
              congrArg
                (fun w : ℂ ↦
                  w * Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)))
                (hgLaurent hzAnn).symm
      _ = f (x + y * Complex.I) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) := by
            simpa using
              congrArg
                (fun w : ℂ ↦
                  w * Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)))
                (hgq hz)
  have hsummed_integral :
      (∫ x in (0 : ℝ)..1, summed x) =
        ∫ x in (0 : ℝ)..1,
          f (x + y * Complex.I) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) := by
    -- The equality of the summed integrands on `[0,1]` transfers directly to the interval
    -- integral.
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le zero_le_one] using hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    exact hsummed_eq (x := x) hxIcc
  calc
    a n = ∫ x in (0 : ℝ)..1, summed x := by
      exact tendsto_nhds_unique hpartial_tendsto_coeff hpartial_tendsto
    _ =
        ∫ x in (0 : ℝ)..1,
          f (x + y * Complex.I) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)) :=
        hsummed_integral

/-- Helper for Exercise 14: points on a positive-radius circle are nonzero. -/
lemma exercise14_ne_zero_of_mem_sphere_zero_of_pos
    {r : ℝ} (hr0 : 0 < r) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) r) :
    z ≠ 0 := by
  have hz_norm : ‖z‖ = r := by
    simpa using mem_sphere_iff_norm.mp hz
  exact fun hz0 ↦ (ne_of_gt hr0) <| by simpa [hz0] using hz_norm.symm

/-- Helper for Exercise 14: the contour integral of `z ^ k` on a positive circle detects exactly
the residue exponent `k = -1`. -/
lemma exercise14_circleIntegral_zpow_eq_residue
    {r : ℝ} (hr0 : 0 < r) (k : ℤ) :
    (∮ z in C(0, r), z ^ k) = if k = -1 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hk : k = -1
  · subst hk
    have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hr0
    rw [if_pos rfl]
    simpa using
      (circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := (0 : ℂ)) (R := r)
        hzero_mem)
  · rw [if_neg hk]
    simpa using
      (circleIntegral.integral_sub_zpow_of_ne hk (c := (0 : ℂ)) (w := (0 : ℂ)) (R := r))

/-- Helper for Exercise 14: on a positive-radius circle, a shifted Laurent term contributes only
when its combined exponent hits the residue value `-1`. -/
lemma exercise14_circleIntegral_shifted_laurent_term_eq_residue
    {a : ℤ → ℂ} {r : ℝ} (hr0 : 0 < r) (k m : ℤ) :
    (∮ z in C(0, r), z ^ k * laurentTerm a m z) =
      if k + m = -1 then (2 * Real.pi * Complex.I : ℂ) * a m else 0 := by
  have hcongr :
      (∮ z in C(0, r), z ^ k * laurentTerm a m z) =
        ∮ z in C(0, r), a m * z ^ (k + m) := by
    refine circleIntegral.integral_congr hr0.le ?_
    intro z hz
    have hz0 : z ≠ 0 := exercise14_ne_zero_of_mem_sphere_zero_of_pos hr0 hz
    -- Collapse the fixed shift and the Laurent monomial to a single `zpow`.
    calc
      z ^ k * laurentTerm a m z
        = z ^ k * (a m * z ^ m) := by simp [laurentTerm]
      _ = a m * (z ^ k * z ^ m) := by ac_rfl
      _ = a m * z ^ (k + m) := by rw [zpow_add₀ hz0]
  calc
    (∮ z in C(0, r), z ^ k * laurentTerm a m z)
      = ∮ z in C(0, r), a m * z ^ (k + m) := hcongr
    _ = a m * (∮ z in C(0, r), z ^ (k + m)) := by
          rw [circleIntegral.integral_const_mul]
    _ = a m * (if k + m = -1 then 2 * Real.pi * Complex.I else 0) := by
          rw [exercise14_circleIntegral_zpow_eq_residue hr0]
    _ = if k + m = -1 then (2 * Real.pi * Complex.I : ℂ) * a m else 0 := by
          by_cases hkm : k + m = -1
          · simp [hkm, mul_comm, mul_left_comm]
          · simp [hkm]

/-- Exercise 14 (1): a holomorphic `1`-periodic function on the upper half-plane descends along
`z ↦ exp (2 * π * I * z)` to a holomorphic function on the punctured unit disc. -/
theorem exists_holomorphicOnNhd_puncturedDisc_of_upper_half_plane_periodic
    {f : ℂ → ℂ} (hfhol : AnalyticOnNhd ℂ f ℍₒ)
    (hperiodic : ∀ z ∈ ℍₒ, f (z + 1) = f z) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) ∧
      Set.EqOn (fun z ↦ g (qParam (1 : ℝ) z)) f ℍₒ := by
  let fh : UpperHalfPlane → ℂ := fun τ ↦ f τ
  let F : ℂ → ℂ := fh ∘ UpperHalfPlane.ofComplex
  let g : ℂ → ℂ := Function.Periodic.cuspFunction (1 : ℝ) F
  have hperiodic_ofComplex : Function.Periodic F (1 : ℝ) := by
    intro z
    -- Adding a real period preserves the sign of the imaginary part, so `ofComplex` stays on the
    -- same branch and the hypothesis applies exactly on the upper-half-plane branch.
    by_cases hz : 0 < Complex.im z
    · have hz1 : 0 < Complex.im (z + 1) := by simpa using hz
      simpa [F, fh, UpperHalfPlane.ofComplex_apply_of_im_pos hz1,
        UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hperiodic z hz
    · have hz' : Complex.im z ≤ 0 := le_of_not_gt hz
      have hz1' : Complex.im (z + 1) ≤ 0 := by simpa using hz'
      exact congrArg fh (UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos hz1' hz')
  refine ⟨g, ?_, ?_⟩
  · have hdiff :
        DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) := by
      intro q hq
      have hqball : q ∈ Metric.ball (0 : ℂ) 1 := hq.1
      have hqnorm : ‖q‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hqball
      have hq0 : q ≠ 0 := hq.2
      have him :
          0 < Complex.im (Function.Periodic.invQParam (1 : ℝ) q) :=
        Function.Periodic.im_invQParam_pos_of_norm_lt_one Real.zero_lt_one hqnorm hq0
      let τ : UpperHalfPlane := ⟨Function.Periodic.invQParam (1 : ℝ) q, him⟩
      have hdiff_F :
          DifferentiableAt ℂ F (Function.Periodic.invQParam (1 : ℝ) q) := by
        have hnear :
            f =ᶠ[𝓝 (Function.Periodic.invQParam (1 : ℝ) q)] F := by
          -- Near an upper-half-plane point, `ofComplex` is the identity on the carrier.
          filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex him] with w hw
          simpa [F, fh] using congrArg f hw.symm
        exact (hfhol _ him).differentiableAt.congr_of_eventuallyEq hnear.symm
      have hdiff_cusp :
          DifferentiableAt ℂ g (Function.Periodic.qParam (1 : ℝ)
            (Function.Periodic.invQParam (1 : ℝ) q)) :=
        Function.Periodic.differentiableAt_cuspFunction
          (h := (1 : ℝ)) (f := F) one_ne_zero hperiodic_ofComplex hdiff_F
      -- The periodic `cuspFunction` is differentiable at every nonzero point of the punctured ball.
      simpa [g, Function.Periodic.qParam_right_inv one_ne_zero hq0] using
        hdiff_cusp.differentiableWithinAt
    have hopen : IsOpen (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) :=
      IsOpen.sdiff Metric.isOpen_ball isClosed_singleton
    -- On this open punctured disc, pointwise complex differentiability upgrades to analyticity.
    exact hdiff.analyticOnNhd hopen
  · intro z hz
    have hcusp :
        g (qParam (1 : ℝ) z) = F z :=
      Function.Periodic.eq_cuspFunction
        (h := (1 : ℝ)) (f := F) one_ne_zero hperiodic_ofComplex z
    -- On the upper half-plane, `ofComplex` is the identity, so the descended function recovers `f`.
    simpa [g, F, fh, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hcusp

/-- Exercise 14 (2): such a function admits a Fourier-Laurent expansion on the upper half-plane,
whose coefficients define a Laurent series on the punctured unit disc; the coefficients are given
by the horizontal-line integral formula, and the pulled-back series converges locally uniformly on
the upper half-plane. -/
theorem exists_upper_half_plane_fourier_laurent_expansion
    {f : ℂ → ℂ} (hfhol : AnalyticOnNhd ℂ f ℍₒ)
    (hperiodic : ∀ z ∈ ℍₒ, f (z + 1) = f z) :
    ∃ a : ℤ → ℂ,
      IsLaurentSeriesOnAnnulus a 0 1 ∧
      (∀ n : ℤ, ∀ y : ℝ, 0 < y →
        a n =
          ∫ x in (0 : ℝ)..1,
            f (x + y * Complex.I) *
              Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))) ∧
      Set.EqOn (fun z ↦ ∑' n : ℤ, a n * qParam (1 : ℝ) z ^ n) f ℍₒ ∧
      HasSumLocallyUniformlyOn
        (fun n z ↦ a n * qParam (1 : ℝ) z ^ n)
        (fun z ↦ ∑' n : ℤ, a n * qParam (1 : ℝ) z ^ n)
        ℍₒ := by
  -- Route correction: the source proof works on the weighted pullback Laurent series along the
  -- horizontal segment `x ↦ x + y * I`, not by adding another contour-reparametrization step.
  obtain ⟨g, hgAnalytic, hgq⟩ :=
    exists_holomorphicOnNhd_puncturedDisc_of_upper_half_plane_periodic hfhol hperiodic
  have hgAnn : AnalyticOnNhd ℂ g (complexOpenAnnulus 0 1) := by
    -- Rewrite the punctured unit disc from part (1) as the standard annulus `0 < ‖q‖ < 1`.
    simpa [punctured_unit_ball_eq_complexOpenAnnulus_zero_one] using hgAnalytic
  rcases hgAnn.hasLaurentExpansionOnAnnulus with ⟨a, ha, hgLaurent⟩
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · intro n y hy
    -- The coefficient formula is exactly the horizontal-line extraction lemma proved above.
    exact
      exercise14_coeff_eq_horizontal_integral_of_descended_annulus_expansion
        (ha := ha) (hgLaurent := hgLaurent) (hgq := hgq) n y hy
  · intro z hz
    have hzAnn : qParam (1 : ℝ) z ∈ complexOpenAnnulus 0 1 :=
      qParam_mem_complexOpenAnnulus_zero_one_of_mem_upper_half_plane hz
    -- Pull the annulus Laurent identity back along `qParam`, then use the descent equality.
    calc
      ∑' n : ℤ, a n * qParam (1 : ℝ) z ^ n = g (qParam (1 : ℝ) z) := by
        symm
        exact hgLaurent hzAnn
      _ = f z := hgq hz
  · -- The normal convergence statement is the annulus Laurent summation composed with `qParam`.
    exact hasSumLocallyUniformlyOn_qParam_pullback ha

/-- Helper for Exercise 14: on a horizontal line `z = x + y * I`, the norm of the `n`th Fourier
weight is the real exponential factor from the source estimate. -/
lemma exercise14_norm_fourier_weight_on_horizontal
    (n : ℤ) (x y : ℝ) :
    ‖Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))‖ =
      Real.exp (2 * Real.pi * (n : ℝ) * y) := by
  -- `Complex.norm_exp` reduces the claim to the real part of the exponent.
  rw [Complex.norm_exp]
  -- A direct computation shows that the real part is exactly `2 * π * n * y`.
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- Helper for Exercise 14: along the heights `max Y 1 + k`, the horizontal coefficient formula
and the eventual growth bound give the textbook coefficient estimate. -/
lemma exercise14_norm_coeff_le_growth_along_nat_shift
    {f : ℂ → ℂ} {a : ℤ → ℂ} {n n₀ : ℤ} {M Y : ℝ}
    (ha :
      ∀ n : ℤ, ∀ y : ℝ, 0 < y →
        a n =
          ∫ x in (0 : ℝ)..1,
            f (x + y * Complex.I) *
              Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)))
    (hY :
      ∀ ⦃y : ℝ⦄, Y ≤ y → ∀ x : ℝ,
        ‖f (x + y * Complex.I)‖ ≤ M * Real.exp ((2 * Real.pi * (n₀ : ℝ) * y) : ℝ)) :
    ∀ k : ℕ,
      ‖a n‖ ≤ M * Real.exp ((2 * Real.pi * (((n + n₀ : ℤ) : ℝ))) * (max Y 1 + k)) := by
  intro k
  let y : ℝ := max Y 1 + k
  have hk_nonneg : (0 : ℝ) ≤ k := by
    exact_mod_cast Nat.zero_le k
  have hy : 0 < y := by
    -- The chosen horizontal line lies above height `1`.
    dsimp [y]
    nlinarith [le_max_right Y 1, hk_nonneg]
  have hYy : Y ≤ y := by
    -- The same height also lies in the eventual-growth range.
    dsimp [y]
    nlinarith [le_max_left Y 1, hk_nonneg]
  calc
    ‖a n‖ =
        ‖∫ x in (0 : ℝ)..1,
          f (x + y * Complex.I) *
            Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))‖ := by
          rw [ha n y hy]
    _ ≤
        (M * Real.exp ((2 * Real.pi * (((n + n₀ : ℤ) : ℝ))) * y)) * |1 - 0| := by
          -- Bound the coefficient integral by a constant integrand norm on one horizontal period.
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ ?_
          have hfx := hY (y := y) hYy x
          have hweight_nonneg : 0 ≤ Real.exp (2 * Real.pi * (n : ℝ) * y) :=
            (Real.exp_pos _).le
          calc
            ‖f (x + y * Complex.I) *
                Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I))‖
                = ‖f (x + y * Complex.I)‖ * Real.exp (2 * Real.pi * (n : ℝ) * y) := by
                    rw [norm_mul, exercise14_norm_fourier_weight_on_horizontal]
            _ ≤
                (M * Real.exp (2 * Real.pi * (n₀ : ℝ) * y)) *
                  Real.exp (2 * Real.pi * (n : ℝ) * y) := by
                    exact mul_le_mul_of_nonneg_right hfx hweight_nonneg
            _ = M * Real.exp ((2 * Real.pi * (((n + n₀ : ℤ) : ℝ))) * y) := by
                  have hexp_add :
                      Real.exp (2 * Real.pi * (n₀ : ℝ) * y) *
                          Real.exp (2 * Real.pi * (n : ℝ) * y) =
                        Real.exp ((2 * Real.pi * (((n + n₀ : ℤ) : ℝ))) * y) := by
                    -- Combine the two real exponentials into the negative-frequency exponent.
                    rw [← Real.exp_add, Int.cast_add]
                    ring
                  calc
                    (M * Real.exp (2 * Real.pi * (n₀ : ℝ) * y)) *
                        Real.exp (2 * Real.pi * (n : ℝ) * y)
                        = M *
                            (Real.exp (2 * Real.pi * (n₀ : ℝ) * y) *
                              Real.exp (2 * Real.pi * (n : ℝ) * y)) := by ring
                    _ = M * Real.exp ((2 * Real.pi * (((n + n₀ : ℤ) : ℝ))) * y) := by
                      rw [hexp_add]
    _ = M * Real.exp ((2 * Real.pi * (((n + n₀ : ℤ) : ℝ))) * (max Y 1 + k)) := by
          simp [y]

/-- Helper for Exercise 14: a negative exponential factor along the heights `max Y 1 + k`
converges to `0`. -/
lemma exercise14_tendsto_negative_frequency_exponential_decay
    {c M Y : ℝ} (hc : c < 0) :
    Filter.Tendsto
      (fun k : ℕ ↦ M * Real.exp (c * (max Y 1 + k)))
      Filter.atTop
      (𝓝 0) := by
  have hshift :
      Filter.Tendsto (fun k : ℕ ↦ (max Y 1 : ℝ) + k) Filter.atTop Filter.atTop := by
    -- The chosen heights are just a constant shift of the natural numbers.
    simpa [add_comm] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (max Y 1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hnegc : 0 < -c := by
    linarith
  have hneg_scale :
      Filter.Tendsto (fun k : ℕ ↦ (-c) * ((max Y 1 : ℝ) + k)) Filter.atTop Filter.atTop :=
    hshift.const_mul_atTop hnegc
  have hlin :
      Filter.Tendsto (fun k : ℕ ↦ c * (max Y 1 + k)) Filter.atTop Filter.atBot := by
    -- Negating the positive multiple converts the `atTop` limit into an `atBot` limit.
    have hneg :
        Filter.Tendsto (fun k : ℕ ↦ -(c * (max Y 1 + k))) Filter.atTop Filter.atTop := by
      simpa [neg_mul, add_comm] using hneg_scale
    simpa using (Filter.tendsto_neg_atBot_iff.2 hneg)
  -- Compose the affine `atBot` limit with `exp`, then restore the fixed coefficient `M`.
  simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul M

/-- Exercise 14 (3): if the periodic holomorphic function has eventual growth bounded by
`exp (2 * π * n₀ * y)` along horizontal lines, then every Fourier coefficient below `-n₀`
vanishes. -/
theorem fourier_laurent_coeff_eq_zero_of_eventual_exponential_growth
    {f : ℂ → ℂ} {a : ℤ → ℂ} {n₀ : ℤ} {M : ℝ}
    (ha :
      ∀ n : ℤ, ∀ y : ℝ, 0 < y →
        a n =
          ∫ x in (0 : ℝ)..1,
            f (x + y * Complex.I) *
              Complex.exp (-2 * π * Complex.I * (n : ℂ) * (x + y * Complex.I)))
    (hgrowth :
      ∃ Y : ℝ,
        ∀ ⦃y : ℝ⦄, Y ≤ y → ∀ x : ℝ,
          ‖f (x + y * Complex.I)‖ ≤ M * Real.exp ((2 * Real.pi * (n₀ : ℝ) * y) : ℝ)) :
    ∀ n : ℤ, n < -n₀ → a n = 0 := by
  -- Route correction: this remains the direct source estimate from the horizontal coefficient
  -- formula, after theorem (2) supplies the missing integral-to-coefficient bridge.
  intro n hn
  rcases hgrowth with ⟨Y, hY⟩
  have hM : 0 ≤ M := by
    -- Evaluate the eventual bound at one admissible height to recover the necessary sign of `M`.
    have hbound :=
      hY (y := max Y 1) (le_max_left Y 1) 0
    have hnonneg_rhs :
        0 ≤ M * Real.exp ((2 * Real.pi * (n₀ : ℝ) * max Y 1) : ℝ) := by
      exact le_trans (norm_nonneg (f (0 + max Y 1 * Complex.I))) hbound
    have hnonneg_rhs' :
        0 ≤ Real.exp ((2 * Real.pi * (n₀ : ℝ) * max Y 1) : ℝ) * M := by
      simpa [mul_comm] using hnonneg_rhs
    exact nonneg_of_mul_nonneg_right hnonneg_rhs' (Real.exp_pos _)
  let c : ℝ := 2 * Real.pi * (((n + n₀ : ℤ) : ℝ))
  have hsum_neg : n + n₀ < 0 := by
    -- Moving `n₀` to the left side shows the combined frequency is negative.
    simpa using Int.add_lt_add_right hn n₀
  have hc : c < 0 := by
    have hcast_neg : (((n + n₀ : ℤ) : ℝ)) < 0 := by
      exact_mod_cast hsum_neg
    dsimp [c]
    exact mul_neg_of_pos_of_neg (by positivity) hcast_neg
  have hbound_coeff :
      ∀ k : ℕ,
        ‖a n‖ ≤ M * Real.exp (c * (max Y 1 + k)) := by
    -- The coefficient formula plus the eventual growth hypothesis give the exact source bound.
    simpa [c] using
      exercise14_norm_coeff_le_growth_along_nat_shift
        (ha := ha) (hY := hY) (n := n) (n₀ := n₀)
  have hdecay :
      Filter.Tendsto (fun k : ℕ ↦ M * Real.exp (c * (max Y 1 + k))) Filter.atTop (𝓝 0) :=
    exercise14_tendsto_negative_frequency_exponential_decay (c := c) (M := M) (Y := Y) hc
  by_contra hne
  have hpos : 0 < ‖a n‖ := norm_pos_iff.mpr hne
  let ε : ℝ := ‖a n‖ / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hsmall := Metric.tendsto_nhds.mp hdecay ε hε
  rcases Filter.eventually_atTop.1 hsmall with ⟨k, hk⟩
  have hexp_nonneg : 0 ≤ Real.exp (c * (max Y 1 + k)) := (Real.exp_pos _).le
  have hseq_nonneg : 0 ≤ M * Real.exp (c * (max Y 1 + k)) := by
    exact mul_nonneg hM hexp_nonneg
  have hlt :
      M * Real.exp (c * (max Y 1 + k)) < ε := by
    -- The decay estimate eventually makes the bound smaller than `‖a n‖ / 2`.
    have hlt_abs :
        |M * Real.exp (c * (max Y 1 + k))| < ε := by
      simpa [dist_eq_norm, Real.norm_eq_abs, ε] using hk k le_rfl
    simpa [abs_of_nonneg hseq_nonneg] using hlt_abs
  have hhalf_lt : ε < ‖a n‖ := by
    dsimp [ε]
    linarith
  have : ‖a n‖ < ‖a n‖ := by
    calc
      ‖a n‖ ≤ M * Real.exp (c * (max Y 1 + k)) := hbound_coeff k
      _ < ε := hlt
      _ < ‖a n‖ := hhalf_lt
  exact (lt_irrefl _ this)
