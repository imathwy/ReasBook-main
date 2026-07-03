import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex
open Filter
open Set
open UpperHalfPlane
open scoped Real Topology

noncomputable section

-- Semantic recall note: `lean_leansearch` was unavailable in this session; local mathlib recall
-- used `Mathlib/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean`, with the proposition
-- here organized as a bridge from the chapter owner `integer_square_pole_series` to the upstream
-- cotangent-series closed form on `Complex.integerComplement`.

/-- Helper for Proposition 2.1: the `n`-th summand in the integer square-pole series. -/
def integer_square_pole_series_term (n : ℤ) (z : ℂ) : ℂ :=
  1 / (z - (n : ℂ)) ^ (2 : ℕ)

/-- Helper for Proposition 2.1: the chapter square-pole series obtained by summing over all
integers. -/
def integer_square_pole_series (z : ℂ) : ℂ :=
  ∑' n : ℤ, integer_square_pole_series_term n z

/-- Helper for Proposition 2.1: reindexing by negation rewrites the chapter series into the
canonical `z + n` form used by mathlib's cotangent expansion. -/
lemma integer_square_pole_series_eq_tsum_add_int {z : ℂ} :
    integer_square_pole_series z = ∑' n : ℤ, 1 / (z + (n : ℂ)) ^ (2 : ℕ) := by
  -- Reindex the integer sum by `n ↦ -n` to match the cotangent-series normalization.
  rw [integer_square_pole_series]
  conv_lhs => rw [← Equiv.tsum_eq (Equiv.neg ℤ)]
  refine tsum_congr fun n ↦ ?_
  simp [integer_square_pole_series_term, sub_eq_add_neg]

/-- Helper for Proposition 2.1: the comparison series `∑ 4 / |n|²` is summable on `ℤ`. -/
private lemma summable_integer_square_majorant :
    Summable (fun n : ℤ ↦ 4 * (‖(n : ℂ)‖ ^ 2)⁻¹) := by
  -- Reduce to the standard square-decay `ℤ`-summability theorem from Eisenstein-series API.
  have hbase :
      Summable (fun n : ℤ ↦ (‖(n : ℂ)‖ ^ 2)⁻¹) := by
    have hsummable :
        Summable (fun n : ℤ ↦ ‖(((0 : ℤ) * (0 : ℂ) + n) ^ (2 : ℤ))⁻¹‖) := by
      simpa using
        (EisensteinSeries.linear_right_summable (0 : ℂ) (0 : ℤ) (k := (2 : ℤ))
          (by norm_num)).norm
    refine hsummable.congr ?_
    intro n
    simp [norm_inv, zpow_ofNat, norm_pow]
  exact hbase.mul_left 4

/-- Helper for Proposition 2.1: once the pole index `n` is at least twice as far from the origin
as `z`, the `n`-th summand is bounded by the square-decay majorant. -/
private lemma integer_square_pole_series_term_norm_le_majorant {R : ℝ} {z : ℂ} {n : ℤ}
    (hz : ‖z‖ ≤ R) (hn : 2 * R ≤ ‖(n : ℂ)‖) :
    ‖integer_square_pole_series_term n z‖ ≤ 4 * (‖(n : ℂ)‖ ^ 2)⁻¹ := by
  by_cases hnzero : n = 0
  · -- If `n = 0`, the size condition forces `R = 0`, hence also `z = 0`.
    have hRnonneg : 0 ≤ R := le_trans (norm_nonneg z) hz
    have hn' : 2 * R ≤ 0 := by
      simpa [hnzero] using hn
    have hRle : R ≤ 0 := by
      linarith
    have hRzero : R = 0 := le_antisymm hRle hRnonneg
    have hzzero : z = 0 := by
      apply norm_eq_zero.mp
      rw [hRzero] at hz
      exact le_antisymm hz (norm_nonneg _)
    simp [integer_square_pole_series_term, hnzero, hzzero]
  -- The reverse triangle inequality gives the denominator bound `‖z - n‖ ≥ ‖n‖ / 2`.
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
    -- Rewrite the term norm into an inverse squared distance.
    simp [integer_square_pole_series_term, norm_inv, norm_pow]
  have hsq : (‖(n : ℂ)‖ / 2) ^ 2 ≤ ‖z - (n : ℂ)‖ ^ 2 := by
    gcongr
  have hnorm_pos : 0 < ‖(n : ℂ)‖ := by
    exact norm_pos_iff.mpr (by simpa using hnzero)
  have hhalf_pos : 0 < (‖(n : ℂ)‖ / 2) ^ 2 := by
    positivity
  have hterm_pos : 0 < ‖z - (n : ℂ)‖ ^ 2 := by
    have hhalf_pos : 0 < ‖(n : ℂ)‖ / 2 := by
      positivity
    have : 0 < ‖z - (n : ℂ)‖ := by
      exact lt_of_lt_of_le hhalf_pos hlower
    positivity
  have hinv : (‖z - (n : ℂ)‖ ^ 2)⁻¹ ≤ ((‖(n : ℂ)‖ / 2) ^ 2)⁻¹ := by
    exact (inv_le_inv₀ hterm_pos hhalf_pos).2 hsq
  have hcalc : ((‖(n : ℂ)‖ / 2) ^ 2)⁻¹ = 4 * (‖(n : ℂ)‖ ^ 2)⁻¹ := by
    have hnorm_ne : ‖(n : ℂ)‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (by simpa using hnzero)
    field_simp [pow_two, hnorm_ne]
    ring
  calc
    ‖integer_square_pole_series_term n z‖ = (‖z - (n : ℂ)‖ ^ 2)⁻¹ := hterm
    _ ≤ ((‖(n : ℂ)‖ / 2) ^ 2)⁻¹ := hinv
    _ = 4 * (‖(n : ℂ)‖ ^ 2)⁻¹ := hcalc

/-- Helper for Proposition 2.1: the square-pole family is summable locally uniformly away from the
integers. -/
lemma integer_square_pole_series_summableLocallyUniformlyOn :
    SummableLocallyUniformlyOn integer_square_pole_series_term integerComplement := by
  -- Compact subsets of `integerComplement` are norm-bounded, so sufficiently far poles admit a
  -- uniform `1 / |n|²` majorant on the whole compact set.
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (by simpa [Complex.integerComplement] using Complex.isOpen_compl_range_intCast)
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  refine ⟨fun n : ℤ ↦ 4 * (‖(n : ℂ)‖ ^ 2)⁻¹, summable_integer_square_majorant, ?_⟩
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

/-- Helper for Proposition 2.1: the complement of the integers in `ℂ` is preconnected. -/
lemma integer_complement_is_preconnected : IsPreconnected (integerComplement : Set ℂ) := by
  -- The integer complement is the complement of a countable set in a real vector space of rank `2`.
  have hcount : (Set.range ((↑) : ℤ → ℂ)).Countable := Set.countable_range _
  have hpath : IsPathConnected (((Set.range ((↑) : ℤ → ℂ))ᶜ : Set ℂ)) :=
    hcount.isPathConnected_compl_of_one_lt_rank (by
      simp only [Complex.rank_real_complex, Nat.one_lt_ofNat])
  simpa [Complex.integerComplement] using hpath.isConnected.isPreconnected

/-- Helper for Proposition 2.1: the explicit coercion of `Real.pi` agrees with the complex scalar
written as `π`. -/
private lemma complex_ofReal_pi : ((Real.pi : ℝ) : ℂ) = (π : ℂ) := by
  -- Compare real and imaginary parts directly.
  apply Complex.ext <;> simp

/-- Helper for Proposition 2.1: the integer square-pole series is analytic away from the
integers. -/
lemma integer_square_pole_series_analytic_on_nhd :
    AnalyticOnNhd ℂ integer_square_pole_series integerComplement := by
  -- The locally uniformly summable series of differentiable summands is differentiable termwise.
  refine DifferentiableOn.analyticOnNhd
    (integer_square_pole_series_summableLocallyUniformlyOn.differentiableOn
      Complex.isOpen_compl_range_intCast ?_) Complex.isOpen_compl_range_intCast
  intro n r hr
  have hrn : r - (n : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hr (-(n : ℤ))
  have hrn_sq : (r - (n : ℂ)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hrn
  have hpow : DifferentiableAt ℂ (fun z : ℂ ↦ (z - (n : ℂ)) ^ (2 : ℕ)) r := by
    fun_prop
  have hterm :
      integer_square_pole_series_term n = fun z : ℂ ↦ ((z - (n : ℂ)) ^ (2 : ℕ))⁻¹ := by
    funext z
    simp [integer_square_pole_series_term, div_eq_mul_inv]
  -- Each summand is a rational function with nonvanishing denominator on `integerComplement`.
  rw [hterm]
  exact hpow.inv hrn_sq

/-- Helper for Proposition 2.1: the derivative of `π cot (π z)` is `-(π / sin (π z))²` away from
the integers. -/
lemma deriv_pi_mul_cot_pi_eq_neg_pi_sq_div_sin_sq {z : ℂ}
    (hz : z ∈ integerComplement) :
    deriv (fun w : ℂ ↦ π * cot (π * w)) z = -((π / sin (π * z)) ^ (2 : ℕ)) := by
  have hpi : ((Real.pi : ℝ) : ℂ) = (π : ℂ) := complex_ofReal_pi
  have hsin : Complex.sin (π * z) ≠ 0 := by
    simpa [hpi] using (sin_pi_mul_ne_zero (x := z) hz)
  have hcos_fun : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.cos (π * w)) z := by
    exact ((Complex.hasDerivAt_cos (π * z)).comp z (hasDerivAt_const_mul (π : ℂ))).differentiableAt
  have hsin_fun : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.sin (π * w)) z := by
    exact ((Complex.hasDerivAt_sin (π * z)).comp z (hasDerivAt_const_mul (π : ℂ))).differentiableAt
  have hquot_deriv :
      deriv (fun w : ℂ ↦ Complex.cos (π * w) / Complex.sin (π * w)) z =
        (deriv (fun w : ℂ ↦ Complex.cos (π * w)) z * Complex.sin (π * z) -
          Complex.cos (π * z) * deriv (fun w : ℂ ↦ Complex.sin (π * w)) z) /
          Complex.sin (π * z) ^ (2 : ℕ) := by
    simpa only [Pi.div_apply] using
      (deriv_div hcos_fun hsin_fun hsin :
        deriv ((fun w : ℂ ↦ Complex.cos (π * w)) / fun w : ℂ ↦ Complex.sin (π * w)) z =
          (deriv (fun w : ℂ ↦ Complex.cos (π * w)) z * (fun w : ℂ ↦ Complex.sin (π * w)) z -
            (fun w : ℂ ↦ Complex.cos (π * w)) z * deriv (fun w : ℂ ↦ Complex.sin (π * w)) z) /
            ((fun w : ℂ ↦ Complex.sin (π * w)) z) ^ (2 : ℕ))
  have hcos_deriv :
      deriv (fun w : ℂ ↦ Complex.cos (π * w)) z = -(Complex.sin (π * z) * π) := by
    -- Differentiate the cosine term by the chain rule.
    simpa using ((Complex.hasDerivAt_cos (π * z)).comp z (hasDerivAt_const_mul (π : ℂ))).deriv
  have hsin_deriv :
      deriv (fun w : ℂ ↦ Complex.sin (π * w)) z = Complex.cos (π * z) * π := by
    -- Differentiate the sine term by the chain rule.
    simpa using ((Complex.hasDerivAt_sin (π * z)).comp z (hasDerivAt_const_mul (π : ℂ))).deriv
  -- Rewrite `cot` as `cos / sin`, apply the quotient rule, and simplify using `sin² + cos² = 1`.
  calc
    deriv (fun w : ℂ ↦ π * cot (π * w)) z
        = π * deriv (fun w : ℂ ↦ Complex.cos (π * w) / Complex.sin (π * w)) z := by
            simp [Complex.cot, deriv_const_mul_field]
    _ = π * (((deriv fun w : ℂ ↦ Complex.cos (π * w)) z * Complex.sin (π * z) -
          Complex.cos (π * z) * deriv (fun w : ℂ ↦ Complex.sin (π * w)) z) /
          Complex.sin (π * z) ^ (2 : ℕ)) := by
            rw [hquot_deriv]
    _ = π * (((-(Complex.sin (π * z) * π)) * Complex.sin (π * z) -
          Complex.cos (π * z) * (Complex.cos (π * z) * π)) /
          Complex.sin (π * z) ^ (2 : ℕ)) := by
            rw [hcos_deriv, hsin_deriv]
    _ = -((π / sin (π * z)) ^ (2 : ℕ)) := by
            field_simp [hsin]
            have htrig :
                -Complex.sin (π * z) ^ (2 : ℕ) - Complex.cos (π * z) ^ (2 : ℕ) =
                  -(Complex.sin (π * z) ^ (2 : ℕ) + Complex.cos (π * z) ^ (2 : ℕ)) := by
              ring
            rw [htrig, sin_sq_add_cos_sq]

/-- Helper for Proposition 2.1: on the upper half-plane, the integer square-pole series matches
the squared cosecant closed form. -/
lemma integer_square_pole_series_eq_pi_sq_div_sin_sq_on_upper_half_plane :
    EqOn integer_square_pole_series
      (fun z ↦ (π / sin (π * z)) ^ (2 : ℕ))
      UpperHalfPlane.upperHalfPlaneSet := by
  intro z hz
  have hz_int : z ∈ integerComplement := UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩
  have hderiv_series :
      deriv (fun w : ℂ ↦ π * cot (π * w)) z = -integer_square_pole_series z := by
    -- Specializing the cotangent derivative series at `k = 1` identifies the derivative with
    -- minus the reindexed square-pole series.
    have hupper :
        ((Real.pi : ℝ) : ℂ) *
            derivWithin (fun w : ℂ ↦ (((Real.pi : ℝ) : ℂ) * w).cot)
              UpperHalfPlane.upperHalfPlaneSet z =
          -∑' n : ℤ, 1 / (z + n) ^ (2 : ℕ) := by
      simpa using
        iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) (by norm_num) hz
    calc
      deriv (fun w : ℂ ↦ π * cot (π * w)) z
          = ((Real.pi : ℝ) : ℂ) *
              derivWithin (fun w : ℂ ↦ (((Real.pi : ℝ) : ℂ) * w).cot)
                UpperHalfPlane.upperHalfPlaneSet z := by
              rw [deriv_const_mul_field]
              rw [← derivWithin_of_isOpen isOpen_upperHalfPlaneSet hz]
      _ = -∑' n : ℤ, 1 / (z + n) ^ (2 : ℕ) := hupper
      _ = -integer_square_pole_series z := by
            rw [integer_square_pole_series_eq_tsum_add_int]
  -- Negating both derivative identities isolates the desired closed form.
  calc
    integer_square_pole_series z = -deriv (fun w : ℂ ↦ π * cot (π * w)) z := by
      simpa [eq_comm] using congrArg Neg.neg hderiv_series
    _ = (π / sin (π * z)) ^ (2 : ℕ) := by
      simpa using congrArg Neg.neg (deriv_pi_mul_cot_pi_eq_neg_pi_sq_div_sin_sq hz_int)

/-- Proposition 2.1: away from the integers, the integer square-pole series from Example 2 is
`(π / sin (π z))²`. -/
theorem integer_square_pole_series_eq_pi_sq_div_sin_sq {z : ℂ}
    (hz : z ∈ integerComplement) :
    integer_square_pole_series z = (π / sin (π * z)) ^ (2 : ℕ) := by
  have hright :
      AnalyticOnNhd ℂ (fun w : ℂ ↦ (π / sin (π * w)) ^ (2 : ℕ)) integerComplement := by
    -- The closed form is analytic away from the integer zeros of `sin (π z)`.
    refine DifferentiableOn.analyticOnNhd ?_ Complex.isOpen_compl_range_intCast
    intro w hw
    have hpi : ((Real.pi : ℝ) : ℂ) = (π : ℂ) := complex_ofReal_pi
    have hsin : Complex.sin (π * w) ≠ 0 := by
      simpa [hpi] using (sin_pi_mul_ne_zero (x := w) hw)
    have hsin_fun_at : DifferentiableAt ℂ (fun t : ℂ ↦ Complex.sin (π * t)) w := by
      exact
        ((Complex.hasDerivAt_sin (π * w)).comp w
          (hasDerivAt_const_mul (π : ℂ))).differentiableAt
    have hsin_fun :
        DifferentiableWithinAt ℂ (fun t : ℂ ↦ Complex.sin (π * t)) integerComplement w := by
      exact hsin_fun_at.differentiableWithinAt
    have hquot :
        DifferentiableWithinAt ℂ (fun t : ℂ ↦ π / Complex.sin (π * t)) integerComplement w := by
      exact (differentiableWithinAt_const (π : ℂ)).div hsin_fun hsin
    exact hquot.pow 2
  have hI_upper : (Complex.I : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simp
  have hI_mem : (Complex.I : ℂ) ∈ integerComplement := by
    simpa using (UpperHalfPlane.coe_mem_integerComplement ⟨Complex.I, hI_upper⟩)
  have hEventually :
      integer_square_pole_series =ᶠ[𝓝 Complex.I]
        (fun w : ℂ ↦ (π / sin (π * w)) ^ (2 : ℕ)) := by
    -- The upper half-plane identity yields equality on a neighborhood of `I`.
    exact integer_square_pole_series_eq_pi_sq_div_sin_sq_on_upper_half_plane.eventuallyEq_of_mem
      (isOpen_upperHalfPlaneSet.mem_nhds hI_upper)
  -- Analytic continuation extends the upper half-plane identity to all of `integerComplement`.
  exact
    (integer_square_pole_series_analytic_on_nhd.eqOn_of_preconnected_of_eventuallyEq
      hright integer_complement_is_preconnected hI_mem hEventually) hz
