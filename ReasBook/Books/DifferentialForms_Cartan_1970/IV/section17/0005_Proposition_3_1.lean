import cartan.IV.section17.«0003_Proposition_2_1»
import cartan.I.section02.«0015_Proposition_I_2_extra_8»
import cartan.IV.section13.«0005_Proposition_2_2»
import cartan.IV.section13.«0006_Lemma_IV_1_extra_4»

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
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere_nat
    {F : ℕ → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ n, ContinuousOn (F n) (Metric.sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (Metric.sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' n : ℕ, F n z) = ∑' n : ℕ, ∮ z in C(0, (R : ℝ)), F n z := by
  have hhas :
      HasSumUniformlyOn F (fun z ↦ ∑' n : ℕ, F n z) (Metric.sphere (0 : ℂ) (R : ℝ)) :=
    hsum.hasSumUniformlyOn
  have hcont_partial :
      ∀ s : Finset ℕ,
        ContinuousOn (fun z : ℂ ↦ ∑ n ∈ s, F n z) (Metric.sphere (0 : ℂ) (R : ℝ)) := by
    -- Finite partial sums preserve continuity on the boundary circle.
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
    · intro n s hn hs
      simpa [Finset.sum_insert, hn] using (hcont n).add hs
  have htendsto :
      Filter.Tendsto (fun s : Finset ℕ ↦ ∮ z in C(0, (R : ℝ)), ∑ n ∈ s, F n z) Filter.atTop
        (𝓝 (∮ z in C(0, (R : ℝ)), ∑' n : ℕ, F n z)) :=
    hhas.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn R.2
      (Filter.Eventually.of_forall hcont_partial)
  have hsum_int :
      HasSum (fun n : ℕ ↦ ∮ z in C(0, (R : ℝ)), F n z)
        (∮ z in C(0, (R : ℝ)), ∑' n : ℕ, F n z) := by
    rw [HasSum]
    convert htendsto using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun n _ ↦ (hcont n).circleIntegrable R.2
  exact hsum_int.tsum_eq.symm

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

/-- Helper for Proposition 3.1: on every smaller closed bidisc, the iterated Cauchy formula from
Proposition 2.1 expands into the nested series of Cauchy coefficients `(3.3)`. -/
lemma cauchy_local_double_series_eq_on_closed_bidisc
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ R₁ R₂ r₁ r₂ : ℝ} {z : ℂ × ℂ}
    (hR₁_pos : 0 < R₁) (hR₁ρ₁ : R₁ < ρ₁) (hR₂_pos : 0 < R₂) (hR₂ρ₂ : R₂ < ρ₂)
    (hr₁_nonneg : 0 ≤ r₁) (hr₁R₁ : r₁ < R₁) (hr₂_nonneg : 0 ≤ r₂) (hr₂R₂ : r₂ < R₂)
    (hz₁ : ‖z.1‖ ≤ r₁) (hz₂ : ‖z.2‖ ≤ r₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    f z = ∑' p : ℕ, ∑' q : ℕ, bidisc_cauchy_coefficient f R₁ R₂ p q * z.1 ^ p * z.2 ^ q := by
  -- Route correction: this helper should follow the source proof literally by commuting the
  -- inner `q`-series through the inner circle integral first, then the outer `p`-series.
  -- TODO: start from `cauchy_integral_formula_two_variables_on_bidisc` with radii `R₁,R₂`,
  -- expand each scalar kernel by `geometric_cauchy_kernel_tsum_of_norm_lt`, and use
  -- `circleIntegral_tsum_of_summableUniformlyOn_sphere_nat` twice before collecting terms into
  -- `bidisc_cauchy_coefficient`.
  sorry

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
  -- Route correction: the uniqueness step is the scalar argument from the source, applied twice.
  -- TODO: compare the two row-generating series on a common smaller bidisc, use
  -- `coeffs_eq_of_hasFPowerSeriesAt_zero` in the `z₁`-variable, and then repeat in the `z₂`
  -- variable to identify each coefficient.
  sorry

/-- Proposition 3.1: if `f` is holomorphic on the bidisc `‖z₁‖ < ρ₁`, `‖z₂‖ < ρ₂`, equivalently
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
