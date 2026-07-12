import Mathlib
import DifferentialForms_Cartan_1970.I.section04.«0031_Exercise_16»
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0027_Remark_II_1_extra_17»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.II.section06.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.III.section10.«0006_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.III.section10.«0009_Theorem_III_4_extra_7»
import DifferentialForms_Cartan_1970.III.section10.«0010_Remark_III_4_extra_8»
import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.ImageNormalization

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: comparing a complex number to
the bisector `Re w = 1 / 2` is equivalent to comparing the two lens radii `‖w‖` and `‖1 - w‖`. -/
lemma norm_le_norm_one_sub_iff_realPart_le_half {w : ℂ} :
    ‖w‖ ≤ ‖1 - w‖ ↔ w.re ≤ (1 : ℝ) / 2 := by
  have hsquare : ‖w‖ ^ 2 ≤ ‖1 - w‖ ^ 2 ↔ w.re ≤ (1 : ℝ) / 2 := by
    have hsub : ‖(1 : ℂ) - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
      -- Expand the squared distance from `w` to `1` once and solve the resulting affine
      -- inequality on `w.re`.
      simpa using (norm_sub_sq (𝕜 := ℂ) (1 : ℂ) w)
    constructor
    · intro h
      rw [hsub] at h
      linarith
    · intro h
      rw [hsub]
      linarith
  constructor
  · intro h
    -- Square the nonnegative norms to move to the explicit affine inequality on `w.re`.
    exact hsquare.mp (by nlinarith [h, norm_nonneg w, norm_nonneg (1 - w)])
  · intro h
    -- Unsquare the already nonnegative norms after solving the affine inequality.
    have hsq : ‖w‖ ^ 2 ≤ ‖1 - w‖ ^ 2 := hsquare.mpr h
    nlinarith [norm_nonneg w, norm_nonneg (1 - w), hsq]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the reversed radius comparison
is the complementary bisector inequality `1 / 2 ≤ Re w`. -/
lemma norm_one_sub_le_norm_iff_half_le_realPart {w : ℂ} :
    ‖1 - w‖ ≤ ‖w‖ ↔ (1 : ℝ) / 2 ≤ w.re := by
  have hsquare : ‖1 - w‖ ^ 2 ≤ ‖w‖ ^ 2 ↔ (1 : ℝ) / 2 ≤ w.re := by
    have hsub : ‖(1 : ℂ) - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
      -- Reuse the same expansion, but now solve the reversed inequality.
      simpa using (norm_sub_sq (𝕜 := ℂ) (1 : ℂ) w)
    constructor
    · intro h
      rw [hsub] at h
      linarith
    · intro h
      rw [hsub]
      linarith
  constructor
  · intro h
    -- Square the nonnegative norms before reading off the sign of `Re w - 1 / 2`.
    exact hsquare.mp (by nlinarith [h, norm_nonneg w, norm_nonneg (1 - w)])
  · intro h
    -- The squared comparison is enough because both norms are nonnegative.
    have hsq : ‖1 - w‖ ^ 2 ≤ ‖w‖ ^ 2 := hsquare.mpr h
    nlinarith [norm_nonneg w, norm_nonneg (1 - w), hsq]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the selector
`Real.log ‖w / (1 - w)‖` is nonpositive exactly on the left cap `Re w ≤ 1 / 2`. -/
lemma selectorNonpos_iff_realPart_le_half {w : ℂ} (_hw0 : w ≠ 0) (h1w : 1 - w ≠ 0) :
    Real.log ‖w / (1 - w)‖ ≤ 0 ↔ w.re ≤ (1 : ℝ) / 2 := by
  -- Rewrite the nonpositive logarithm condition as the direct radius comparison.
  rw [Real.log_nonpos_iff (norm_nonneg _), norm_div, div_le_one₀ (norm_pos_iff.mpr h1w)]
  exact norm_le_norm_one_sub_iff_realPart_le_half

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the selector
`Real.log ‖w / (1 - w)‖` is nonnegative exactly on the right cap `1 / 2 ≤ Re w`. -/
lemma selectorNonneg_iff_half_le_realPart {w : ℂ} (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0) :
    0 ≤ Real.log ‖w / (1 - w)‖ ↔ (1 : ℝ) / 2 ≤ w.re := by
  -- Rewrite the nonnegative logarithm condition as the reversed radius comparison.
  rw [Real.log_nonneg_iff (norm_pos_iff.mpr (div_ne_zero hw0 h1w)), norm_div,
    one_le_div₀ (norm_pos_iff.mpr h1w)]
  exact norm_one_sub_le_norm_iff_half_le_realPart

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the selector vanishes exactly
on the bisector `Re w = 1 / 2`. -/
lemma selectorEqZero_iff_realPart_eq_half {w : ℂ} (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0) :
    Real.log ‖w / (1 - w)‖ = 0 ↔ w.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    -- A zero selector is both nonpositive and nonnegative, so both cap inequalities hold.
    have hle : w.re ≤ (1 : ℝ) / 2 := by
      exact (selectorNonpos_iff_realPart_le_half hw0 h1w).mp <| by rw [h]
    have hge : (1 : ℝ) / 2 ≤ w.re := by
      exact (selectorNonneg_iff_half_le_realPart hw0 h1w).mp <| by rw [h]
    linarith
  · intro h
    -- Conversely the bisector point satisfies both sign tests, hence the selector is zero.
    apply le_antisymm
    · exact (selectorNonpos_iff_realPart_le_half hw0 h1w).2 <| by linarith [h]
    · exact (selectorNonneg_iff_half_le_realPart hw0 h1w).2 <| by linarith [h]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: outside the Exercise-16 lens,
remaining inside the unit ball around `0` forces the left-cap inequality `Re w ≤ 1 / 2`. -/
lemma realPart_le_half_of_norm_lt_one_of_not_mem_exercise16Domain {w : ℂ}
    (hw_norm_lt : ‖w‖ < 1) (hw_not_mem : w ∉ exercise16Domain) :
    w.re ≤ (1 : ℝ) / 2 := by
  have hone_sub_not_lt : ¬ ‖1 - w‖ < 1 := by
    -- If both radii were below `1`, the point would lie in the Exercise-16 lens after all.
    intro hone_sub_norm_lt
    apply hw_not_mem
    refine ⟨?_, ?_⟩
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hw_norm_lt
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using
        hone_sub_norm_lt
  have hone_sub_ge_one : 1 ≤ ‖1 - w‖ := by
    linarith
  -- Compare the two radii and translate the inequality back to the bisector geometry.
  exact norm_le_norm_one_sub_iff_realPart_le_half.mp <|
    le_trans (le_of_lt hw_norm_lt) hone_sub_ge_one

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: outside the Exercise-16 lens,
remaining inside the unit ball around `1` forces the right-cap inequality `1 / 2 ≤ Re w`. -/
lemma half_le_realPart_of_norm_one_sub_lt_one_of_not_mem_exercise16Domain {w : ℂ}
    (hone_sub_norm_lt : ‖1 - w‖ < 1) (hw_not_mem : w ∉ exercise16Domain) :
    (1 : ℝ) / 2 ≤ w.re := by
  have hw_not_lt : ¬ ‖w‖ < 1 := by
    -- If both radii were below `1`, the point would again lie inside the lens.
    intro hw_norm_lt
    apply hw_not_mem
    refine ⟨?_, ?_⟩
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hw_norm_lt
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using
        hone_sub_norm_lt
  have hw_ge_one : 1 ≤ ‖w‖ := by
    linarith
  -- The reversed radius comparison is the right-cap bisector inequality.
  exact norm_one_sub_le_norm_iff_half_le_realPart.mp <|
    le_trans (le_of_lt hone_sub_norm_lt) hw_ge_one

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: outside the Exercise-16 lens,
if `‖w‖ < 1`, then the selector is already nonpositive. -/
lemma selectorNonpos_of_norm_lt_one_of_not_mem_exercise16Domain {w : ℂ}
    (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0)
    (hw_norm_lt : ‖w‖ < 1) (hw_not_mem : w ∉ exercise16Domain) :
    Real.log ‖w / (1 - w)‖ ≤ 0 := by
  -- Reduce the selector sign to the left-cap geometry supplied by the failed lens membership.
  exact (selectorNonpos_iff_realPart_le_half hw0 h1w).2 <|
    realPart_le_half_of_norm_lt_one_of_not_mem_exercise16Domain hw_norm_lt hw_not_mem

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: outside the Exercise-16 lens,
if `‖1 - w‖ < 1`, then the selector is already nonnegative. -/
lemma selectorNonneg_of_norm_one_sub_lt_one_of_not_mem_exercise16Domain {w : ℂ}
    (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0)
    (hone_sub_norm_lt : ‖1 - w‖ < 1) (hw_not_mem : w ∉ exercise16Domain) :
    0 ≤ Real.log ‖w / (1 - w)‖ := by
  -- Reduce the selector sign to the right-cap geometry supplied by the failed lens membership.
  exact (selectorNonneg_iff_half_le_realPart hw0 h1w).2 <|
    half_le_realPart_of_norm_one_sub_lt_one_of_not_mem_exercise16Domain
      hone_sub_norm_lt hw_not_mem

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a continuous real-valued
function on a preconnected set either has a zero or keeps one strict sign. -/
lemma zeroOrStrictSignOnPreconnected {s : Set ℝ} {u : ℝ → ℝ}
    (hs : IsPreconnected s) (hu : ContinuousOn u s) :
    (∃ x ∈ s, u x = 0) ∨ (∀ x ∈ s, 0 < u x) ∨ (∀ x ∈ s, u x < 0) := by
  by_cases hzero : ∃ x ∈ s, u x = 0
  · exact Or.inl hzero
  have himage_convex : Convex ℝ (u '' s) := by
    -- Preconnected subsets of `ℝ` are exactly convex sets, so the image contains every interval
    -- between two attained values.
    exact Real.convex_iff_isPreconnected.mpr (hs.image u hu)
  by_cases hpos : ∀ x ∈ s, 0 < u x
  · exact Or.inr <| Or.inl hpos
  push Not at hpos
  rcases hpos with ⟨x, hx, hx_nonpos⟩
  have hx_neg : u x < 0 := by
    -- Once zeros are excluded, a nonpositive image value is automatically strictly negative.
    exact lt_of_le_of_ne hx_nonpos <| Ne.symm <| by
      intro hux
      exact hzero ⟨x, hx, hux.symm⟩
  have hOrd : Set.OrdConnected (u '' s) := himage_convex.ordConnected
  have hnegall : ∀ y ∈ s, u y < 0 := by
    intro y hy
    by_contra hy_not
    have hy_nonneg : 0 ≤ u y := by linarith
    have hx_image : u x ∈ u '' s := ⟨x, hx, rfl⟩
    have hy_image : u y ∈ u '' s := ⟨y, hy, rfl⟩
    have hIcc : Set.Icc (u x) (u y) ⊆ u '' s := by
      -- Ord-connectedness of the image supplies the whole interval between `u x < 0` and
      -- `u y ≥ 0`.
      exact (Set.ordConnected_iff.mp hOrd) _ hx_image _ hy_image (by linarith)
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (u x) (u y) := ⟨le_of_lt hx_neg, hy_nonneg⟩
    rcases hIcc hzero_mem with ⟨z, hz, hz0⟩
    exact hzero ⟨z, hz, hz0⟩
  exact Or.inr <| Or.inr hnegall

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a reciprocal logarithm above a
threshold `T ≥ 1` forces the original norm below `1`. -/
lemma norm_lt_one_of_reciprocalLog_gt
    {w : ℂ} {T : ℝ} (hw : w ≠ 0) (hT_ge_one : 1 ≤ T)
    (hlarge : T < Real.log ‖w⁻¹‖) :
    ‖w‖ < 1 := by
  -- Convert the logarithmic lower bound into an inverse-norm lower bound above `1`.
  have hpos : 0 < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw)
  have hexp_lt : Real.exp T < ‖w⁻¹‖ := (Real.lt_log_iff_exp_lt hpos).1 hlarge
  have hone_lt_expT : 1 < Real.exp T := by
    have hone_lt_exp1 : 1 < Real.exp (1 : ℝ) := (Real.one_lt_exp_iff).2 (by norm_num)
    exact lt_of_lt_of_le hone_lt_exp1 (Real.exp_le_exp.mpr hT_ge_one)
  have hone_lt_inv : 1 < ‖w‖⁻¹ := by
    simpa [norm_inv] using lt_of_lt_of_le hone_lt_expT (le_of_lt hexp_lt)
  exact (one_lt_inv₀ (norm_pos_iff.mpr hw)).1 hone_lt_inv

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a preconnected interval, one
weak nonpositive witness and one weak nonnegative witness eliminate the strict-sign alternatives in
the zero-versus-sign trichotomy. -/
lemma existsZeroOfWeakSignsOfZeroOrStrictSign
    {s : Set ℝ} {u : ℝ → ℝ}
    (htrichotomy :
      (∃ x ∈ s, u x = 0) ∨ (∀ x ∈ s, 0 < u x) ∨ (∀ x ∈ s, u x < 0))
    (hweakNonpos : ∃ x ∈ s, u x ≤ 0)
    (hweakNonneg : ∃ x ∈ s, 0 ≤ u x) :
    ∃ x ∈ s, u x = 0 := by
  rcases htrichotomy with hzero | hposall | hnegall
  · exact hzero
  · -- The all-positive branch contradicts the internal nonpositive witness.
    rcases hweakNonpos with ⟨x, hx, hx_le⟩
    exfalso
    linarith [hposall x hx]
  · -- The all-negative branch contradicts the internal nonnegative witness.
    rcases hweakNonneg with ⟨x, hx, hx_ge⟩
    exfalso
    linarith [hnegall x hx]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a fixed radius circle, the
quotient selector is the real part of the punctured-ball normal form `c * z^n * exp F`. -/
lemma circleSelector_eq_normalForm
    {g : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {F : ℂ → ℂ} {c : ℂ} {θ : ℝ}
    (hρpos : 0 < ρ) (hc_ne : c ≠ 0)
    (hEqRatio :
      EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzeta_mem : circleMap 0 ρ θ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ)) :
    Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖ =
      Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (F (circleMap 0 ρ θ)).re := by
  have hratio := hEqRatio hzeta_mem
  have hzeta_nonzero : circleMap 0 ρ θ ≠ 0 := by
    -- Radius-`ρ` points on the witness circle stay away from the puncture because `ρ > 0`.
    have hnorm : ‖circleMap 0 ρ θ‖ = ρ := by
      rw [norm_circleMap_zero, abs_of_nonneg (le_of_lt hρpos)]
    exact norm_ne_zero_iff.mp <| by simpa [hnorm] using hρpos.ne'
  have hnorm_c_ne : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc_ne
  have hnorm_zpow_ne : ‖circleMap 0 ρ θ ^ n‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (zpow_ne_zero n hzeta_nonzero)
  have hnorm_exp_ne : ‖Complex.exp (F (circleMap 0 ρ θ))‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
  have hnorm_circle : ‖circleMap 0 ρ θ‖ = ρ := by
    rw [norm_circleMap_zero, abs_of_nonneg (le_of_lt hρpos)]
  -- Expand the norm of the normal form into the constant, radius, and exponential pieces.
  calc
    Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖
        = Real.log ‖c * circleMap 0 ρ θ ^ n * Complex.exp (F (circleMap 0 ρ θ))‖ := by
            simpa using congrArg (fun z : ℂ ↦ Real.log ‖z‖) hratio
    _ = Real.log ‖c‖ + Real.log ‖circleMap 0 ρ θ ^ n‖ +
          Real.log ‖Complex.exp (F (circleMap 0 ρ θ))‖ := by
            rw [norm_mul, norm_mul, mul_assoc]
            rw [Real.log_mul hnorm_c_ne (mul_ne_zero hnorm_zpow_ne hnorm_exp_ne)]
            rw [Real.log_mul hnorm_zpow_ne hnorm_exp_ne]
            ring
    _ = Real.log ‖c‖ + (n : ℝ) * Real.log ρ +
          Real.log ‖Complex.exp (F (circleMap 0 ρ θ))‖ := by
            rw [norm_zpow, Real.log_zpow, hnorm_circle]
    _ = Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (F (circleMap 0 ρ θ)).re := by
            rw [Complex.norm_exp, Real.log_exp]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: an open real set containing
`x` contains a smaller closed interval around `x`. -/
lemma exists_Icc_subset_of_mem_real
    {s : Set ℝ} {x : ℝ} (hs : IsOpen s) (hx : x ∈ s) :
    ∃ u v : ℝ, u < x ∧ x < v ∧ Set.Icc u v ⊆ s := by
  -- Start from an open interval neighborhood of `x` and then shrink to a closed midpoint interval.
  rcases (mem_nhds_iff_exists_Ioo_subset).1 (hs.mem_nhds hx) with ⟨a, b, habx, hab_subset⟩
  let u : ℝ := (a + x) / 2
  let v : ℝ := (x + b) / 2
  refine ⟨u, v, ?_, ?_, ?_⟩
  · dsimp [u]
    nlinarith [habx.1]
  · dsimp [v]
    nlinarith [habx.2]
  · intro y hy
    have hy_left : a < y := by
      dsimp [u] at hy
      linarith [hy.1, habx.1]
    have hy_right : y < b := by
      dsimp [v] at hy
      linarith [hy.2, habx.2]
    exact hab_subset ⟨hy_left, hy_right⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a preconnected real source
domain, two continuous complex-valued branches with the same exponential differ by one fixed
integral multiple of `2π i`. -/
lemma eqOn_add_two_pi_I_mul_int_of_exp_eq_on_preconnected_real
    {E : Set ℝ} {F₁ F₂ : ℝ → ℂ}
    (hE : IsPreconnected E)
    (hF₁ : ContinuousOn F₁ E)
    (hF₂ : ContinuousOn F₂ E)
    (hexp : Set.EqOn (fun x ↦ Complex.exp (F₁ x)) (fun x ↦ Complex.exp (F₂ x)) E) :
    ∃ k : ℤ, Set.EqOn F₂ (fun x ↦ F₁ x + k * (2 * (Real.pi : ℂ) * Complex.I)) E := by
  let E' : Set ℂ := Complex.ofReal '' E
  let G₁ : ℂ → ℂ := fun z ↦ F₁ z.re
  let G₂ : ℂ → ℂ := fun z ↦ F₂ z.re
  have hE' : IsPreconnected E' := by
    -- Transport the real preconnected set through the continuous embedding `ℝ ↪ ℂ`.
    exact hE.image Complex.ofReal Complex.continuous_ofReal.continuousOn
  have hG₁ : ContinuousOn G₁ E' := by
    -- Restrict the real branch to the embedded real line inside `ℂ`.
    exact hF₁.comp Complex.continuous_re.continuousOn <| by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hx
  have hG₂ : ContinuousOn G₂ E' := by
    -- The same restriction argument applies to the second branch.
    exact hF₂.comp Complex.continuous_re.continuousOn <| by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hx
  have hexp' :
      Set.EqOn (fun z ↦ Complex.exp (G₁ z)) (fun z ↦ Complex.exp (G₂ z)) E' := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    simpa [G₁, G₂] using hexp hx
  rcases eqOn_add_two_pi_I_mul_int_of_exp_eq_on_preconnected hE' hG₁ hG₂ hexp' with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro x hx
  have hx' : (x : ℂ) ∈ E' := ⟨x, hx, rfl⟩
  simpa [G₁, G₂] using hk hx'

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the left and right endpoint
analyses already return one-sided sign neighborhoods inside `C = Ioo a b`, then the existing
weak-sign zero extractor produces an interior zero of `u` on `C`. -/
lemma boundaryNeighborhoods_giveZeroInOpenInterval
    {u : ℝ → ℝ} {a b : ℝ} {C : Set ℝ}
    (hab : a < b)
    (hC : C = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C, u sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C, 0 ≤ u sigmaPos) →
          ∃ θ ∈ C, u θ = 0)
    (hleft :
      (∃ θ ∈ C, u θ = 0) ∨
        ∃ η > 0, ∀ θ ∈ Set.Ioo a (min (a + η) b), u θ < 0)
    (hright :
      (∃ θ ∈ C, u θ = 0) ∨
        ∃ η > 0, ∀ θ ∈ Set.Ioo (max a (b - η)) b, 0 < u θ) :
    ∃ θ ∈ C, u θ = 0 := by
  rcases hleft with hzeroC | ⟨ηNeg, hηNeg, hneg⟩
  · -- If the left boundary analysis already found a zero in `C`, we are done immediately.
    exact hzeroC
  rcases hright with hzeroC | ⟨ηPos, hηPos, hpos⟩
  · -- The symmetric right-boundary zero case closes the goal just as directly.
    exact hzeroC
  let sigmaNeg : ℝ := (a + min (a + ηNeg) b) / 2
  let sigmaPos : ℝ := (max a (b - ηPos) + b) / 2
  have hsigmaNeg_mem_left :
      sigmaNeg ∈ Set.Ioo a (min (a + ηNeg) b) := by
    -- Choose an explicit interior point of the left one-sided neighborhood.
    have hleft_upper : a < min (a + ηNeg) b := by
      refine lt_min ?_ hab
      linarith
    constructor
    · dsimp [sigmaNeg]
      linarith
    · dsimp [sigmaNeg]
      linarith
  have hsigmaPos_mem_right :
      sigmaPos ∈ Set.Ioo (max a (b - ηPos)) b := by
    -- Choose an explicit interior point of the right one-sided neighborhood.
    have hright_lower : max a (b - ηPos) < b := by
      refine max_lt hab ?_
      linarith
    constructor
    · dsimp [sigmaPos]
      linarith
    · dsimp [sigmaPos]
      linarith
  have hsigmaNeg_mem_C : sigmaNeg ∈ C := by
    -- The chosen left midpoint already lies in the ambient open interval `C = Ioo a b`.
    rw [hC]
    refine ⟨hsigmaNeg_mem_left.1, ?_⟩
    exact lt_of_lt_of_le hsigmaNeg_mem_left.2 (min_le_right _ _)
  have hsigmaPos_mem_C : sigmaPos ∈ C := by
    -- The chosen right midpoint lies in the same open interval component.
    rw [hC]
    refine ⟨?_, hsigmaPos_mem_right.2⟩
    exact lt_of_le_of_lt (le_max_left _ _) hsigmaPos_mem_right.1
  have hsigmaNeg_nonpos : u sigmaNeg ≤ 0 := le_of_lt (hneg sigmaNeg hsigmaNeg_mem_left)
  have hsigmaPos_nonneg : 0 ≤ u sigmaPos := le_of_lt (hpos sigmaPos hsigmaPos_mem_right)
  -- Feed the two interior weak-sign witnesses into the pre-existing zero-extraction package.
  exact hzero
    ⟨sigmaNeg, hsigmaNeg_mem_C, hsigmaNeg_nonpos⟩
    ⟨sigmaPos, hsigmaPos_mem_C, hsigmaPos_nonneg⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a continuous real function
that is already negative at the left endpoint of an interval stays negative on a smaller right-hand
subinterval. -/
lemma leftNeighborhood_lt_zero_of_continuous_of_lt
    {u : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hu : Continuous u) (ha : u a < 0) :
    ∃ η > 0, ∀ θ ∈ Set.Ioo a (min (a + η) b), u θ < 0 := by
  have hpre :
      u ⁻¹' {x : ℝ | x < 0} ∈ 𝓝 a := by
    -- Pull the open negative half-line back to a neighborhood of the endpoint `a`.
    exact hu.continuousAt (isOpen_Iio.mem_nhds ha)
  rcases (mem_nhds_iff_exists_Ioo_subset).1 hpre with ⟨l, r, ha_mem, hlr_subset⟩
  let η : ℝ := min ((r - a) / 2) (b - a)
  have hη_pos : 0 < η := by
    -- Shrink simultaneously inside the continuity neighborhood and inside `(a, b)`.
    refine lt_min ?_ (sub_pos.mpr hab)
    linarith [ha_mem.2]
  refine ⟨η, hη_pos, ?_⟩
  intro θ hθ
  have hθ_mem : θ ∈ Set.Ioo l r := by
    constructor
    · exact lt_of_lt_of_le ha_mem.1 hθ.1.le
    · have hθ_lt_aη : θ < a + η := lt_of_lt_of_le hθ.2 (min_le_left _ _)
      have hη_le : η ≤ (r - a) / 2 := min_le_left _ _
      linarith
  exact hlr_subset hθ_mem

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a continuous real function
that is already positive at the right endpoint of an interval stays positive on a smaller left-hand
subinterval. -/
lemma rightNeighborhood_gt_zero_of_continuous_of_lt
    {u : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hu : Continuous u) (hb : 0 < u b) :
    ∃ η > 0, ∀ θ ∈ Set.Ioo (max a (b - η)) b, 0 < u θ := by
  have hpre :
      u ⁻¹' {x : ℝ | 0 < x} ∈ 𝓝 b := by
    -- Pull the open positive half-line back to a neighborhood of the endpoint `b`.
    exact hu.continuousAt (isOpen_Ioi.mem_nhds hb)
  rcases (mem_nhds_iff_exists_Ioo_subset).1 hpre with ⟨l, r, hb_mem, hlr_subset⟩
  let η : ℝ := min ((b - l) / 2) (b - a)
  have hη_pos : 0 < η := by
    -- Shrink simultaneously inside the continuity neighborhood and inside `(a, b)`.
    refine lt_min ?_ (sub_pos.mpr hab)
    linarith [hb_mem.1]
  refine ⟨η, hη_pos, ?_⟩
  intro θ hθ
  have hθ_mem : θ ∈ Set.Ioo l r := by
    constructor
    · have hbη_lt_θ : b - η < θ := lt_of_le_of_lt (le_max_right _ _) hθ.1
      have hη_le : η ≤ (b - l) / 2 := min_le_left _ _
      linarith
    · exact lt_of_le_of_lt hθ.2.le hb_mem.2
  exact hlr_subset hθ_mem

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if a continuous map sends an
open interval into `exercise16Domain`, then the left endpoint image lies in the closure of the
lens domain. -/
lemma image_leftEndpoint_mem_closure_of_mapsTo_Ioo
    {h : ℝ → ℂ} {a b : ℝ}
    (hab : a < b)
    (hcont : Continuous h)
    (hmap : MapsTo h (Set.Ioo a b) exercise16Domain) :
    h a ∈ closure exercise16Domain := by
  -- The left endpoint belongs to the closure of the open interval, so continuity transports it to
  -- the closure of the image and hence to the closure of the lens domain.
  have ha_mem_closure : a ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
    exact ⟨le_rfl, le_of_lt hab⟩
  have himage_mem : h a ∈ closure (h '' Set.Ioo a b) :=
    mem_closure_image hcont.continuousAt ha_mem_closure
  exact (closure_mono <| by
    rintro _ ⟨x, hx, rfl⟩
    exact hmap hx) himage_mem

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the same closure transport
holds for the right endpoint of an open interval mapping into `exercise16Domain`. -/
lemma image_rightEndpoint_mem_closure_of_mapsTo_Ioo
    {h : ℝ → ℂ} {a b : ℝ}
    (hab : a < b)
    (hcont : Continuous h)
    (hmap : MapsTo h (Set.Ioo a b) exercise16Domain) :
    h b ∈ closure exercise16Domain := by
  -- The right endpoint is handled by the symmetric closure formula for `Ioo`.
  have hb_mem_closure : b ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
    exact ⟨le_of_lt hab, le_rfl⟩
  have himage_mem : h b ∈ closure (h '' Set.Ioo a b) :=
    mem_closure_image hcont.continuousAt hb_mem_closure
  exact (closure_mono <| by
    rintro _ ⟨x, hx, rfl⟩
    exact hmap hx) himage_mem

