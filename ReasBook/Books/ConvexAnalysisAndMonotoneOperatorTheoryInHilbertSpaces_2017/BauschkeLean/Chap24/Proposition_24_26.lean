import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.Proposition_12_27
import BauschkeLean.Chap12.Proposition_12_29

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Domain-style sampling: the owner abstraction here is the Chapter 12 proximal-operator surface
-- `Prox[f, hf]` together with the canonical minimizer owner `Argmin f.asEReal`. These theorems
-- add only the source-facing Güler gap inequalities, so they keep the primitive data
-- `f ∈ Γ₀(H)`, `x`, `z`, and the minimizer/non-minimizer hypotheses, with no extra wrapper API.

section Guler

variable (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x z : H)
variable (hz : z ∈ Argmin f.asEReal) (hprox : Prox[f, hf] x ∉ Argmin f.asEReal)

/-- Helper for Proposition 24.26: every global minimizer of a `Γ₀` function lies in its effective
domain. -/
private theorem mem_effectiveDomain_of_mem_argmin
    (hf : f ∈ Γ₀(H)) {y : H} (hy : y ∈ Argmin f.asEReal) :
    y ∈ effectiveDomain f := by
  -- Compare the minimizing value with one known finite point from the `Γ₀` hypothesis.
  rcases hf.2.nonempty with ⟨w, hw⟩
  rw [mem_argmin_iff, isMinOn_univ_iff] at hy
  exact mem_effectiveDomain_iff.mpr (lt_of_le_of_lt (hy w) (mem_effectiveDomain_iff.mp hw))

/-- Helper for Proposition 24.26: the proximal point is finite because the minimizer comparison
point has finite value. -/
private theorem prox_mem_effectiveDomain
    (z : H) (hz : z ∈ Argmin f.asEReal) :
    let p := Prox[f, hf] x
    p ∈ effectiveDomain f := by
  let p := Prox[f, hf] x
  have hp_prox : IsProxPoint f x p := by
    simpa [p] using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x
  have hz_dom : z ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argmin (f := f) (hf := hf) hz
  have hvar := (isProxPoint_iff_forall_inner_add_le f hf.2 x p).mp hp_prox z
  -- If `f p = ⊤`, the variational inequality would force the finite value `f z` to be `⊤`.
  by_contra hp_dom
  have hfp_top : (f p : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hp_dom))
  have hsum_top :
      (⟪z - p, x - p⟫_ℝ : EReal) + (f p : EReal) = ⊤ := by
    rw [hfp_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  have hz_top : (f z : EReal) = ⊤ := by
    simpa [hsum_top] using hvar
  exact (ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)) hz_top

/-- Helper for Proposition 24.26: if the proximal point is not a minimizer, then neither is the
base point. -/
theorem base_point_not_mem_argmin_of_prox_not_mem_argmin
    (hprox : Prox[f, hf] x ∉ Argmin f.asEReal) :
    x ∉ Argmin f.asEReal := by
  intro hx
  -- Fixed points of the proximal map are exactly the minimizers from Proposition 12.29.
  have hfixed : x ∈ Function.fixedPoints (Prox[f, hf]) := by
    exact (mem_fixedPoints_proximityOperator_iff_mem_argmin_of_mem_gammaZero hf).2 hx
  have hpx : Prox[f, hf] x = x := by
    simpa [Function.mem_fixedPoints_iff] using hfixed
  have hp_argmin : Prox[f, hf] x ∈ Argmin f.asEReal := by
    simpa [hpx] using hx
  exact hprox hp_argmin

/-- Helper for Proposition 24.26: the proximal value gap is controlled by the residual norm times
the distance to a minimizer, which is the Lean form of `(24.28)`. -/
theorem prox_gap_le_residual_mul_dist_to_minimizer
    (z : H) (hz : z ∈ Argmin f.asEReal) :
    let p := Prox[f, hf] x
    (f p : EReal).toReal - (f z : EReal).toReal ≤ ‖x - p‖ * ‖x - z‖ := by
  let p := Prox[f, hf] x
  have hp_prox : IsProxPoint f x p := by
    simpa [p] using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x
  have hz_dom : z ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argmin (f := f) (hf := hf) hz
  have hp_dom : p ∈ effectiveDomain f := by
    simpa [p] using prox_mem_effectiveDomain (f := f) (hf := hf) (x := x) (z := z) hz
  have hvar := (isProxPoint_iff_forall_inner_add_le f hf.2 x p).mp hp_prox z
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hvar_real :
      ⟪z - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f z : EReal).toReal := by
    have hcast :
        (((⟪z - p, x - p⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal)) ≤
          (((f z : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hfp_top hfp_bot, ← EReal.coe_toReal hz_top hz_bot,
        ← EReal.coe_add] at hvar
      exact hvar
    exact_mod_cast hcast
  have hsplit :
      ⟪z - p, x - p⟫_ℝ = ⟪x - p, z - x⟫_ℝ + ‖x - p‖ ^ 2 := by
    -- Rewrite the comparison inner product exactly as in the source proof.
    calc
      ⟪z - p, x - p⟫_ℝ = ⟪z - x + (x - p), x - p⟫_ℝ := by
        congr 1
        abel_nf
      _ = ⟪z - x, x - p⟫_ℝ + ⟪x - p, x - p⟫_ℝ := by
        rw [inner_add_left]
      _ = ⟪x - p, z - x⟫_ℝ + ‖x - p‖ ^ 2 := by
        rw [real_inner_comm, real_inner_self_eq_norm_sq]
  have hcs : -(‖x - p‖ * ‖x - z‖) ≤ ⟪x - p, z - x⟫_ℝ := by
    -- This is Cauchy-Schwarz after rewriting `z - x = -(x - z)`.
    have hnorm : ⟪x - p, x - z⟫_ℝ ≤ ‖x - p‖ * ‖x - z‖ :=
      real_inner_le_norm (x - p) (x - z)
    have hneg : -(‖x - p‖ * ‖x - z‖) ≤ -⟪x - p, x - z⟫_ℝ := by
      linarith
    have hzx : z - x = -(x - z) := by
      abel_nf
    calc
      -(‖x - p‖ * ‖x - z‖) ≤ -⟪x - p, x - z⟫_ℝ := hneg
      _ = ⟪x - p, z - x⟫_ℝ := by rw [hzx, inner_neg_right]
  -- Combine the variational inequality with Cauchy-Schwarz and drop the nonnegative square term.
  rw [hsplit] at hvar_real
  nlinarith [hvar_real, hcs, sq_nonneg ‖x - p‖]

/-- Helper for Proposition 24.26: specializing the proximal variational inequality at `y = x`
gives the source estimate `(24.29)`. -/
private theorem sqdist_add_prox_value_le_self :
    let p := Prox[f, hf] x
    (((‖x - p‖ ^ 2 : ℝ) : EReal) + (f p : EReal)) ≤ (f x : EReal) := by
  let p := Prox[f, hf] x
  have hp_prox : IsProxPoint f x p := by
    simpa [p] using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x
  have hvar := (isProxPoint_iff_forall_inner_add_le f hf.2 x p).mp hp_prox x
  simpa [real_inner_self_eq_norm_sq] using hvar

/-- Helper for Proposition 24.26: the normalized proximal gap is at most `1 / 2`, which is the
source inequality `(24.32)`. -/
theorem prox_gap_div_sqdist_le_one_half
    (z : H) (hz : z ∈ Argmin f.asEReal)
    (hprox : Prox[f, hf] x ∉ Argmin f.asEReal) :
    let p := Prox[f, hf] x
    ((f p : EReal).toReal - (f z : EReal).toReal) / ‖x - z‖ ^ 2 ≤ 1 / 2 := by
  let p := Prox[f, hf] x
  have hp_prox : IsProxPoint f x p := by
    simpa [p] using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x
  have hz_dom : z ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argmin (f := f) (hf := hf) hz
  have hp_dom : p ∈ effectiveDomain f := by
    simpa [p] using prox_mem_effectiveDomain (f := f) (hf := hf) (x := x) (z := z) hz
  have hx_not_argmin :
      x ∉ Argmin f.asEReal :=
    base_point_not_mem_argmin_of_prox_not_mem_argmin
      (f := f) (hf := hf) (x := x) hprox
  have hx_ne_z : x ≠ z := by
    intro hxz
    apply hx_not_argmin
    simpa [hxz] using hz
  have hp_min : ∀ y, proximalObjective f x p ≤ proximalObjective f x y := by
    rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp_prox
    exact hp_prox
  have hobj := hp_min z
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hobj_real :
      (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
        (f z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    -- Compare the proximal objective at `p` and at the minimizer `z`, then forget the `EReal`
    -- wrappers because both values are finite.
    have hcast :
        (((f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤
          (((f z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal) := by
      simpa [proximalObjective, EReal.coe_toReal hfp_top hfp_bot,
        EReal.coe_toReal hz_top hz_bot, EReal.coe_add] using hobj
    exact_mod_cast hcast
  have hgap :
      (f p : EReal).toReal - (f z : EReal).toReal ≤ (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    nlinarith [hobj_real, sq_nonneg ‖x - p‖]
  have hdist_pos : 0 < ‖x - z‖ ^ 2 := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx_ne_z))
  -- Divide the textbook upper bound by the positive squared distance.
  exact (div_le_iff₀ hdist_pos).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgap)

/-- Helper for Proposition 24.26: the minimizer value is a lower bound for the proximal value. -/
private theorem prox_gap_nonneg
    (z : H) (hz : z ∈ Argmin f.asEReal) :
    let p := Prox[f, hf] x
    0 ≤ (f p : EReal).toReal - (f z : EReal).toReal := by
  let p := Prox[f, hf] x
  have hz_dom : z ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argmin (f := f) (hf := hf) hz
  have hp_dom : p ∈ effectiveDomain f := by
    simpa [p] using prox_mem_effectiveDomain (f := f) (hf := hf) (x := x) (z := z) hz
  have hz_le_fp : (f z : EReal) ≤ (f p : EReal) := by
    rw [mem_argmin_iff, isMinOn_univ_iff] at hz
    exact hz p
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hcast :
      (((f z : EReal).toReal : ℝ) : EReal) ≤ (((f p : EReal).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hz_top hz_bot, EReal.coe_toReal hfp_top hfp_bot] using hz_le_fp
  have hreal : (f z : EReal).toReal ≤ (f p : EReal).toReal := by
    exact_mod_cast hcast
  linarith

/-- Helper for Proposition 24.26: the proximal value gap is strictly positive because the proximal
point is assumed not to minimize `f`. -/
private theorem prox_gap_pos
    (z : H) (hz : z ∈ Argmin f.asEReal)
    (hprox : Prox[f, hf] x ∉ Argmin f.asEReal) :
    let p := Prox[f, hf] x
    0 < (f p : EReal).toReal - (f z : EReal).toReal := by
  let p := Prox[f, hf] x
  have hz_dom : z ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argmin (f := f) (hf := hf) hz
  have hp_dom : p ∈ effectiveDomain f := by
    simpa [p] using prox_mem_effectiveDomain (f := f) (hf := hf) (x := x) (z := z) hz
  have hgap_nonneg :
      0 ≤ (f p : EReal).toReal - (f z : EReal).toReal := by
    simpa [p] using prox_gap_nonneg (f := f) (hf := hf) (x := x) (z := z) hz
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hgap_ne : (f p : EReal).toReal - (f z : EReal).toReal ≠ 0 := by
    intro hzero
    have hp_eq_hz : (f p : EReal) = (f z : EReal) := by
      have hreal : (f p : EReal).toReal = (f z : EReal).toReal := by
        linarith
      calc
        (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) := by
          exact (EReal.coe_toReal hfp_top hfp_bot).symm
        _ = (((f z : EReal).toReal : ℝ) : EReal) := by simp [hreal]
        _ = (f z : EReal) := by
          exact EReal.coe_toReal hz_top hz_bot
    have hz_sInf : (f z : EReal) = sInf (Set.range f.asEReal) :=
      mem_argmin_iff_eq_sInf.mp hz
    have hp_argmin : p ∈ Argmin f.asEReal := by
      rw [mem_argmin_iff_eq_sInf]
      exact hp_eq_hz.trans hz_sInf
    exact hprox (by simpa [p] using hp_argmin)
  exact lt_of_le_of_ne hgap_nonneg hgap_ne.symm

/-- Helper for Proposition 24.26: on `[0, 1 / 2]`, the reciprocal graph lies below the affine
secant `t ↦ 1 - (2 / 3) t`, which is the source estimate `(24.33)`. -/
theorem inv_one_add_le_one_sub_two_thirds_mul
    {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_half : t ≤ 1 / 2) :
    (1 + t)⁻¹ ≤ 1 - (2 / 3) * t := by
  -- Clear denominators against the positive factor `1 + t`.
  have ht_pos : 0 < 1 + t := by
    linarith
  have hmain : 0 ≤ (1 - (2 / 3) * t) - (1 + t)⁻¹ := by
    field_simp [ht_pos.ne']
    nlinarith
  linarith

/-- Proposition 24.26 (1) (Güler): if `z` minimizes `f` and the proximal point `Prox_f x` is not
a minimizer of `f`, then the proximal value-gap ratio is bounded by the affine correction term from
`(24.25)`. -/
theorem guler_prox_gap_ratio_bound
    (hz : z ∈ Argmin f.asEReal) (hprox : Prox[f, hf] x ∉ Argmin f.asEReal)
    :
    let p := Prox[f, hf] x
    ((f p : EReal) - (f z : EReal)) / ((f x : EReal) - (f z : EReal)) ≤
      (1 : EReal) -
        ((((2 / 3 : ℝ) : EReal) * (((f p : EReal) - (f z : EReal)) /
          (((‖x - z‖ ^ 2 : ℝ) : EReal))))) := by
  let p := Prox[f, hf] x
  have hz_dom : z ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argmin (f := f) (hf := hf) hz
  have hp_dom : p ∈ effectiveDomain f := by
    simpa [p] using prox_mem_effectiveDomain (f := f) (hf := hf) (x := x) (z := z) hz
  have hgap_residual :
      (f p : EReal).toReal - (f z : EReal).toReal ≤ ‖x - p‖ * ‖x - z‖ := by
    simpa [p] using
      prox_gap_le_residual_mul_dist_to_minimizer (f := f) (hf := hf) (x := x) (z := z) hz
  have hgap_half :
      ((f p : EReal).toReal - (f z : EReal).toReal) / ‖x - z‖ ^ 2 ≤ 1 / 2 := by
    simpa [p] using prox_gap_div_sqdist_le_one_half (f := f) (hf := hf) (x := x) (z := z) hz hprox
  have hgap_pos :
      0 < (f p : EReal).toReal - (f z : EReal).toReal := by
    simpa [p] using prox_gap_pos (f := f) (hf := hf) (x := x) (z := z) hz hprox
  by_cases hx : x ∈ effectiveDomain f
  · -- In the finite branch, translate everything to real inequalities and follow the source proof.
    have hx_not_argmin :
        x ∉ Argmin f.asEReal :=
      base_point_not_mem_argmin_of_prox_not_mem_argmin
        (f := f) (hf := hf) (x := x) hprox
    have hx_ne_z : x ≠ z := by
      intro hxz
      apply hx_not_argmin
      simpa [hxz] using hz
    have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hprox_value :
        (((‖x - p‖ ^ 2 : ℝ) : EReal) + (f p : EReal)) ≤ (f x : EReal) := by
      -- This is the `y = x` specialization of the proximal variational inequality, i.e. `(24.29)`.
      simpa [p] using sqdist_add_prox_value_le_self (f := f) (hf := hf) (x := x)
    have hprox_value_real :
        ‖x - p‖ ^ 2 + (f p : EReal).toReal ≤ (f x : EReal).toReal := by
      have hcast :
          (((‖x - p‖ ^ 2 + (f p : EReal).toReal : ℝ) : EReal)) ≤
            (((f x : EReal).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_toReal hfp_top hfp_bot, ← EReal.coe_toReal hx_top hx_bot,
          ← EReal.coe_add] at hprox_value
        exact hprox_value
      exact_mod_cast hcast
    let a : ℝ := (f p : EReal).toReal - (f z : EReal).toReal
    let b : ℝ := (f x : EReal).toReal - (f z : EReal).toReal
    let d2 : ℝ := ‖x - z‖ ^ 2
    have ha_nonneg : 0 ≤ a := by
      have hgap_nonneg :
          0 ≤ (f p : EReal).toReal - (f z : EReal).toReal := by
        simpa [p] using prox_gap_nonneg (f := f) (hf := hf) (x := x) (z := z) hz
      simpa [a] using hgap_nonneg
    have ha_pos : 0 < a := by
      simpa [a] using hgap_pos
    have hd2_pos : 0 < d2 := by
      simpa [d2] using
        sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx_ne_z))
    have hdist_nonneg : 0 ≤ ‖x - z‖ := norm_nonneg _
    have hres_sq : a ^ 2 ≤ ‖x - p‖ ^ 2 * d2 := by
      -- Square the residual estimate `(24.28)`.
      have haux : a ≤ ‖x - p‖ * ‖x - z‖ := by
        simpa [a, p] using hgap_residual
      nlinarith [haux]
    have hba : ‖x - p‖ ^ 2 ≤ b - a := by
      -- Proposition 12.27 yields the `f x - f p` lower bound from `(24.29)`.
      nlinarith [hprox_value_real]
    have hsub : a ^ 2 / d2 ≤ b - a := by
      exact (div_le_iff₀ hd2_pos).2 (by nlinarith [hres_sq, hba])
    let t : ℝ := a / d2
    have ht_nonneg : 0 ≤ t := by
      exact div_nonneg ha_nonneg hd2_pos.le
    have ht_half : t ≤ 1 / 2 := by
      simpa [t, a, d2, p] using hgap_half
    have h31 : a * (1 + t) ≤ b := by
      -- This is the real form of textbook estimate `(24.31)`.
      have ht_mul : a * t = a ^ 2 / d2 := by
        dsimp [t]
        field_simp [hd2_pos.ne']
      nlinarith [hsub, ht_mul]
    have hb_pos : 0 < b := by
      nlinarith [h31, ha_pos, ht_nonneg]
    have hratio :
        a / b ≤ (1 + t)⁻¹ := by
      have hb_ne : b ≠ 0 := by
        linarith
      have h1t_pos : 0 < 1 + t := by
        linarith
      field_simp [hb_ne, h1t_pos.ne']
      nlinarith [h31]
    have hfinal_real :
        a / b ≤ 1 - (2 / 3) * t := by
      exact le_trans hratio (inv_one_add_le_one_sub_two_thirds_mul ht_nonneg ht_half)
    have hcast :
        (((a / b : ℝ) : EReal)) ≤ (((1 - (2 / 3) * t : ℝ) : EReal)) := by
      exact_mod_cast hfinal_real
    -- Cast the real inequality back to the original `EReal` statement.
    simpa [a, b, d2, t, p, EReal.coe_sub, EReal.coe_div, EReal.coe_mul,
      EReal.coe_toReal hfp_top hfp_bot, EReal.coe_toReal hz_top hz_bot,
      EReal.coe_toReal hx_top hx_bot, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hcast
  · -- When `f x = ⊤`, the left-hand ratio is `0`; the right-hand side stays nonnegative because
    -- `(24.32)` bounds the normalized gap by `1 / 2`.
    have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hxtop : (f x : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    have hz_real : (f z : EReal) = (((f z : EReal).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hz_top hz_bot).symm
    have hfp_real : (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hfp_top hfp_bot).symm
    have hden_top : ((f x : EReal) - (f z : EReal)) = ⊤ := by
      rw [hxtop, hz_real, EReal.top_sub_coe]
    let t : ℝ := ((f p : EReal).toReal - (f z : EReal).toReal) / ‖x - z‖ ^ 2
    have hgap_cast :
        ((((f p : EReal).toReal - (f z : EReal).toReal : ℝ) : EReal)) =
          ((f p : EReal) - (f z : EReal)) := by
      rw [hfp_real, hz_real]
      simp
    have hfactor_cast :
        ((((2 / 3 : ℝ) * t : ℝ) : EReal)) =
          (((2 / 3 : ℝ) : EReal) *
            (((f p : EReal) - (f z : EReal)) / (((‖x - z‖ ^ 2 : ℝ) : EReal)))) := by
      -- Rewrite the normalized gap once before multiplying by the scalar factor.
      have ht_cast :
          (((t : ℝ) : EReal)) =
            (((f p : EReal) - (f z : EReal)) / (((‖x - z‖ ^ 2 : ℝ) : EReal))) := by
        dsimp [t]
        rw [EReal.coe_div, hgap_cast]
      calc
        ((((2 / 3 : ℝ) * t : ℝ) : EReal))
            = (((2 / 3 : ℝ) : EReal) * (((t : ℝ) : EReal))) := by
                rw [EReal.coe_mul]
        _ =
            (((2 / 3 : ℝ) : EReal) *
              (((f p : EReal) - (f z : EReal)) / (((‖x - z‖ ^ 2 : ℝ) : EReal)))) := by
                rw [ht_cast]
    have ht_half : t ≤ 1 / 2 := by
      simpa [t, p] using hgap_half
    have hfactor_real : (2 / 3 : ℝ) * t ≤ 1 := by
      nlinarith [ht_half]
    have hfactor_le_one :
        (((2 / 3 : ℝ) : EReal) *
            (((f p : EReal) - (f z : EReal)) / (((‖x - z‖ ^ 2 : ℝ) : EReal)))) ≤
          (1 : EReal) := by
      have hcast : ((((2 / 3 : ℝ) * t : ℝ) : EReal)) ≤ (1 : EReal) := by
        exact_mod_cast hfactor_real
      rw [hfactor_cast] at hcast
      exact hcast
    have hrhs_nonneg :
        (0 : EReal) ≤
          (1 : EReal) -
            ((((2 / 3 : ℝ) : EReal) *
              (((f p : EReal) - (f z : EReal)) / (((‖x - z‖ ^ 2 : ℝ) : EReal))))) := by
      have hrhs_nonneg_real : 0 ≤ 1 - (2 / 3 : ℝ) * t := by
        nlinarith [hfactor_real]
      have hcast_rhs : (0 : EReal) ≤ (((1 - (2 / 3 : ℝ) * t : ℝ) : EReal)) := by
        exact_mod_cast hrhs_nonneg_real
      have hrhs_cast :
          (((1 - (2 / 3 : ℝ) * t : ℝ) : EReal)) =
            (1 : EReal) -
              ((((2 / 3 : ℝ) : EReal) *
                (((f p : EReal) - (f z : EReal)) / (((‖x - z‖ ^ 2 : ℝ) : EReal))))) := by
        calc
          (((1 - (2 / 3 : ℝ) * t : ℝ) : EReal))
              = (1 : EReal) - ((((2 / 3 : ℝ) * t : ℝ) : EReal)) := by
                  rw [EReal.coe_sub]
                  norm_num
          _ = (1 : EReal) -
                ((((2 / 3 : ℝ) : EReal) *
                  (((f p : EReal) - (f z : EReal)) / (((‖x - z‖ ^ 2 : ℝ) : EReal))))) := by
                  simpa using congrArg (fun s : EReal ↦ (1 : EReal) - s) hfactor_cast
      rw [← hrhs_cast]
      exact hcast_rhs
    simpa [hden_top, EReal.div_top] using hrhs_nonneg

/-- Proposition 24.26 (2) (Güler): equivalently, the reciprocal value gaps differ by at least
`(2 / 3) / ‖x - z‖²`, as in `(24.26)`. -/
theorem guler_inv_gap_difference_bound
    (hz : z ∈ Argmin f.asEReal) (hprox : Prox[f, hf] x ∉ Argmin f.asEReal)
    :
    let p := Prox[f, hf] x
    (((2 / 3 : ℝ) : EReal) / (((‖x - z‖ ^ 2 : ℝ) : EReal))) ≤
      (1 : EReal) / ((f p : EReal) - (f z : EReal)) -
        (1 : EReal) / ((f x : EReal) - (f z : EReal)) := by
  let p := Prox[f, hf] x
  have hz_dom : z ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argmin (f := f) (hf := hf) hz
  have hp_dom : p ∈ effectiveDomain f := by
    simpa [p] using prox_mem_effectiveDomain (f := f) (hf := hf) (x := x) (z := z) hz
  have hx_not_argmin :
      x ∉ Argmin f.asEReal :=
    base_point_not_mem_argmin_of_prox_not_mem_argmin
      (f := f) (hf := hf) (x := x) hprox
  have hx_ne_z : x ≠ z := by
    intro hxz
    apply hx_not_argmin
    simpa [hxz] using hz
  have hgap_half :
      ((f p : EReal).toReal - (f z : EReal).toReal) / ‖x - z‖ ^ 2 ≤ 1 / 2 := by
    simpa [p] using prox_gap_div_sqdist_le_one_half (f := f) (hf := hf) (x := x) (z := z) hz hprox
  have hgap_pos :
      0 < (f p : EReal).toReal - (f z : EReal).toReal := by
    simpa [p] using prox_gap_pos (f := f) (hf := hf) (x := x) (z := z) hz hprox
  by_cases hx : x ∈ effectiveDomain f
  · -- In the finite branch, rearrange the already established ratio inequality.
    have hratio :
        ((f p : EReal) - (f z : EReal)) / ((f x : EReal) - (f z : EReal)) ≤
          (1 : EReal) -
            ((((2 / 3 : ℝ) : EReal) * (((f p : EReal) - (f z : EReal)) /
              (((‖x - z‖ ^ 2 : ℝ) : EReal))))) := by
      simpa [p] using guler_prox_gap_ratio_bound (f := f) (hf := hf) (x := x) (z := z) hz hprox
    have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hfp_real : (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hfp_top hfp_bot).symm
    have hz_real : (f z : EReal) = (((f z : EReal).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hz_top hz_bot).symm
    have hx_real : (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hx_top hx_bot).symm
    have hprox_value :
        (((‖x - p‖ ^ 2 : ℝ) : EReal) + (f p : EReal)) ≤ (f x : EReal) := by
      -- Reuse the `y = x` specialization of the proximal variational inequality.
      simpa [p] using sqdist_add_prox_value_le_self (f := f) (hf := hf) (x := x)
    have hprox_value_real :
        ‖x - p‖ ^ 2 + (f p : EReal).toReal ≤ (f x : EReal).toReal := by
      have hcast :
          (((‖x - p‖ ^ 2 + (f p : EReal).toReal : ℝ) : EReal)) ≤
            (((f x : EReal).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_toReal hfp_top hfp_bot, ← EReal.coe_toReal hx_top hx_bot,
          ← EReal.coe_add] at hprox_value
        exact hprox_value
      exact_mod_cast hcast
    let a : ℝ := (f p : EReal).toReal - (f z : EReal).toReal
    let b : ℝ := (f x : EReal).toReal - (f z : EReal).toReal
    let d2 : ℝ := ‖x - z‖ ^ 2
    have ha_pos : 0 < a := by
      simpa [a, p] using hgap_pos
    have hd2_pos : 0 < d2 := by
      simpa [d2] using
        sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx_ne_z))
    have hb_pos : 0 < b := by
      nlinarith [hprox_value_real, hgap_pos]
    have hratio_cast :
        (((a / b : ℝ) : EReal)) ≤ (((1 - (2 / 3) * (a / d2) : ℝ) : EReal)) := by
      simpa [a, b, d2, p, EReal.coe_sub, EReal.coe_div, EReal.coe_mul,
        EReal.coe_toReal hfp_top hfp_bot, EReal.coe_toReal hz_top hz_bot,
        EReal.coe_toReal hx_top hx_bot, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hratio
    have hratio_real :
        a / b ≤ 1 - (2 / 3) * (a / d2) := by
      exact_mod_cast hratio_cast
    have htarget_real :
        (2 / 3) / d2 ≤ 1 / a - 1 / b := by
      have ha_ne : a ≠ 0 := by
        linarith
      have hb_ne : b ≠ 0 := by
        linarith
      have hab_pos : 0 < a * b := by
        positivity
      have hright :
          1 / a - 1 / b = (b - a) / (a * b) := by
        field_simp [ha_ne, hb_ne]
      rw [hright]
      have hratio_num : a ≤ (1 - (2 / 3) * (a / d2)) * b := by
        exact (div_le_iff₀ hb_pos).1 hratio_real
      have hcross : (2 / 3) * (a * b) ≤ d2 * (b - a) := by
        -- Clear the positive denominator `d2` before rearranging the terms.
        have hmul :
            a * d2 ≤ ((1 - (2 / 3) * (a / d2)) * b) * d2 := by
          exact mul_le_mul_of_nonneg_right hratio_num hd2_pos.le
        have hrewrite :
            ((1 - (2 / 3) * (a / d2)) * b) * d2 = b * d2 - (2 / 3) * (a * b) := by
          field_simp [ne_of_gt hd2_pos]
        rw [hrewrite] at hmul
        nlinarith
      exact (div_le_div_iff₀ hd2_pos hab_pos).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)
    have hcast :
        ((((2 / 3) / d2 : ℝ) : EReal)) ≤ (((1 / a - 1 / b : ℝ) : EReal)) := by
      exact_mod_cast htarget_real
    have hleft_cast :
        ((((2 / 3) / d2 : ℝ) : EReal)) =
          (((2 / 3 : ℝ) : EReal) / (((‖x - z‖ ^ 2 : ℝ) : EReal))) := by
      dsimp [d2]
      rw [EReal.coe_div]
    have hp_gap_cast :
        (((a : ℝ) : EReal)) = ((f p : EReal) - (f z : EReal)) := by
      rw [hfp_real, hz_real]
      simp [a]
    have hx_gap_cast :
        (((b : ℝ) : EReal)) = ((f x : EReal) - (f z : EReal)) := by
      rw [hx_real, hz_real]
      simp [b]
    have hright_cast :
        (((1 / a - 1 / b : ℝ) : EReal)) =
          (1 : EReal) / ((f p : EReal) - (f z : EReal)) -
            (1 : EReal) / ((f x : EReal) - (f z : EReal)) := by
      calc
        (((1 / a - 1 / b : ℝ) : EReal))
            = (((1 / a : ℝ) : EReal) - (((1 / b : ℝ) : EReal))) := by
                rw [EReal.coe_sub]
        _ = (1 : EReal) / (((a : ℝ) : EReal)) - (1 : EReal) / (((b : ℝ) : EReal)) := by
              rw [show (((1 / a : ℝ) : EReal)) = (1 : EReal) / (((a : ℝ) : EReal)) by
                    rw [← EReal.coe_one, ← EReal.coe_div]]
              rw [show (((1 / b : ℝ) : EReal)) = (1 : EReal) / (((b : ℝ) : EReal)) by
                    rw [← EReal.coe_one, ← EReal.coe_div]]
        _ = (1 : EReal) / ((f p : EReal) - (f z : EReal)) -
              (1 : EReal) / ((f x : EReal) - (f z : EReal)) := by
              rw [hp_gap_cast, hx_gap_cast]
    rw [hleft_cast, hright_cast] at hcast
    exact hcast
  · -- If `f x = ⊤`, the second reciprocal term vanishes and `(24.32)` gives the remaining bound.
    have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hxtop : (f x : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    have hz_real : (f z : EReal) = (((f z : EReal).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hz_top hz_bot).symm
    have hfp_real : (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hfp_top hfp_bot).symm
    have hden_top : ((f x : EReal) - (f z : EReal)) = ⊤ := by
      rw [hxtop, hz_real, EReal.top_sub_coe]
    let a : ℝ := (f p : EReal).toReal - (f z : EReal).toReal
    let d2 : ℝ := ‖x - z‖ ^ 2
    have hd2_pos : 0 < d2 := by
      simpa [d2] using
        sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx_ne_z))
    have htarget_real :
        (2 / 3) / d2 ≤ 1 / a := by
      have ha_pos : 0 < a := by
        simpa [a, p] using hgap_pos
      have hhalf : a / d2 ≤ 1 / 2 := by
        simpa [a, d2, p] using hgap_half
      have hhalf_num : a ≤ (1 / 2 : ℝ) * d2 := by
        exact (div_le_iff₀ hd2_pos).1 hhalf
      have hcross : (2 / 3) * a ≤ d2 := by
        nlinarith [hhalf_num]
      exact (div_le_div_iff₀ hd2_pos ha_pos).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)
    have hcast_base : ((((2 / 3) / d2 : ℝ) : EReal)) ≤ (((1 / a : ℝ) : EReal)) := by
      exact_mod_cast htarget_real
    have hcast_zero : ((((2 / 3) / d2 : ℝ) : EReal)) ≤ (((1 / a : ℝ) : EReal) - (0 : EReal)) := by
      simpa using hcast_base
    have hleft_cast :
        ((((2 / 3) / d2 : ℝ) : EReal)) =
          (((2 / 3 : ℝ) : EReal) / (((‖x - z‖ ^ 2 : ℝ) : EReal))) := by
      dsimp [d2]
      rw [EReal.coe_div]
    have hp_gap_cast :
        (((a : ℝ) : EReal)) = ((f p : EReal) - (f z : EReal)) := by
      rw [hfp_real, hz_real]
      simp [a]
    have hright_cast :
        (((1 / a : ℝ) : EReal)) =
          (1 : EReal) / ((f p : EReal) - (f z : EReal)) := by
      calc
        (((1 / a : ℝ) : EReal)) = (1 : EReal) / (((a : ℝ) : EReal)) := by
          rw [← EReal.coe_one, ← EReal.coe_div]
        _ = (1 : EReal) / ((f p : EReal) - (f z : EReal)) := by
          rw [hp_gap_cast]
    rw [hleft_cast, hright_cast] at hcast_zero
    rw [hden_top, EReal.div_top]
    exact hcast_zero

end Guler

end ERealFunction
