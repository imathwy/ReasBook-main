import Mathlib
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap07.Exercise_7_9
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Example_13_32

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal InnerProductSpace
open Set

namespace ERealFunction

/-- Helper for Example 13 41: a continuous convex real-valued function on all of `ℝ^N` packages
canonically as a member of `Γ₀`. -/
lemma continuous_convexOn_univ_toEReal_mem_gammaZero
    {N : ℕ} (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  -- Reuse the canonical Chapter 12 owner for continuous convex functions on all of `ℝ^N`.
  exact real_toEReal_mem_gammaZero_of_continuous_convexOn_univ φ hcont hconv

/-- Helper for Example 13 41: the coordinate `ℓ^q` norm on `ℝ^N`, viewed through `Function.toEReal`,
belongs to `Γ₀`. -/
lemma lpNorm_toEReal_mem_gammaZero
    (N : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ((fun u : EuclideanSpace ℝ (Fin N) ↦ ‖u‖_[q]).toEReal) ∈
      Γ₀(EuclideanSpace ℝ (Fin N)) := by
  let L :=
    ((PiLp.continuousLinearEquiv q ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap).comp
      (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  have hcont : Continuous (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖L u‖) := by
    -- The coordinate `ℓ^q` norm is the ordinary norm after transporting along `L`.
    exact continuous_norm.comp L.continuous
  have hconv : _root_.ConvexOn ℝ Set.univ (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖L u‖) := by
    -- Convexity is inherited from the norm by precomposition with the linear transport.
    simpa using
      (convexOn_univ_norm :
        _root_.ConvexOn ℝ Set.univ (fun z : _ ↦ ‖z‖)).comp_linearMap
        L.toLinearMap
  -- Package the transported norm via the Chapter 12 criterion, then unfold back to `‖u‖_[q]`.
  simpa [EuclideanSpace.lpNorm, L] using
    continuous_convexOn_univ_toEReal_mem_gammaZero
      (φ := fun u : EuclideanSpace ℝ (Fin N) ↦ ‖L u‖) hcont hconv

/-- Helper for Example 13 41: the indicator of the coordinate `ℓ^p` closed unit ball belongs to
`Γ₀`. -/
lemma indicator_lpClosedUnitBall_mem_gammaZero
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ι[lpClosedUnitBall N p] ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  have hnonempty : (lpClosedUnitBall N p).Nonempty := by
    -- The origin belongs to the unit ball because its `ℓ^p` norm is `0`.
    refine ⟨0, ?_⟩
    rw [Set.mem_lpClosedUnitBall_iff]
    simp [EuclideanSpace.lpNorm]
  have hclosed : IsClosed (lpClosedUnitBall N p) := by
    -- The unit ball is the closed sublevel set `{u | ‖u‖_[p] ≤ 1}` of a continuous function.
    have hcont :
        Continuous (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖u‖_[p]) := by
      let L :=
        ((PiLp.continuousLinearEquiv p ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap).comp
          (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
      simpa [EuclideanSpace.lpNorm, L] using
        (continuous_norm.comp L.continuous :
          Continuous (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖L u‖))
    simpa [Set.lpClosedUnitBall, Set.preimage, Set.setOf_mem_eq] using
      isClosed_Iic.preimage hcont
  have hconv : Convex ℝ (lpClosedUnitBall N p) := by
    -- The unit ball is the `≤ 1` sublevel set of a convex norm.
    have hnorm_conv :
        _root_.ConvexOn ℝ Set.univ (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖u‖_[p]) := by
      let L :=
        ((PiLp.continuousLinearEquiv p ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap).comp
          (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
      simpa [EuclideanSpace.lpNorm, L] using
        (convexOn_univ_norm :
          _root_.ConvexOn ℝ Set.univ (fun z : _ ↦ ‖z‖)).comp_linearMap
          L.toLinearMap
    simpa [Set.lpClosedUnitBall, Set.setOf_mem_eq] using hnorm_conv.convex_le (1 : ℝ)
  have hindicator_lsc :
      LowerSemicontinuous
        (fun y : EuclideanSpace ℝ (Fin N) ↦ ((ι[lpClosedUnitBall N p]) y : EReal)) := by
    -- Closedness of the ball is equivalent to lower semicontinuity of its indicator.
    simpa using
      (lowerSemicontinuous_indicator_compl_top_iff_isClosed (lpClosedUnitBall N p)).2 hclosed
  have hindicator_dom :
      effectiveDomain (ι[lpClosedUnitBall N p]) = lpClosedUnitBall N p := by
    -- The indicator is finite exactly on the set itself.
    ext y
    by_cases hy : y ∈ lpClosedUnitBall N p
    · simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
    · simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  -- Repackage the closed convex indicator directly into the `Γ₀` structure.
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hnonempty, fun _ hy ↦ hy, ?_⟩
  intro x hx y hy a ha0 ha1
  have hx_ball : x ∈ lpClosedUnitBall N p := by
    simpa [hindicator_dom] using hx
  have hy_ball : y ∈ lpClosedUnitBall N p := by
    simpa [hindicator_dom] using hy
  have hxy_ball : a • x + (1 - a) • y ∈ lpClosedUnitBall N p :=
    hconv hx_ball hy_ball ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hx_ball, hy_ball, hxy_ball]

/-- Helper for Example 13 41: every value of the support function of the coordinate `ℓ^p` unit
ball is bounded above by the coordinate `ℓ^{p*}` norm. -/
lemma supportFunction_lpClosedUnitBall_le_lpNorm_conjExponent
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    σ[lpClosedUnitBall N p] ≤
      fun u : EuclideanSpace ℝ (Fin N) ↦ (‖u‖_[p.conjExponent] : EReal) := by
  letI : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  intro u
  by_cases hu : u = 0
  · -- At the origin, every support value vanishes.
    subst hu
    rw [supportFunction_eq_sSup_image]
    refine sSup_le ?_
    intro b hb
    rcases hb with ⟨x, hx, rfl⟩
    simp
  · have hnorm_ne_zero : EuclideanSpace.lpNorm N p.conjExponent u ≠ 0 := by
      exact fun hzero ↦ hu ((lpNorm_eq_zero_iff N p.conjExponent u).1 hzero)
    have hnorm_nonneg : 0 ≤ EuclideanSpace.lpNorm N p.conjExponent u := by
      rw [EuclideanSpace.lpNorm_apply]
      exact norm_nonneg _
    have hnorm_pos : 0 < EuclideanSpace.lpNorm N p.conjExponent u := by
      exact lt_of_le_of_ne hnorm_nonneg (by simpa using hnorm_ne_zero.symm)
    let c : ℝ := (EuclideanSpace.lpNorm N p.conjExponent u)⁻¹
    have hc_pos : 0 < c := by
      simpa [c] using inv_pos.mpr hnorm_pos
    have hu_scaled_mem : c • u ∈ lpClosedUnitBall N p.conjExponent := by
      -- Normalizing by the conjugate norm lands on the conjugate unit sphere.
      rw [Set.mem_lpClosedUnitBall_iff]
      have hscale :
        EuclideanSpace.lpNorm N p.conjExponent (c • u)
            = ‖c‖ * EuclideanSpace.lpNorm N p.conjExponent u :=
          lpNorm_smul N p.conjExponent c u
      have habs : ‖c‖ = c := by
        simp [Real.norm_eq_abs, abs_of_pos hc_pos]
      have hnorm_one : EuclideanSpace.lpNorm N p.conjExponent (c • u) = 1 := by
        calc
          EuclideanSpace.lpNorm N p.conjExponent (c • u)
              = ‖c‖ * EuclideanSpace.lpNorm N p.conjExponent u := hscale
          _ = c * EuclideanSpace.lpNorm N p.conjExponent u := by rw [habs]
          _ = 1 := by
            change (EuclideanSpace.lpNorm N p.conjExponent u)⁻¹ *
                EuclideanSpace.lpNorm N p.conjExponent u = 1
            exact inv_mul_cancel₀ hnorm_ne_zero
      exact hnorm_one.le
    rw [supportFunction_eq_sSup_image]
    refine sSup_le ?_
    intro b hb
    rcases hb with ⟨x, hx, rfl⟩
    have hx_le_one : EuclideanSpace.lpNorm N p x ≤ 1 := by
      rw [Set.mem_lpClosedUnitBall_iff] at hx
      exact hx
    have hinner_scaled :
        ⟪x, c • u⟫_ℝ ≤ EuclideanSpace.lpNorm N p x :=
      inner_le_lpNorm_of_mem_conj_ball N p hu_scaled_mem x
    have hinner_le_one : c * ⟪x, u⟫_ℝ ≤ 1 := by
      calc
        c * ⟪x, u⟫_ℝ = ⟪x, c • u⟫_ℝ := by rw [real_inner_smul_right]
        _ ≤ EuclideanSpace.lpNorm N p x := hinner_scaled
        _ ≤ 1 := hx_le_one
    have hinner_le_div : ⟪x, u⟫_ℝ ≤ 1 / c := by
      rw [le_div_iff₀ hc_pos]
      simpa [mul_comm] using hinner_le_one
    have hc_inv : 1 / c = EuclideanSpace.lpNorm N p.conjExponent u := by
      simp [c]
    have hinner_le :
        ⟪x, u⟫_ℝ ≤ EuclideanSpace.lpNorm N p.conjExponent u := by
      rwa [hc_inv] at hinner_le_div
    change ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
        ((EuclideanSpace.lpNorm N p.conjExponent u : ℝ) : EReal)
    exact_mod_cast hinner_le

/-- Helper for Example 13 41: every positive real threshold strictly below the coordinate
`ℓ^{p*}` norm is exceeded by pairing with some point of the primal `ℓ^p` unit ball. -/
lemma exists_mem_lpClosedUnitBall_inner_gt_of_pos_lt_lpNorm_conjExponent
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {u : EuclideanSpace ℝ (Fin N)} {r : ℝ}
    (hr_pos : 0 < r) (hr : r < ‖u‖_[p.conjExponent]) :
    ∃ x ∈ lpClosedUnitBall N p, r < ⟪x, u⟫_ℝ := by
  letI : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let v : EuclideanSpace ℝ (Fin N) := r⁻¹ • u
  have hv_not_mem : v ∉ lpClosedUnitBall N p.conjExponent := by
    -- Scaling by `r⁻¹` pushes `u` outside the conjugate ball because `r` is too small.
    intro hv_mem
    have hscale :
        EuclideanSpace.lpNorm N p.conjExponent v =
          ‖r⁻¹‖ * EuclideanSpace.lpNorm N p.conjExponent u := by
      simpa [v] using lpNorm_smul N p.conjExponent r⁻¹ u
    have hv_scaled_le : r⁻¹ * EuclideanSpace.lpNorm N p.conjExponent u ≤ 1 := by
      have hnorm_inv : ‖r⁻¹‖ = r⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr hr_pos.le)
      calc
        r⁻¹ * EuclideanSpace.lpNorm N p.conjExponent u
            = ‖r⁻¹‖ * EuclideanSpace.lpNorm N p.conjExponent u := by
                rw [hnorm_inv]
        _ = EuclideanSpace.lpNorm N p.conjExponent v := hscale.symm
        _ ≤ 1 := by
              simpa [Set.mem_lpClosedUnitBall_iff] using hv_mem
    have hnorm_le_r : EuclideanSpace.lpNorm N p.conjExponent u ≤ r := by
      have hmul :
          r * (r⁻¹ * EuclideanSpace.lpNorm N p.conjExponent u) ≤ r * 1 :=
        mul_le_mul_of_nonneg_left hv_scaled_le hr_pos.le
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      calc
        EuclideanSpace.lpNorm N p.conjExponent u
            = r * (r⁻¹ * EuclideanSpace.lpNorm N p.conjExponent u) := by
                calc
                  EuclideanSpace.lpNorm N p.conjExponent u
                      = 1 * EuclideanSpace.lpNorm N p.conjExponent u := by ring
                  _ = (r * r⁻¹) * EuclideanSpace.lpNorm N p.conjExponent u := by
                        simp [hr_ne]
                  _ = r * (r⁻¹ * EuclideanSpace.lpNorm N p.conjExponent u) := by ring
        _ ≤ r * 1 := hmul
        _ = r := by ring
    exact (not_le_of_gt hr) hnorm_le_r
  have hv_not_polar : v ∉ polarSet (lpClosedUnitBall N p) := by
    -- The public Exercise 7.9 identification converts the norm obstruction
    -- into polar nonmembership.
    rw [Set.polarSet_lpClosedUnitBall_eq_conj_unitBall]
    exact hv_not_mem
  rw [Set.mem_polarSet_iff_forall_inner_le_one (C := lpClosedUnitBall N p) (u := v)] at hv_not_polar
  push Not at hv_not_polar
  rcases hv_not_polar with ⟨x, hx, hx_gt⟩
  refine ⟨x, hx, ?_⟩
  have hscaled_inner : 1 < r⁻¹ * ⟪x, u⟫_ℝ := by
    -- Rewrite the violating polar inequality in scaled-inner-product form.
    simpa [v, real_inner_smul_right] using hx_gt
  have hmul : r * 1 < r * (r⁻¹ * ⟪x, u⟫_ℝ) :=
    mul_lt_mul_of_pos_left hscaled_inner hr_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  -- Multiply back by `r` to recover a strict lower bound for the original inner product.
  calc
    r = r * 1 := by ring
    _ < r * (r⁻¹ * ⟪x, u⟫_ℝ) := hmul
    _ = ⟪x, u⟫_ℝ := by
          rw [← mul_assoc]
          simp [hr_ne]

/-- Helper for Example 13 41: every real threshold strictly below the coordinate `ℓ^{p*}` norm is
exceeded by pairing with some point of the primal `ℓ^p` unit ball. -/
lemma exists_mem_lpClosedUnitBall_inner_gt_of_lt_lpNorm_conjExponent
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {u : EuclideanSpace ℝ (Fin N)} {r : ℝ}
    (hr : r < ‖u‖_[p.conjExponent]) :
    ∃ x ∈ lpClosedUnitBall N p, r < ⟪x, u⟫_ℝ := by
  by_cases hr_neg : r < 0
  · -- Negative thresholds are already beaten by the origin.
    refine ⟨0, ?_, ?_⟩
    · rw [Set.mem_lpClosedUnitBall_iff]
      simp [EuclideanSpace.lpNorm]
    · simpa using hr_neg
  · have hr_nonneg : 0 ≤ r := le_of_not_gt hr_neg
    let s : ℝ := (r + ‖u‖_[p.conjExponent]) / 2
    have hs_pos : 0 < s := by
      -- The midpoint with the norm is positive because `r` is nonnegative and strictly smaller.
      have hnorm_pos : 0 < ‖u‖_[p.conjExponent] := lt_of_le_of_lt hr_nonneg hr
      have hsum_pos : 0 < r + ‖u‖_[p.conjExponent] :=
        add_pos_of_nonneg_of_pos hr_nonneg hnorm_pos
      dsimp [s]
      exact div_pos hsum_pos (by norm_num)
    have hs_lt : s < ‖u‖_[p.conjExponent] := by
      -- The midpoint lies strictly below the upper endpoint.
      have hdiv_lt :
          (r + ‖u‖_[p.conjExponent]) / 2 < ‖u‖_[p.conjExponent] := by
        refine (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2 ?_
        nlinarith [hr]
      dsimp [s]
      exact hdiv_lt
    have hr_lt_s : r < s := by
      -- The same midpoint lies strictly above the lower endpoint.
      have hdiv_lt :
          r < (r + ‖u‖_[p.conjExponent]) / 2 := by
        refine (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 ?_
        nlinarith [hr]
      dsimp [s]
      exact hdiv_lt
    rcases exists_mem_lpClosedUnitBall_inner_gt_of_pos_lt_lpNorm_conjExponent
        N p hs_pos hs_lt with ⟨x, hx, hx_gt⟩
    exact ⟨x, hx, lt_trans hr_lt_s hx_gt⟩

/-- Helper for Example 13 41: pointwise, the coordinate `ℓ^{p*}` norm is bounded above by the
support function of the coordinate `ℓ^p` unit ball. -/
lemma lpNorm_conjExponent_le_supportFunction_lpClosedUnitBall
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (fun u : EuclideanSpace ℝ (Fin N) ↦ (‖u‖_[p.conjExponent] : EReal)) ≤
      σ[lpClosedUnitBall N p] := by
  intro u
  refine le_of_forall_lt fun ξ hξ ↦ ?_
  rcases EReal.lt_iff_exists_real_btwn.mp hξ with ⟨r, hξ_lt, hr_lt⟩
  have hr_lt_norm : r < ‖u‖_[p.conjExponent] := EReal.coe_lt_coe_iff.mp hr_lt
  rcases exists_mem_lpClosedUnitBall_inner_gt_of_lt_lpNorm_conjExponent
      N p hr_lt_norm with ⟨x, hx, hx_gt⟩
  have hr_lt_support : (r : EReal) < σ[lpClosedUnitBall N p] u := by
    have himage :
        (((⟪x, u⟫_ℝ : ℝ) : EReal)) ∈
          (fun y : EuclideanSpace ℝ (Fin N) ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal)) ''
            lpClosedUnitBall N p :=
      Set.mem_image_of_mem _ hx
    have hr_lt_inner : (r : EReal) < (((⟪x, u⟫_ℝ : ℝ) : EReal)) := by
      exact_mod_cast hx_gt
    -- A witness in the image gives a strict lower bound for the support supremum.
    exact lt_of_lt_of_le hr_lt_inner <| by
      rw [supportFunction_eq_sSup_image]
      exact le_sSup himage
  exact lt_trans hξ_lt hr_lt_support

-- Proof sketch: keep the existing upper bound from Hölder's inequality and prove the reverse
-- bound by extracting strict lower-bound witnesses from polar-set nonmembership after scaling.
/-- Example 13 41: the support function of the coordinate `ℓ^p` unit ball in `ℝ^N` is the
coordinate `ℓ^{p*}` norm, written on the theorem surface with the Chapter 7 notation
`u ↦ ‖u‖_[p*]` and viewed in `EReal`. -/
theorem lpDualNorm_eq_lpNorm_conjExponent
    (N : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    σ[lpClosedUnitBall N p] =
      fun u ↦ (‖u‖_[p.conjExponent] : EReal) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  have hupper :
      σ[lpClosedUnitBall N p] ≤
        fun u : EuclideanSpace ℝ (Fin N) ↦ (‖u‖_[p.conjExponent] : EReal) :=
    supportFunction_lpClosedUnitBall_le_lpNorm_conjExponent N p
  have hlower :
      (fun u : EuclideanSpace ℝ (Fin N) ↦ (‖u‖_[p.conjExponent] : EReal)) ≤
        σ[lpClosedUnitBall N p] :=
    lpNorm_conjExponent_le_supportFunction_lpClosedUnitBall N p
  -- Route correction: use the direct Exercise 7.9 polar-witness argument for the reverse bound.
  exact le_antisymm hupper hlower

end ERealFunction
