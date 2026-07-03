import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Taylor

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology ContDiff
open Filter
open FormalMultilinearSeries

-- Domain sampling note: the textbook derivative-growth criterion is source-facing, and this
-- theorem is the bridge/view to Mathlib's owner abstraction `AnalyticOnNhd`. The supporting
-- chapter/mathlib API checked here is
-- `AnalyticAt.hasFPowerSeriesAt`, `HasFPowerSeriesOnBall.exchange_radius`,
-- `norm_iteratedDeriv_ofScalarsSum_div_factorial_le_powerSeriesAbsSum`, and
-- `Set.EqOn.iteratedDeriv_of_isOpen`.

variable {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {D : Set 𝕜}

/-- Helper for Theorem I.4-extra-2: reindexing the global change-of-origin majorant by total
degree recovers the scalar majorant at radius `r₀ + R`. -/
private lemma changeOrigin_global_majorant_tsum_eq
    (P : FormalMultilinearSeries 𝕜 𝕜 𝕜) (r₀ R : NNReal)
    (hR : (↑(r₀ + R) : ENNReal) < P.radius) :
    (∑' s : Σ k l : ℕ, { t : Finset (Fin (k + l)) // t.card = l },
      ‖P (s.1 + s.2.1)‖₊ * r₀ ^ s.2.1 * R ^ s.1) =
      ∑' n : ℕ, ‖P n‖₊ * (r₀ + R) ^ n := by
  have hsummable :
      Summable
        (fun s : Σ k l : ℕ, { t : Finset (Fin (k + l)) // t.card = l } ↦
          ‖P (s.1 + s.2.1)‖₊ * r₀ ^ s.2.1 * R ^ s.1) :=
    P.changeOriginSeries_summable_aux₁ hR
  have hrew :
      Summable
        (fun s : Σ n : ℕ, Finset (Fin n) ↦
          ‖P (s.1 - s.2.card + s.2.card)‖₊ * r₀ ^ s.2.card * R ^ (s.1 - s.2.card)) := by
    -- Reindex the sigma-series by total degree.
    simpa only [Function.comp_def, changeOriginIndexEquiv_symm_apply_fst,
      changeOriginIndexEquiv_symm_apply_snd_fst] using
      (changeOriginIndexEquiv.symm.summable_iff.2 hsummable)
  have hfiber :
      ∀ n : ℕ,
        HasSum
          (fun s : Finset (Fin n) ↦
            ‖P (n - s.card + s.card)‖₊ * r₀ ^ s.card * R ^ (n - s.card))
          (‖P n‖₊ * (r₀ + R) ^ n) := by
    intro n
    -- Each total-degree fiber is the binomial expansion of `(r₀ + R)^n`.
    convert_to
      HasSum (fun s : Finset (Fin n) ↦ ‖P n‖₊ * (r₀ ^ s.card * R ^ (n - s.card)))
        (‖P n‖₊ * (r₀ + R) ^ n)
    · ext s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assoc]
    rw [← Fin.sum_pow_mul_eq_add_pow]
    exact (hasSum_fintype _).mul_left _
  -- Collapse the sigma-sum fiberwise after the reindexing.
  rw [← changeOriginIndexEquiv.symm.tsum_eq]
  calc
    ∑' s : Σ n : ℕ, Finset (Fin n),
        ‖P (s.1 - s.2.card + s.2.card)‖₊ * r₀ ^ s.2.card * R ^ (s.1 - s.2.card) =
      ∑' n : ℕ, ∑' s : Finset (Fin n),
        ‖P (n - s.card + s.card)‖₊ * r₀ ^ s.card * R ^ (n - s.card) := by
        exact hrew.tsum_sigma' (fun n ↦ (hfiber n).summable)
    _ = ∑' n : ℕ, ‖P n‖₊ * (r₀ + R) ^ n := by
        refine tsum_congr fun n ↦ ?_
        exact (hfiber n).tsum_eq

/-- Helper for Theorem I.4-extra-2: the fixed `p`-fiber of the change-of-origin majorant is
bounded by the full majorant divided by `R ^ p`. -/
private lemma fixed_changeOrigin_fiber_le_div_global_majorant
    (P : FormalMultilinearSeries 𝕜 𝕜 𝕜) (p : ℕ) (r₀ R : NNReal)
    (hR : 0 < R) (hr : (↑(r₀ + R) : ENNReal) < P.radius) :
    (∑' s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l },
      ‖P (p + s.1)‖₊ * r₀ ^ s.1) ≤
      (∑' n : ℕ, ‖P n‖₊ * (r₀ + R) ^ n) / R ^ p := by
  let G :
      (Σ k l : ℕ, { t : Finset (Fin (k + l)) // t.card = l }) → NNReal :=
    fun s ↦ ‖P (s.1 + s.2.1)‖₊ * r₀ ^ s.2.1 * R ^ s.1
  have hGsummable : Summable G := by
    -- This is the global sigma-majorant furnished by the change-of-origin API.
    simpa only [G] using P.changeOriginSeries_summable_aux₁ hr
  have hfiber_mul_le :
      (∑' s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l },
        ‖P (p + s.1)‖₊ * r₀ ^ s.1) * R ^ p ≤
        ∑' s, G s := by
    -- Embed the fixed `p`-fiber into the full sigma-majorant via `Sigma.mk p`.
    calc
      (∑' s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l },
          ‖P (p + s.1)‖₊ * r₀ ^ s.1) * R ^ p =
        ∑' s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l },
          (‖P (p + s.1)‖₊ * r₀ ^ s.1) * R ^ p := by
          rw [← NNReal.tsum_mul_right]
      _ = ∑' s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l }, G (Sigma.mk p s) := by
          refine tsum_congr fun s ↦ ?_
          simp only [G, mul_assoc]
      _ ≤ ∑' s, G s := NNReal.tsum_comp_le_tsum_of_inj hGsummable sigma_mk_injective
  have hRpow_pos : 0 < R ^ p := pow_pos hR p
  -- Divide by the positive gap factor `R ^ p`.
  refine (le_div_iff₀ hRpow_pos).2 ?_
  simpa only [G] using hfiber_mul_le.trans_eq (changeOrigin_global_majorant_tsum_eq P r₀ R hr)

/-- Helper for Theorem I.4-extra-2: the coefficients of the recentered scalar series are bounded
by the absolute-value scalar majorant. -/
theorem norm_changeOrigin_coeff_le_powerSeriesAbsSum
    (a : ℕ → 𝕜) (p : ℕ) {r r₀ : ℝ} {x : 𝕜}
    (hr : ENNReal.ofReal r < (ofScalars 𝕜 a).radius)
    (hx : ‖x‖ ≤ r₀) (hr₀ : r₀ < r) :
    ‖((ofScalars 𝕜 a).changeOrigin x).coeff p‖ ≤
      ofScalarsSum (fun n ↦ ‖a n‖) r / (r - r₀) ^ p := by
  let P : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  let u : NNReal := ‖x‖₊
  have hu_lt_radius : ((u : ENNReal) < P.radius) := by
    -- The recentering point stays inside the original convergence radius.
    simpa [P, u] using
      (ENNReal.coe_lt_ofReal.2 (lt_of_le_of_lt hx hr₀)).trans hr
  have hcoeff_norm :
      ‖P.changeOrigin x p‖₊ = ‖(P.changeOrigin x).coeff p‖₊ := by
    -- In the scalar-series case, operator norms and coefficient norms agree.
    apply Subtype.ext
    simpa using (FormalMultilinearSeries.norm_apply_eq_norm_coef (p := P.changeOrigin x) (n := p))
  have hcoeffs :
      ∀ n : ℕ, ‖P n‖₊ = ‖a n‖₊ := by
    intro n
    -- The `n`-th multilinear term of `ofScalars` has coefficient `a n`.
    apply Subtype.ext
    simpa [P] using (FormalMultilinearSeries.norm_apply_eq_norm_coef (p := P) (n := n))
  let fiberTerm :
      (Σ l : ℕ, { s : Finset (Fin (p + l)) // s.card = l }) → NNReal :=
    fun s ↦ ‖P (p + s.1)‖₊ * u ^ s.1
  have hcoeff_nn :
      ‖(P.changeOrigin x).coeff p‖₊ ≤ ∑' s, fiberTerm s := by
    -- `nnnorm_changeOrigin_le` isolates the fixed-order change-of-origin fiber.
    simpa [fiberTerm, u, hcoeff_norm] using P.nnnorm_changeOrigin_le (x := x) p hu_lt_radius
  have hr₀_nonneg : 0 ≤ r₀ := le_trans (norm_nonneg x) hx
  have hr_pos : 0 < r := lt_of_le_of_lt hr₀_nonneg hr₀
  have hgap_pos : 0 < r - r₀ := sub_pos.mpr hr₀
  let R : NNReal := ⟨r - r₀, hgap_pos.le⟩
  let rN : NNReal := ⟨r, hr_pos.le⟩
  let r₀N : NNReal := ⟨r₀, hr₀_nonneg⟩
  have hmajorant_nn :
      ∑' s, fiberTerm s ≤ (∑' n : ℕ, ‖P n‖₊ * rN ^ n) / R ^ p := by
    have hu_le_r₀N : u ≤ r₀N := by
      -- The center norm is bounded by the chosen inner radius.
      simpa only [u, r₀N] using hx
    have hr_split : r₀N + R = rN := by
      -- The majorant radius decomposes as `r = r₀ + (r - r₀)`.
      apply Subtype.ext
      change r₀ + (r - r₀) = r
      linarith
    have hr_majorant : (↑(r₀N + R) : ENNReal) < P.radius := by
      calc
        (↑(r₀N + R) : ENNReal) = (rN : ENNReal) := by simp [hr_split]
        _ = ENNReal.ofReal r := by
          simpa [rN] using (ENNReal.ofReal_eq_coe_nnreal hr_pos.le).symm
        _ < P.radius := hr
    have hfiber_mono :
        ∑' s, fiberTerm s ≤
          ∑' s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l },
            ‖P (p + s.1)‖₊ * r₀N ^ s.1 := by
      have hu_summable :
          Summable
            (fun s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l } ↦
              ‖P (p + s.1)‖₊ * u ^ s.1) :=
        P.changeOriginSeries_summable_aux₂ hu_lt_radius p
      have hr₀_lt_radius : (↑r₀N : ENNReal) < P.radius := by
        exact (ENNReal.coe_le_coe.2 <| le_add_right le_rfl).trans_lt hr_majorant
      have hr₀_summable :
          Summable
            (fun s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l } ↦
              ‖P (p + s.1)‖₊ * r₀N ^ s.1) :=
        P.changeOriginSeries_summable_aux₂ hr₀_lt_radius p
      -- Replace `‖x‖₊` by the larger radius `r₀`.
      refine Summable.tsum_le_tsum (fun s ↦ ?_) hu_summable hr₀_summable
      dsimp only [fiberTerm]
      gcongr
    -- Compare the fixed fiber to the full scalar majorant at radius `r`.
    exact hfiber_mono.trans <| by
      simpa only [hr_split] using
        fixed_changeOrigin_fiber_le_div_global_majorant P p r₀N R hgap_pos hr_majorant
  have hsum_eq :
      (((∑' n : ℕ, ‖P n‖₊ * rN ^ n : NNReal) : ℝ)) = ofScalarsSum (fun n ↦ ‖a n‖) r := by
    -- The `NNReal` majorant sum is exactly the textbook scalar absolute-value series.
    have hterm : ∀ n : ℕ, ↑(‖P n‖₊ * rN ^ n : NNReal) = ‖a n‖ * r ^ n := by
      intro n
      calc
        ↑(‖P n‖₊ * rN ^ n : NNReal) = ‖P n‖ * (rN : ℝ) ^ n := by
          simp
        _ = ‖P.coeff n‖ * (rN : ℝ) ^ n := by
          rw [FormalMultilinearSeries.norm_apply_eq_norm_coef (p := P) (n := n)]
        _ = ‖P.coeff n‖ * r ^ n := by
          have hrN_pow : ((rN : ℝ) ^ n) = r ^ n := by rfl
          rw [hrN_pow]
        _ = ‖a n‖ * r ^ n := by
          simp [P]
    rw [NNReal.coe_tsum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
    simpa [hterm]
  have hmajorant_real :
      ‖(P.changeOrigin x).coeff p‖ ≤
        ((((∑' n : ℕ, ‖P n‖₊ * rN ^ n : NNReal) / R ^ p : NNReal) : ℝ)) := by
    exact_mod_cast (le_trans hcoeff_nn hmajorant_nn)
  -- Convert the `NNReal` estimate back to the real-valued denominator `(r - r₀)^p`.
  calc
    ‖(P.changeOrigin x).coeff p‖ ≤
        ((((∑' n : ℕ, ‖P n‖₊ * rN ^ n : NNReal) / R ^ p : NNReal) : ℝ)) := hmajorant_real
    _ = ofScalarsSum (fun n ↦ ‖a n‖) r / (r - r₀) ^ p := by
        rw [NNReal.coe_div, NNReal.coe_pow, hsum_eq]
        rw [show (R : ℝ) = r - r₀ by rfl]

section

variable [CompleteSpace 𝕜] [CharZero 𝕜]

/-- Helper for Theorem I.4-extra-2: the normalized iterated derivatives of a convergent scalar
power series obey the same absolute-value majorant estimate after recentering. -/
theorem norm_iteratedDeriv_ofScalarsSum_div_factorial_le_powerSeriesAbsSum
    (a : ℕ → 𝕜) (p : ℕ) {r r₀ : ℝ} {x : 𝕜}
    (hr : ENNReal.ofReal r < (ofScalars 𝕜 a).radius)
    (hx : ‖x‖ ≤ r₀) (hr₀ : r₀ < r) :
    ‖iteratedDeriv p (ofScalarsSum a) x / (p.factorial : 𝕜)‖ ≤
      ofScalarsSum (fun n ↦ ‖a n‖) r / (r - r₀) ^ p := by
  have hr₀_nonneg : 0 ≤ r₀ := le_trans (norm_nonneg x) hx
  have hr_pos : 0 < r := lt_of_le_of_lt hr₀_nonneg hr₀
  have hxr : ‖x‖ < r := lt_of_le_of_lt hx hr₀
  have hseries :
      HasFPowerSeriesOnBall (ofScalarsSum a) (ofScalars 𝕜 a) 0 (ENNReal.ofReal r) := by
    have hradius_pos : 0 < (ofScalars 𝕜 a).radius := lt_of_le_of_lt bot_le hr
    -- Restrict the canonical scalar-series expansion to the working radius `r`.
    exact
      ((ofScalars 𝕜 a).hasFPowerSeriesOnBall hradius_pos).mono
        (ENNReal.ofReal_pos.mpr hr_pos) hr.le
  have hshift :
      HasFPowerSeriesAt
        (fun z ↦ ofScalarsSum a (z + x))
        ((ofScalars 𝕜 a).changeOrigin x) 0 := by
    -- Recenter the power series at the evaluation point `x`.
    simpa [sub_eq_add_neg] using
      ((hseries.changeOrigin <| ENNReal.coe_lt_ofReal.2 hxr).comp_sub (-x)).hasFPowerSeriesAt
  have hcoeff :
      ((ofScalars 𝕜 a).changeOrigin x).coeff p =
        iteratedDeriv p (ofScalarsSum a) x / (p.factorial : 𝕜) := by
    have hformal :
        ofScalars 𝕜 (fun n ↦ iteratedDeriv n (fun z ↦ ofScalarsSum a (z + x)) 0 / n.factorial) =
          (ofScalars 𝕜 a).changeOrigin x :=
      (hshift.analyticAt.hasFPowerSeriesAt).eq_formalMultilinearSeries hshift
    -- The coefficient of the recentered series is the normalized derivative at `x`.
    simpa [iteratedDeriv_comp_add_const] using
      congrArg (fun q : FormalMultilinearSeries 𝕜 𝕜 𝕜 ↦ q.coeff p) hformal.symm
  -- Now reuse the coefficient estimate for the recentered scalar series.
  simpa [hcoeff] using norm_changeOrigin_coeff_le_powerSeriesAbsSum a p hr hx hr₀

end

/-- Helper for Theorem I.4-extra-2: analyticity at a point yields a smaller ball on which the
normalized iterated derivatives admit a uniform geometric bound. -/
lemma analyticAt_has_local_bounded_normalized_iteratedDeriv
    (hD : IsOpen D) {x₀ : 𝕜} (hx₀ : x₀ ∈ D) (ha : AnalyticAt 𝕜 f x₀) :
    ∃ r M t : ℝ,
      0 < r ∧ Metric.ball x₀ r ⊆ D ∧ 0 < M ∧ 0 < t ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
          ‖iteratedDeriv p f x / (p.factorial : 𝕜)‖ ≤ M * t ^ p := by
  let a : ℕ → 𝕜 := fun n ↦ iteratedDeriv n f x₀ / n.factorial
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  obtain ⟨rD, hrD_pos, hrD_sub⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx₀)
  have hpAt : HasFPowerSeriesAt f p x₀ := by
    simpa [p, a] using ha.hasFPowerSeriesAt
  have hp_radius_pos : 0 < p.radius := hpAt.radius_pos
  -- Move the power series to the origin and work on a smaller explicit radius.
  obtain ⟨ρ, hρ⟩ := hpAt.comp_sub (-x₀)
  obtain ⟨R, hR_nonneg, hR_pos_ball, hR_lt_ρ⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hρ.r_pos
  have hR_pos : 0 < R := ENNReal.ofReal_pos.mp hR_pos_ball
  have hR_lt_radius : ENNReal.ofReal R < p.radius := lt_of_lt_of_le hR_lt_ρ hρ.r_le
  let r : ℝ := min rD (R / 2)
  let A : ℝ := ofScalarsSum (fun n ↦ ‖a n‖) R
  let M : ℝ := max 1 A
  let t : ℝ := (R - r)⁻¹
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min hrD_pos (half_pos hR_pos)
  have hr_le_rD : r ≤ rD := by
    dsimp [r]
    exact min_le_left _ _
  have hr_lt_R : r < R := by
    calc
      r ≤ R / 2 := by
        dsimp [r]
        exact min_le_right _ _
      _ < R := by
        nlinarith
  have ht_pos : 0 < t := by
    dsimp [t]
    exact inv_pos.mpr (sub_pos.mpr hr_lt_R)
  have hsum_full : HasFPowerSeriesOnBall (ofScalarsSum a) p 0 p.radius := by
    simpa [p, a] using p.hasFPowerSeriesOnBall hp_radius_pos
  have hsum_R : HasFPowerSeriesOnBall (ofScalarsSum a) p 0 (ENNReal.ofReal R) := by
    exact hsum_full.mono hR_pos_ball hR_lt_radius.le
  have hshift_R : HasFPowerSeriesOnBall (fun z ↦ f (z + x₀)) p 0 (ENNReal.ofReal R) := by
    simpa [sub_eq_add_neg] using hρ.mono hR_pos_ball hR_lt_ρ.le
  have hEqOn :
      Set.EqOn (fun z ↦ f (z + x₀)) (ofScalarsSum a) (Metric.eball 0 (ENNReal.ofReal R)) := by
    exact hshift_R.unique hsum_R
  refine ⟨r, M, t, hr_pos, ?_, by positivity, ht_pos, ?_⟩
  · -- The smaller analytic ball is chosen inside the original neighborhood contained in `D`.
    intro x hx
    exact hrD_sub (by
      simpa [Metric.mem_ball] using lt_of_lt_of_le hx hr_le_rD)
  · intro x hx q
    let y : 𝕜 := x - x₀
    have hy_lt_r : ‖y‖ < r := by
      simpa [y, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
    have hy_le_r : ‖y‖ ≤ r := le_of_lt hy_lt_r
    have hy_lt_R : ‖y‖ < R := lt_of_lt_of_le hy_lt_r hr_lt_R.le
    have hy_mem : y ∈ Metric.eball (0 : 𝕜) (ENNReal.ofReal R) := by
      simpa [Metric.mem_eball, edist_dist, hR_pos] using hy_lt_R
    have hiter_eq :
        iteratedDeriv q (fun z ↦ f (z + x₀)) y = iteratedDeriv q (ofScalarsSum a) y := by
      exact Set.EqOn.iteratedDeriv_of_isOpen hEqOn Metric.isOpen_eball q hy_mem
    have hshift_iter :
        iteratedDeriv q (fun z ↦ f (z + x₀)) y = iteratedDeriv q f x := by
      -- Shifting the input by a constant commutes with iterated derivatives.
      simpa [y, sub_eq_add_neg, add_assoc, sub_add_cancel] using
        congrArg (fun g : 𝕜 → 𝕜 ↦ g y) (iteratedDeriv_comp_add_const (f := f) (n := q) (s := x₀))
    have hbound_sum :
        ‖iteratedDeriv q (ofScalarsSum a) y / (q.factorial : 𝕜)‖ ≤ A / (R - r) ^ q := by
      simpa [A, p, a] using
        norm_iteratedDeriv_ofScalarsSum_div_factorial_le_powerSeriesAbsSum
          (𝕜 := 𝕜) a q hR_lt_radius hy_le_r hr_lt_R
    -- Transfer the estimate from the shifted scalar series back to the original function.
    calc
      ‖iteratedDeriv q f x / (q.factorial : 𝕜)‖
          = ‖iteratedDeriv q (fun z ↦ f (z + x₀)) y / (q.factorial : 𝕜)‖ := by
              rw [← hshift_iter]
      _ = ‖iteratedDeriv q (ofScalarsSum a) y / (q.factorial : 𝕜)‖ := by
            rw [hiter_eq]
      _ ≤ A / (R - r) ^ q := hbound_sum
      _ ≤ M / (R - r) ^ q := by
            have hA_le_M : A ≤ M := by
              dsimp [M]
              exact le_max_right _ _
            have hpow_nonneg : 0 ≤ (R - r) ^ q := pow_nonneg (sub_nonneg.mpr hr_lt_R.le) q
            exact div_le_div_of_nonneg_right hA_le_M hpow_nonneg
      _ = M * t ^ q := by
            rw [div_eq_mul_inv, inv_pow]

/-- Helper for Theorem I.4-extra-2: a pointwise geometric bound on the centered normalized
iterated derivatives gives the reciprocal growth rate as a lower bound for the centered scalar
Taylor radius. -/
lemma formal_series_radius_ge_inv_of_center_growth_bound
    {K : Type*} [NontriviallyNormedField K] {g : K → K} {x₀ : K} {M t : ℝ}
    (hM : 0 < M) (ht : 0 < t)
    (hbound : ∀ n : ℕ, ‖iteratedDeriv n g x₀ / (n.factorial : K)‖ ≤ M * t ^ n) :
    ENNReal.ofReal t⁻¹ ≤
      (FormalMultilinearSeries.ofScalars K
          (fun n ↦ iteratedDeriv n g x₀ / (n.factorial : K))).radius := by
  let a : ℕ → K := fun n ↦ iteratedDeriv n g x₀ / (n.factorial : K)
  let p : FormalMultilinearSeries K K K := FormalMultilinearSeries.ofScalars K a
  let r : NNReal := ⟨t⁻¹, inv_nonneg.mpr ht.le⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hr_le : (r : ENNReal) ≤ p.radius := by
    -- The centered coefficients are dominated by the same geometric majorant at the reciprocal
    -- radius `t⁻¹`.
    refine p.le_radius_of_bound M fun n ↦ ?_
    have hcoeff :
        ‖p n‖ = ‖a n‖ := by
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, FormalMultilinearSeries.coeff_ofScalars]
    rw [hcoeff]
    calc
      ‖a n‖ * (r : ℝ) ^ n = ‖a n‖ * t⁻¹ ^ n := by rfl
      _ ≤ (M * t ^ n) * t⁻¹ ^ n := by
        exact mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg (inv_nonneg.mpr ht.le) _)
      _ = M * (t ^ n * t⁻¹ ^ n) := by rw [mul_assoc]
      _ = M * ((t * t⁻¹) ^ n) := by rw [← mul_pow]
      _ = M := by rw [mul_inv_cancel₀ ht_ne, one_pow, mul_one]
  -- Rewrite the chosen `NNReal` radius back to the source-facing real reciprocal `t⁻¹`.
  have hr_eq : (r : ENNReal) = ENNReal.ofReal t⁻¹ := by
    exact (ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr ht.le)).symm
  simpa [p, a, hr_eq] using hr_le

/-- Helper for Theorem I.4-extra-2: the previous lower bound immediately implies positivity of the
centered scalar Taylor radius. -/
lemma formal_series_radius_pos_of_center_growth_bound
    {K : Type*} [NontriviallyNormedField K] {g : K → K} {x₀ : K} {M t : ℝ}
    (hM : 0 < M) (ht : 0 < t)
    (hbound : ∀ n : ℕ, ‖iteratedDeriv n g x₀ / (n.factorial : K)‖ ≤ M * t ^ n) :
    0 <
      (FormalMultilinearSeries.ofScalars K
          (fun n ↦ iteratedDeriv n g x₀ / (n.factorial : K))).radius := by
  -- The strengthened reciprocal-radius estimate is the exact input needed later; positivity is
  -- its immediate corollary.
  have hradius :=
    formal_series_radius_ge_inv_of_center_growth_bound (g := g) (x₀ := x₀) hM ht hbound
  have ht_inv_pos : 0 < t⁻¹ := inv_pos.mpr ht
  have hzero_lt : (0 : ENNReal) < ENNReal.ofReal t⁻¹ := by
    exact ENNReal.ofReal_pos.mpr ht_inv_pos
  exact lt_of_lt_of_le hzero_lt hradius

/-- Helper for Theorem I.4-extra-2: if the endpoint `x` lies in a smaller ball around `x₀`, then
the whole real segment `x₀ + s • (x - x₀)` for `s ∈ [0,1]` stays in the larger ball. -/
private lemma line_point_mem_ball_of_mem_Icc
    {K : Type*} [RCLike K] {x₀ x : K} {ρ r s : ℝ} (hx : ‖x - x₀‖ < ρ) (hρr : ρ ≤ r)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    x₀ + (s : K) * (x - x₀) ∈ Metric.ball x₀ r := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hs_abs_le : |s| ≤ 1 := by
    rw [abs_of_nonneg hs.1]
    exact hs.2
  have hsub :
      (x₀ + (s : K) * (x - x₀)) - x₀ = (s : K) * (x - x₀) := by
    abel_nf
  calc
    ‖(x₀ + (s : K) * (x - x₀)) - x₀‖ = ‖(s : K) * (x - x₀)‖ := by
      rw [hsub]
    _ = |s| * ‖x - x₀‖ := by
      rw [norm_mul, RCLike.norm_ofReal]
    _ ≤ ‖x - x₀‖ := by
      exact mul_le_of_le_one_left (norm_nonneg _) hs_abs_le
    _ < r := lt_of_lt_of_le hx hρr

/-- Helper for Theorem I.4-extra-2: points on the segment from `x₀` to `x` stay within the same
distance from `x₀` as the endpoint `x`. -/
private lemma abs_sub_le_of_mem_uIcc {x₀ x z : ℝ} (hz : z ∈ Set.uIcc x₀ x) :
    |z - x₀| ≤ |x - x₀| := by
  rcases le_total x₀ x with hx | hx
  · -- On the right-hand segment, both differences are nonnegative.
    simp only [Set.uIcc_of_le hx] at hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr hx)]
    linarith [hz.2]
  · -- On the left-hand segment, both differences are nonpositive.
    simp only [Set.uIcc_of_ge hx] at hz
    rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr hx)]
    linarith [hz.1]

/-- Helper for Theorem I.4-extra-2: a closed segment whose endpoint stays inside the radius-`r`
ball around `x₀` is itself contained in that ball. -/
private lemma uIcc_subset_ball_of_abs_sub_lt {x₀ x r : ℝ} (hx : |x - x₀| < r) :
    Set.uIcc x₀ x ⊆ Metric.ball x₀ r := by
  intro z hz
  -- Reduce the ball membership to the segment distance estimate.
  rw [Metric.mem_ball, Real.dist_eq]
  exact lt_of_le_of_lt (abs_sub_le_of_mem_uIcc hz) hx

/-- Helper for Theorem I.4-extra-2: a `C^∞` germ has differentiable iterated derivatives at the
center point. -/
private lemma differentiableAt_iteratedDeriv_of_contDiffAt
    {K : Type*} [RCLike K] {g : K → K} {z : K} (hg : ContDiffAt K ∞ g z) (m : ℕ) :
    DifferentiableAt K (iteratedDeriv m g) z := by
  -- Pass to the iterated Fréchet derivative, where `ContDiffAt` already provides the exact
  -- differentiability statement at finite order `m`.
  have hF : DifferentiableAt K (iteratedFDeriv K m g) z :=
    hg.differentiableAt_iteratedFDeriv (by
      exact_mod_cast ENat.coe_lt_top m)
  -- Transport differentiability back through the `piFieldEquiv` presentation of `iteratedDeriv`.
  simpa only [iteratedDeriv_eq_equiv_comp] using
    ((ContinuousMultilinearMap.piFieldEquiv K (Fin m) K).symm.comp_differentiableAt_iff.2 hF)

/-- Helper for Theorem I.4-extra-2: if a point on the real line restriction lands in the smooth
ball, then the restriction is `C^∞` over `ℝ` at that parameter. -/
private lemma contDiffAt_real_line_restriction_of_mem_ball
    {K : Type*} [RCLike K] {g : K → K} {x₀ x : K} {r : ℝ} {y : ℝ}
    (hg : ContDiffOn K ∞ g (Metric.ball x₀ r))
    (hy : x₀ + (y : K) * (x - x₀) ∈ Metric.ball x₀ r) :
    ContDiffAt ℝ ∞ (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) y := by
  -- Restrict the ambient `K`-smoothness to `ℝ` at the segment point.
  have hg_at_K : ContDiffAt K ∞ g (x₀ + (y : K) * (x - x₀)) :=
    hg.contDiffAt (Metric.isOpen_ball.mem_nhds hy)
  have hg_at_R : ContDiffAt ℝ ∞ g (x₀ + (y : K) * (x - x₀)) :=
    hg_at_K.restrict_scalars ℝ
  -- The affine line map is `C^∞` over `ℝ`, so composition finishes the scalar-restriction bridge.
  have hline : ContDiffAt ℝ ∞ (fun s : ℝ ↦ x₀ + (s : K) * (x - x₀)) y := by
    have hofReal : ContDiffAt ℝ ∞ (fun s : ℝ ↦ (s : K)) y := by
      simpa [RCLike.ofRealCLM_apply] using
        ((ContinuousLinearMap.contDiff (n := ∞) (RCLike.ofRealCLM : ℝ →L[ℝ] K)).contDiffAt :
          ContDiffAt ℝ ∞ (RCLike.ofRealCLM : ℝ → K) y)
    have hmul : ContDiffAt ℝ ∞ (fun s : ℝ ↦ (s : K) * (x - x₀)) y := by
      simpa using hofReal.mul (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ x - x₀) y)
    simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ x₀) y).add hmul
  simpa [Function.comp] using hg_at_R.comp y hline

/-- Helper for Theorem I.4-extra-2: on any real line whose image stays inside the smooth ball, the
ordinary iterated derivatives are the ambient iterated derivatives multiplied by the direction
powers. -/
private lemma iteratedDeriv_line_eq_of_mem_ball
    {K : Type*} [RCLike K] {g : K → K} {x₀ x : K} {r : ℝ}
    (hg : ContDiffOn K ∞ g (Metric.ball x₀ r)) (m : ℕ) {y : ℝ}
    (hy : x₀ + (y : K) * (x - x₀) ∈ Metric.ball x₀ r) :
    iteratedDeriv (𝕜 := ℝ) m (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) y =
      (x - x₀) ^ m * iteratedDeriv m g (x₀ + (y : K) * (x - x₀)) := by
  induction m generalizing y with
  | zero =>
      -- At order zero, the line restriction is just evaluation of `g` along the segment.
      simp
  | succ m ih =>
      let l : ℝ → K := fun s ↦ x₀ + (s : K) * (x - x₀)
      have hy_ball : l y ∈ Metric.ball x₀ r := by
        simpa [l] using hy
      have hline_cont : ContinuousAt l y := by
        -- The affine line map is continuous over `ℝ`.
        have hofReal : ContinuousAt (fun s : ℝ ↦ (s : K)) y := by
          simpa [RCLike.ofRealCLM_apply] using
            ((RCLike.ofRealCLM : ℝ →L[ℝ] K).continuous.continuousAt : ContinuousAt _ y)
        have hmul : ContinuousAt (fun s : ℝ ↦ (s : K) * (x - x₀)) y := by
          simpa using hofReal.mul continuousAt_const
        simpa [l] using continuousAt_const.add hmul
      have hmem :
          ∀ᶠ z in 𝓝 y, l z ∈ Metric.ball x₀ r := by
        -- Openness of the ambient ball gives local validity of the induction hypothesis.
        exact hline_cont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hy_ball)
      have hEq :
          (fun z ↦ iteratedDeriv (𝕜 := ℝ) m (fun s : ℝ ↦ g (l s)) z) =ᶠ[𝓝 y]
            (fun z ↦ (x - x₀) ^ m * iteratedDeriv m g (l z)) := by
        filter_upwards [hmem] with z hz
        simpa [l] using ih hz
      have hline_contDiff : ContDiffAt ℝ ∞ (fun s : ℝ ↦ g (l s)) y :=
        contDiffAt_real_line_restriction_of_mem_ball hg hy_ball
      have hleft_diff :
          DifferentiableAt ℝ (iteratedDeriv (𝕜 := ℝ) m (fun s : ℝ ↦ g (l s))) y := by
        -- The restricted line map is `C^(m+1)`, so its `m`-th iterated Fréchet derivative is
        -- differentiable; then we transport back through `piFieldEquiv`.
        have hline_contDiff_succ :
            ContDiffAt ℝ (m + 1) (fun s : ℝ ↦ g (l s)) y :=
          hline_contDiff.of_le (m := (m + 1 : ℕ∞ω))
            (show (((m + 1 : ℕ∞) : ℕ∞ω) ≤ (∞ : ℕ∞ω)) by
              exact_mod_cast (show (m + 1 : ℕ∞) ≤ (⊤ : ℕ∞) by exact le_top))
        have hF :
            DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun s : ℝ ↦ g (l s))) y :=
          hline_contDiff_succ.differentiableAt_iteratedFDeriv
            (by exact Nat.cast_lt.2 m.lt_succ_self)
        simpa only [iteratedDeriv_eq_equiv_comp] using
          ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) K).symm.comp_differentiableAt_iff.2 hF)
      have hg_at :
          ContDiffAt K ∞ g (l y) :=
        hg.contDiffAt (Metric.isOpen_ball.mem_nhds hy_ball)
      have houter_hasDeriv :
          HasDerivAt (iteratedDeriv m g) (iteratedDeriv (m + 1) g (l y)) (l y) := by
        -- Rewrite the outer scalar derivative as the next iterated derivative.
        simpa [iteratedDeriv_succ] using
          (differentiableAt_iteratedDeriv_of_contDiffAt hg_at m).hasDerivAt
      have hline_hasDeriv : HasDerivAt l (x - x₀) y := by
        -- The derivative of the affine line map is its direction vector.
        have hofReal : HasDerivAt (fun s : ℝ ↦ (s : K)) (1 : K) y := by
          simpa [RCLike.ofRealCLM_apply] using
            ((RCLike.ofRealCLM : ℝ →L[ℝ] K).hasDerivAt : HasDerivAt _ _ y)
        have hmul : HasDerivAt (fun s : ℝ ↦ (s : K) * (x - x₀)) (1 * (x - x₀)) y := by
          simpa using hofReal.mul_const (x - x₀)
        simpa [l] using hmul.const_add x₀
      have hright_hasDeriv :
          HasDerivAt (fun z ↦ (x - x₀) ^ m * iteratedDeriv m g (l z))
            ((x - x₀) ^ (m + 1) * iteratedDeriv (m + 1) g (l y)) y := by
        -- Differentiate the right-hand side by the chain rule, then absorb one more direction
        -- factor into the power.
        have hcomp :
            HasDerivAt (fun z ↦ iteratedDeriv m g (l z))
              ((x - x₀) * iteratedDeriv (m + 1) g (l y)) y := by
          simpa [l] using houter_hasDeriv.scomp y hline_hasDeriv
        simpa [pow_succ, mul_assoc] using hcomp.const_mul ((x - x₀) ^ m)
      -- Convert the induction hypothesis into an equality of derivatives at `y`.
      calc
        iteratedDeriv (𝕜 := ℝ) (m + 1) (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) y =
            deriv (fun z ↦ iteratedDeriv (𝕜 := ℝ) m (fun s : ℝ ↦ g (l s)) z) y := by
              simp [iteratedDeriv_succ, l]
        _ = deriv (fun z ↦ (x - x₀) ^ m * iteratedDeriv m g (l z)) y := by
              exact hEq.deriv_eq
        _ = (x - x₀) ^ (m + 1) * iteratedDeriv (m + 1) g (l y) := hright_hasDeriv.deriv
        _ = (x - x₀) ^ (m + 1) * iteratedDeriv (m + 1) g (x₀ + (y : K) * (x - x₀)) := by
              simp [l]

/-- Helper for Theorem I.4-extra-2: on the Taylor interval `[0,1]`, the restricted iterated
derivatives coincide with the ambient ones along the line. -/
private lemma iteratedDerivWithin_line_eq
    {K : Type*} [RCLike K] {g : K → K} {x₀ x : K} {ρ r : ℝ}
    (hg : ContDiffOn K ∞ g (Metric.ball x₀ r)) (hx : ‖x - x₀‖ < ρ) (hρr : ρ ≤ r)
    (m : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin m (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) (Set.Icc 0 1) y =
      (x - x₀) ^ m * iteratedDeriv m g (x₀ + (y : K) * (x - x₀)) := by
  -- First keep the entire segment inside the smooth ball so the scalar-restriction adapter applies.
  have hline_mem : x₀ + (y : K) * (x - x₀) ∈ Metric.ball x₀ r :=
    line_point_mem_ball_of_mem_Icc hx hρr hy
  have hcont :
      ContDiffAt ℝ ∞ (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) y :=
    contDiffAt_real_line_restriction_of_mem_ball hg hline_mem
  have hcont_m :
      ContDiffAt ℝ m (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) y :=
    hcont.of_le (by
      exact_mod_cast (show (m : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  -- On `Icc 0 1`, interval iterated derivatives agree with ordinary iterated derivatives.
  calc
    iteratedDerivWithin m (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) (Set.Icc 0 1) y =
        iteratedDeriv (𝕜 := ℝ) m (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) y := by
          exact iteratedDerivWithin_eq_iteratedDeriv (n := m)
            (uniqueDiffOn_Icc zero_lt_one) hcont_m hy
    _ = (x - x₀) ^ m * iteratedDeriv m g (x₀ + (y : K) * (x - x₀)) :=
        iteratedDeriv_line_eq_of_mem_ball hg m hline_mem

/-- Helper for Theorem I.4-extra-2: the line restriction inherits the source geometric derivative
bound, with ratio multiplied by the segment length. -/
private lemma norm_iteratedDerivWithin_line_div_factorial_le
    {K : Type*} [RCLike K] {g : K → K} {x₀ x : K} {ρ r M t : ℝ}
    (hg : ContDiffOn K ∞ g (Metric.ball x₀ r))
    (hx : ‖x - x₀‖ < ρ) (hρr : ρ ≤ r)
    (hbound : ∀ z ∈ Metric.ball x₀ r, ∀ m : ℕ,
      ‖iteratedDeriv m g z / (m.factorial : K)‖ ≤ M * t ^ m)
    (m : ℕ) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedDerivWithin m (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) (Set.Icc 0 1) y /
        (m.factorial : K)‖ ≤
      M * (t * ‖x - x₀‖) ^ m := by
  -- Evaluate the ambient bound at the segment point provided by the source line argument.
  have hline_mem : x₀ + (y : K) * (x - x₀) ∈ Metric.ball x₀ r :=
    line_point_mem_ball_of_mem_Icc hx hρr hy
  have hambient :
      ‖iteratedDeriv m g (x₀ + (y : K) * (x - x₀)) / (m.factorial : K)‖ ≤ M * t ^ m :=
    hbound _ hline_mem m
  -- Rewrite the interval derivative using the line formula and isolate the displacement factor.
  rw [iteratedDerivWithin_line_eq hg hx hρr m hy]
  calc
    ‖((x - x₀) ^ m * iteratedDeriv m g (x₀ + (y : K) * (x - x₀))) / (m.factorial : K)‖ =
        ‖(x - x₀) ^ m * (iteratedDeriv m g (x₀ + (y : K) * (x - x₀)) / (m.factorial : K))‖ := by
          simp only [div_eq_mul_inv, mul_assoc]
    _ = ‖(x - x₀) ^ m‖ *
          ‖iteratedDeriv m g (x₀ + (y : K) * (x - x₀)) / (m.factorial : K)‖ := by
          rw [norm_mul]
    _ = ‖x - x₀‖ ^ m *
          ‖iteratedDeriv m g (x₀ + (y : K) * (x - x₀)) / (m.factorial : K)‖ := by
          rw [norm_pow]
    _ ≤ ‖x - x₀‖ ^ m * (M * t ^ m) := by
          exact mul_le_mul_of_nonneg_left hambient (pow_nonneg (norm_nonneg _) _)
    _ = M * (t * ‖x - x₀‖) ^ m := by
          rw [← mul_assoc, mul_comm (‖x - x₀‖ ^ m) M, mul_assoc, ← mul_pow,
            mul_comm ‖x - x₀‖ t]

/-- Helper for Theorem I.4-extra-2: at the segment basepoint, the normalized interval derivatives
are the centered Taylor coefficients multiplied by the displacement powers. -/
private lemma iteratedDerivWithin_line_at_zero_div_factorial_eq
    {K : Type*} [RCLike K] {g : K → K} {x₀ x : K} {ρ r : ℝ}
    (hg : ContDiffOn K ∞ g (Metric.ball x₀ r)) (hx : ‖x - x₀‖ < ρ) (hρr : ρ ≤ r)
    (m : ℕ) :
    iteratedDerivWithin m (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) (Set.Icc 0 1) 0 /
        (m.factorial : K) =
      (iteratedDeriv m g x₀ / (m.factorial : K)) * (x - x₀) ^ m := by
  -- Specialize the line-derivative identity at the Taylor basepoint `s = 0`.
  rw [iteratedDerivWithin_line_eq hg hx hρr m (by simp)]
  -- Reorder the scalar factors so the coefficient matches the centered-series convention.
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem I.4-extra-2: the Taylor polynomial of the line restriction is exactly the
partial sum of the centered scalar series. -/
private lemma taylorWithinEval_line_eq_partialSum_centered_series
    {K : Type*} [RCLike K] {g : K → K} {x₀ x : K} {ρ r : ℝ}
    (hg : ContDiffOn K ∞ g (Metric.ball x₀ r)) (hx : ‖x - x₀‖ < ρ) (hρr : ρ ≤ r)
    (n : ℕ) :
    taylorWithinEval (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) n (Set.Icc 0 1) 0 1 =
      (FormalMultilinearSeries.ofScalars K
          (fun m ↦ iteratedDeriv m g x₀ / (m.factorial : K))).partialSum (n + 1) (x - x₀) := by
  -- Expand the Taylor polynomial and the scalar-series partial sum in the same finite basis.
  rw [taylor_within_apply, FormalMultilinearSeries.partialSum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  -- Each Taylor coefficient is the normalized interval derivative at `0`, which is exactly the
  -- centered scalar coefficient times the corresponding power of the displacement.
  simpa [RCLike.real_smul_eq_coe_mul, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using
    iteratedDerivWithin_line_at_zero_div_factorial_eq hg hx hρr m

/-- Helper for Theorem I.4-extra-2: the real line restriction of the ambient `C^∞` germ is
`C^n` on the Taylor interval. -/
private lemma contDiffOn_line_restriction_Icc
    {K : Type*} [RCLike K] {g : K → K} {x₀ x : K} {ρ r : ℝ}
    (hg : ContDiffOn K ∞ g (Metric.ball x₀ r)) (hx : ‖x - x₀‖ < ρ) (hρr : ρ ≤ r) (n : ℕ) :
    ContDiffOn ℝ n (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) (Set.Icc 0 1) := by
  intro y hy
  -- Every point on the segment stays in the smooth ball, so scalar restriction gives the interval
  -- regularity required by Taylor's theorem.
  have hline :
      ContDiffAt ℝ ∞ (fun s : ℝ ↦ g (x₀ + (s : K) * (x - x₀))) y :=
    contDiffAt_real_line_restriction_of_mem_ball hg (line_point_mem_ball_of_mem_Icc hx hρr hy)
  have hle : (((n : ℕ∞) : ℕ∞ω) ≤ (∞ : ℕ∞ω)) := by
    exact_mod_cast (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  exact (hline.of_le hle).contDiffWithinAt

/-- Helper for Theorem I.4-extra-2: the polynomial prefactor in the Taylor remainder is absorbed
by a dyadic power. -/
private lemma nat_succ_le_two_pow_succ (n : ℕ) : n + 1 ≤ 2 ^ (n + 1) := by
  calc
    n + 1 ≤ 2 ^ n := by
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            n.succ + 1 ≤ (n + 1) + (n + 1) := by omega
            _ ≤ 2 ^ n + 2 ^ n := by gcongr
            _ = 2 ^ (n + 1) := by
                  rw [Nat.pow_succ']
                  omega
    _ ≤ 2 ^ n * 2 := by
      have hpow_pos : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ']
          omega

/-- Helper for Theorem I.4-extra-2: Taylor's theorem on each short real segment yields a geometric
bound for the centered scalar partial sums. -/
private lemma line_taylor_partialSum_error_le_geometric
    {K : Type*} [RCLike K] {g : K → K} {x₀ : K} {ρ r M t : ℝ}
    (hM : 0 < M) (ht : 0 < t) (hg : ContDiffOn K ∞ g (Metric.ball x₀ r)) (hρr : ρ ≤ r)
    (hbound : ∀ z ∈ Metric.ball x₀ r, ∀ m : ℕ,
      ‖iteratedDeriv m g z / (m.factorial : K)‖ ≤ M * t ^ m)
    {x : K} (hx : x ∈ Metric.ball x₀ ρ) (n : ℕ) :
    ‖g x -
        (FormalMultilinearSeries.ofScalars K
          (fun m ↦ iteratedDeriv m g x₀ / (m.factorial : K))).partialSum (n + 1) (x - x₀)‖ ≤
      M * (2 * (t * ‖x - x₀‖)) ^ (n + 1) := by
  let φ : ℝ → K := fun s ↦ g (x₀ + (s : K) * (x - x₀))
  let p : FormalMultilinearSeries K K K :=
    FormalMultilinearSeries.ofScalars K (fun m ↦ iteratedDeriv m g x₀ / (m.factorial : K))
  have hxnorm : ‖x - x₀‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
  have hcont : ContDiffOn ℝ (n + 1) φ (Set.Icc 0 1) :=
    contDiffOn_line_restriction_Icc hg hxnorm hρr (n + 1)
  have hfactorial_bound :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (n + 1) φ (Set.Icc 0 1) y‖ ≤
          ((n + 1).factorial : ℝ) * (M * (t * ‖x - x₀‖) ^ (n + 1)) := by
    intro y hy
    have hnorm_div :
        ‖iteratedDerivWithin (n + 1) φ (Set.Icc 0 1) y / (((n + 1).factorial : ℕ) : K)‖ ≤
          M * (t * ‖x - x₀‖) ^ (n + 1) :=
      norm_iteratedDerivWithin_line_div_factorial_le hg hxnorm hρr hbound (n + 1) hy
    have hfac_ne : ((((n + 1).factorial : ℕ) : K)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n + 1)
    calc
      ‖iteratedDerivWithin (n + 1) φ (Set.Icc 0 1) y‖ =
          ‖((((n + 1).factorial : ℕ) : K) *
              (iteratedDerivWithin (n + 1) φ (Set.Icc 0 1) y /
                ((((n + 1).factorial : ℕ) : K))))‖ := by
            congr 1
            field_simp [div_eq_mul_inv, hfac_ne]
      _ = ‖((((n + 1).factorial : ℕ) : K))‖ *
            ‖iteratedDerivWithin (n + 1) φ (Set.Icc 0 1) y /
              ((((n + 1).factorial : ℕ) : K))‖ := by
            rw [norm_mul]
      _ ≤ ‖((((n + 1).factorial : ℕ) : K))‖ * (M * (t * ‖x - x₀‖) ^ (n + 1)) := by
            exact mul_le_mul_of_nonneg_left hnorm_div (norm_nonneg _)
      _ = ((n + 1).factorial : ℝ) * (M * (t * ‖x - x₀‖) ^ (n + 1)) := by
            rw [RCLike.norm_natCast]
  have hTaylor :=
    taylor_mean_remainder_bound (f := φ) (a := 0) (b := 1) (x := 1) (n := n)
      (by norm_num) hcont (by simp) hfactorial_bound
  have hraw :
      ‖g x - p.partialSum (n + 1) (x - x₀)‖ ≤
        ((n + 1 : ℝ) * M) * (t * ‖x - x₀‖) ^ (n + 1) := by
    -- Rewrite the Taylor polynomial into the centered scalar partial sum, then simplify the
    -- factorial ratio coming from the remainder formula.
    have hrewrite :
        ‖φ 1 - taylorWithinEval φ n (Set.Icc 0 1) 0 1‖ =
          ‖g x - p.partialSum (n + 1) (x - x₀)‖ := by
      rw [show φ 1 = g x by simp [φ, sub_eq_add_neg, add_assoc]]
      rw [taylorWithinEval_line_eq_partialSum_centered_series hg hxnorm hρr n]
    rw [hrewrite] at hTaylor
    have hfac_ne : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    let q : ℝ := M * (t * ‖x - x₀‖) ^ (n + 1)
    have hratio :
        (((n + 1).factorial : ℝ) * q) / (n.factorial : ℝ) = ((n + 1 : ℝ) * M) * (t * ‖x - x₀‖) ^ (n + 1) := by
      have hcancel : (((n.factorial : ℝ) * q) / (n.factorial : ℝ)) = q := by
        calc
          ((n.factorial : ℝ) * q) / (n.factorial : ℝ) =
              q * (((n.factorial : ℝ)) / (n.factorial : ℝ)) := by
                field_simp [hfac_ne]
          _ = q := by rw [div_self hfac_ne, mul_one]
      rw [Nat.factorial_succ, Nat.cast_mul]
      calc
        ((((((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ)) * q) / (n.factorial : ℝ))) =
            (((n + 1 : ℕ) : ℝ) * (((n.factorial : ℝ) * q) / (n.factorial : ℝ))) := by
              rw [mul_assoc, mul_div_assoc]
        _ = (((n + 1 : ℕ) : ℝ) * q) := by rw [hcancel]
        _ = ((n + 1 : ℝ) * M) * (t * ‖x - x₀‖) ^ (n + 1) := by
              simpa [q, mul_assoc]
    calc
      ‖g x - p.partialSum (n + 1) (x - x₀)‖ ≤
          (((n + 1).factorial : ℝ) * (M * (t * ‖x - x₀‖) ^ (n + 1))) * (1 - 0) ^ (n + 1) /
            (n.factorial : ℝ) :=
        hTaylor
      _ = (((n + 1).factorial : ℝ) * (M * (t * ‖x - x₀‖) ^ (n + 1))) / (n.factorial : ℝ) := by
            simp
      _ = ((n + 1 : ℝ) * M) * (t * ‖x - x₀‖) ^ (n + 1) := by
            simpa [q] using hratio
  have hdyadic :
      (n + 1 : ℝ) ≤ 2 ^ (n + 1) := by
    exact_mod_cast nat_succ_le_two_pow_succ n
  have hq_nonneg : 0 ≤ t * ‖x - x₀‖ := mul_nonneg ht.le (norm_nonneg _)
  have hcalc :
      ‖g x - p.partialSum (n + 1) (x - x₀)‖ ≤ M * (2 * (t * ‖x - x₀‖)) ^ (n + 1) := by
    calc
      ‖g x - p.partialSum (n + 1) (x - x₀)‖ ≤
          ((n + 1 : ℝ) * M) * (t * ‖x - x₀‖) ^ (n + 1) :=
        hraw
      _ ≤ (2 ^ (n + 1) * M) * (t * ‖x - x₀‖) ^ (n + 1) := by
            have hmul :
                ((n + 1 : ℝ) * M) ≤ 2 ^ (n + 1) * M := by
              exact mul_le_mul_of_nonneg_right hdyadic hM.le
            exact mul_le_mul_of_nonneg_right hmul (pow_nonneg hq_nonneg _)
      _ = M * (2 * (t * ‖x - x₀‖)) ^ (n + 1) := by
            calc
              (2 ^ (n + 1) * M) * (t * ‖x - x₀‖) ^ (n + 1) =
                  2 ^ (n + 1) * (M * (t * ‖x - x₀‖) ^ (n + 1)) := by ring
              _ =
                  M * (2 ^ (n + 1) * (t * ‖x - x₀‖) ^ (n + 1)) := by ring
              _ = M * (2 * (t * ‖x - x₀‖)) ^ (n + 1) := by
                    rw [← mul_pow]
  simpa [p] using hcalc

/-- Helper for Theorem I.4-extra-2: if the shifted centered partial sums already converge to `g`,
then they must agree with the centered power-series sum on the whole smaller ball. -/
private lemma centered_series_eq_on_subball_of_shifted_partialSum_limit
    {K : Type*} [RCLike K] {g : K → K} {x₀ : K} {ρ : ℝ}
    (hρpos : 0 < ρ) (p : FormalMultilinearSeries K K K) (hρradius : ENNReal.ofReal ρ < p.radius)
    (hlim : ∀ x ∈ Metric.ball x₀ ρ,
      Tendsto (fun n : ℕ ↦ p.partialSum (n + 1) (x - x₀)) atTop (𝓝 (g x))) :
    Set.EqOn g (fun x ↦ p.sum (x - x₀)) (Metric.ball x₀ ρ) := by
  intro x hx
  have hxnorm : ‖x - x₀‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
  have hy_radius : ENNReal.ofReal ‖x - x₀‖ < p.radius := by
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hρpos).2 hxnorm) hρradius.le
  have hy : x - x₀ ∈ Metric.eball (0 : K) p.radius := by
    simpa [Metric.mem_eball, edist_dist, dist_eq_norm] using hy_radius
  have hpRadiusPos : 0 < p.radius := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρpos) hρradius.le
  have hsum :
      Tendsto (fun n : ℕ ↦ p.partialSum (n + 1) (x - x₀)) atTop (𝓝 (p.sum (x - x₀))) := by
    simpa using ((p.hasFPowerSeriesOnBall hpRadiusPos).tendsto_partialSum hy).comp
      (tendsto_add_atTop_nat 1)
  -- The shifted partial sums have a unique limit on the smaller ball.
  exact tendsto_nhds_unique (hlim x hx) hsum

/-- Helper for Theorem I.4-extra-2: on a ball, a geometric bound on the normalized iterated
derivatives at the center gives positive radius for the centered Taylor series, and the existing
`AnalyticOn` structure from `C^∞` then upgrades to neighborhood analyticity. -/
lemma analyticAt_of_locally_bounded_normalized_iteratedDeriv
    {K : Type*} [RCLike K] {g : K → K} {x₀ : K} {r M t : ℝ} (hr : 0 < r) (hM : 0 < M)
    (ht : 0 < t) (hg : ContDiffOn K ∞ g (Metric.ball x₀ r))
    (hbound : ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
      ‖iteratedDeriv p g x / (p.factorial : K)‖ ≤ M * t ^ p) :
    AnalyticAt K g x₀ := by
  -- Route correction: the old real-only detour was the wrong split point. The source-faithful
  -- route is now fixed in this file: use the strengthened radius lower bound at `x₀` together
  -- with the segment lemma `line_point_mem_ball_of_mem_Icc`, then apply Taylor with remainder to
  -- the real line restriction `s ↦ g (x₀ + (s : K) * (x - x₀))`.
  let p : FormalMultilinearSeries K K K :=
    FormalMultilinearSeries.ofScalars K (fun n ↦ iteratedDeriv n g x₀ / (n.factorial : K))
  let ρ : ℝ := min (r / 2) ((4 * t)⁻¹)
  have hradius_ge : ENNReal.ofReal t⁻¹ ≤ p.radius :=
    formal_series_radius_ge_inv_of_center_growth_bound (g := g) (x₀ := x₀) hM ht
      (fun n ↦ by simpa [p] using hbound x₀ (by simpa [Metric.mem_ball]) n)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    refine lt_min ?_ ?_
    · exact half_pos hr
    · exact inv_pos.mpr (by positivity)
  have hρle_r : ρ ≤ r := by
    dsimp [ρ]
    calc
      min (r / 2) ((4 * t)⁻¹) ≤ r / 2 := min_le_left _ _
      _ ≤ r := by nlinarith
  have htwotρ_lt_one : 2 * t * ρ < 1 := by
    have hρle : ρ ≤ (4 * t)⁻¹ := by
      dsimp [ρ]
      exact min_le_right _ _
    have ht_ne : t ≠ 0 := ne_of_gt ht
    calc
      2 * t * ρ ≤ 2 * t * ((4 * t)⁻¹) := by gcongr
      _ = (1 : ℝ) / 2 := by
            field_simp [ht_ne]
            ring
      _ < 1 := by norm_num
  have hρlt_tinv : ρ < t⁻¹ := by
    have hρle : ρ ≤ (4 * t)⁻¹ := by
      dsimp [ρ]
      exact min_le_right _ _
    have ht_ne : t ≠ 0 := ne_of_gt ht
    calc
      ρ ≤ (4 * t)⁻¹ := hρle
      _ < t⁻¹ := by
            field_simp [ht_ne]
            nlinarith
  have hρradius : ENNReal.ofReal ρ < p.radius := by
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr ht)).2 hρlt_tinv) hradius_ge
  have hshifted_limit :
      ∀ x ∈ Metric.ball x₀ ρ,
        Tendsto (fun n : ℕ ↦ p.partialSum (n + 1) (x - x₀)) atTop (𝓝 (g x)) := by
    intro x hx
    have hq_lt_one : 2 * (t * ‖x - x₀‖) < 1 := by
      have hxnorm : ‖x - x₀‖ < ρ := by
        simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
      have htx_le : t * ‖x - x₀‖ ≤ t * ρ := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hxnorm) ht.le
      calc
        2 * (t * ‖x - x₀‖) = 2 * t * ‖x - x₀‖ := by ring
        _ ≤ 2 * t * ρ := by
              have := mul_le_mul_of_nonneg_left htx_le (by positivity : 0 ≤ (2 : ℝ))
              simpa [mul_assoc]
        _ < 1 := htwotρ_lt_one
    have hq_nonneg : 0 ≤ 2 * (t * ‖x - x₀‖) := by positivity
    have hgeom :
        Tendsto (fun n : ℕ ↦ M * (2 * (t * ‖x - x₀‖)) ^ (n + 1)) atTop (𝓝 0) := by
      have hpow :
          Tendsto (fun n : ℕ ↦ (2 * (t * ‖x - x₀‖)) ^ (n + 1)) atTop (𝓝 0) := by
        exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one).comp
          (tendsto_add_atTop_nat 1)
      simpa using tendsto_const_nhds.mul hpow
    have hnorm :
        Tendsto
          (fun n : ℕ ↦
            ‖p.partialSum (n + 1) (x - x₀) - g x‖)
          atTop (𝓝 0) := by
      -- The Taylor remainder is trapped by a geometric sequence with ratio `< 1`.
      refine squeeze_zero (fun _ ↦ norm_nonneg _) ?_ hgeom
      intro n
      simpa [norm_sub_rev, p] using
        line_taylor_partialSum_error_le_geometric hM ht hg hρle_r hbound hx n
    exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm
  have hEqOn :
      Set.EqOn g (fun x ↦ p.sum (x - x₀)) (Metric.ball x₀ ρ) :=
    centered_series_eq_on_subball_of_shifted_partialSum_limit hρpos p hρradius hshifted_limit
  have hpRadiusPos : 0 < p.radius := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr ht)) hradius_ge
  have hpAnalytic : AnalyticAt K (fun x ↦ p.sum (x - x₀)) x₀ := by
    -- The centered scalar series is analytic on its convergence ball, hence analytic at `x₀`
    -- after translating back from the origin.
    simpa using ((p.hasFPowerSeriesOnBall hpRadiusPos).analyticAt.comp_sub x₀)
  have hEventually :
      (fun x ↦ p.sum (x - x₀)) =ᶠ[𝓝 x₀] g := by
    filter_upwards [Metric.ball_mem_nhds x₀ hρpos] with x hx
    exact (hEqOn hx).symm
  -- Neighborhood agreement with the centered power series upgrades the smooth germ to analytic.
  exact hpAnalytic.congr hEventually

/-- Helper for Theorem I.4-extra-2: a local geometric bound on normalized iterated derivatives of
a smooth real-valued function yields analyticity at the center point. -/
lemma analyticAt_of_locally_bounded_normalized_iteratedDeriv_real
    {g : ℝ → ℝ} {x₀ r M t : ℝ} (hr : 0 < r) (hM : 0 < M) (ht : 0 < t)
    (hg : ContDiffOn ℝ ∞ g (Metric.ball x₀ r))
    (hbound : ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
      ‖iteratedDeriv p g x / (p.factorial : ℝ)‖ ≤ M * t ^ p) :
    AnalyticAt ℝ g x₀ := by
  -- The real statement is the generic subball-upgrade lemma specialized to `ℝ`.
  exact analyticAt_of_locally_bounded_normalized_iteratedDeriv hr hM ht hg hbound

/-- Theorem I.4-extra-2: for a `C^∞` function on `D`, neighborhood analyticity on `D` is
equivalent to the local existence, near each `x₀ ∈ D`, of positive constants `M` and `t` such that
the normalized iterated derivatives satisfy the bound
`‖iteratedDeriv p f x / p!‖ ≤ M * t^p` on some open ball around `x₀` contained in `D`. -/
theorem analyticOnNhd_iff_locally_bounded_normalized_iteratedDeriv_of_contDiffOn
    (hD : IsOpen D) (hf : ContDiffOn 𝕜 ∞ f D) :
    AnalyticOnNhd 𝕜 f D ↔
      ∀ x₀ ∈ D, ∃ r M t : ℝ,
        0 < r ∧ Metric.ball x₀ r ⊆ D ∧ 0 < M ∧ 0 < t ∧
          ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
            ‖iteratedDeriv p f x / (p.factorial : 𝕜)‖ ≤ M * t ^ p := by
  constructor
  · intro h x₀ hx₀
    -- The forward direction is the standard change-of-origin estimate for the local power series.
    exact analyticAt_has_local_bounded_normalized_iteratedDeriv hD hx₀ (h x₀ hx₀)
  · intro h
    intro x₀ hx₀
    rcases h x₀ hx₀ with ⟨r, M, t, hr, hrD, hM, ht, hbound⟩
    -- Route correction: use the local derivative bound only to give positive radius for the
    -- centered Taylor series; `hf` already supplies the ambient `AnalyticOn` structure needed to
    -- upgrade that positive radius to neighborhood analyticity on a smaller ball.
    exact analyticAt_of_locally_bounded_normalized_iteratedDeriv hr hM ht (hf.mono hrD) hbound
