import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section04.«0004_Proposition_2_2»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-
Remark 2 is `source-facing`: the textbook statement is about normalized iterated derivatives.
Its `core/canonical` owner is the coefficient of the recentered scalar power series
`(ofScalars 𝕜 a).changeOrigin x`.
-/
/-- Helper for Cartan section04 frozen_0006_Remark_2: reindexing the global change-origin
majorant by total degree recovers the scalar majorant at radius `r₀ + R`. -/
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
    -- Reindex the summable sigma-series along `changeOriginIndexEquiv`.
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
    -- Collapse each finite total-degree fiber with the binomial theorem.
    convert_to
      HasSum (fun s : Finset (Fin n) ↦ ‖P n‖₊ * (r₀ ^ s.card * R ^ (n - s.card)))
        (‖P n‖₊ * (r₀ + R) ^ n)
    · ext s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assoc]
    rw [← Fin.sum_pow_mul_eq_add_pow]
    exact (hasSum_fintype _).mul_left _
  -- Reindex first, then sum the binomial fibers degree by degree.
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

/-- Helper for Cartan section04 frozen_0006_Remark_2: the fixed `p`-fiber of the change-origin
majorant is bounded by the full majorant after division by `R^p`. -/
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
    -- This is the global sigma-majorant supplied by the change-origin API.
    simpa only [G] using P.changeOriginSeries_summable_aux₁ hr
  have hfiber_mul_le :
      (∑' s : Σ l : ℕ, { t : Finset (Fin (p + l)) // t.card = l },
        ‖P (p + s.1)‖₊ * r₀ ^ s.1) * R ^ p ≤
        ∑' s, G s := by
    -- Embed the fixed `p`-fiber into the full sigma-series via `Sigma.mk p`.
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
  -- Divide by the positive gap factor to isolate the `p`-th coefficient layer.
  refine (le_div_iff₀ hRpow_pos).2 ?_
  simpa only [G] using hfiber_mul_le.trans_eq (changeOrigin_global_majorant_tsum_eq P r₀ R hr)

/-- Helper for Cartan section04 frozen_0006_Remark_2: the scalar-series majorant written with
`NNReal` norms is exactly the textbook sum `A(r)`. -/
private lemma ofScalarsMajorant_eq_powerSeriesAbsSum
    (a : ℕ → 𝕜) (r : ℝ) (rN : NNReal) (hrN : (rN : ℝ) = r) :
    (((∑' n : ℕ, ‖(ofScalars 𝕜 a) n‖₊ * rN ^ n : NNReal) : ℝ)) =
      ofScalarsSum (fun n ↦ ‖a n‖) r := by
  have hterm : ∀ n : ℕ, ↑(‖(ofScalars 𝕜 a) n‖₊ * rN ^ n : NNReal) = ‖a n‖ * r ^ n := by
    intro n
    calc
      ↑(‖(ofScalars 𝕜 a) n‖₊ * rN ^ n : NNReal) = ‖(ofScalars 𝕜 a) n‖ * (rN : ℝ) ^ n := by
        simp
      _ = ‖(ofScalars 𝕜 a).coeff n‖ * (rN : ℝ) ^ n := by
        rw [FormalMultilinearSeries.norm_apply_eq_norm_coef (p := ofScalars 𝕜 a) (n := n)]
      _ = ‖(ofScalars 𝕜 a).coeff n‖ * r ^ n := by rw [hrN]
      _ = ‖a n‖ * r ^ n := by simp
  -- Rewrite the `NNReal` majorant termwise and then use the standard `ofScalarsSum` formula.
  rw [NNReal.coe_tsum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp [hterm]

/-- Cartan section04 frozen_0006_Remark_2: core/canonical coefficient estimate underlying
Remark 2. -/
theorem norm_changeOrigin_coeff_le_powerSeriesAbsSum
    (a : ℕ → 𝕜) (p : ℕ) {r r₀ : ℝ} {x : 𝕜}
    (hr : ENNReal.ofReal r < (ofScalars 𝕜 a).radius)
    (hx : ‖x‖ ≤ r₀) (hr₀ : r₀ < r) :
    ‖((ofScalars 𝕜 a).changeOrigin x).coeff p‖ ≤
      ofScalarsSum (fun n ↦ ‖a n‖) r / (r - r₀) ^ p := by
  let P : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  let u : NNReal := ‖x‖₊
  have hu_lt_radius : ((u : ENNReal) < P.radius) := by
    -- The recentering point stays inside the original radius of convergence.
    simpa [P, u] using
      (ENNReal.coe_lt_ofReal.2 (lt_of_le_of_lt hx hr₀)).trans hr
  have hcoeff_norm :
      ‖P.changeOrigin x p‖₊ = ‖(P.changeOrigin x).coeff p‖₊ := by
    -- Coefficients and multilinear maps have the same norm for scalar series.
    apply Subtype.ext
    exact FormalMultilinearSeries.norm_apply_eq_norm_coef (p := P.changeOrigin x) (n := p)
  let fiberTerm :
      (Σ l : ℕ, { s : Finset (Fin (p + l)) // s.card = l }) → NNReal :=
    fun s ↦ ‖P (p + s.1)‖₊ * u ^ s.1
  have hcoeff_nn :
      ‖(P.changeOrigin x).coeff p‖₊ ≤ ∑' s, fiberTerm s := by
    -- `nnnorm_changeOrigin_le` bounds the coefficient by the fixed-`p` majorant fiber.
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
      -- Replace `‖x‖` by the inner radius `r₀`.
      simpa only [u, r₀N] using hx
    have hr_split : r₀N + R = rN := by
      -- The outer majorant radius is `r₀ + (r - r₀) = r`.
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
      -- Monotonicity of the power factor upgrades `u` to `r₀`.
      refine Summable.tsum_le_tsum (fun s ↦ ?_) hu_summable hr₀_summable
      dsimp only [fiberTerm]
      gcongr
    -- Compare the fixed fiber with the global majorant at radius `r`.
    exact hfiber_mono.trans <| by
      simpa only [hr_split] using
        fixed_changeOrigin_fiber_le_div_global_majorant P p r₀N R hgap_pos hr_majorant
  have hmajorant_real :
      ‖(P.changeOrigin x).coeff p‖ ≤
        ((((∑' n : ℕ, ‖P n‖₊ * rN ^ n : NNReal) / R ^ p : NNReal) : ℝ)) := by
    exact_mod_cast (le_trans hcoeff_nn hmajorant_nn)
  have hsum_eq :
      (((∑' n : ℕ, ‖P n‖₊ * rN ^ n : NNReal) : ℝ)) = ofScalarsSum (fun n ↦ ‖a n‖) r := by
    -- Rewrite the majorant series into the textbook sum `A(r)`.
    exact ofScalarsMajorant_eq_powerSeriesAbsSum a r rN rfl
  -- Convert the `NNReal` estimate back to the stated real-valued bound.
  calc
    ‖(P.changeOrigin x).coeff p‖ ≤
        ((((∑' n : ℕ, ‖P n‖₊ * rN ^ n : NNReal) / R ^ p : NNReal) : ℝ)) := hmajorant_real
    _ = ofScalarsSum (fun n ↦ ‖a n‖) r / (r - r₀) ^ p := by
      rw [NNReal.coe_div, NNReal.coe_pow, hsum_eq]
      rw [show (R : ℝ) = r - r₀ by rfl]

/-- Source-facing reformulation of Cartan section04 frozen_0006_Remark_2: if `r` lies strictly
inside the radius of convergence and `‖x‖ ≤ r₀ < r`, then the
normalized `p`-th derivative of the summed scalar power series is bounded by
`A(r) / (r - r₀)^p`, where `A(r)` is the canonical scalar-series sum
`ofScalarsSum (fun n ↦ ‖a n‖) r = ∑ |a_n| r^n`. -/
-- Proof sketch: differentiate the scalar power series termwise `p` times, divide by `p!`, use
-- `‖x‖ ≤ r₀ < r` to bound each term by the geometric majorant at radius `r`, and then sum the
-- resulting estimate.
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
    have hq_pos : 0 < (ofScalars 𝕜 a).radius :=
      lt_of_le_of_lt bot_le hr
    exact
      ((ofScalars 𝕜 a).hasFPowerSeriesOnBall hq_pos).mono
        (ENNReal.ofReal_pos.mpr hr_pos) hr.le
  simpa [scalar_changeOrigin_coeff_eq_iteratedDeriv_div_factorial hseries hxr p] using
    norm_changeOrigin_coeff_le_powerSeriesAbsSum a p hr hx hr₀
