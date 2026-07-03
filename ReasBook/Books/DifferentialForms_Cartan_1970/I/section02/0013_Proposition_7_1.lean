import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Ostrowski

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries Filter
open scoped ENNReal NNReal Topology

universe u

noncomputable section

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Helper for Proposition 7.1: prepend a zero coefficient to shift a scalar power series by one
degree. -/
def prependZero (a : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => a n

/-- Helper for Proposition 7.1: the root sequence appearing in the scalar Cauchy-Hadamard
formula. -/
abbrev scalar_root_sequence (a : ℕ → 𝕜) (n : ℕ) : ℝ≥0∞ :=
  ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)

/-- Helper for Proposition 7.1: each scalar root term can be viewed as an `ENNReal.ofReal`
of the corresponding real norm power. -/
theorem scalar_root_sequence_eq_ofReal (a : ℕ → 𝕜) (n : ℕ) :
    scalar_root_sequence a n = ENNReal.ofReal (‖a n‖ ^ (1 / (n : ℝ))) := by
  have hpow_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
  -- Rewrite the `NNReal` root first, then move the common power back under `ENNReal.ofReal`.
  calc
    scalar_root_sequence a n = (ENNReal.ofReal ‖a n‖) ^ (1 / (n : ℝ)) := by
      rw [scalar_root_sequence]
      have hof : ENNReal.ofReal ‖a n‖ = (‖a n‖₊ : ℝ≥0∞) := by
        simpa using ENNReal.ofReal_eq_coe_nnreal (norm_nonneg (a n))
      rw [hof, ← ENNReal.coe_rpow_of_nonneg ‖a n‖₊ hpow_nonneg]
    _ = ENNReal.ofReal (‖a n‖ ^ (1 / (n : ℝ))) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpow_nonneg]

/-- Helper for Proposition 7.1: adding a leading zero coefficient does not change the scalar
radius of convergence. -/
theorem radius_prependZero_eq_radius (a : ℕ → 𝕜) :
    (ofScalars 𝕜 (prependZero a)).radius = (ofScalars 𝕜 a).radius := by
  let P : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 (prependZero a)
  let Q : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  apply le_antisymm
  · -- Any convergence bound for the shifted series gives one for the original series.
    refine ENNReal.le_of_forall_nnreal_lt ?_
    intro r hr
    by_cases hr0 : r = 0
    · simpa [hr0] using (show (0 : ℝ≥0∞) ≤ Q.radius from by simp)
    have hrpos : 0 < r := by
      exact pos_iff_ne_zero.mpr hr0
    have hrposR : 0 < (r : ℝ) := by
      exact_mod_cast hrpos
    rcases P.norm_le_div_pow_of_pos_of_lt_radius hrposR hr with ⟨C, hC, hP⟩
    have hQbound : ∀ n : ℕ, ‖Q n‖ * (r : ℝ) ^ n ≤ C / (r : ℝ) := by
      intro n
      have hPn : ‖P (n + 1)‖ ≤ C / (r : ℝ) ^ (n + 1) := hP (n + 1)
      have hPn' : ‖a n‖ ≤ C / (r : ℝ) ^ (n + 1) := by
        simpa [P, prependZero, ofScalars_norm] using hPn
      calc
        ‖Q n‖ * (r : ℝ) ^ n = ‖a n‖ * (r : ℝ) ^ n := by
          simp [Q, ofScalars_norm]
        _ ≤ (C / (r : ℝ) ^ (n + 1)) * (r : ℝ) ^ n := by
          gcongr
        _ = C / (r : ℝ) := by
          rw [pow_succ]
          field_simp [hrposR.ne', pow_ne_zero n hrposR.ne']
    exact Q.le_radius_of_bound (C / (r : ℝ)) hQbound
  · -- Conversely, a bound for the original series controls the shifted coefficients as well.
    refine ENNReal.le_of_forall_nnreal_lt ?_
    intro r hr
    by_cases hr0 : r = 0
    · simpa [hr0] using (show (0 : ℝ≥0∞) ≤ P.radius from by simp)
    have hrposNN : 0 < r := by
      exact pos_iff_ne_zero.mpr hr0
    have hrpos : 0 < (r : ℝ) := by
      exact_mod_cast hrposNN
    rcases Q.norm_mul_pow_le_of_lt_radius hr with ⟨C, hC, hQ⟩
    have hPbound : ∀ n : ℕ, ‖P n‖ * (r : ℝ) ^ n ≤ C * (r : ℝ) := by
      intro n
      cases n with
      | zero =>
          have hCr : 0 ≤ C * (r : ℝ) := by positivity
          simpa [P, prependZero] using hCr
      | succ n =>
          have hQn : ‖Q n‖ * (r : ℝ) ^ n ≤ C := hQ n
          calc
            ‖P (n + 1)‖ * (r : ℝ) ^ (n + 1)
                = (‖Q n‖ * (r : ℝ) ^ n) * (r : ℝ) := by
                    simp [P, Q, prependZero, ofScalars_norm, pow_succ, mul_assoc, mul_comm]
            _ ≤ C * (r : ℝ) := by
                gcongr
    exact P.le_radius_of_bound (C * (r : ℝ)) hPbound

/-- Helper for Proposition 7.1: the scalar Cauchy-Hadamard formula specialized to `ofScalars`. -/
theorem ofScalars_radius_inv_eq_limsup (a : ℕ → 𝕜) :
    (ofScalars 𝕜 a).radius⁻¹ = limsup (scalar_root_sequence a) atTop := by
  have hnorm : ∀ n, ‖ofScalars 𝕜 a n‖₊ = ‖a n‖₊ := fun n ↦
    Subtype.ext (ofScalars_norm 𝕜 a n)
  -- Rewrite the multilinear Hadamard formula through the scalar coefficient norm identity.
  change
    (ofScalars 𝕜 a).radius⁻¹ =
      limsup (fun n ↦ ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop
  simpa [hnorm] using radius_inv_eq_limsup (ofScalars 𝕜 a)

/-- Helper for Proposition 7.1: the source-facing derived scalar coefficients. -/
def ofScalarsDerivCoeff (a : ℕ → 𝕜) : ℕ → 𝕜 :=
  fun n ↦ (n.succ : 𝕜) * a n.succ

/-- Helper for Proposition 7.1: the ambient field norm restricted to rational scalars defines an
absolute value on `ℚ`. -/
def rational_norm_absolute_value [CharZero 𝕜] : AbsoluteValue ℚ ℝ :=
  AbsoluteValue.comp (NormedField.toAbsoluteValue 𝕜) (f := Rat.castHom 𝕜)
    (Rat.cast_injective (α := 𝕜))

/-- Helper for Proposition 7.1: the reciprocal nat-cast root factor that compares the original and
derived coefficient root sequences. -/
def inverse_succ_root_sequence [CharZero 𝕜] : ℕ → ℝ≥0∞ :=
  fun n ↦ ENNReal.ofReal (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ)))

/-- Helper for Proposition 7.1: the `p`-adic absolute value of a positive integer is bounded below
by its reciprocal. -/
theorem padic_nat_recip_le (p n : ℕ) [Fact p.Prime] :
    ((n.succ : ℝ)⁻¹) ≤ Rat.AbsoluteValue.padic p n.succ := by
  have hp_prime : Nat.Prime p := Fact.out
  have hpow_le : ((p : ℚ) ^ padicValNat p n.succ) ≤ n.succ := by
    exact_mod_cast
      (le_trans
        (Nat.pow_le_pow_right hp_prime.pos (padicValNat_le_nat_log (p := p) n.succ))
        (Nat.pow_log_le_self p n.succ_ne_zero))
  have hpow_inv :
      ((n.succ : ℚ)⁻¹) ≤ (((p : ℚ) ^ padicValNat p n.succ)⁻¹) := by
    -- Inverting reverses the inequality because both sides are positive rationals.
    have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp_prime.pos
    have hpow_pos : (0 : ℚ) < (p : ℚ) ^ padicValNat p n.succ := by
      exact pow_pos hp_pos _
    exact (inv_le_inv₀ (by positivity) hpow_pos).2 hpow_le
  have hpadic :
      (((p : ℚ) ^ padicValNat p n.succ)⁻¹ : ℚ) = padicNorm p n.succ := by
    -- Rewrite the `p`-adic norm through its valuation formula on the nonzero integer `n + 1`.
    rw [padicNorm.eq_zpow_of_nonzero (p := p)]
    · rw [padicValRat.of_nat]
      simp [zpow_neg, Rat.cast_natCast]
    · exact_mod_cast n.succ_ne_zero
  have hpow_inv_real :
      ((n.succ : ℚ)⁻¹ : ℝ) ≤ (padicNorm p n.succ : ℝ) := by
    exact_mod_cast hpow_inv.trans_eq hpadic
  -- Transfer the rational inequality to the real-valued absolute value used by Ostrowski.
  simpa [Rat.AbsoluteValue.padic_eq_padicNorm] using hpow_inv_real

/-- Helper for Proposition 7.1: in the trivial rational-absolute-value case, the reciprocal root
sequence is constantly `1`. -/
theorem inverse_succ_root_tendsto_one_of_trivial [CharZero 𝕜]
    (hvQ : ¬ (rational_norm_absolute_value (𝕜 := 𝕜)).IsNontrivial) :
    Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (nhds 1) := by
  -- In the trivial branch, every nonzero rational has absolute value `1`, hence so does each
  -- reciprocal nat-cast transported to `𝕜`.
  refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) tendsto_const_nhds
  have hnorm_absv :
      rational_norm_absolute_value (𝕜 := 𝕜) (((n.succ : ℚ)⁻¹ : ℚ)) = 1 := by
    exact (rational_norm_absolute_value (𝕜 := 𝕜)).not_isNontrivial_apply hvQ
      (show (((n.succ : ℚ)⁻¹ : ℚ)) ≠ 0 by
        exact inv_ne_zero (show (n.succ : ℚ) ≠ 0 by exact_mod_cast n.succ_ne_zero))
  have hnorm :
      ‖(((n.succ : ℚ)⁻¹ : ℚ) : 𝕜)‖ = 1 := by
    change rational_norm_absolute_value (𝕜 := 𝕜) (((n.succ : ℚ)⁻¹ : ℚ)) = 1
    exact hnorm_absv
  -- Rewrite the sequence term through that constant norm value.
  have hnorm' : ‖(((n.succ : 𝕜) : 𝕜)⁻¹)‖ = 1 := by
    simpa using hnorm
  have hterm : inverse_succ_root_sequence (𝕜 := 𝕜) n = 1 := by
    rw [inverse_succ_root_sequence, hnorm']
    simp
  simpa using hterm.symm

/-- Helper for Proposition 7.1: a real-equivalent rational absolute value turns the reciprocal
nat-cast norms into explicit negative powers. -/
theorem real_equiv_norm_inv_natCast_eq_rpow_neg [CharZero 𝕜]
    (hreal : (rational_norm_absolute_value (𝕜 := 𝕜)).IsEquiv Rat.AbsoluteValue.real) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ = (n.succ : ℝ) ^ (-d) := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hreal
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro n
  have hpow_n :
      ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c = ((n.succ : ℝ)⁻¹) := by
    have happly := congrFun hpow (((n.succ : ℚ))⁻¹)
    change ‖((((n.succ : ℚ))⁻¹ : ℚ) : 𝕜)‖ ^ c = Rat.AbsoluteValue.real (((n.succ : ℚ))⁻¹) at happly
    have happly' :
        ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c = Rat.AbsoluteValue.real (((n.succ : ℚ))⁻¹) := by
      simpa [Rat.cast_inv] using happly
    have hreal_inv :
        Rat.AbsoluteValue.real (((n.succ : ℚ))⁻¹) = (((n.succ : ℚ)⁻¹ : ℚ) : ℝ) := by
      rw [Rat.AbsoluteValue.real_eq_abs, abs_of_nonneg]
      positivity
    -- Evaluate the equivalence identity on the reciprocal nat-cast and rewrite both sides.
    calc
      ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c = Rat.AbsoluteValue.real (((n.succ : ℚ))⁻¹) := happly'
      _ = (((n.succ : ℚ)⁻¹ : ℚ) : ℝ) := hreal_inv
      _ = ((n.succ : ℝ)⁻¹) := by simp [Rat.cast_inv]
  have hnorm_n :
      ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ = ((n.succ : ℝ)⁻¹) ^ c⁻¹ := by
    -- Take the positive `c`-th root of the equivalence identity.
    exact (Real.eq_rpow_inv (norm_nonneg _) (by positivity) hc.ne').2 hpow_n
  -- Rewrite the reciprocal base as a negative power of `n + 1`.
  calc
    ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ = ((n.succ : ℝ)⁻¹) ^ c⁻¹ := hnorm_n
    _ = (n.succ : ℝ) ^ (-c⁻¹) := by
      rw [Real.inv_rpow (by positivity : 0 ≤ (n.succ : ℝ)), Real.rpow_neg (by positivity)]

/-- Helper for Proposition 7.1: in the Archimedean branch of Ostrowski's theorem, the reciprocal
root sequence tends to `1`. -/
theorem inverse_succ_root_tendsto_one_of_real_equiv [CharZero 𝕜]
    (hreal : (rational_norm_absolute_value (𝕜 := 𝕜)).IsEquiv Rat.AbsoluteValue.real) :
    Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (nhds 1) := by
  obtain ⟨d, hd, hnorm⟩ := real_equiv_norm_inv_natCast_eq_rpow_neg (𝕜 := 𝕜) hreal
  have hsucc :
      Tendsto (fun n : ℕ ↦ (n.succ : ℝ)) atTop atTop := by
    have hsucc' :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact
        (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ ↦ (m : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1)
    simpa [Nat.succ_eq_add_one] using
      hsucc'
  have hmodel :
      Tendsto (fun n : ℕ ↦ (n.succ : ℝ) ^ (-d / (n.succ : ℝ))) atTop (nhds 1) := by
    -- The explicit real model sequence is a standard `x ^ (a / x)` limit.
    refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_)
      ((tendsto_rpow_div_mul_add (-d) 1 0 zero_ne_one).comp hsucc)
    simp
  have hrealTerms_eq :
      (fun n : ℕ ↦ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))) =
        fun n : ℕ ↦ (n.succ : ℝ) ^ (-d / (n.succ : ℝ)) := by
    funext n
    -- Use the explicit norm formula to match the standard real asymptotic.
    calc
      ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))
          = ((n.succ : ℝ) ^ (-d)) ^ (1 / (n.succ : ℝ)) := by rw [hnorm n]
      _ = (n.succ : ℝ) ^ ((-d) * (1 / (n.succ : ℝ))) := by
        rw [← Real.rpow_mul (by positivity : 0 ≤ (n.succ : ℝ))]
      _ = (n.succ : ℝ) ^ (-d / (n.succ : ℝ)) := by congr 1; ring
  have hrealTerms :
      Tendsto
        (fun n : ℕ ↦ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ)))
        atTop (nhds 1) := by
    rw [hrealTerms_eq]
    exact hmodel
  have hENN :
      Tendsto
        (fun n : ℕ ↦ ENNReal.ofReal (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))))
        atTop (nhds 1) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 1).comp hrealTerms
  have hInverseEq :
      inverse_succ_root_sequence (𝕜 := 𝕜) =
        fun n : ℕ ↦ ENNReal.ofReal (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))) := rfl
  -- Return from the real model sequence to the `ENNReal`-valued root factor.
  rw [hInverseEq]
  exact hENN

/-- Helper for Proposition 7.1: the `p`-adic absolute value sends reciprocal positive integers to
the reciprocal of their `p`-adic value. -/
theorem padic_inv_natcast_eq_inv_padic_natcast (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Rat.AbsoluteValue.padic p (((n.succ : ℚ))⁻¹) = (Rat.AbsoluteValue.padic p n.succ)⁻¹ := by
  -- This is the multiplicativity of the absolute value specialized to inverses.
  simpa using (Rat.AbsoluteValue.padic p).map_inv₀ (n.succ : ℚ)

/-- Helper for Proposition 7.1: in the non-Archimedean branch of Ostrowski's theorem, the
reciprocal root sequence still tends to `1`. -/
theorem inverse_succ_root_tendsto_one_of_padic_equiv [CharZero 𝕜]
    (p : ℕ) [Fact p.Prime]
    (hpadic : (rational_norm_absolute_value (𝕜 := 𝕜)).IsEquiv (Rat.AbsoluteValue.padic p)) :
    Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (nhds 1) := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hpadic
  have hsucc :
      Tendsto (fun n : ℕ ↦ (n.succ : ℝ)) atTop atTop := by
    have hsucc' :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact
        (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ ↦ (m : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1)
    simpa [Nat.succ_eq_add_one] using
      hsucc'
  have hupper :
      Tendsto (fun n : ℕ ↦ (n.succ : ℝ) ^ (c⁻¹ / (n.succ : ℝ))) atTop (nhds 1) := by
    -- The squeeze upper bound is again a standard `x ^ (a / x)` limit.
    refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_)
      ((tendsto_rpow_div_mul_add c⁻¹ 1 0 zero_ne_one).comp hsucc)
    simp
  have hrealTerms :
      Tendsto
        (fun n : ℕ ↦ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ)))
        atTop (nhds 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n ↦ ?_) (fun n ↦ ?_)
    · have hpow_n :
          ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c = (Rat.AbsoluteValue.padic p n.succ)⁻¹ := by
        have happly := congrFun hpow (((n.succ : ℚ))⁻¹)
        change ‖((((n.succ : ℚ))⁻¹ : ℚ) : 𝕜)‖ ^ c =
          Rat.AbsoluteValue.padic p (((n.succ : ℚ))⁻¹) at happly
        -- Evaluate the equivalence identity on the reciprocal nat-cast and normalize the p-adic
        -- side once.
        simpa [Rat.cast_inv, padic_inv_natcast_eq_inv_padic_natcast] using happly
      have hpadic_pos : 0 < Rat.AbsoluteValue.padic p n.succ := by
        exact (Rat.AbsoluteValue.padic p).pos (by exact_mod_cast n.succ_ne_zero)
      have hpadic_le : Rat.AbsoluteValue.padic p n.succ ≤ 1 := by
        simpa using Rat.AbsoluteValue.padic_le_one p (n.succ : ℤ)
      have hpow_lower : 1 ≤ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c := by
        calc
          1 ≤ (Rat.AbsoluteValue.padic p n.succ)⁻¹ := (one_le_inv₀ hpadic_pos).2 hpadic_le
          _ = ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c := by rw [hpow_n]
      have hnorm_ge_one : 1 ≤ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ := by
        -- The p-adic value of a nonzero integer is at most `1`, so its reciprocal is at least
        -- `1`, and the positive `c`-th root preserves that lower bound.
        rw [← Real.rpow_le_rpow_iff (by positivity : 0 ≤ (1 : ℝ))
          (norm_nonneg _) hc]
        simpa using hpow_lower
      exact Real.one_le_rpow hnorm_ge_one (by positivity : 0 ≤ 1 / (n.succ : ℝ))
    · have hpow_n :
          ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c = (Rat.AbsoluteValue.padic p n.succ)⁻¹ := by
        have happly := congrFun hpow (((n.succ : ℚ))⁻¹)
        change ‖((((n.succ : ℚ))⁻¹ : ℚ) : 𝕜)‖ ^ c =
          Rat.AbsoluteValue.padic p (((n.succ : ℚ))⁻¹) at happly
        -- Reuse the normalized p-adic identity for the upper squeeze bound.
        simpa [Rat.cast_inv, padic_inv_natcast_eq_inv_padic_natcast] using happly
      have hpadic_pos : 0 < Rat.AbsoluteValue.padic p n.succ := by
        exact (Rat.AbsoluteValue.padic p).pos (by exact_mod_cast n.succ_ne_zero)
      have hpadic_inv_le : (Rat.AbsoluteValue.padic p n.succ)⁻¹ ≤ (n.succ : ℝ) := by
        -- Inverting the standard lower bound `1 / (n + 1) ≤ |n + 1|_p` gives the needed upper
        -- bound on the reciprocal p-adic value.
        have hpadic_inv_le' : (Rat.AbsoluteValue.padic p n.succ)⁻¹ ≤ ((n.succ : ℝ)⁻¹)⁻¹ := by
          exact (inv_le_inv₀ hpadic_pos (by positivity : 0 < ((n.succ : ℝ)⁻¹))).2
            (padic_nat_recip_le p n)
        simpa using hpadic_inv_le'
      have hpow_upper : ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c ≤ (n.succ : ℝ) := by
        calc
          ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ c = (Rat.AbsoluteValue.padic p n.succ)⁻¹ := hpow_n
          _ ≤ (n.succ : ℝ) := hpadic_inv_le
      have hnorm_le : ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ≤ (n.succ : ℝ) ^ c⁻¹ := by
        -- Taking the positive `c`-th root of the reciprocal p-adic bound yields the comparison on
        -- field norms.
        exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by positivity) hc).2 hpow_upper
      calc
        ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))
            ≤ ((n.succ : ℝ) ^ c⁻¹) ^ (1 / (n.succ : ℝ)) := by
              exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le (by positivity)
        _ = (n.succ : ℝ) ^ (c⁻¹ / (n.succ : ℝ)) := by
          rw [← Real.rpow_mul (by positivity : 0 ≤ (n.succ : ℝ))]
          congr 1
          ring
  have hENN :
      Tendsto
        (fun n : ℕ ↦ ENNReal.ofReal (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))))
        atTop (nhds 1) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 1).comp hrealTerms
  have hInverseEq :
      inverse_succ_root_sequence (𝕜 := 𝕜) =
        fun n : ℕ ↦ ENNReal.ofReal (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))) := rfl
  -- Transport the squeezed real limit back to the `ENNReal`-valued reciprocal root sequence.
  rw [hInverseEq]
  exact hENN

/-- Helper for Proposition 7.1: the reciprocal nat-cast factor is asymptotically neutral in the
root-limsup comparison. -/
theorem inverse_succ_root_limsup_eq_one [CharZero 𝕜] :
    limsup (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop = 1 := by
  set vQ : AbsoluteValue ℚ ℝ := rational_norm_absolute_value (𝕜 := 𝕜)
  have hlim :
      Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (nhds 1) := by
    by_cases hvQ : vQ.IsNontrivial
    · obtain hreal | hpadic := Rat.AbsoluteValue.equiv_real_or_padic vQ hvQ
      · -- In the Archimedean branch, the sequence behaves like a polynomial root.
        simpa [vQ] using inverse_succ_root_tendsto_one_of_real_equiv (𝕜 := 𝕜) hreal
      · rcases hpadic with ⟨p, ⟨hpPrime, hpadic⟩, _⟩
        letI : Fact p.Prime := hpPrime
        -- In the non-Archimedean branch, Ostrowski still forces subexponential growth.
        simpa [vQ] using inverse_succ_root_tendsto_one_of_padic_equiv (𝕜 := 𝕜) p hpadic
    · -- The remaining branch is the trivial absolute value on `ℚ`.
      simpa [vQ] using inverse_succ_root_tendsto_one_of_trivial (𝕜 := 𝕜) hvQ
  exact hlim.limsup_eq

/-- Helper for Proposition 7.1: each shifted original root is bounded by the reciprocal nat-cast
root factor times the corresponding shifted derived-coefficient root. -/
theorem tail_root_le_inverse_succ_root_mul_derivCoeff_root [CharZero 𝕜]
    (a : ℕ → 𝕜) (n : ℕ) :
    scalar_root_sequence a n.succ ≤
      inverse_succ_root_sequence (𝕜 := 𝕜) n *
        scalar_root_sequence (prependZero (ofScalarsDerivCoeff a)) n.succ := by
  have hcoeff :
      (((n.succ : 𝕜))⁻¹ : 𝕜) * prependZero (ofScalarsDerivCoeff a) n.succ = a n.succ := by
    -- Route correction: instead of forcing the inequality through repeated coercion rewrites,
    -- factor the shifted coefficient exactly before taking norms and roots.
    calc
      (((n.succ : 𝕜))⁻¹ : 𝕜) * prependZero (ofScalarsDerivCoeff a) n.succ
          = (((n.succ : 𝕜))⁻¹ : 𝕜) * ((n.succ : 𝕜) * a n.succ) := by
              simp [prependZero, ofScalarsDerivCoeff]
      _ = a n.succ := by
        rw [← mul_assoc, inv_mul_cancel₀ (show (n.succ : 𝕜) ≠ 0 by exact_mod_cast n.succ_ne_zero),
          one_mul]
  have hnorm :
      ‖a n.succ‖ =
        ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ * ‖prependZero (ofScalarsDerivCoeff a) n.succ‖ := by
    -- The textbook shift identity becomes multiplicative after taking norms.
    rw [← hcoeff, norm_mul]
  have hexp_nonneg : 0 ≤ 1 / (n.succ : ℝ) := by positivity
  -- Normalize each root factor to `ENNReal.ofReal`, then use the exact multiplicative identity.
  rw [scalar_root_sequence_eq_ofReal (a := a) (n := n.succ)]
  rw [inverse_succ_root_sequence,
    scalar_root_sequence_eq_ofReal (a := prependZero (ofScalarsDerivCoeff a)) (n := n.succ)]
  exact le_of_eq <|
    calc
      ENNReal.ofReal (‖a n.succ‖ ^ (1 / (n.succ : ℝ)))
          = ENNReal.ofReal
              ((‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ *
                  ‖prependZero (ofScalarsDerivCoeff a) n.succ‖) ^
                (1 / (n.succ : ℝ))) := by rw [hnorm]
      _ = ENNReal.ofReal
            (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ)) *
              ‖prependZero (ofScalarsDerivCoeff a) n.succ‖ ^ (1 / (n.succ : ℝ))) := by
            rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _) ]
      _ = ENNReal.ofReal (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n.succ : ℝ))) *
            ENNReal.ofReal
              (‖prependZero (ofScalarsDerivCoeff a) n.succ‖ ^ (1 / (n.succ : ℝ))) := by
            rw [ENNReal.ofReal_mul]
            positivity

/-- Helper for Proposition 7.1: the derived scalar coefficient series cannot have smaller radius
than the original series. -/
theorem ofScalars_radius_derivCoeff_le_radius [CharZero 𝕜] (a : ℕ → 𝕜) :
    (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius ≤ (ofScalars 𝕜 a).radius := by
  let tail : ℕ → ℝ≥0∞ := fun n ↦ scalar_root_sequence a n.succ
  let derivShift : ℕ → ℝ≥0∞ :=
    fun n ↦ scalar_root_sequence (prependZero (ofScalarsDerivCoeff a)) n.succ
  have htail :
      limsup tail atTop = (ofScalars 𝕜 a).radius⁻¹ := by
    -- Shift the Hadamard root sequence by one step; limsup is unchanged.
    calc
      limsup tail atTop = limsup (scalar_root_sequence a) atTop := by
        simpa [tail, Nat.add_comm] using (limsup_nat_add (scalar_root_sequence a) 1)
      _ = (ofScalars 𝕜 a).radius⁻¹ := by
        rw [← ofScalars_radius_inv_eq_limsup (𝕜 := 𝕜) a]
  have hderivShift :
      limsup derivShift atTop = (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius⁻¹ := by
    -- The shifted derived sequence is the root sequence of the prepended-zero series.
    calc
      limsup derivShift atTop =
          limsup (scalar_root_sequence (prependZero (ofScalarsDerivCoeff a))) atTop := by
            simpa [derivShift, Nat.add_comm] using
              (limsup_nat_add (scalar_root_sequence (prependZero (ofScalarsDerivCoeff a))) 1)
      _ = (ofScalars 𝕜 (prependZero (ofScalarsDerivCoeff a))).radius⁻¹ := by
        rw [← ofScalars_radius_inv_eq_limsup (𝕜 := 𝕜) (prependZero (ofScalarsDerivCoeff a))]
      _ = (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius⁻¹ := by
        simpa using congrArg (fun x : ℝ≥0∞ => x⁻¹)
          (radius_prependZero_eq_radius (𝕜 := 𝕜) (ofScalarsDerivCoeff a))
  have htail_le_prod :
      limsup tail atTop ≤
        limsup (fun n ↦ inverse_succ_root_sequence (𝕜 := 𝕜) n * derivShift n) atTop := by
    exact limsup_le_limsup
      (Eventually.of_forall
        (fun n ↦ tail_root_le_inverse_succ_root_mul_derivCoeff_root (𝕜 := 𝕜) a n))
  have hprod_le :
      limsup (fun n ↦ inverse_succ_root_sequence (𝕜 := 𝕜) n * derivShift n) atTop ≤
        limsup (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop * limsup derivShift atTop := by
    exact ENNReal.limsup_mul_le'
      (Or.inl (by simpa [inverse_succ_root_limsup_eq_one (𝕜 := 𝕜)]))
      (Or.inl (by simpa [inverse_succ_root_limsup_eq_one (𝕜 := 𝕜)]))
  have hradius_inv :
      (ofScalars 𝕜 a).radius⁻¹ ≤ (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius⁻¹ := by
    -- Combine the tail comparison with the fact that the reciprocal nat-cast roots converge to `1`.
    calc
      (ofScalars 𝕜 a).radius⁻¹ = limsup tail atTop := htail.symm
      _ ≤ limsup (fun n ↦ inverse_succ_root_sequence (𝕜 := 𝕜) n * derivShift n) atTop :=
        htail_le_prod
      _ ≤ limsup (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop * limsup derivShift atTop :=
        hprod_le
      _ = 1 * limsup derivShift atTop := by
        rw [inverse_succ_root_limsup_eq_one (𝕜 := 𝕜)]
      _ = limsup derivShift atTop := by simp
      _ = (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius⁻¹ := hderivShift
  exact ENNReal.inv_le_inv.mp hradius_inv

/-- Bridge/view: evaluating the canonical derivative series at `1` recovers the textbook derived
scalar coefficients. -/
theorem ofScalars_derivSeries_coeff_one_eq_derivCoeff
    (a : ℕ → 𝕜) (n : ℕ) :
    (ofScalars 𝕜 a).derivSeries.coeff n 1 = ofScalarsDerivCoeff a n := by
  -- Evaluating the canonical derivative coefficient at `1` gives the textbook scalar coefficient.
  simpa [ofScalarsDerivCoeff, Nat.succ_eq_add_one] using
    (ofScalars 𝕜 a).derivSeries_coeff_one n

/-- Helper for Proposition 7.1: evaluating the canonical derivative series at `1` recovers the
textbook derived scalar series. -/
theorem apply_one_comp_derivSeries_eq_ofScalars_derivCoeff
    (a : ℕ → 𝕜) :
    (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
        ((ofScalars 𝕜 a).derivSeries) =
      ofScalars 𝕜 (ofScalarsDerivCoeff a) := by
  -- The bridge is coefficientwise: both scalar series have the same coefficient at every order.
  ext n
  simp [FormalMultilinearSeries.coeff_ofScalars,
    ofScalarsDerivCoeff, smul_eq_mul]

/-- Bridge/view: summing the canonical derivative series and evaluating at `1` recovers the
textbook scalar derived series. -/
theorem ofScalars_derivSeries_sum_apply_one_eq_ofScalarsSum_derivCoeff
    (a : ℕ → 𝕜) (z : 𝕜) :
    ((ofScalars 𝕜 a).derivSeries.sum z) 1 = ofScalarsSum (ofScalarsDerivCoeff a) z := by
  have happly :
      ((ofScalars 𝕜 a).derivSeries.sum z) 1 =
        (((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
          ((ofScalars 𝕜 a).derivSeries)).sum z) := by
    -- Evaluation at `1` commutes with `tsum` because scalar multiplication by the identity map is
    -- a continuous left inverse.
    simpa [FormalMultilinearSeries.sum, Function.comp_apply] using
      Function.LeftInverse.map_tsum
        (f := fun n : ℕ ↦ (ofScalars 𝕜 a).derivSeries n fun _ ↦ z)
        ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).continuous)
        (show Continuous fun t : 𝕜 ↦ t • (1 : 𝕜 →L[𝕜] 𝕜) from
          continuous_id.smul continuous_const)
        (fun x ↦
          ContinuousLinearMap.ext fun t ↦ by
            simpa [smul_eq_mul, mul_comm] using (x.map_smul t (1 : 𝕜)).symm)
  -- First push evaluation at `1` through the summed derivative series.
  calc
    ((ofScalars 𝕜 a).derivSeries.sum z) 1 =
        (((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
          ((ofScalars 𝕜 a).derivSeries)).sum z) := happly
    -- Then rewrite the resulting scalar series by the coefficientwise bridge.
    _ = ofScalarsSum (ofScalarsDerivCoeff a) z := by
      simpa [ofScalarsSum] using
        congrArg (fun p : FormalMultilinearSeries 𝕜 𝕜 𝕜 => p.sum z)
          (apply_one_comp_derivSeries_eq_ofScalars_derivCoeff a)

/-- Helper for Proposition 7.1: composing the canonical derivative series with evaluation at `1`
cannot decrease the radius past the scalar derived series. -/
theorem ofScalars_derivSeries_radius_le_radius_derivCoeff
    [CharZero 𝕜]
    (a : ℕ → 𝕜) :
    ((ofScalars 𝕜 a).derivSeries).radius ≤ (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius := by
  -- Evaluation at `1` is continuous, so the radius only increases under composition.
  calc
    ((ofScalars 𝕜 a).derivSeries).radius ≤
        ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
          ((ofScalars 𝕜 a).derivSeries)).radius :=
      radius_le_radius_continuousLinearMap_comp _ _
    _ = (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius := by
      simpa using
        congrArg FormalMultilinearSeries.radius
          (apply_one_comp_derivSeries_eq_ofScalars_derivCoeff a)

/-- Proposition 7.1 (1): a scalar formal power series and its textbook derived scalar series have
the same radius of convergence. -/
theorem ofScalars_radius_eq_radius_derivCoeff [CharZero 𝕜] (a : ℕ → 𝕜) :
    (ofScalars 𝕜 a).radius = (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius := by
  apply le_antisymm
  · -- The forward inequality follows from the canonical derivative-radius bound.
    calc
      (ofScalars 𝕜 a).radius ≤ ((ofScalars 𝕜 a).derivSeries).radius :=
        (ofScalars 𝕜 a).radius_le_radius_derivSeries
      _ ≤ (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius :=
        ofScalars_derivSeries_radius_le_radius_derivCoeff a
  · -- Route correction: the reverse inequality uses the scalar Hadamard formula together with the
    -- Ostrowski control on the reciprocal nat-cast factor.
    exact ofScalars_radius_derivCoeff_le_radius a

/-- Bridge/view radius statement for the canonical derivative-series owner. -/
theorem ofScalars_radius_eq_derivSeries_radius [CharZero 𝕜] (a : ℕ → 𝕜) :
    (ofScalars 𝕜 a).radius = (ofScalars 𝕜 a).derivSeries.radius := by
  -- Sandwich the canonical derivative radius between the original radius and the scalar bridge.
  apply le_antisymm
  · exact (ofScalars 𝕜 a).radius_le_radius_derivSeries
  · calc
      (ofScalars 𝕜 a).derivSeries.radius ≤
          (ofScalars 𝕜 (ofScalarsDerivCoeff a)).radius :=
        ofScalars_derivSeries_radius_le_radius_derivCoeff a
      _ = (ofScalars 𝕜 a).radius := by
        rw [ofScalars_radius_eq_radius_derivCoeff a]

/-- Bridge/view derivative statement phrased directly with the canonical `derivSeries` owner. -/
theorem hasDerivAt_ofScalarsSum_eq_derivSeries_sum
    [CompleteSpace 𝕜]
    (a : ℕ → 𝕜)
    {z : 𝕜}
    (hz : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 a).radius) :
    HasDerivAt (ofScalarsSum a) (((ofScalars 𝕜 a).derivSeries.sum z) 1) z := by
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  have hzp : (‖z‖₊ : ℝ≥0∞) < p.radius := by
    simpa [ENNReal.ofReal_eq_coe_nnreal] using hz
  have hzp_mem : z ∈ Metric.eball (0 : 𝕜) p.radius := by
    simpa [Metric.mem_eball, edist_zero_right] using hzp
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hzp
  have hp : HasFPowerSeriesOnBall (ofScalarsSum a) p 0 p.radius := p.hasFPowerSeriesOnBall hp0
  have hf :
      HasFDerivAt (ofScalarsSum a)
        (continuousMultilinearCurryFin1 𝕜 𝕜 𝕜 (p.changeOrigin z 1)) z := by
    simpa [p] using hp.hasFDerivAt hzp
  have hs : fderiv 𝕜 (ofScalarsSum a) z = p.derivSeries.sum z := by
    simpa [p] using hp.fderiv.sum hzp_mem
  have hs' :
      continuousMultilinearCurryFin1 𝕜 𝕜 𝕜 (p.changeOrigin z 1) 1 =
        p.derivSeries.sum z 1 := by
    -- The Fréchet derivative computed from the analytic power series matches the formal derivative
    -- series at the evaluation point.
    rw [← hs]
    exact (congrArg (fun f ↦ f 1) hf.fderiv).symm
  simpa [p] using hf.hasDerivAt.congr_deriv hs'

/-- Proposition 7.1 (2): for every `z` strictly inside the radius of convergence, the summed
scalar power series has derivative given by the sum of the textbook scalar derived series. -/
theorem hasDerivAt_ofScalarsSum_eq_ofScalarsSum_derivCoeff
    [CompleteSpace 𝕜]
    (a : ℕ → 𝕜)
    {z : 𝕜}
    (hz : ENNReal.ofReal ‖z‖ < (ofScalars 𝕜 a).radius) :
    HasDerivAt (ofScalarsSum a) (ofScalarsSum (ofScalarsDerivCoeff a) z) z := by
  simpa [ofScalars_derivSeries_sum_apply_one_eq_ofScalarsSum_derivCoeff] using
    hasDerivAt_ofScalarsSum_eq_derivSeries_sum a hz
