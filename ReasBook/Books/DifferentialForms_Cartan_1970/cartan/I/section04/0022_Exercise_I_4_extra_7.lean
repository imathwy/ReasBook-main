import Mathlib
import DifferentialForms_Cartan_1970.I.section02.«0007_Example_I_2_extra_5»
import DifferentialForms_Cartan_1970.I.section02.«0008_Proposition_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open PowerSeries

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the owner/API
-- choices below were checked against local Mathlib's `FormalMultilinearSeries.ofScalars`,
-- `ofScalarsSum`, `formalMultilinearSeries_geometric_eq_ofScalars`,
-- `hasFPowerSeriesOnBall_inv_one_sub`, and the nearby section04 radius-of-convergence precedent.

universe u

open FormalMultilinearSeries

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The coefficients `s_n = a₀ + ⋯ + aₙ` attached to the scalar series in the exercise. -/
def exerciseI4Extra7PartialSums (a : ℕ → 𝕜) (n : ℕ) : 𝕜 :=
  Finset.sum (Finset.range (n + 1)) fun i ↦ a i

/-- The Cesàro means `t_n = (s₀ + ⋯ + sₙ) / (n + 1)` attached to the exercise. -/
def exerciseI4Extra7CesaroMeans (a : ℕ → 𝕜) (n : ℕ) : 𝕜 :=
  ((n + 1 : 𝕜)⁻¹) *
    Finset.sum (Finset.range (n + 1)) fun k ↦ exerciseI4Extra7PartialSums a k

/-- Helper for Exercise I.4-extra-7: inserting a leading zero coefficient. -/
def exerciseI4Extra7PrependZero (a : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => a n

/-- Helper for Exercise I.4-extra-7: for scalar-valued `ofScalars` series, the operator norm of
the `n`-th multilinear coefficient is just the norm of the scalar coefficient. -/
lemma ofScalars_norm_eq_coeff (a : ℕ → 𝕜) (n : ℕ) :
    ‖ofScalars 𝕜 a n‖ = ‖a n‖ := by
  -- Over the scalar algebra, `mkPiAlgebraFin` has norm `1`, so no extra factor remains.
  rw [FormalMultilinearSeries.ofScalars_norm_eq_mul]
  simp [ContinuousMultilinearMap.norm_mkPiAlgebraFin]

/-- Helper for Exercise I.4-extra-7: the partial-sum coefficients are obtained by multiplying the
original scalar power series by the geometric series. -/
lemma partialSums_powerSeries_eq_mul_geometric (a : ℕ → 𝕜) :
    PowerSeries.mk (exerciseI4Extra7PartialSums a) =
      PowerSeries.mk a * PowerSeries.mk (fun _ ↦ (1 : 𝕜)) := by
  -- Compare coefficients termwise via the finite Cauchy-product formula.
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l ↦
        coeff k (PowerSeries.mk a) * coeff l (PowerSeries.mk (fun _ ↦ (1 : 𝕜)))) n]
  simp [exerciseI4Extra7PartialSums]

/-- Helper for Exercise I.4-extra-7: multiplying the partial-sum series by `1 - X` recovers the
original scalar power series. -/
lemma partialSums_mul_one_sub_eq_powerSeries (a : ℕ → 𝕜) :
    PowerSeries.mk (exerciseI4Extra7PartialSums a) * (1 - (PowerSeries.X : 𝕜⟦X⟧)) =
      PowerSeries.mk a := by
  -- Cancel the geometric factor using the standard identity
  -- `(\sum X^n) * (1 - X) = 1`.
  calc
    PowerSeries.mk (exerciseI4Extra7PartialSums a) * (1 - (PowerSeries.X : 𝕜⟦X⟧))
        = (PowerSeries.mk a * PowerSeries.mk (fun _ ↦ (1 : 𝕜))) *
            (1 - (PowerSeries.X : 𝕜⟦X⟧)) := by
            rw [partialSums_powerSeries_eq_mul_geometric]
    _ = PowerSeries.mk a *
          (PowerSeries.mk (fun _ ↦ (1 : 𝕜)) * (1 - (PowerSeries.X : 𝕜⟦X⟧))) := by
          rw [mul_assoc]
    _ = PowerSeries.mk a * 1 := by
          rw [show PowerSeries.mk (fun _ ↦ (1 : 𝕜)) * (1 - (PowerSeries.X : 𝕜⟦X⟧)) = 1 by
            simpa using PowerSeries.mk_one_mul_one_sub_eq_one 𝕜]
    _ = PowerSeries.mk a := by simp

/-- Helper for Exercise I.4-extra-7: the polynomial factor `1 - X` has infinite radius of
convergence. -/
lemma radius_one_sub_X_eq_top :
    ((1 - (PowerSeries.X : 𝕜⟦X⟧))).radius = ⊤ := by
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
    ofScalars 𝕜 fun n ↦ coeff n (1 - (PowerSeries.X : 𝕜⟦X⟧))
  -- The coefficients vanish from degree `2` onward, so the radius is infinite.
  change p.radius = ⊤
  refine p.radius_eq_top_of_forall_image_add_eq_zero 2 ?_
  intro m
  simp [p, PowerSeries.coeff_one, PowerSeries.coeff_X]

/-- Helper for Exercise I.4-extra-7: taking partial sums cannot enlarge the convergence radius. -/
lemma radius_partialSums_le_radius (a : ℕ → 𝕜) :
    (ofScalars 𝕜 (exerciseI4Extra7PartialSums a)).radius ≤ (ofScalars 𝕜 a).radius := by
  let U : 𝕜⟦X⟧ := PowerSeries.mk (exerciseI4Extra7PartialSums a)
  let S : 𝕜⟦X⟧ := PowerSeries.mk a
  have hUS : U * (1 - (PowerSeries.X : 𝕜⟦X⟧)) = S := by
    -- Rewrite the source identity at the `PowerSeries` level.
    simpa [U, S] using partialSums_mul_one_sub_eq_powerSeries (𝕜 := 𝕜) a
  refine ENNReal.le_of_forall_nnreal_lt ?_
  intro r hr
  have hU : (r : ENNReal) ≤ U.radius := by
    simpa [U, PowerSeries.radius, PowerSeries.coeff_mk] using hr.le
  have hX : (r : ENNReal) ≤ (1 - (PowerSeries.X : 𝕜⟦X⟧)).radius := by
    rw [radius_one_sub_X_eq_top (𝕜 := 𝕜)]
    simp
  have hmul : (r : ENNReal) ≤ (U * (1 - (PowerSeries.X : 𝕜⟦X⟧))).radius :=
    radius_ge_mul U (1 - (PowerSeries.X : 𝕜⟦X⟧)) r hU hX
  -- Any disk of convergence for `U` is also a disk of convergence for `S`.
  simpa [U, S, hUS, PowerSeries.radius, PowerSeries.coeff_mk] using hmul

/-- Helper for Exercise I.4-extra-7: multiplying the Cesàro means by `n + 1` recovers the
iterated partial sums. -/
lemma natSucc_mul_cesaro_eq_iteratedPartialSums
    (a : ℕ → 𝕜) (n : ℕ) :
    (n + 1 : 𝕜) * exerciseI4Extra7CesaroMeans a n =
      exerciseI4Extra7PartialSums (exerciseI4Extra7PartialSums a) n := by
  have hne : (n + 1 : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  -- The scalar factor `(n + 1)⁻¹` in the Cesàro mean cancels against `(n + 1)`.
  rw [exerciseI4Extra7CesaroMeans]
  simp [exerciseI4Extra7PartialSums, hne, mul_assoc]

/-- Helper for Exercise I.4-extra-7: adding a leading zero coefficient leaves the convergence
radius unchanged. -/
lemma radius_prependZero_eq_radius (a : ℕ → 𝕜) :
    (ofScalars 𝕜 (exerciseI4Extra7PrependZero a)).radius = (ofScalars 𝕜 a).radius := by
  let P : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 (exerciseI4Extra7PrependZero a)
  let Q : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt ?_
    intro r hr
    by_cases hr0 : r = 0
    · simpa [hr0] using (show (0 : ENNReal) ≤ Q.radius from by simp)
    have hrpos : 0 < r := by
      exact pos_iff_ne_zero.mpr hr0
    have hrposR : 0 < (r : ℝ) := by
      exact_mod_cast hrpos
    rcases P.norm_le_div_pow_of_pos_of_lt_radius hrpos hr with ⟨C, hC, hP⟩
    have hQbound : ∀ n : ℕ, ‖Q n‖ * (r : ℝ) ^ n ≤ C / (r : ℝ) := by
      intro n
      have hPn : ‖P (n + 1)‖ ≤ C / (r : ℝ) ^ (n + 1) := hP (n + 1)
      have hPn' : ‖a n‖ ≤ C / (r : ℝ) ^ (n + 1) := by
        simpa [P, exerciseI4Extra7PrependZero, ofScalars_norm_eq_coeff] using hPn
      calc
        ‖Q n‖ * (r : ℝ) ^ n = ‖a n‖ * (r : ℝ) ^ n := by
          simp [Q, ofScalars_norm_eq_coeff]
        _ ≤ (C / (r : ℝ) ^ (n + 1)) * (r : ℝ) ^ n := by
          gcongr
        _ = C / (r : ℝ) := by
          rw [pow_succ]
          field_simp [hrposR.ne', pow_ne_zero n hrposR.ne']
    exact Q.le_radius_of_bound (C / (r : ℝ)) hQbound
  · refine ENNReal.le_of_forall_nnreal_lt ?_
    intro r hr
    by_cases hr0 : r = 0
    · simpa [hr0] using (show (0 : ENNReal) ≤ P.radius from by simp)
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
          simpa [P, exerciseI4Extra7PrependZero] using hCr
      | succ n =>
          have hQn : ‖Q n‖ * (r : ℝ) ^ n ≤ C := hQ n
          calc
            ‖P (n + 1)‖ * (r : ℝ) ^ (n + 1)
                = (‖Q n‖ * (r : ℝ) ^ n) * (r : ℝ) := by
                    simp [P, Q, exerciseI4Extra7PrependZero, pow_succ, mul_assoc, mul_comm]
            _ ≤ C * (r : ℝ) := by
                gcongr
    exact P.le_radius_of_bound (C * (r : ℝ)) hPbound

/-- Helper for Exercise I.4-extra-7: weighting coefficients by `n + 1` cannot decrease the
convergence radius. -/
lemma radius_le_radius_natSucc_mul (a : ℕ → 𝕜) :
    (ofScalars 𝕜 a).radius ≤
      (ofScalars 𝕜 (fun n ↦ (n + 1 : 𝕜) * a n)).radius := by
  let P : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 (exerciseI4Extra7PrependZero a)
  let W : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 (fun n ↦ (n + 1 : 𝕜) * a n)
  refine ENNReal.le_of_forall_nnreal_lt ?_
  intro r hr
  have hprepend : P.radius = (ofScalars 𝕜 a).radius := by
    simpa [P] using radius_prependZero_eq_radius (𝕜 := 𝕜) a
  have hrP : (r : ENNReal) < P.radius := by
    rwa [hprepend]
  have hrD : (r : ENNReal) < P.derivSeries.radius :=
    lt_of_lt_of_le hrP P.radius_le_radius_derivSeries
  rcases P.derivSeries.norm_mul_pow_le_of_lt_radius hrD with ⟨C, hC, hD⟩
  have hWbound : ∀ n : ℕ, ‖W n‖ * (r : ℝ) ^ n ≤ C := by
    intro n
    have hcoeffEq : P.derivSeries.coeff n 1 = (n + 1 : 𝕜) * a n := by
      simpa [P, exerciseI4Extra7PrependZero, Nat.succ_eq_add_one, smul_eq_mul] using
        (FormalMultilinearSeries.derivSeries_coeff_one (p := P) n)
    have hcoeffLe : ‖(n + 1 : 𝕜) * a n‖ ≤ ‖P.derivSeries n‖ := by
      calc
        ‖(n + 1 : 𝕜) * a n‖ = ‖P.derivSeries.coeff n 1‖ := by
          rw [hcoeffEq]
        _ ≤ ‖P.derivSeries.coeff n‖ := by
          simpa using (P.derivSeries.coeff n).le_opNorm (1 : 𝕜)
        _ ≤ ‖P.derivSeries n‖ := by
          simpa using (P.derivSeries n).le_opNorm (fun _ ↦ (1 : 𝕜))
    calc
      ‖W n‖ * (r : ℝ) ^ n = ‖(n + 1 : 𝕜) * a n‖ * (r : ℝ) ^ n := by
        simp [W, ofScalars_norm_eq_coeff]
      _ ≤ ‖P.derivSeries n‖ * (r : ℝ) ^ n := by
        gcongr
      _ ≤ C := hD n
  exact W.le_radius_of_bound C hWbound

/-- Exercise I.4-extra-7 (1): if `S(X) = ∑ a_n X^n` has radius `1`, then the series
`U(X) = ∑ s_n X^n` built from the partial sums `s_n = a₀ + ⋯ + aₙ` also has radius `1`. -/
theorem radius_exerciseI4Extra7U_eq_one
    (a : ℕ → 𝕜)
    (hρ : (ofScalars 𝕜 a).radius = 1) :
    (ofScalars 𝕜 (exerciseI4Extra7PartialSums a)).radius = 1 := by
  let S : 𝕜⟦X⟧ := PowerSeries.mk a
  let U : 𝕜⟦X⟧ := PowerSeries.mk (exerciseI4Extra7PartialSums a)
  let G : 𝕜⟦X⟧ := PowerSeries.mk (fun _ ↦ (1 : 𝕜))
  have hS : (1 : ENNReal) ≤ S.radius := by
    -- Rewrite the hypothesis through the scalar `PowerSeries` owner.
    simpa [S, PowerSeries.radius, PowerSeries.coeff_mk] using hρ.ge
  have hG : (1 : ENNReal) ≤ G.radius := by
    -- The geometric series has radius exactly `1`.
    have hG_eq : G.radius = 1 := by
      simpa [G] using (radius_one_eq_one : (PowerSeries.mk fun _ ↦ (1 : 𝕜)).radius = 1)
    simpa [hG_eq]
  have hUG : U = S * G := by
    -- This is the textbook identity `U = S / (1 - X)`.
    simpa [S, U, G] using partialSums_powerSeries_eq_mul_geometric (𝕜 := 𝕜) a
  have hU_ge : (1 : ENNReal) ≤ U.radius := by
    -- Multiplying by the geometric series preserves radius `1`.
    simpa [hUG] using radius_ge_mul S G 1 hS hG
  have hU_le : U.radius ≤ S.radius := by
    -- The inverse multiplication by `1 - X` recovers the original series.
    simpa [S, U, PowerSeries.radius, PowerSeries.coeff_mk] using
      radius_partialSums_le_radius (𝕜 := 𝕜) a
  have hS_eq : S.radius = 1 := by
    simpa [S, PowerSeries.radius, PowerSeries.coeff_mk] using hρ
  have hU_eq : U.radius = 1 := by
    exact le_antisymm (hU_le.trans hS_eq.le) hU_ge
  simpa [U, PowerSeries.radius, PowerSeries.coeff_mk] using hU_eq

/-- Exercise I.4-extra-7 (2): if `S(X) = ∑ a_n X^n` has radius `1`, then the series
`V(X) = ∑ t_n X^n` built from the Cesàro means
`t_n = (s₀ + ⋯ + sₙ) / (n + 1)` also has radius `1`. -/
theorem radius_exerciseI4Extra7V_eq_one
    (a : ℕ → 𝕜)
    (hρ : (ofScalars 𝕜 a).radius = 1) :
    (ofScalars 𝕜 (exerciseI4Extra7CesaroMeans a)).radius = 1 := by
  let V : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 (exerciseI4Extra7CesaroMeans a)
  let W : FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
    ofScalars 𝕜 (fun n ↦ (n + 1 : 𝕜) * exerciseI4Extra7CesaroMeans a n)
  have hU : (ofScalars 𝕜 (exerciseI4Extra7PartialSums a)).radius = 1 :=
    radius_exerciseI4Extra7U_eq_one (𝕜 := 𝕜) a hρ
  have hWseq :
      (fun n : ℕ ↦ (n + 1 : 𝕜) * exerciseI4Extra7CesaroMeans a n) =
        exerciseI4Extra7PartialSums (exerciseI4Extra7PartialSums a) := by
    -- The weighted Cesàro coefficients are the iterated partial sums.
    funext n
    exact natSucc_mul_cesaro_eq_iteratedPartialSums (𝕜 := 𝕜) a n
  have hW_eq_one : W.radius = 1 := by
    -- Apply part (1) once more to the partial-sum sequence.
    have hW : W = ofScalars 𝕜 (exerciseI4Extra7PartialSums (exerciseI4Extra7PartialSums a)) := by
      simp [W, hWseq]
    rw [hW]
    exact radius_exerciseI4Extra7U_eq_one (𝕜 := 𝕜) (exerciseI4Extra7PartialSums a) hU
  have hcoeff_le : ∀ n : ℕ, ‖V n‖ ≤ ‖W n‖ := by
    intro n
    have hne : (n + 1 : 𝕜) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hInv : ‖((n + 1 : 𝕜)⁻¹ : 𝕜)‖ ≤ 1 := by
      have hnat : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hnorm : ‖(n : 𝕜) + 1‖ = (n + 1 : ℝ) := by
        simpa [Nat.cast_add] using (_root_.norm_natCast (α := 𝕜) (n + 1))
      rw [norm_inv]
      rw [hnorm]
      exact inv_le_one_of_one_le₀ hnat
    -- The coefficients of `V` are obtained from the weighted coefficients by multiplication by
    -- `(n + 1)⁻¹`, whose norm is at most `1`.
    calc
      ‖V n‖ = ‖exerciseI4Extra7CesaroMeans a n‖ := by
        simp [V]
      _ = ‖(n + 1 : 𝕜)⁻¹ * ((n + 1 : 𝕜) * exerciseI4Extra7CesaroMeans a n)‖ := by
        have hmul :
            exerciseI4Extra7CesaroMeans a n =
              (n + 1 : 𝕜)⁻¹ * ((n + 1 : 𝕜) * exerciseI4Extra7CesaroMeans a n) := by
          field_simp [hne, mul_assoc]
        exact congrArg norm hmul
      _ = ‖((n + 1 : 𝕜)⁻¹ : 𝕜)‖ *
            ‖(n + 1 : 𝕜) * exerciseI4Extra7CesaroMeans a n‖ := by
            rw [norm_mul]
      _ ≤ ‖(n + 1 : 𝕜) * exerciseI4Extra7CesaroMeans a n‖ := by
            exact mul_le_of_le_one_left (norm_nonneg _) hInv
      _ = ‖W n‖ := by
            simp [W]
  have hW_le_V : W.radius ≤ V.radius := by
    -- Coefficientwise domination gives the radius comparison in the easy direction.
    exact FormalMultilinearSeries.radius_le_of_le hcoeff_le
  have hV_le : V.radius ≤ 1 := by
    -- The derivative comparison shows that weighting by `n + 1` cannot reduce the radius.
    calc
      V.radius ≤ W.radius := by
        simpa [V, W] using radius_le_radius_natSucc_mul
          (𝕜 := 𝕜) (exerciseI4Extra7CesaroMeans a)
      _ = 1 := hW_eq_one
  have hV_ge : (1 : ENNReal) ≤ V.radius := by
    calc
      (1 : ENNReal) = W.radius := hW_eq_one.symm
      _ ≤ V.radius := hW_le_V
  have hV_eq : V.radius = 1 := le_antisymm hV_le hV_ge
  simpa [V] using hV_eq

/-- Exercise I.4-extra-7 (3): on the unit disk inside the convergence disk of `∑ a_n z^n`, the
scalar-series sum for the partial-sum coefficients `s_n = a₀ + ⋯ + aₙ` is obtained by multiplying
the original scalar-series sum by `(1 - z)⁻¹`. -/
theorem inv_one_sub_mul_ofScalarsSum_eq_ofScalarsSum_exerciseI4Extra7PartialSums
    (a : ℕ → 𝕜)
    (hρ : (1 : ENNReal) ≤ (ofScalars 𝕜 a).radius)
    {z : 𝕜} (hz : ‖z‖ < 1) :
    (1 - z)⁻¹ * ofScalarsSum a z =
      ofScalarsSum (exerciseI4Extra7PartialSums a) z := by
  let S : 𝕜⟦X⟧ := PowerSeries.mk a
  let U : 𝕜⟦X⟧ := PowerSeries.mk (exerciseI4Extra7PartialSums a)
  let G : 𝕜⟦X⟧ := PowerSeries.mk (fun _ ↦ (1 : 𝕜))
  have hUG : U = S * G := by
    -- This is the same structural identity used in part (1).
    simpa [S, U, G] using partialSums_powerSeries_eq_mul_geometric (𝕜 := 𝕜) a
  have hzENN : (‖z‖₊ : ENNReal) < 1 := by
    exact_mod_cast hz
  have hzS : (‖z‖₊ : ENNReal) < S.radius := by
    -- The evaluation point lies strictly inside the radius of `S`.
    calc
      (‖z‖₊ : ENNReal) < 1 := hzENN
      _ ≤ S.radius := by
        simpa [S, PowerSeries.radius, PowerSeries.coeff_mk] using hρ
  have hS_norm : Summable (fun n : ℕ ↦ ‖coeff n S * z ^ n‖) := by
    -- Absolute convergence follows from the radius bound.
    simpa [norm_mul, norm_pow] using summable_norm_coeff_mul_pow_of_lt_radius S hzS
  have hS : Summable (fun n : ℕ ↦ coeff n S * z ^ n) := hS_norm.of_norm
  have hG_norm : Summable (fun n : ℕ ↦ ‖coeff n G * z ^ n‖) := by
    -- The geometric series is absolutely summable on `‖z‖ < 1`.
    simpa [G, PowerSeries.coeff_mk, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz)
  have hG : Summable (fun n : ℕ ↦ coeff n G * z ^ n) := by
    simpa [G, PowerSeries.coeff_mk] using (summable_geometric_of_norm_lt_one hz : Summable fun n ↦ z ^ n)
  have hmul :
      U.sum z = S.sum z * G.sum z := by
    -- Evaluate the product identity inside the open unit disk.
    simpa [hUG] using sum_mul_eq_mul_sum S G z hS_norm hS hG_norm hG
  have hGsum : G.sum z = (1 - z)⁻¹ := by
    -- The geometric series evaluates to `(1 - z)⁻¹`.
    simpa [G, PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul] using
      (tsum_geometric_of_norm_lt_one (ξ := z) hz)
  have hSsum : S.sum z = ofScalarsSum a z := by
    simp [S, PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul]
  have hUsum : U.sum z = ofScalarsSum (exerciseI4Extra7PartialSums a) z := by
    simp [U, PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul]
  -- Translate the power-series identity back to the source-facing `ofScalarsSum`.
  calc
    (1 - z)⁻¹ * ofScalarsSum a z = G.sum z * S.sum z := by
      rw [hGsum, hSsum]
    _ = S.sum z * G.sum z := by
      ac_rfl
    _ = U.sum z := hmul.symm
    _ = ofScalarsSum (exerciseI4Extra7PartialSums a) z := hUsum

/-- Exercise I.4-extra-7 (3), textbook form: if `S(X) = ∑ a_n X^n` has radius `1`, then for
`‖z‖ < 1` one has `(1 - z)⁻¹ * ∑ a_n z^n = ∑ s_n z^n`. -/
theorem inv_one_sub_mul_tsum_eq_tsum_exerciseI4Extra7PartialSums
    (a : ℕ → 𝕜)
    (hρ : (ofScalars 𝕜 a).radius = 1)
    {z : 𝕜} (hz : ‖z‖ < 1) :
    (1 - z)⁻¹ * (∑' n : ℕ, a n * z ^ n) =
      ∑' n : ℕ, exerciseI4Extra7PartialSums a n * z ^ n := by
  -- Rewrite both sums as `ofScalarsSum` and apply the previous theorem.
  simpa [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using
    inv_one_sub_mul_ofScalarsSum_eq_ofScalarsSum_exerciseI4Extra7PartialSums
      (𝕜 := 𝕜) a (by simpa [hρ] using hρ.ge) hz
