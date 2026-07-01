import Mathlib
import cartan.I.section02.«0007_Example_I_2_extra_5»
import cartan.I.section02.«0008_Proposition_4_1»
import cartan.I.section02.«0010_Proposition_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open PowerSeries
open scoped PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the API choice
-- was checked directly against Mathlib's `PowerSeries.coeff_one`, `PowerSeries.coeff_mul`, and the
-- nearby local section02 `PowerSeries.radius` owner for Proposition 4.1.

/-- Proposition 6.1: if a scalar power series `S` has nonzero radius of convergence and `T` is a
scalar power series with `S * T = 1`, then `T` also has
nonzero radius of convergence. -/
theorem radius_ne_zero_of_mul_eq_one
    (S T : 𝕜⟦X⟧)
    (hS : S.radius ≠ 0)
    (hST : S * T = 1) :
    T.radius ≠ 0 := by
  let a : 𝕜 := S.constantCoeff
  let G : 𝕜⟦X⟧ := mk fun _ ↦ (1 : 𝕜)
  let W : 𝕜⟦X⟧ := a⁻¹ • S
  let U : 𝕜⟦X⟧ := 1 - W
  have hconst : a * T.constantCoeff = 1 := by
    simpa [a] using congrArg constantCoeff hST
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hconst
  have radius_smul_eq_powerSeries (c : 𝕜) (F : 𝕜⟦X⟧) (hc : c ≠ 0) :
      (c • F).radius = F.radius := by
    let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 fun n ↦ coeff n F
    have hsmul : ofScalars 𝕜 (fun n ↦ coeff n (c • F)) = c • p := by
      ext n
      simp [p]
    calc
      (c • F).radius = (ofScalars 𝕜 fun n ↦ coeff n (c • F)).radius := rfl
      _ = (c • p).radius := by rw [hsmul]
      _ = p.radius := FormalMultilinearSeries.radius_smul_eq p hc
      _ = F.radius := rfl
  have radius_neg_powerSeries (F : 𝕜⟦X⟧) : (-F).radius = F.radius := by
    simpa using radius_smul_eq_powerSeries (-1) F (neg_ne_zero.2 one_ne_zero)
  have hWradius : W.radius = S.radius := by
    dsimp [W]
    exact radius_smul_eq_powerSeries a⁻¹ S (inv_ne_zero ha)
  have hW : W.radius ≠ 0 := by
    rw [hWradius]
    exact hS
  have hU0 : U.constantCoeff = 0 := by
    simp [U, W, a, ha]
  have hconstRadius : (1 : 𝕜⟦X⟧).radius = ⊤ := by
    let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 fun n ↦ coeff n (1 : 𝕜⟦X⟧)
    change p.radius = ⊤
    refine p.radius_eq_top_of_forall_image_add_eq_zero 1 ?_
    intro m
    simp [p, PowerSeries.coeff_one]
  have hWpos : 0 < W.radius := pos_iff_ne_zero.2 hW
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hWpos with ⟨ρ, hρ0, hρW⟩
  have hρconst : (ρ : ENNReal) ≤ (1 : 𝕜⟦X⟧).radius := by
    rw [hconstRadius]
    simp
  have hρnegW : (ρ : ENNReal) ≤ (-W).radius := by
    rw [radius_neg_powerSeries W]
    exact hρW.le
  have hρU : (ρ : ENNReal) ≤ U.radius := by
    simpa [U, sub_eq_add_neg] using radius_ge_add (1 : 𝕜⟦X⟧) (-W) ρ hρconst hρnegW
  have hU : U.radius ≠ 0 := by
    exact pos_iff_ne_zero.1 <| lt_of_lt_of_le hρ0 hρU
  have hG : G.radius ≠ 0 := by
    rw [show G.radius = 1 by simpa [G] using (radius_one_eq_one : (mk fun _ ↦ (1 : 𝕜)).radius = 1)]
    norm_num
  have hexists :
      ∃ r : NNReal, 0 < r ∧ Summable (fun n : ℕ => ‖coeff n U‖₊ * r ^ n) ∧ ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n U‖₊ * r ^ n) < G.radius :=
    exists_radius_for_scalar_series_composition hU0 hG hU
  obtain ⟨r, hr0, hsum, hr⟩ := hexists
  let GU : 𝕜⟦X⟧ := G.subst U
  have hGsubstRadius : GU.radius ≠ 0 := by
    have hradius : (r : ENNReal) ≤ GU.radius := by
      simpa [GU] using radius_ge_comp_of_scalar_series_bound hU0 hsum hr
    exact pos_iff_ne_zero.1 <| lt_of_lt_of_le (ENNReal.coe_pos.2 hr0) hradius
  have hUsub : HasSubst U := HasSubst.of_constantCoeff_zero hU0
  have hgeom_mul : GU * (1 - U) = 1 := by
    calc
      GU * (1 - U) = GU * (((1 : 𝕜⟦X⟧) - X).subst U) := by
        rw [PowerSeries.subst_sub hUsub (1 : 𝕜⟦X⟧) X, PowerSeries.subst_X hUsub]
        rw [show PowerSeries.subst U (1 : 𝕜⟦X⟧) = (1 : 𝕜⟦X⟧) by
          rw [show (1 : 𝕜⟦X⟧) = C (1 : 𝕜) by simp, PowerSeries.subst_C]
          simp]
      _ = (G * ((1 : 𝕜⟦X⟧) - X)).subst U := by
        simp [GU, ← PowerSeries.subst_mul hUsub G ((1 : 𝕜⟦X⟧) - X)]
      _ = 1 := by
        rw [show G * ((1 : 𝕜⟦X⟧) - X) = (1 : 𝕜⟦X⟧) by
          simpa [G] using PowerSeries.mk_one_mul_one_sub_eq_one 𝕜]
        rw [show (1 : 𝕜⟦X⟧) = C (1 : 𝕜) by simp, PowerSeries.subst_C]
        simp
  have hscaled_mul : (a • T) * (1 - U) = 1 := by
    calc
      (a • T) * (1 - U) = (a • T) * (a⁻¹ • S) := by
        simp [U, W]
      _ = a • (a⁻¹ • (T * S)) := by
        rw [smul_mul_assoc, mul_smul_comm]
      _ = 1 := by
        rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
        simpa [mul_comm] using hST
  have hgeom_inv : GU = (1 - U)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp [hU0])]
    exact hgeom_mul
  have hscaled_inv : a • T = (1 - U)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp [hU0])]
    exact hscaled_mul
  have hscaledRadius : (a • T).radius = T.radius := radius_smul_eq_powerSeries a T ha
  rw [← hscaledRadius]
  rw [hscaled_inv, ← hgeom_inv]
  exact hGsubstRadius
