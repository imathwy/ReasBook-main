import Mathlib
import BauschkeLean.Chap04.Example_4_17
import BauschkeLean.Chap08.Text_8_0_3
import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap12.Proposition_12_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section ProximityHelpers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 14 5: the soft-thresholded point satisfies the proximal variational
inequality for the scaled norm. -/
private theorem softThresholder_isProxPoint_scaledNormKernelOfPos
    (ρ : Set.Ioi (0 : ℝ)) (x : H) :
    IsProxPoint (scaledNormKernelOfPos (H := H) ρ) x (softThresholder (ρ : ℝ) x) := by
  let p : H := softThresholder (ρ : ℝ) x
  rw [isProxPoint_iff_forall_inner_add_le
    (scaledNormKernelOfPos (H := H) ρ)
    (scaledNormKernelOfPos_mem_gammaZero (H := H) ρ).2 x p]
  intro y
  by_cases hx : (ρ : ℝ) < ‖x‖
  · have hnormx_pos : 0 < ‖x‖ := lt_trans ρ.2 hx
    have hnormx_ne : ‖x‖ ≠ 0 := hnormx_pos.ne'
    have hp_eq : p = (1 - (ρ : ℝ) / ‖x‖) • x := by
      simp [p, softThresholder_apply, hx]
    have hsub_eq : x - p = ((ρ : ℝ) / ‖x‖) • x := by
      rw [hp_eq]
      calc
        x - (1 - (ρ : ℝ) / ‖x‖) • x
            = (1 : ℝ) • x - (1 - (ρ : ℝ) / ‖x‖) • x := by simp
        _ = (((1 : ℝ) - (1 - (ρ : ℝ) / ‖x‖)) : ℝ) • x := by
              simpa using (sub_smul (1 : ℝ) (1 - (ρ : ℝ) / ‖x‖) x).symm
        _ = ((ρ : ℝ) / ‖x‖) • x := by ring
    have hcoeff_nonneg : 0 ≤ 1 - (ρ : ℝ) / ‖x‖ := by
      rw [sub_nonneg]
      rw [div_le_iff₀ hnormx_pos]
      simpa using (hx.le : (ρ : ℝ) ≤ ‖x‖)
    have hp_norm : ‖p‖ = ‖x‖ - (ρ : ℝ) := by
      rw [hp_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
      field_simp [hnormx_ne]
    have hsub_norm : ‖x - p‖ = (ρ : ℝ) := by
      rw [hsub_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ρ.2 hnormx_pos)]
      field_simp [hnormx_ne]
    have hinner_pp : ⟪p, x - p⟫_ℝ = (ρ : ℝ) * ‖p‖ := by
      rw [hp_eq]
      have hsub_eq' :
          x - (1 - (ρ : ℝ) / ‖x‖) • x = ((ρ : ℝ) / ‖x‖) • x := by
        simpa [hp_eq] using hsub_eq
      rw [hsub_eq', inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
      simp
      field_simp [hnormx_ne]
    have hleft :
        ⟪y - p, x - p⟫_ℝ + (ρ : ℝ) * ‖p‖ = ⟪y, x - p⟫_ℝ := by
      rw [inner_sub_left, hinner_pp]
      ring
    have hinner_abs : |⟪y, x - p⟫_ℝ| ≤ ‖y‖ * ‖x - p‖ := by
      simpa [mul_comm] using abs_real_inner_le_norm y (x - p)
    have hinner_le : ⟪y, x - p⟫_ℝ ≤ ‖y‖ * ‖x - p‖ := by
      exact le_trans (le_abs_self _) hinner_abs
    have hreal : ⟪y - p, x - p⟫_ℝ + (ρ : ℝ) * ‖p‖ ≤ (ρ : ℝ) * ‖y‖ := by
      rw [hleft]
      calc
        ⟪y, x - p⟫_ℝ ≤ ‖y‖ * ‖x - p‖ := hinner_le
        _ = (ρ : ℝ) * ‖y‖ := by rw [hsub_norm]; ring
    have hcast :
        (((⟪y - p, x - p⟫_ℝ + (ρ : ℝ) * ‖p‖ : ℝ) : EReal)) ≤
          (((ρ : ℝ) * ‖y‖ : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [p, scaledNormKernelOfPos_apply, EReal.coe_add] using hcast
  · have hp_eq : p = 0 := by
      simp [p, softThresholder_apply, hx]
    have hinner_abs : |⟪y, x⟫_ℝ| ≤ ‖y‖ * ‖x‖ := by
      simpa [mul_comm] using abs_real_inner_le_norm y x
    have hinner_le : ⟪y, x⟫_ℝ ≤ ‖y‖ * ‖x‖ := by
      exact le_trans (le_abs_self _) hinner_abs
    have hnormx_le : ‖x‖ ≤ (ρ : ℝ) := le_of_not_gt hx
    have hreal' : ⟪y, x⟫_ℝ ≤ (ρ : ℝ) * ‖y‖ := by
      calc
        ⟪y, x⟫_ℝ ≤ ‖y‖ * ‖x‖ := hinner_le
        _ ≤ (ρ : ℝ) * ‖y‖ := by nlinarith [norm_nonneg y, hnormx_le]
    have hreal : ⟪y - p, x - p⟫_ℝ + (ρ : ℝ) * ‖p‖ ≤ (ρ : ℝ) * ‖y‖ := by
      simpa [hp_eq] using hreal'
    have hcast :
        (((⟪y - p, x - p⟫_ℝ + (ρ : ℝ) * ‖p‖ : ℝ) : EReal)) ≤
          (((ρ : ℝ) * ‖y‖ : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [p, hp_eq, scaledNormKernelOfPos_apply, EReal.coe_add] using hcast

/-- Helper for Example 14 5: the scaled norm has a unique proximal point at each base point,
namely the soft thresholder. -/
private theorem hasUniqueProxPoint_scaledNormKernelOfPos
    (ρ : Set.Ioi (0 : ℝ)) :
    HasUniqueProxPoint (scaledNormKernelOfPos (H := H) ρ) := by
  intro x
  let p : H := softThresholder (ρ : ℝ) x
  refine ⟨p, softThresholder_isProxPoint_scaledNormKernelOfPos (H := H) ρ x, ?_⟩
  intro q hq
  have hp_var :
      ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (scaledNormKernelOfPos (H := H) ρ p : EReal) ≤
        (scaledNormKernelOfPos (H := H) ρ y : EReal) :=
    (isProxPoint_iff_forall_inner_add_le
      (scaledNormKernelOfPos (H := H) ρ)
      (scaledNormKernelOfPos_mem_gammaZero (H := H) ρ).2 x p).1
      (softThresholder_isProxPoint_scaledNormKernelOfPos (H := H) ρ x)
  have hq_var :
      ∀ y, (⟪y - q, x - q⟫_ℝ : EReal) + (scaledNormKernelOfPos (H := H) ρ q : EReal) ≤
        (scaledNormKernelOfPos (H := H) ρ y : EReal) :=
    (isProxPoint_iff_forall_inner_add_le
      (scaledNormKernelOfPos (H := H) ρ)
      (scaledNormKernelOfPos_mem_gammaZero (H := H) ρ).2 x q).1 hq
  have hpq :
      (⟪q - p, x - p⟫_ℝ : EReal) + (scaledNormKernelOfPos (H := H) ρ p : EReal) ≤
        (scaledNormKernelOfPos (H := H) ρ q : EReal) := hp_var q
  have hqp :
      (⟪p - q, x - q⟫_ℝ : EReal) + (scaledNormKernelOfPos (H := H) ρ q : EReal) ≤
        (scaledNormKernelOfPos (H := H) ρ p : EReal) := hq_var p
  have hpq_real : ⟪q - p, x - p⟫_ℝ + (ρ : ℝ) * ‖p‖ ≤ (ρ : ℝ) * ‖q‖ := by
    have hcast :
        (((⟪q - p, x - p⟫_ℝ + (ρ : ℝ) * ‖p‖ : ℝ) : EReal)) ≤
          (((ρ : ℝ) * ‖q‖ : ℝ) : EReal) := by
      simpa [scaledNormKernelOfPos_apply, EReal.coe_add] using hpq
    exact_mod_cast hcast
  have hqp_real : ⟪p - q, x - q⟫_ℝ + (ρ : ℝ) * ‖q‖ ≤ (ρ : ℝ) * ‖p‖ := by
    have hcast :
        (((⟪p - q, x - q⟫_ℝ + (ρ : ℝ) * ‖q‖ : ℝ) : EReal)) ≤
          (((ρ : ℝ) * ‖p‖ : ℝ) : EReal) := by
      simpa [scaledNormKernelOfPos_apply, EReal.coe_add] using hqp
    exact_mod_cast hcast
  have hsum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, x - q⟫_ℝ ≤ 0 := by
    nlinarith [hpq_real, hqp_real]
  have hrewrite_real :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, x - q⟫_ℝ = ‖q - p‖ ^ (2 : ℕ) := by
    have hpq_neg : p - q = -(q - p) := by
      abel_nf
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, x - q⟫_ℝ
          = ⟪q - p, x - p⟫_ℝ - ⟪q - p, x - q⟫_ℝ := by
              rw [hpq_neg, inner_neg_left]
              ring
      _ = -⟪q - p, p⟫_ℝ + ⟪q - p, q⟫_ℝ := by
            rw [inner_sub_right, inner_sub_right]
            ring
      _ = ⟪q - p, q - p⟫_ℝ := by
            rw [inner_sub_right]
            ring
      _ = ‖q - p‖ ^ (2 : ℕ) := by rw [real_inner_self_eq_norm_sq]
  have hnorm_sq : ‖q - p‖ ^ (2 : ℕ) ≤ 0 := by
    simpa [hrewrite_real] using hsum
  have hnorm_sq_real : ‖q - p‖ ^ (2 : ℕ) ≤ 0 := by
    exact hnorm_sq
  have hsq_zero : ‖q - p‖ ^ (2 : ℕ) = 0 := by
    exact le_antisymm hnorm_sq_real (sq_nonneg ‖q - p‖)
  have hnorm_zero : ‖q - p‖ = 0 := sq_eq_zero_iff.mp hsq_zero
  simpa [p] using sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

end ProximityHelpers

section ProximityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: verify directly that the soft-thresholded point satisfies the proximal
-- variational inequality for `x ↦ ρ ‖x‖`, then use uniqueness of proximal points.
/-- Example 14 5: for the scaled-norm kernel `f = ρ ‖·‖` with `ρ ∈ ℝ_{++}`, the proximal
operator `Prox_f` is the soft thresholder with threshold `ρ`. -/
theorem proximityOperator_scaledNorm_eq_softThresholder
    (ρ : Set.Ioi (0 : ℝ)) :
    Prox[scaledNormKernelOfPos ρ, scaledNormKernelOfPos_mem_gammaZero ρ] =
      (softThresholder (ρ : ℝ) : H → H) := by
  let _ : CompleteSpace H := inferInstance
  ext x
  symm
  exact eq_proximityOperator_of_isProxPoint
    (scaledNormKernelOfPos (H := H) ρ)
    (hasUniqueProxPoint_scaledNormKernelOfPos (H := H) ρ)
    (softThresholder_isProxPoint_scaledNormKernelOfPos (H := H) ρ x)

/-- Evaluating the proximal operator of the scaled-norm kernel yields the standard soft-threshold
formula. -/
theorem proximityOperator_scaledNorm_apply
    (ρ : Set.Ioi (0 : ℝ)) (x : H) :
    Prox[scaledNormKernelOfPos ρ, scaledNormKernelOfPos_mem_gammaZero ρ] x =
      if (ρ : ℝ) < ‖x‖ then (1 - (ρ : ℝ) / ‖x‖) • x else 0 := by
  simpa [softThresholder_apply] using
    congrFun (proximityOperator_scaledNorm_eq_softThresholder (H := H) ρ) x

end ProximityOperator

section MoreauEnvelope

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: evaluate the unit Moreau envelope at the proximal point given by the soft
-- thresholder, then simplify the two radial cases.
/-- The unit Moreau envelope of the scaled-norm kernel is the radial Huber profile
`u ↦ huberFunction ρ ‖u‖`, viewed in `EReal`. -/
theorem moreauEnvelope_scaledNorm_eq_huberFunction_comp_norm
    (ρ : Set.Ioi (0 : ℝ)) :
    {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos (H := H) ρ) =
      (huberFunction ρ ∘ (norm : H → ℝ)).toEReal.asEReal := by
  funext u
  let p : H := softThresholder (ρ : ℝ) u
  have hp_value :
      {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos (H := H) ρ) u =
        (scaledNormKernelOfPos (H := H) ρ p : EReal) +
          ((((1 / 2 : ℝ) * ‖u - p‖ ^ 2 : ℝ) : EReal)) := by
    exact
      (isProxPoint_iff_moreauEnvelope_eq (scaledNormKernelOfPos (H := H) ρ) u p).1
        (softThresholder_isProxPoint_scaledNormKernelOfPos (H := H) ρ u)
  by_cases hu : (ρ : ℝ) < ‖u‖
  · have hnormu_pos : 0 < ‖u‖ := lt_trans ρ.2 hu
    have hnormu_ne : ‖u‖ ≠ 0 := hnormu_pos.ne'
    have hp_eq : p = (1 - (ρ : ℝ) / ‖u‖) • u := by
      simp [p, softThresholder_apply, hu]
    have hp_norm : ‖p‖ = ‖u‖ - (ρ : ℝ) := by
      have hcoeff_nonneg : 0 ≤ 1 - (ρ : ℝ) / ‖u‖ := by
        rw [sub_nonneg]
        rw [div_le_iff₀ hnormu_pos]
        simpa using (hu.le : (ρ : ℝ) ≤ ‖u‖)
      rw [hp_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
      field_simp [hnormu_ne]
    have hsub_norm : ‖u - p‖ = (ρ : ℝ) := by
      rw [hp_eq]
      calc
        ‖u - (1 - (ρ : ℝ) / ‖u‖) • u‖
            = ‖((ρ : ℝ) / ‖u‖) • u‖ := by
                congr 1
                calc
                  u - (1 - (ρ : ℝ) / ‖u‖) • u
                      = (1 : ℝ) • u - (1 - (ρ : ℝ) / ‖u‖) • u := by simp
                  _ = ((ρ : ℝ) / ‖u‖) • u := by
                        simpa using
                          (sub_smul (1 : ℝ) (1 - (ρ : ℝ) / ‖u‖) u).symm
        _ = (ρ : ℝ) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ρ.2 hnormu_pos)]
              field_simp [hnormu_ne]
    have hhuber : huberFunction ρ ‖u‖ = (ρ : ℝ) * ‖u‖ - (ρ : ℝ) ^ 2 / 2 := by
      have hu_abs : (ρ : ℝ) < |‖u‖| := by
        simpa [abs_of_nonneg (norm_nonneg u)] using hu
      simpa [abs_of_nonneg (norm_nonneg u)] using huberFunction_eq_of_lt ρ hu_abs
    calc
      {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos (H := H) ρ) u
          = ((((ρ : ℝ) * ‖p‖ + (1 / 2 : ℝ) * ‖u - p‖ ^ 2 : ℝ) : EReal)) := by
              simpa [scaledNormKernelOfPos_apply, EReal.coe_add] using hp_value
      _ = (((((ρ : ℝ) * ‖u‖ - (ρ : ℝ) ^ 2 / 2 : ℝ)) : EReal)) := by
            rw [hp_norm, hsub_norm]
            congr 1
            ring
      _ = (((huberFunction ρ ‖u‖ : ℝ) : EReal)) := by rw [hhuber]
      _ = (huberFunction ρ ∘ (norm : H → ℝ)).toEReal.asEReal u := by
            simp [Function.asEReal_apply, Function.toEReal_apply, Function.comp_apply]
  · have hp_eq : p = 0 := by
      simp [p, softThresholder_apply, hu]
    have hhuber : huberFunction ρ ‖u‖ = ‖u‖ ^ 2 / 2 := by
      have hu_le : |‖u‖| ≤ (ρ : ℝ) := by
        simpa [abs_of_nonneg (norm_nonneg u)] using le_of_not_gt hu
      simpa [abs_of_nonneg (norm_nonneg u)] using huberFunction_eq_of_le ρ hu_le
    calc
      {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos (H := H) ρ) u
          = ((((ρ : ℝ) * ‖p‖ + (1 / 2 : ℝ) * ‖u - p‖ ^ 2 : ℝ) : EReal)) := by
              simpa [scaledNormKernelOfPos_apply, EReal.coe_add] using hp_value
      _ = ((((1 / 2 : ℝ) * ‖u‖ ^ 2 : ℝ) : EReal)) := by
            simp [hp_eq]
      _ = (((‖u‖ ^ 2 / 2 : ℝ) : EReal)) := by
            congr 1
            ring
      _ = (((huberFunction ρ ‖u‖ : ℝ) : EReal)) := by rw [hhuber]
      _ = (huberFunction ρ ∘ (norm : H → ℝ)).toEReal.asEReal u := by
            simp [Function.asEReal_apply, Function.toEReal_apply, Function.comp_apply]

end MoreauEnvelope

-- Proof sketch: specialize the Hilbert-space radial formula to `H = ℝ`, where the radial Huber
-- profile becomes the scalar owner `huberFunction ρ`.
/-- In one dimension, the unit Moreau envelope of the scaled-norm kernel is the canonical
extended-real Huber function with threshold `ρ`. -/
theorem moreauEnvelope_scaledNorm_real_eq_huberFunction
    (ρ : Set.Ioi (0 : ℝ)) :
    {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos (H := ℝ) ρ) =
      (huberFunction ρ).toEReal.asEReal := by
  calc
    {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos (H := ℝ) ρ) =
        (huberFunction ρ ∘ (norm : ℝ → ℝ)).toEReal.asEReal :=
          moreauEnvelope_scaledNorm_eq_huberFunction_comp_norm (H := ℝ) ρ
    _ = (huberFunction ρ).toEReal.asEReal := by
      funext x
      by_cases hx : (ρ : ℝ) < |x|
      · simp [Function.comp_def, huberFunction, Real.norm_eq_abs, hx]
      · simp [Function.comp_def, huberFunction, Real.norm_eq_abs, hx]

end

end ERealFunction
