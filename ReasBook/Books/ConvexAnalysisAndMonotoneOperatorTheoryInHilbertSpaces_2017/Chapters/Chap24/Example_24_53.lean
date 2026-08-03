import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap17.Corollary_17_12
import BauschkeLean.Chap24.Example_24_41
import BauschkeLean.Chap24.Proposition_24_54
import BauschkeLean.Chap24.Theorem_24_52

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

private theorem real_inner_eq_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  calc
    ⟪x, y⟫_ℝ = (starRingEnd ℝ) x * y := RCLike.inner_apply' x y
    _ = x * y := by simp

-- Semantic recall/local precedent: `lean_leansearch` only surfaced unrelated `Gamma` and generic
-- support-function hits, so this item uses the existing Chapter 24 scalar `Γ₀(ℝ)`, `σ[Ω]`,
-- `Function.IsProximalThresholderOn`, and split-log-barrier surfaces from Theorem 24.52 and
-- Example 24.41.

/-- The `]-∞,+∞]`-valued logarithmic barrier `φ` from `(24.97)`, realized as the symmetric
specialization of `splitLogBarrier`. -/
abbrev logAbsBarrier (ω : PosReal) : ℝ → Set.Ioi (⊥ : EReal) :=
  splitLogBarrier
    ⟨-(ω : ℝ), by
      simpa using neg_neg_iff_pos.mpr ω.2
    ⟩
    ω

/-- On `|ξ| < ω`, `logAbsBarrier ω` agrees with the finite branch from `(24.97)`. -/
@[simp] theorem logAbsBarrier_apply_of_abs_lt (ω : PosReal) {ξ : ℝ}
    (hξ : |ξ| < (ω : ℝ)) :
    (logAbsBarrier ω ξ : EReal) =
      (Real.log (ω : ℝ) - Real.log ((ω : ℝ) - |ξ|) : ℝ) := by
  have hmem : ξ ∈ Set.Ioo (-(ω : ℝ)) (ω : ℝ) := by
    rcases abs_lt.mp hξ with ⟨hleft, hright⟩
    exact ⟨by linarith, hright⟩
  by_cases hξ_nonpos : ξ ≤ 0
  · rw [splitLogBarrier_apply_of_mem_Ioo_nonpos hmem hξ_nonpos]
    simp [sub_eq_add_neg, abs_of_nonpos hξ_nonpos, add_comm]
  · have hξ_pos : 0 < ξ := lt_of_not_ge hξ_nonpos
    rw [splitLogBarrier_apply_of_mem_Ioo_pos hmem hξ_pos]
    simp [sub_eq_add_neg, abs_of_pos hξ_pos, add_comm]

/-- On `ω ≤ |ξ|`, `logAbsBarrier ω` takes the value `+∞`. -/
@[simp] theorem logAbsBarrier_apply_of_le_abs (ω : PosReal) {ξ : ℝ}
    (hξ : (ω : ℝ) ≤ |ξ|) :
    (logAbsBarrier ω ξ : EReal) = ⊤ := by
  apply splitLogBarrier_apply_of_not_mem_Ioo
  intro hmem
  have habs : |ξ| < (ω : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith [hmem.1, hmem.2]
  exact not_lt_of_ge hξ habs

/-- The `]-∞,+∞]`-valued function `ψ` from `(24.98)`. -/
def logAbsBarrierResidual (ω : PosReal) : ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ : ℝ ↦
    if hξ : |ξ| < (ω : ℝ) then
      ⟨((Real.log (ω : ℝ) - Real.log ((ω : ℝ) - |ξ|) - |ξ| / (ω : ℝ) : ℝ) : EReal),
        EReal.bot_lt_coe _⟩
    else
      ⟨(⊤ : EReal), by simp⟩

/-- On `|ξ| < ω`, `logAbsBarrierResidual ω` agrees with the finite branch from `(24.98)`. -/
@[simp] theorem logAbsBarrierResidual_apply_of_abs_lt (ω : PosReal) {ξ : ℝ}
    (hξ : |ξ| < (ω : ℝ)) :
    (logAbsBarrierResidual ω ξ : EReal) =
      (Real.log (ω : ℝ) - Real.log ((ω : ℝ) - |ξ|) - |ξ| / (ω : ℝ) : ℝ) := by
  simp [logAbsBarrierResidual, hξ]

/-- On `ω ≤ |ξ|`, `logAbsBarrierResidual ω` takes the value `+∞`. -/
@[simp] theorem logAbsBarrierResidual_apply_of_le_abs (ω : PosReal) {ξ : ℝ}
    (hξ : (ω : ℝ) ≤ |ξ|) :
    (logAbsBarrierResidual ω ξ : EReal) = ⊤ := by
  simp [logAbsBarrierResidual, not_lt_of_ge hξ]

private theorem neg_inv_le_inv (ω : PosReal) :
    (-(ω : ℝ)⁻¹ : ℝ) ≤ (ω : ℝ)⁻¹ := by
  have hωinv : 0 < ((ω : ℝ)⁻¹) := inv_pos.mpr ω.2
  linarith

private theorem supportFunction_Icc_neg_one_one_eq_abs :
    σ[Set.Icc (-1 : ℝ) 1] = (fun ξ : ℝ ↦ |ξ|).toEReal.asEReal := by
  funext ξ
  have hIcc : (-1 : ℝ) ≤ 1 := by norm_num
  have hnonempty : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by simp⟩
  have hinner :
      (fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) =
        fun x : ℝ ↦ ((x * ξ : ℝ) : EReal) := by
    funext x
    simp [real_inner_eq_mul]
  by_cases hξ_neg : ξ < 0
  · have hanti :
        AntitoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (-1 : ℝ) 1) := by
      intro x hx y hy hxy
      have hmul : y * ξ ≤ x * ξ := mul_le_mul_of_nonpos_right hxy hξ_neg.le
      simpa using (EReal.coe_le_coe hmul)
    have hsSup :
        sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc (-1 : ℝ) 1) =
          (((-1 : ℝ) * ξ : ℝ) : EReal) :=
      AntitoneOn.sSup_image_Icc hIcc hanti
    rw [supportFunction_eq_sSup_image, hinner, hsSup]
    simp [abs_of_neg hξ_neg]
  · by_cases hξ_zero : ξ = 0
    · rw [hξ_zero]
      simpa using supportFunction_zero_eq_zero_of_nonempty (Set.Icc (-1 : ℝ) 1) hnonempty
    · have hξ_pos : 0 < ξ := lt_of_le_of_ne (le_of_not_gt hξ_neg) (Ne.symm hξ_zero)
      have hmono :
          MonotoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (-1 : ℝ) 1) := by
        intro x hx y hy hxy
        have hmul : x * ξ ≤ y * ξ := mul_le_mul_of_nonneg_right hxy hξ_pos.le
        simpa using (EReal.coe_le_coe hmul)
      have hsSup :
          sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc (-1 : ℝ) 1) =
            (((1 : ℝ) * ξ : ℝ) : EReal) :=
        MonotoneOn.sSup_image_Icc hIcc hmono
      rw [supportFunction_eq_sSup_image, hinner, hsSup]
      simp [abs_of_pos hξ_pos]

private theorem supportFunction_Icc_neg_inv_inv_eq_abs_div (ω : PosReal) :
    σ[Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹] =
      (fun ξ : ℝ ↦ |ξ| / (ω : ℝ)).toEReal.asEReal := by
  have hωinv : 0 < ((ω : ℝ)⁻¹) := inv_pos.mpr ω.2
  have hIcc :
      ((ω : ℝ)⁻¹ • Set.Icc (-1 : ℝ) 1) = Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹ := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (LinearOrderedField.smul_Icc hωinv :
        ((ω : ℝ)⁻¹ • Set.Icc (-1 : ℝ) 1) =
          Set.Icc (((ω : ℝ)⁻¹) * (-1 : ℝ)) (((ω : ℝ)⁻¹) * (1 : ℝ)))
  funext ξ
  calc
    σ[Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹] ξ
        = σ[((ω : ℝ)⁻¹ • Set.Icc (-1 : ℝ) 1)] ξ := by rw [hIcc]
    _ = (σ[Set.Icc (-1 : ℝ) 1] ∘ fun u : ℝ ↦ ((ω : ℝ)⁻¹) • u) ξ := by
          simpa using
            (congrFun
              (supportFunction_comp_smul_eq_supportFunction_smul_set
                (Set.Icc (-1 : ℝ) 1) ((ω : ℝ)⁻¹))
              ξ).symm
    _ = (((ω : ℝ)⁻¹ : EReal) * σ[Set.Icc (-1 : ℝ) 1] ξ) := by
          simpa using
            (congrFun
              (supportFunction_comp_pos_smul_eq_mul_supportFunction
                (Set.Icc (-1 : ℝ) 1) hωinv)
              ξ)
    _ = (((ω : ℝ)⁻¹ * |ξ| : ℝ) : EReal) := by
          have habs : σ[Set.Icc (-1 : ℝ) 1] ξ = ((|ξ| : ℝ) : EReal) := by
            simpa [Function.asEReal_apply] using congrFun supportFunction_Icc_neg_one_one_eq_abs ξ
          rw [habs]
          exact (EReal.coe_mul ((ω : ℝ)⁻¹) |ξ|).symm
    _ = (((|ξ| / (ω : ℝ) : ℝ)) : EReal) := by
          simp [div_eq_mul_inv, mul_comm]

private theorem zero_mem_interior_effectiveDomain_logAbsBarrierResidual (ω : PosReal) :
    0 ∈ interior (effectiveDomain (logAbsBarrierResidual ω)) := by
  rw [mem_interior_iff_mem_nhds]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-(ω : ℝ)) (ω : ℝ) := by
    constructor <;> linarith [ω.2]
  refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hmem) ?_
  intro x hx
  rw [mem_effectiveDomain_iff]
  have habs : |x| < (ω : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  rw [logAbsBarrierResidual_apply_of_abs_lt ω habs]
  exact EReal.coe_lt_top _

/-- Example 24.53 (1): `ψ = logAbsBarrierResidual ω` belongs to `Γ₀(ℝ)`. -/
theorem logAbsBarrierResidual_mem_gammaZero (ω : PosReal) :
    logAbsBarrierResidual ω ∈ Γ₀(ℝ) := sorry

/-- Example 24.53 (2): the finite representative of `ψ = logAbsBarrierResidual ω` has derivative
`0` at the origin. -/
theorem hasDerivAt_logAbsBarrierResidual_zero (ω : PosReal) :
    HasDerivAt (fun ξ ↦ (logAbsBarrierResidual ω ξ : EReal).toReal) 0 0 := sorry

/-- Example 24.53 (3): the barrier `φ = logAbsBarrier ω` splits as
`ψ + σ_[−1 / ω, 1 / ω]`. -/
theorem logAbsBarrier_eq_add_supportFunction_Icc (ω : PosReal) :
    logAbsBarrier ω =
      logAbsBarrierResidual ω +
        properIoi (σ[Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹])
          (isProper_supportFunction_of_nonempty
            (Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹)
            (Set.nonempty_Icc.2 (by
              have hωinv : 0 < ((ω : ℝ)⁻¹) := inv_pos.mpr ω.2
              linarith))) := by
  let σω : ℝ → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹])
      (isProper_supportFunction_of_nonempty
        (Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹)
        (Set.nonempty_Icc.2 (by
          have hωinv : 0 < ((ω : ℝ)⁻¹) := inv_pos.mpr ω.2
          linarith)))
  change logAbsBarrier ω = logAbsBarrierResidual ω + σω
  funext ξ
  apply Subtype.ext
  by_cases hξ : |ξ| < (ω : ℝ)
  · rw [logAbsBarrier_apply_of_abs_lt ω hξ]
    change ((Real.log (ω : ℝ) - Real.log ((ω : ℝ) - |ξ|) : ℝ) : EReal) =
        ((logAbsBarrierResidual ω ξ : EReal) + (σω ξ : EReal))
    rw [logAbsBarrierResidual_apply_of_abs_lt ω hξ]
    have hsupport : (σω ξ : EReal) = ((|ξ| / (ω : ℝ) : ℝ) : EReal) := by
      simpa [σω] using congrFun (supportFunction_Icc_neg_inv_inv_eq_abs_div ω) ξ
    rw [hsupport]
    exact_mod_cast (show
      Real.log (ω : ℝ) - Real.log ((ω : ℝ) - |ξ|) =
        (Real.log (ω : ℝ) - Real.log ((ω : ℝ) - |ξ|) - |ξ| / (ω : ℝ)) +
          |ξ| / (ω : ℝ) by ring)
  · have hξ' : (ω : ℝ) ≤ |ξ| := by
      exact le_of_not_gt hξ
    rw [logAbsBarrier_apply_of_le_abs ω hξ']
    change (⊤ : EReal) = ((logAbsBarrierResidual ω ξ : EReal) + (σω ξ : EReal))
    rw [logAbsBarrierResidual_apply_of_le_abs ω hξ']
    have hsupport : (σω ξ : EReal) = ((|ξ| / (ω : ℝ) : ℝ) : EReal) := by
      simpa [σω] using congrFun (supportFunction_Icc_neg_inv_inv_eq_abs_div ω) ξ
    simp [hsupport]

/-- Helper for Example 24.53: the barrier `logAbsBarrier ω` belongs to `Γ₀(ℝ)`. -/
theorem logAbsBarrier_mem_gammaZero (ω : PosReal) :
    logAbsBarrier ω ∈ Γ₀(ℝ) := by
  have hmem :
      logAbsBarrierResidual ω +
          properIoi (σ[Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹])
            (isProper_supportFunction_of_nonempty
              (Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹)
              (Set.nonempty_Icc.2 (neg_inv_le_inv ω))) ∈
        Γ₀(ℝ) :=
    add_supportFunction_Icc_mem_gammaZero_of_zero_mem_effectiveDomain
      (logAbsBarrierResidual_mem_gammaZero ω)
      (neg_inv_le_inv ω)
      (interior_subset (zero_mem_interior_effectiveDomain_logAbsBarrierResidual ω))
  simpa [logAbsBarrier_eq_add_supportFunction_Icc ω] using hmem

/-- Example 24.53 (4): `Prox_φ` is a proximal thresholder on `[-1 / ω, 1 / ω]`. -/
theorem prox_logAbsBarrier_isProximalThresholderOn_Icc
    (ω : PosReal) :
    (Prox[logAbsBarrier ω, logAbsBarrier_mem_gammaZero ω]).IsProximalThresholderOn
      (Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹) := by
  have hIcc_nonempty :
      (Set.Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹).Nonempty := by
    exact Set.nonempty_Icc.2 (neg_inv_le_inv ω)
  have hiff :=
    prox_isProximalThresholderOn_iff_exists_eq_add_supportFunction_and_deriv_zero
      hIcc_nonempty
      isClosed_Icc
      (convex_Icc (-(ω : ℝ)⁻¹) (ω : ℝ)⁻¹)
      (logAbsBarrier_mem_gammaZero ω)
  refine hiff.2 ?_
  refine ⟨logAbsBarrierResidual ω, logAbsBarrierResidual_mem_gammaZero ω, ?_, ?_, ?_⟩
  · exact zero_mem_interior_effectiveDomain_logAbsBarrierResidual ω
  · simpa using hasDerivAt_logAbsBarrierResidual_zero ω
  · simpa using logAbsBarrier_eq_add_supportFunction_Icc ω

/-- Example 24.53 (5): the proximity operator of `φ = logAbsBarrier ω` is the displayed
piecewise scalar thresholder from `(24.99)`. -/
theorem prox_logAbsBarrier_eq_piecewise (ω : PosReal) :
    Prox[logAbsBarrier ω, logAbsBarrier_mem_gammaZero ω] =
      fun ξ : ℝ ↦
        if (ω : ℝ)⁻¹ < |ξ| then
          Real.sign ξ *
            ((|ξ| + (ω : ℝ) -
                Real.sqrt ((|ξ| - (ω : ℝ)) ^ (2 : ℕ) + 4)) / 2)
        else
          0 := sorry

end

end ERealFunction
