import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap24.Example_24_34

open scoped InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

section RealLine

/-- Helper for Example 24.35: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  calc
    ⟪x, y⟫_ℝ = (starRingEnd ℝ) x * y := RCLike.inner_apply' x y
    _ = x * y := by simp

/-- The scalar positive-part function `ξ ↦ ξ⁺` as an `]-∞,+∞]`-valued function. -/
def positivePartFunction : ℝ → Set.Ioi (⊥ : EReal) :=
  (fun ξ : ℝ ↦ ξ⁺).toEReal

/-- The scalar positive-part function is canonically the support function of the interval
`[0,1]`. -/
theorem positivePartFunction_eq_supportFunction_Icc_zero_one :
    positivePartFunction =
      properIoi (σ[Set.Icc (0 : ℝ) 1])
        (isProper_supportFunction_of_nonempty
          (Set.Icc (0 : ℝ) 1) (Set.nonempty_Icc.2 zero_le_one)) := by
  funext ξ
  apply Subtype.ext
  change ((ξ⁺ : ℝ) : EReal) = σ[Set.Icc (0 : ℝ) 1] ξ
  have hinner :
      (fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) =
        fun x : ℝ ↦ ((x * ξ : ℝ) : EReal) := by
    funext x
    simp [real_inner_eq_mul]
  by_cases hξ_nonpos : ξ ≤ 0
  · have hanti :
        AntitoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      have hmul : y * ξ ≤ x * ξ := mul_le_mul_of_nonpos_right hxy hξ_nonpos
      simpa using (EReal.coe_le_coe hmul)
    have hsSup :
        sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc (0 : ℝ) 1) = (0 : EReal) := by
      simpa using AntitoneOn.sSup_image_Icc zero_le_one hanti
    rw [supportFunction_eq_sSup_image, hinner, hsSup]
    simp [posPart_eq_zero.2 hξ_nonpos]
  · have hξ_pos : 0 < ξ := lt_of_not_ge hξ_nonpos
    have hmono :
        MonotoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      have hmul : x * ξ ≤ y * ξ := mul_le_mul_of_nonneg_right hxy hξ_pos.le
      simpa using (EReal.coe_le_coe hmul)
    have hsSup :
        sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc (0 : ℝ) 1) =
          (((1 : ℝ) * ξ : ℝ) : EReal) := by
      simpa using MonotoneOn.sSup_image_Icc zero_le_one hmono
    rw [supportFunction_eq_sSup_image, hinner, hsSup]
    simp [posPart_eq_self.2 hξ_pos.le]

/-- The positive-part function is the distance to the closed half-line `]-∞,0]`. -/
theorem positivePartFunction_eq_distance_Iic_zero :
    positivePartFunction =
      (fun ξ : ℝ ↦ Metric.infDist ξ (Set.Iic (0 : ℝ))).toEReal := by
  funext ξ
  apply Subtype.ext
  change ((ξ⁺ : ℝ) : EReal) = ((Metric.infDist ξ (Set.Iic (0 : ℝ)) : ℝ) : EReal)
  by_cases hξ_nonpos : ξ ≤ 0
  · have hdist : Metric.infDist ξ (Set.Iic (0 : ℝ)) = 0 := Metric.infDist_zero_of_mem hξ_nonpos
    rw [posPart_eq_zero.2 hξ_nonpos, hdist]
  · have hξ_pos : 0 < ξ := lt_of_not_ge hξ_nonpos
    have hdist : Metric.infDist ξ (Set.Iic (0 : ℝ)) = ξ := by
      refine le_antisymm ?_ ?_
      · have hle : Metric.infDist ξ (Set.Iic (0 : ℝ)) ≤ dist ξ 0 :=
            Metric.infDist_le_dist_of_mem (show (0 : ℝ) ∈ Set.Iic (0 : ℝ) by simp)
        simpa [Real.dist_eq, abs_of_nonneg hξ_pos.le] using hle
      · rw [Metric.le_infDist ⟨0, by simp⟩]
        intro y hy
        have hy_le : y ≤ 0 := by simpa using hy
        have hsub_nonneg : 0 ≤ ξ - y := sub_nonneg.mpr (le_trans hy_le hξ_pos.le)
        have hξ_le : ξ ≤ ξ - y := by nlinarith
        simpa [Real.dist_eq, abs_of_nonneg hsub_nonneg] using hξ_le
    simp [hdist, posPart_eq_self.2 hξ_pos.le]

/-- The scalar positive-part function belongs to `Γ₀(ℝ)`. -/
theorem positivePartFunction_mem_gammaZero :
    positivePartFunction ∈ Γ₀(ℝ) := by
  rw [positivePartFunction_eq_supportFunction_Icc_zero_one]
  simpa using
    example_11_2_2_supportFunction_mem_gammaZero
      (Set.Icc (0 : ℝ) 1) (Set.nonempty_Icc.2 zero_le_one)

/-- Scaling the positive-part function by `γ ∈ ℝ_{++}` gives the support
function of `[0,γ]`. -/
theorem posReal_smul_positivePartFunction_eq_supportFunction_Icc_zero_gamma (γ : PosReal) :
    γ • positivePartFunction =
      properIoi (σ[Set.Icc (0 : ℝ) (γ : ℝ)])
        (isProper_supportFunction_of_nonempty
          (Set.Icc (0 : ℝ) (γ : ℝ))
          (Set.nonempty_Icc.2 (le_of_lt γ.2))) := by
  funext ξ
  apply Subtype.ext
  have hIcc :
      ((γ : ℝ) • Set.Icc (0 : ℝ) 1) = Set.Icc (0 : ℝ) (γ : ℝ) := by
    simpa [zero_mul, one_mul] using
      (LinearOrderedField.smul_Icc γ.2 :
        ((γ : ℝ) • Set.Icc (0 : ℝ) 1) = Set.Icc ((γ : ℝ) * 0) ((γ : ℝ) * 1))
  change (((γ : ℝ) : EReal) * ((positivePartFunction ξ : Set.Ioi (⊥ : EReal)) : EReal)) =
    σ[Set.Icc (0 : ℝ) (γ : ℝ)] ξ
  have hpp :
      ((positivePartFunction ξ : Set.Ioi (⊥ : EReal)) : EReal) = σ[Set.Icc (0 : ℝ) 1] ξ := by
    simpa [properIoi_apply] using
      congrArg
        (fun f : ℝ → Set.Ioi (⊥ : EReal) ↦ ((f ξ : Set.Ioi (⊥ : EReal)) : EReal))
        positivePartFunction_eq_supportFunction_Icc_zero_one
  rw [hpp]
  calc
    ((γ : ℝ) : EReal) * σ[Set.Icc (0 : ℝ) 1] ξ
        = (σ[Set.Icc (0 : ℝ) 1] ∘ fun u : ℝ ↦ (γ : ℝ) • u) ξ := by
            simpa using
              (congrFun
                (supportFunction_comp_pos_smul_eq_mul_supportFunction
                  (Set.Icc (0 : ℝ) 1) γ.2) ξ).symm
    _ = σ[((γ : ℝ) • Set.Icc (0 : ℝ) 1)] ξ := by
          simpa using
            congrFun
              (supportFunction_comp_smul_eq_supportFunction_smul_set
                (Set.Icc (0 : ℝ) 1) (γ : ℝ)) ξ
    _ = σ[Set.Icc (0 : ℝ) (γ : ℝ)] ξ := by simp [hIcc]

/-- For `γ ∈ ℝ_{++}`, Example 24.35 is the interval-soft-threshold prox of the support function
`σ_[0,γ]` from Example 24.34. -/
theorem prox_positivePartFunction_eq_intervalSoftThresholder (γ : PosReal) :
    Prox[γ, positivePartFunction, positivePartFunction_mem_gammaZero] =
      intervalSoftThresholder 0 (γ : ℝ) := by
  funext ξ
  let σγ : ℝ → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[Set.Icc (0 : ℝ) (γ : ℝ)])
      (isProper_supportFunction_of_nonempty
        (Set.Icc (0 : ℝ) (γ : ℝ))
        (Set.nonempty_Icc.2 (le_of_lt γ.2)))
  have hscaled : γ • positivePartFunction = σγ :=
    posReal_smul_positivePartFunction_eq_supportFunction_Icc_zero_gamma γ
  have hproxσ :
      IsProxPoint σγ ξ (intervalSoftThresholder 0 (γ : ℝ) ξ) := by
    have hEq :
        Prox[σγ,
          example_11_2_2_supportFunction_mem_gammaZero
            (Set.Icc (0 : ℝ) (γ : ℝ))
            (Set.nonempty_Icc.2 (le_of_lt γ.2))] =
          intervalSoftThresholder 0 (γ : ℝ) := by
      simpa [σγ] using
        example_24_34_2_proximityOperator_supportFunction_Icc_eq_intervalSoftThresholder
          (le_of_lt γ.2)
    simpa [hEq] using
      proximityOperator_isProxPoint σγ
        (hasUniqueProxPoint_of_mem_gammaZero σγ
          (example_11_2_2_supportFunction_mem_gammaZero
            (Set.Icc (0 : ℝ) (γ : ℝ))
            (Set.nonempty_Icc.2 (le_of_lt γ.2))))
        ξ
  have hproxScaled :
      IsProxPoint (γ • positivePartFunction) ξ (intervalSoftThresholder 0 (γ : ℝ) ξ) := by
    simpa [hscaled] using hproxσ
  simpa [scaledProximityOperator] using
    (eq_proximityOperator_of_isProxPoint
      (γ • positivePartFunction)
      (hasUniqueProxPoint_of_mem_gammaZero
        (γ • positivePartFunction)
        (smul_mem_gammaZero positivePartFunction positivePartFunction_mem_gammaZero γ))
      hproxScaled).symm

/-- Example 24.35: for `φ(η) = η⁺` and `γ ∈ ℝ_{++}`, the proximity operator of `γ φ`
is the three-branch formula `(24.67)`. -/
theorem prox_positivePartFunction_eq_piecewise (γ : PosReal) :
    Prox[γ, positivePartFunction, positivePartFunction_mem_gammaZero] =
      fun ξ : ℝ ↦
        if ξ < 0 then ξ
        else if 0 ≤ ξ ∧ ξ ≤ (γ : ℝ) then 0
        else ξ - (γ : ℝ) := by
  rw [prox_positivePartFunction_eq_intervalSoftThresholder]
  funext ξ
  simp [intervalSoftThresholder, Set.mem_Icc]

end RealLine

end

end ERealFunction
