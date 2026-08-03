import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Example_16_32
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap24.Proposition_24_27

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section BasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P_C" =>
  P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]

-- Source/core/bridge triage:
-- - `source-facing`: Example 24.28 is the `φ = γ ‖·‖` specialization of Proposition 24.27.
-- - `core/canonical`: the reusable owners are `scaledNormKernelOfPos`, `∂`, `Γ₀`, and
--   `Prox`.
-- - `bridge/view`: on `ℝ`, Example 16.32 identifies the norm subdifferential explicitly, so the
--   scalar threshold in Proposition 24.27 becomes exactly `γ`.

local notation "hγC" =>
  Set.distanceToSet_toEReal_mem_gammaZero_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex

/-- Helper for Example 24.28: on `ℝ`, the scaled norm kernel is the positive scalar multiple of
the norm. -/
private theorem scaledNormKernelOfPos_real_eq_posReal_smul_norm (γ : PosReal) :
    scaledNormKernelOfPos (H := ℝ) γ = γ • ((norm : ℝ → ℝ).toEReal) := by
  -- Rewrite the pointwise formula `x ↦ γ ‖x‖` through the scalar action on `toEReal`.
  funext ξ
  apply Subtype.ext
  simpa [posReal_smul_apply] using scaledNormKernelOfPos_apply (H := ℝ) γ ξ

/-- Helper for Example 24.28: the closed unit ball in `ℝ` is the interval `[-1,1]`. -/
private theorem closedBall_zero_one_eq_Icc :
    Metric.closedBall (0 : ℝ) 1 = Set.Icc (-1 : ℝ) 1 := by
  -- On the line, the closed ball condition is the absolute-value inequality `|x| ≤ 1`.
  ext x
  simp [Metric.mem_closedBall, abs_le]

/-- Helper for Example 24.28: the scalar subdifferential of `t ↦ γ |t|` is the scaled
piecewise interval from Example 16.32 specialized to `ℝ`. -/
private theorem subdifferential_scaledNormKernelOfPos_real_eq_piecewise
    (γ : PosReal) (ξ : ℝ) :
    (∂ (scaledNormKernelOfPos (H := ℝ) γ)) ξ =
      if ξ < 0 then {(-(γ : ℝ))}
      else if ξ = 0 then Set.Icc (-(γ : ℝ)) (γ : ℝ)
      else {(γ : ℝ)} := by
  -- Scale the norm subdifferential branchwise and normalize the real one-dimensional formulas.
  rw [scaledNormKernelOfPos_real_eq_posReal_smul_norm (γ := γ)]
  rw [subdifferential_posReal_smul_eq_smul (f := ((norm : ℝ → ℝ).toEReal)) (γ := γ)]
  rw [Pi.smul_apply]
  rw [subdifferential_norm_eq_singleton_or_closedBall (H := ℝ) ξ]
  by_cases hξ_zero : ξ = 0
  · rw [if_pos hξ_zero]
    have hIcc :
        ((γ : ℝ) • (Set.Icc (-1 : ℝ) 1 : Set ℝ)) = Set.Icc (-(γ : ℝ)) (γ : ℝ) := by
      simpa [neg_mul, one_mul] using
        (LinearOrderedField.smul_Icc γ.2 :
          ((γ : ℝ) • Set.Icc (-1 : ℝ) 1) = Set.Icc ((γ : ℝ) * (-1)) ((γ : ℝ) * 1))
    simp [hξ_zero, closedBall_zero_one_eq_Icc, hIcc]
  · rw [if_neg hξ_zero]
    by_cases hξ_neg : ξ < 0
    · have hunit : ‖ξ‖⁻¹ • ξ = (-1 : ℝ) := by
        have hnorm : ‖ξ‖ = -ξ := by
          simp [Real.norm_eq_abs, abs_of_neg hξ_neg]
        rw [smul_eq_mul, hnorm, inv_neg, neg_mul, inv_mul_cancel₀ hξ_zero]
      have hunit' : |ξ|⁻¹ * ξ = (-1 : ℝ) := by
        simpa [Real.norm_eq_abs, smul_eq_mul] using hunit
      simp [hξ_neg, hunit']
    · have hξ_pos : 0 < ξ := by
        exact lt_of_le_of_ne (le_of_not_gt hξ_neg) (Ne.symm hξ_zero)
      have hunit : ‖ξ‖⁻¹ • ξ = (1 : ℝ) := by
        have hnorm : ‖ξ‖ = ξ := by
          simp [Real.norm_eq_abs, abs_of_pos hξ_pos]
        rw [smul_eq_mul, hnorm, inv_mul_cancel₀ hξ_zero]
      have hunit' : |ξ|⁻¹ * ξ = (1 : ℝ) := by
        simpa [Real.norm_eq_abs, smul_eq_mul] using hunit
      simp [hξ_zero, hξ_neg, hunit']

/-- Helper for Example 24.28: the branch threshold from Proposition 24.27 becomes exactly `γ`
for the scalar profile `t ↦ γ |t|`. -/
private theorem sSup_subdifferential_scaledNormKernelOfPos_zero_eq_gamma (γ : PosReal) :
    sSup ((∂ (scaledNormKernelOfPos (H := ℝ) γ)) 0) = (γ : ℝ) := by
  have hIcc : (-(γ : ℝ) : ℝ) ≤ (γ : ℝ) := by
    linarith [γ.2]
  -- At the origin the subdifferential is the interval `[-γ, γ]`, whose supremum is `γ`.
  rw [subdifferential_scaledNormKernelOfPos_real_eq_piecewise (γ := γ) (ξ := 0)]
  simp [hIcc, csSup_Icc]

/-- Helper for Example 24.28: above the threshold `γ`, the scalar proximal point of `t ↦ γ |t|`
is `d - γ`. -/
private theorem prox_scaledNormKernelOfPos_real_eq_sub_of_gt
    (γ : PosReal) {d : ℝ} (hd : d > (γ : ℝ)) :
    Prox[scaledNormKernelOfPos (H := ℝ) γ,
      scaledNormKernelOfPos_mem_gammaZero (H := ℝ) γ] d =
        d - (γ : ℝ) := by
  -- Verify the proximal optimality condition at the candidate point `d - γ`.
  symm
  apply (eq_proximityOperator_iff_sub_mem_subdifferential
    (f := scaledNormKernelOfPos (H := ℝ) γ)
    (hf := scaledNormKernelOfPos_mem_gammaZero (H := ℝ) γ)
    (x := d) (p := d - (γ : ℝ))).2
  have hnot_neg : ¬ d - (γ : ℝ) < 0 := by
    linarith
  have hnot_zero : d - (γ : ℝ) ≠ 0 := by
    linarith
  have hresidual : d - (d - (γ : ℝ)) = (γ : ℝ) := by
    ring
  rw [subdifferential_scaledNormKernelOfPos_real_eq_piecewise
    (γ := γ) (ξ := d - (γ : ℝ))]
  simp [hnot_neg, hnot_zero, hresidual]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 24.28: the radial distance profile attached to `t ↦ γ |t|` is the scaled
distance-to-set function `γ d_C`. -/
private theorem distanceProfile_scaledNormKernelOfPos_eq_scaled_distanceToSet
    (γ : PosReal) :
    distanceProfile C (scaledNormKernelOfPos (H := ℝ) γ) =
      γ • (fun y : H ↦ Metric.infDist y C).toEReal := by
  -- Evaluate the profile pointwise and simplify `‖d_C(y)‖` using nonnegativity of the distance.
  funext y
  apply Subtype.ext
  simpa [distanceProfile, posReal_smul_apply, Real.norm_eq_abs,
    abs_of_nonneg (Metric.infDist_nonneg (x := y) (s := C))] using
    scaledNormKernelOfPos_apply (H := ℝ) γ (Metric.infDist y C)

/-- Example 24.28: if `C` is a nonempty closed convex subset of `H`, if `γ ∈ ℝ_{++}`, and if
`x ∈ H`, then the proximity operator of `γ d_C` is the piecewise projection formula `(24.54)`. -/
theorem prox_distanceToSet_eq_piecewise (γ : PosReal) (x : H) :
    Prox[γ, (fun y : H ↦ Metric.infDist y C).toEReal, hγC] x =
      if h : Metric.infDist x C > (γ : ℝ) then
        x + (((γ : ℝ) / Metric.infDist x C) • (P_C x - x))
      else
        P_C x := by
  let φ : ℝ → Set.Ioi (⊥ : EReal) := scaledNormKernelOfPos (H := ℝ) γ
  have hφ : φ ∈ Γ₀(ℝ) := by
    simpa [φ] using scaledNormKernelOfPos_mem_gammaZero (H := ℝ) γ
  have heven : Function.Even φ := by
    -- The scalar profile depends only on the norm, so it is even.
    intro t
    apply Subtype.ext
    simp [φ, norm_neg]
  have hdiff : DifferentiableOn ℝ (fun t : ℝ ↦ (φ t : EReal).toReal) (({0} : Set ℝ)ᶜ) := by
    -- Away from `0`, the scalar profile is just the differentiable function `t ↦ γ |t|`.
    have habs : DifferentiableOn ℝ (fun t : ℝ ↦ |t|) (({0} : Set ℝ)ᶜ) :=
      differentiableOn_abs fun t ht ↦ by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    simpa [φ, scaledNormKernelOfPos_apply, Real.norm_eq_abs] using
      habs.const_mul (γ : ℝ)
  have hdist : distanceProfile C φ ∈ Γ₀(H) := by
    -- Replace the abstract distance profile by the concrete scaled distance-to-set function.
    simpa [φ, distanceProfile_scaledNormKernelOfPos_eq_scaled_distanceToSet (C := C) (γ := γ)] using
      smul_mem_gammaZero (f := (fun y : H ↦ Metric.infDist y C).toEReal) (hf := hγC) γ
  have hpiece :
      Prox[γ, (fun y : H ↦ Metric.infDist y C).toEReal, hγC] x =
        if Metric.infDist x C > sSup ((∂ φ) 0) then
          x +
            ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
                Metric.infDist x C) •
              (P_C x - x)
        else
          P_C x := by
    -- Specialize Proposition 24.27 exactly to the scalar profile `φ = γ |·|`.
    simpa [scaledProximityOperator, φ,
      distanceProfile_scaledNormKernelOfPos_eq_scaled_distanceToSet (C := C) (γ := γ)] using
      (prox_distanceProfile_eq_piecewise
        (C := C) hC_nonempty hC_closed hC_convex φ hφ heven hdiff hdist x)
  rw [hpiece, sSup_subdifferential_scaledNormKernelOfPos_zero_eq_gamma (γ := γ)]
  by_cases h : Metric.infDist x C > (γ : ℝ)
  · have hprox_conj :
      Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C) = (γ : ℝ) := by
      -- Moreau's identity turns the conjugate prox into `d_C(x) - Prox_{γ |·|}(d_C(x)) = γ`.
      calc
        Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C) =
            Metric.infDist x C - Prox[φ, hφ] (Metric.infDist x C) := by
              rw [conjugate_proximityOperator_eq_sub_proximityOperator
                (g := φ) (hg := hφ) (Metric.infDist x C)]
        _ = (γ : ℝ) := by
          rw [prox_scaledNormKernelOfPos_real_eq_sub_of_gt (γ := γ) h]
          ring
    -- The high branch coefficient therefore collapses from the abstract conjugate prox to `γ`.
    simp [h, hprox_conj]
  · -- On the low branch, Proposition 24.27 already returns the projection point.
    simp [h]

end BasicProperties

end

end ERealFunction
