import BauschkeLean.Chap11.Example_11_2
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap14.Remark_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

-- Semantic recall note: `lean_leansearch` surfaced mathlib's canonical interval projection
-- `Set.projIcc`; the local proximal owners used here are Example 12.25, Example 11.2 (2),
-- and Example 24.20 (2).

section RealInterval

variable {a b : ℝ}

local notation "Ω" => Set.Icc a b

/-- The soft thresholder on the interval `[a,b] ⊆ ℝ`, as in formula `(24.65)`. -/
def intervalSoftThresholder (a b : ℝ) : ℝ → ℝ :=
  fun η ↦ if η < a then η - a else if η ∈ Set.Icc a b then 0 else η - b

/-- The metric projection onto `[a,b]` viewed as an `ℝ → ℝ` clamp map. -/
def projIccReal (h : a ≤ b) : ℝ → ℝ :=
  fun ξ ↦ Set.projIcc a b h ξ

/-- `projIccReal` is the scalar-valued coercion of the canonical projection `Set.projIcc`. -/
@[simp] theorem projIccReal_apply (h : a ≤ b) (ξ : ℝ) :
    projIccReal h ξ = ((Set.projIcc a b h ξ : Ω) : ℝ) := rfl

/-- Helper for Example 24.34: a point of `C` whose distance is bounded by every distance to `C`
realizes `Metric.infDist x C`. -/
private theorem dist_eq_infDist_of_forall_le {X : Type*} [MetricSpace X] {C : Set X} {x p : X}
    (hp : p ∈ C) (hmin : ∀ q ∈ C, dist x p ≤ dist x q) :
    dist x p = Metric.infDist x C := by
  -- Convert the pointwise minimizing property into the defining infimum formula.
  apply le_antisymm
  · rw [Metric.le_infDist ⟨p, hp⟩]
    intro q hq
    exact hmin q hq
  · exact Metric.infDist_le_dist_of_mem hp

/-- Helper for Example 24.34: projection onto `[a,b]` minimizes the scalar distance to every
point of the interval. -/
private theorem abs_sub_projIccReal_le_abs_sub_of_mem_Icc (h : a ≤ b) (ξ η : ℝ)
    (hη : η ∈ Ω) :
    |ξ - projIccReal h ξ| ≤ |ξ - η| := by
  rcases hη with ⟨hη_left, hη_right⟩
  -- Split according to whether `ξ` lies to the left, inside, or to the right of the interval.
  by_cases hξ_left : ξ ≤ a
  · rw [projIccReal, Set.projIcc_of_le_left h hξ_left]
    have hξa_nonpos : ξ - a ≤ 0 := by
      linarith
    have hξη_nonpos : ξ - η ≤ 0 := by
      linarith
    rw [abs_of_nonpos hξa_nonpos, abs_of_nonpos hξη_nonpos]
    linarith
  · by_cases hξ_right : b ≤ ξ
    · rw [projIccReal, Set.projIcc_of_right_le h hξ_right]
      have hξb_nonneg : 0 ≤ ξ - b := by
        linarith
      have hξη_nonneg : 0 ≤ ξ - η := by
        linarith
      rw [abs_of_nonneg hξb_nonneg, abs_of_nonneg hξη_nonneg]
      linarith
    · have hξ_mem : ξ ∈ Ω := by
        constructor <;> linarith
      rw [projIccReal, Set.projIcc_of_mem h hξ_mem]
      simp

/-- Helper for Example 24.34: the interval clamp `projIccReal h ξ` is the best approximation to
`ξ` from `Ω = Set.Icc a b`. -/
private theorem isBestApproximation_projIccReal (h : a ≤ b) (ξ : ℝ) :
    IsBestApproximation ξ Ω (projIccReal h ξ) := by
  refine (isBestApproximation_iff_mem_and_dist_eq_infDist ξ Ω (projIccReal h ξ)).2 ?_
  refine ⟨?_, ?_⟩
  · -- The scalar clamp lands in the interval by construction.
    change ((Set.projIcc a b h ξ : Ω) : ℝ) ∈ Ω
    exact (Set.projIcc a b h ξ).2
  · -- The clamp minimizes the distance to every interval point, hence realizes `Metric.infDist`.
    apply dist_eq_infDist_of_forall_le
    · change ((Set.projIcc a b h ξ : Ω) : ℝ) ∈ Ω
      exact (Set.projIcc a b h ξ).2
    · intro η hη
      simpa [Real.dist_eq] using
        abs_sub_projIccReal_le_abs_sub_of_mem_Icc h ξ η hη

/-- The projection onto the closed interval `[a,b]` is the usual clamp map. -/
theorem projIcc_eq_piecewise (h : a ≤ b) :
    projIccReal h =
      fun ξ ↦ if ξ < a then a else if ξ ∈ Ω then ξ else b := by
  funext ξ
  -- Split by the same three branches as the textbook clamp formula.
  by_cases hξ_left : ξ < a
  · simp [projIccReal, hξ_left, Set.projIcc_of_le_left, hξ_left.le]
  · by_cases hξ_mem : ξ ∈ Ω
    · simp [projIccReal, hξ_left, Set.projIcc_of_mem, hξ_mem]
    · have hξ_right : b ≤ ξ := by
        by_contra hξ_right
        exact hξ_mem ⟨le_of_not_gt hξ_left, le_of_not_ge hξ_right⟩
      simp [projIccReal, hξ_left, hξ_mem, Set.projIcc_of_right_le, hξ_right]

/-- The interval soft thresholder is the residual `Id - P_[a,b]`. -/
theorem intervalSoftThresholder_eq_sub_projIcc (h : a ≤ b) :
    intervalSoftThresholder a b =
      fun ξ ↦ ξ - projIccReal h ξ := by
  funext ξ
  -- Rewrite the projection by the clamp formula and check the same three scalar branches.
  rw [projIcc_eq_piecewise h]
  by_cases hξ_left : ξ < a
  · simp [intervalSoftThresholder, hξ_left]
  · by_cases hξ_mem : ξ ∈ Ω
    · simp [intervalSoftThresholder, hξ_left, hξ_mem]
    · simp [intervalSoftThresholder, hξ_left, hξ_mem]

/-- Part (i) of Example 24.34: for a nonempty closed interval `Ω = [a,b] ⊆ ℝ`,
the proximity operator of the indicator of `Ω` is the metric projection onto `Ω`. -/
theorem example_24_34_1_proximityOperator_indicator_Icc_eq_projIcc (h : a ≤ b) :
    proximityOperator (ι[Ω])
      (hasUniqueProxPoint_indicator_of_nonempty_isClosed_convex
        (Set.nonempty_Icc.2 h)
        isClosed_Icc
        (convex_Icc a b)) =
      projIccReal h := by
  funext ξ
  -- Promote the scalar best-approximation statement to a proximal-point statement.
  have hprox : IsProxPoint (ι[Ω]) ξ (projIccReal h ξ) := by
    have hnonempty : Set.Nonempty Ω := Set.nonempty_Icc.2 h
    exact (isProxPoint_indicator_iff_isBestApproximation hnonempty ξ (projIccReal h ξ)).2
      (isBestApproximation_projIccReal h ξ)
  -- Uniqueness of proximal points for the indicator identifies the proximal operator value.
  exact
    (eq_proximityOperator_of_isProxPoint
      (ι[Ω])
      (hasUniqueProxPoint_indicator_of_nonempty_isClosed_convex
        (Set.nonempty_Icc.2 h)
        isClosed_Icc
        (convex_Icc a b))
      hprox).symm

/-- Example 24.34 (2): for a nonempty closed interval `Ω = [a,b] ⊆ ℝ`, the proximity operator of
the support function `σ_Ω` is the interval soft thresholder from formula `(24.65)`. -/
theorem example_24_34_2_proximityOperator_supportFunction_Icc_eq_intervalSoftThresholder
    (h : a ≤ b) :
    Prox[
      properIoi (σ[Ω])
        (isProper_supportFunction_of_nonempty Ω (Set.nonempty_Icc.2 h)),
      example_11_2_2_supportFunction_mem_gammaZero Ω
        (Set.nonempty_Icc.2 h)
    ] = intervalSoftThresholder a b := by
  have hΩ_nonempty : Set.Nonempty Ω := Set.nonempty_Icc.2 h
  have hιΩ : ι[Ω] ∈ Γ₀(ℝ) := by
    -- The interval indicator is a `Γ₀` function by closed-convex packaging.
    exact
      indicator_mem_gammaZero_of_nonempty_isClosed_convex
        hΩ_nonempty
        isClosed_Icc
        (convex_Icc a b)
  have hconj :
      ι[Ω]∗[hιΩ] =
        properIoi (σ[Ω])
          (isProper_supportFunction_of_nonempty Ω hΩ_nonempty) := by
    -- Identify the conjugate of the indicator with the support function.
    funext ξ
    apply Subtype.ext
    change ((ι[Ω]∗[hιΩ] ξ : EReal)) =
      (((properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω hΩ_nonempty) ξ :
          Set.Ioi (⊥ : EReal)) : EReal))
    rw [gammaZeroConjugate_apply, conjugate_indicator_eq_supportFunction]
  have hproxConj :
      Prox⋆[ι[Ω], hιΩ] =
        Prox[
          properIoi (σ[Ω])
            (isProper_supportFunction_of_nonempty Ω hΩ_nonempty),
          example_11_2_2_supportFunction_mem_gammaZero Ω hΩ_nonempty
        ] := by
    -- Transport the conjugate proximal operator through the identified support-function witness.
    funext ξ
    apply eq_proximityOperator_of_isProxPoint
      (properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω hΩ_nonempty))
      (hasUniqueProxPoint_of_mem_gammaZero
        (properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω hΩ_nonempty))
        (example_11_2_2_supportFunction_mem_gammaZero Ω hΩ_nonempty))
    simpa [hconj] using
      (proximityOperator_isProxPoint
        (ι[Ω]∗[hιΩ])
        (hasUniqueProxPoint_of_mem_gammaZero
          (ι[Ω]∗[hιΩ])
          (gammaZeroConjugate_mem_gammaZero hιΩ))
        ξ)
  have hproj :
      Prox[ι[Ω], hιΩ] = projIccReal h := by
    -- Part (i) already identifies the indicator proximal map with the interval projection.
    funext ξ
    simpa using
      congrFun (example_24_34_1_proximityOperator_indicator_Icc_eq_projIcc h) ξ
  calc
    Prox[
        properIoi (σ[Ω])
          (isProper_supportFunction_of_nonempty Ω hΩ_nonempty),
        example_11_2_2_supportFunction_mem_gammaZero Ω hΩ_nonempty
      ] = Prox⋆[ι[Ω], hιΩ] := by
        rw [hproxConj]
    _ = fun ξ : ℝ ↦ ξ - Prox[ι[Ω], hιΩ] ξ := by
        -- Moreau's decomposition at parameter `1` gives the projection residual.
        funext ξ
        simpa using conjugate_proximityOperator_eq_sub_proximityOperator (ι[Ω]) hιΩ ξ
    _ = fun ξ : ℝ ↦ ξ - projIccReal h ξ := by rw [hproj]
    _ = intervalSoftThresholder a b := by
        rw [← intervalSoftThresholder_eq_sub_projIcc h]

end RealInterval

section RealSoftThreshold

/-- Helper for Example 24.34: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem realInner_eq_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  -- Collapse the one-dimensional inner product to scalar multiplication.
  calc
    ⟪x, y⟫_ℝ = (starRingEnd ℝ) x * y := RCLike.inner_apply' x y
    _ = x * y := by simp

/-- The support function of `[-1,1] ⊆ ℝ` is the absolute value. -/
theorem supportFunction_Icc_neg_one_one_eq_abs :
    σ[Set.Icc (-1 : ℝ) 1] = (fun ξ : ℝ ↦ |ξ|).toEReal.asEReal := by
  funext ξ
  have hIcc : (-1 : ℝ) ≤ 1 := by
    norm_num
  have hnonempty : (Set.Icc (-1 : ℝ) 1).Nonempty := by
    exact ⟨0, by simp⟩
  have hinner :
      (fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) =
        fun x : ℝ ↦ ((x * ξ : ℝ) : EReal) := by
    -- Rewrite the scalar pairing before maximizing over the interval.
    funext x
    simp [realInner_eq_mul]
  by_cases hξ_neg : ξ < 0
  · have hanti :
        AntitoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (-1 : ℝ) 1) := by
      -- A negative slope makes the affine map decrease on the interval.
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
    · -- At the origin, the support value of any nonempty set is zero.
      rw [hξ_zero]
      simpa using supportFunction_zero_eq_zero_of_nonempty
        (C := Set.Icc (-1 : ℝ) 1) hnonempty
    · have hξ_pos : 0 < ξ := by
        exact lt_of_le_of_ne (le_of_not_gt hξ_neg) (Ne.symm hξ_zero)
      have hmono :
          MonotoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (-1 : ℝ) 1) := by
        -- A positive slope makes the affine map increase on the interval.
        intro x hx y hy hxy
        have hmul : x * ξ ≤ y * ξ := mul_le_mul_of_nonneg_right hxy hξ_pos.le
        simpa using (EReal.coe_le_coe hmul)
      have hsSup :
          sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc (-1 : ℝ) 1) =
            (((1 : ℝ) * ξ : ℝ) : EReal) :=
        MonotoneOn.sSup_image_Icc hIcc hmono
      rw [supportFunction_eq_sSup_image, hinner, hsSup]
      simp [abs_of_pos hξ_pos]

/-- Helper for Example 24.34: the scaled absolute-value kernel `ξ ↦ ω |ξ|` is the support
function of the symmetric interval `[-ω, ω]`. -/
private theorem scaledNormKernelOfPos_eq_supportFunction_Icc_neg_self_self (ω : PosReal) :
    scaledNormKernelOfPos ω =
      properIoi (σ[Set.Icc (-(ω : ℝ)) (ω : ℝ)])
        (isProper_supportFunction_of_nonempty
          (Set.Icc (-(ω : ℝ)) (ω : ℝ))
          (Set.nonempty_Icc.2 (by linarith [ω.2]))) := by
  funext ξ
  apply Subtype.ext
  have habs :
      σ[Set.Icc (-1 : ℝ) 1] ξ = ((|ξ| : ℝ) : EReal) := by
    simpa [Function.asEReal_apply] using
      congrFun supportFunction_Icc_neg_one_one_eq_abs ξ
  have hIcc :
      ((ω : ℝ) • Set.Icc (-1 : ℝ) 1) = Set.Icc (-(ω : ℝ)) (ω : ℝ) := by
    ext u
    constructor
    · intro hu
      rcases Set.mem_smul_set.mp hu with ⟨t, ht, rfl⟩
      constructor
      · change -(ω : ℝ) ≤ (ω : ℝ) * t
        nlinarith [ht.1, ω.2]
      · change (ω : ℝ) * t ≤ (ω : ℝ)
        nlinarith [ht.2, ω.2]
    · intro hu
      refine Set.mem_smul_set.mpr ?_
      refine ⟨u / (ω : ℝ), ?_, ?_⟩
      · constructor
        · rw [le_div_iff₀ ω.2]
          simpa using hu.1
        · rw [div_le_iff₀ ω.2]
          simpa using hu.2
      · change (ω : ℝ) * (u / (ω : ℝ)) = u
        field_simp [ω.2.ne']
  -- Scale the unit interval support function and identify the scaled set.
  calc
    ((scaledNormKernelOfPos ω ξ : Set.Ioi (⊥ : EReal)) : EReal) =
        (((ω : ℝ) * ‖ξ‖ : ℝ) : EReal) := scaledNormKernelOfPos_apply ω ξ
    _ = (((ω : ℝ) * |ξ| : ℝ) : EReal) := by simp [Real.norm_eq_abs]
    _ = ((ω : ℝ) : EReal) * σ[Set.Icc (-1 : ℝ) 1] ξ := by
          rw [habs]
          exact (EReal.coe_mul (ω : ℝ) |ξ|).symm
    _ = (σ[Set.Icc (-1 : ℝ) 1] ∘ fun u : ℝ ↦ (ω : ℝ) • u) ξ := by
          simpa using
            (congrFun
              (supportFunction_comp_pos_smul_eq_mul_supportFunction
                (Set.Icc (-1 : ℝ) 1) ω.2)
              ξ).symm
    _ = σ[((ω : ℝ) • Set.Icc (-1 : ℝ) 1)] ξ := by
          simpa using
            congrFun
              (supportFunction_comp_smul_eq_supportFunction_smul_set
                (Set.Icc (-1 : ℝ) 1) (ω : ℝ))
              ξ
    _ = σ[Set.Icc (-(ω : ℝ)) (ω : ℝ)] ξ := by rw [hIcc]

/-- Helper for Example 24.34: the symmetric interval soft thresholder is the usual real
soft-threshold formula. -/
private theorem intervalSoftThresholder_eq_sign_mul_max (ω : PosReal) :
    intervalSoftThresholder (-(ω : ℝ)) (ω : ℝ) =
      fun ξ : ℝ ↦ Real.sign ξ * max (|ξ| - (ω : ℝ)) 0 := by
  funext ξ
  -- Split according to the three scalar regions in formula `(24.66)`.
  by_cases hξ_left : ξ < -(ω : ℝ)
  · have hξ_neg : ξ < 0 := lt_trans hξ_left (by linarith [ω.2])
    have hω_lt_negξ : (ω : ℝ) < -ξ := by
      linarith
    have hsoft :
        intervalSoftThresholder (-(ω : ℝ)) (ω : ℝ) ξ = ξ + (ω : ℝ) := by
      simp [intervalSoftThresholder, hξ_left]
    rw [hsoft]
    rw [Real.sign_of_neg hξ_neg, abs_of_neg hξ_neg,
      max_eq_left (sub_nonneg.mpr hω_lt_negξ.le)]
    ring
  · by_cases hξ_mid : ξ ≤ (ω : ℝ)
    · have hnegω_le_ξ : -(ω : ℝ) ≤ ξ := le_of_not_gt hξ_left
      have habs_le : |ξ| ≤ (ω : ℝ) := abs_le.mpr ⟨by linarith, hξ_mid⟩
      have hξ_mem : ξ ∈ Set.Icc (-(ω : ℝ)) (ω : ℝ) := ⟨hnegω_le_ξ, hξ_mid⟩
      simp [intervalSoftThresholder, hξ_left, hξ_mem, habs_le]
    · have hω_lt_ξ : (ω : ℝ) < ξ := lt_of_not_ge hξ_mid
      have hξ_pos : 0 < ξ := lt_trans ω.2 hω_lt_ξ
      have hξ_mem : ξ ∉ Set.Icc (-(ω : ℝ)) (ω : ℝ) := by
        intro hmem
        exact hξ_mid hmem.2
      have hsoft :
          intervalSoftThresholder (-(ω : ℝ)) (ω : ℝ) ξ = ξ - (ω : ℝ) := by
        simp [intervalSoftThresholder, hξ_left, hξ_mem]
      rw [hsoft]
      rw [Real.sign_of_pos hξ_pos, abs_of_pos hξ_pos,
        max_eq_left (sub_nonneg.mpr hω_lt_ξ.le)]
      ring

/-- Part (iii) of Example 24.34: for `ω ∈ ℝ_{++}`, the proximity operator of `ξ ↦ ω |ξ|` on `ℝ`
is the soft-threshold map `ξ ↦ sign(ξ) max {|ξ| - ω, 0}`. -/
theorem example_24_34_3_proximityOperator_scaledNorm_real_eq_sign_mul_max
    (ω : PosReal) :
    Prox[scaledNormKernelOfPos ω, scaledNormKernelOfPos_mem_gammaZero ω] =
      fun ξ : ℝ ↦ Real.sign ξ * max (|ξ| - (ω : ℝ)) 0 := by
  funext ξ
  let σω : ℝ → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[Set.Icc (-(ω : ℝ)) (ω : ℝ)])
      (isProper_supportFunction_of_nonempty
        (Set.Icc (-(ω : ℝ)) (ω : ℝ))
        (Set.nonempty_Icc.2 (by linarith [ω.2])))
  have hscaled : scaledNormKernelOfPos ω = σω := by
    simpa [σω] using scaledNormKernelOfPos_eq_supportFunction_Icc_neg_self_self ω
  have hproxσ :
      IsProxPoint σω ξ (intervalSoftThresholder (-(ω : ℝ)) (ω : ℝ) ξ) := by
    have hEq :
        Prox[σω,
          example_11_2_2_supportFunction_mem_gammaZero
            (Set.Icc (-(ω : ℝ)) (ω : ℝ))
            (Set.nonempty_Icc.2 (by linarith [ω.2]))] =
          intervalSoftThresholder (-(ω : ℝ)) (ω : ℝ) := by
      simpa [σω] using
        example_24_34_2_proximityOperator_supportFunction_Icc_eq_intervalSoftThresholder
          (show -(ω : ℝ) ≤ (ω : ℝ) by linarith [ω.2])
    -- Read the interval-soft-threshold formula as the support-function proximal point.
    simpa [hEq] using
      proximityOperator_isProxPoint σω
        (hasUniqueProxPoint_of_mem_gammaZero σω
          (example_11_2_2_supportFunction_mem_gammaZero
            (Set.Icc (-(ω : ℝ)) (ω : ℝ))
            (Set.nonempty_Icc.2 (by linarith [ω.2]))))
        ξ
  have hproxScaled :
      IsProxPoint (scaledNormKernelOfPos ω) ξ
        (intervalSoftThresholder (-(ω : ℝ)) (ω : ℝ) ξ) := by
    -- Transport the proximal-point statement across the support-function identification.
    simpa [hscaled] using hproxσ
  calc
    Prox[scaledNormKernelOfPos ω, scaledNormKernelOfPos_mem_gammaZero ω] ξ =
        intervalSoftThresholder (-(ω : ℝ)) (ω : ℝ) ξ := by
          simpa using
            (eq_proximityOperator_of_isProxPoint
              (scaledNormKernelOfPos ω)
              (hasUniqueProxPoint_of_mem_gammaZero
                (scaledNormKernelOfPos ω)
                (scaledNormKernelOfPos_mem_gammaZero ω))
              hproxScaled).symm
    _ = Real.sign ξ * max (|ξ| - (ω : ℝ)) 0 := by
          rw [intervalSoftThresholder_eq_sign_mul_max]

end RealSoftThreshold

end

end ERealFunction
