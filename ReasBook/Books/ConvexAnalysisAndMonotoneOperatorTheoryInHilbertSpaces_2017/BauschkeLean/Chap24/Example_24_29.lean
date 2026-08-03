import BauschkeLean.Chap24.Example_24_28

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

/-- The `ε`-insensitive loss from Example 24.29, owned canonically as the distance to the closed
ball `B(0; ε)`. The source-facing radial profile is recorded by
`epsilonInsensitiveLoss_eq_radialProfile`. -/
def epsilonInsensitiveLoss {H : Type u} [NormedAddCommGroup H] (ε : PosReal) :
    H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ Metric.infDist x (Metric.closedBall (0 : H) (ε : ℝ))).toEReal

private theorem closedBall_zero_nonempty {H : Type u} [NormedAddCommGroup H] (ε : PosReal) :
    (Metric.closedBall (0 : H) (ε : ℝ) : Set H).Nonempty := by
  refine ⟨0, ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using
    (show (0 : ℝ) ≤ (ε : ℝ) from le_of_lt ε.2)

/-- The `ε`-insensitive loss is the distance to the closed ball `B(0; ε)`. -/
theorem epsilonInsensitiveLoss_eq_distance_closedBall {H : Type u} [NormedAddCommGroup H]
    (ε : PosReal) :
    epsilonInsensitiveLoss ε =
      (fun x : H ↦ Metric.infDist x (Metric.closedBall (0 : H) (ε : ℝ))).toEReal := rfl

/-- Helper for Example 24.29: the distance to the closed ball `B(0; ε)` is the radial profile
`x ↦ max (‖x‖ - ε, 0)`. -/
private theorem infDist_closedBall_zero_eq_max_sub_radius {H : Type u} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (ε : PosReal) (x : H) :
    Metric.infDist x (Metric.closedBall (0 : H) (ε : ℝ)) = max (‖x‖ - (ε : ℝ)) 0 := by
  by_cases hx : ‖x‖ ≤ (ε : ℝ)
  · have hx_mem : x ∈ Metric.closedBall (0 : H) (ε : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    -- Inside the ball, the distance vanishes and so does the radial profile.
    rw [Metric.infDist_zero_of_mem hx_mem, max_eq_right (sub_nonpos.mpr hx)]
  · have hεx : (ε : ℝ) < ‖x‖ := lt_of_not_ge hx
    have hnormx_pos : 0 < ‖x‖ := lt_trans ε.2 hεx
    have hnormx_ne : ‖x‖ ≠ 0 := hnormx_pos.ne'
    let p : H := ((ε : ℝ) / ‖x‖) • x
    have hp_mem : p ∈ Metric.closedBall (0 : H) (ε : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      change ‖((ε : ℝ) / ‖x‖) • x‖ ≤ (ε : ℝ)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ε.2 hnormx_pos)]
      calc
        ((ε : ℝ) / ‖x‖) * ‖x‖ = (ε : ℝ) := by
          field_simp [hnormx_ne]
        _ ≤ (ε : ℝ) := le_rfl
    have hp_dist : dist x p = ‖x‖ - (ε : ℝ) := by
      calc
        dist x p = ‖x - p‖ := by
          rw [dist_eq_norm]
        _ = ‖(1 - (ε : ℝ) / ‖x‖) • x‖ := by
          congr 1
          calc
            x - p = (1 : ℝ) • x - ((ε : ℝ) / ‖x‖) • x := by
              simp [p]
            _ = (1 - (ε : ℝ) / ‖x‖) • x := by
              rw [sub_smul]
        _ = |1 - (ε : ℝ) / ‖x‖| * ‖x‖ := norm_smul _ _
        _ = (1 - (ε : ℝ) / ‖x‖) * ‖x‖ := by
          have hdiv_le_one : (ε : ℝ) / ‖x‖ ≤ 1 := by
            rw [div_le_iff₀ hnormx_pos, one_mul]
            exact hεx.le
          rw [abs_of_nonneg (sub_nonneg.mpr hdiv_le_one)]
        _ = ‖x‖ - (ε : ℝ) := by
          field_simp [hnormx_ne]
    have hmax : max (‖x‖ - (ε : ℝ)) 0 = ‖x‖ - (ε : ℝ) :=
      max_eq_left (sub_nonneg.mpr hεx.le)
    apply le_antisymm
    · -- The radial point on the sphere gives the matching upper bound.
      simpa [hmax, hp_dist] using
        (Metric.infDist_le_dist_of_mem hp_mem :
          Metric.infDist x (Metric.closedBall (0 : H) (ε : ℝ)) ≤ dist x p)
    · -- Any point of the ball has norm at most `ε`, so the triangle inequality gives the lower bound.
      rw [hmax, Metric.le_infDist ⟨p, hp_mem⟩]
      intro y hy
      have hy_norm : ‖y‖ ≤ (ε : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy
      have htriangle : ‖x‖ ≤ dist x y + ‖y‖ := by
        simpa [dist_eq_norm, sub_add_cancel] using norm_add_le (x - y) y
      linarith

/-- The `ε`-insensitive loss is the radial profile `x ↦ max (‖x‖ - ε, 0)`. -/
theorem epsilonInsensitiveLoss_eq_radialProfile {H : Type u} [NormedAddCommGroup H]
    [NormedSpace ℝ H]
    (ε : PosReal) :
    epsilonInsensitiveLoss ε = (fun x : H ↦ max (‖x‖ - (ε : ℝ)) 0).toEReal := by
  -- Rewrite the distance-to-ball definition pointwise through the closed-ball distance formula.
  funext x
  apply Subtype.ext
  simpa [epsilonInsensitiveLoss, Function.toEReal_apply,
    infDist_closedBall_zero_eq_max_sub_radius (ε := ε) x]

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The `ε`-insensitive loss belongs to `Γ₀(H)`. -/
theorem epsilonInsensitiveLoss_mem_gammaZero (ε : PosReal) :
    epsilonInsensitiveLoss ε ∈ Γ₀(H) := by
  let C : Set H := Metric.closedBall (0 : H) (ε : ℝ)
  have hC_nonempty : C.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [C, Metric.mem_closedBall, dist_eq_norm] using
      (show (0 : ℝ) ≤ (ε : ℝ) from le_of_lt ε.2)
  have hC_closed : IsClosed C := by
    simpa [C] using
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) (ε : ℝ)))
  have hC_convex : Convex ℝ C := by
    simpa [C] using convex_closedBall (0 : H) (ε : ℝ)
  simpa [epsilonInsensitiveLoss, C] using
    Set.distanceToSet_toEReal_mem_gammaZero_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex

end Hilbert

section Prox

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (ε : PosReal)

private theorem isChebyshev_closedBall_zero : IsChebyshev (Metric.closedBall (0 : H) (ε : ℝ)) :=
  isChebyshev_of_nonempty_isClosed_convex
    (closedBall_zero_nonempty ε)
    (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) (ε : ℝ)))
    (convex_closedBall (0 : H) (ε : ℝ))

local notation "Bε" => Metric.closedBall (0 : H) (ε : ℝ)
local notation "Pε" => P[Bε, isChebyshev_closedBall_zero ε]

/-- Helper for Example 24.29: the metric projector onto `B(0; ε)` clips a vector radially to norm
`ε` outside the ball and fixes it inside. -/
private theorem projection_closedBall_zero_eq_radial_clip (x : H) :
    Pε x = if (ε : ℝ) < ‖x‖ then ((ε : ℝ) / ‖x‖) • x else x := by
  have hB_nonempty : Set.Nonempty Bε := closedBall_zero_nonempty ε
  have hB_closed : IsClosed Bε := Metric.isClosed_closedBall
  have hB_convex : Convex ℝ Bε := convex_closedBall (0 : H) (ε : ℝ)
  by_cases hx : (ε : ℝ) < ‖x‖
  · have hnormx_pos : 0 < ‖x‖ := lt_trans ε.2 hx
    have hnormx_ne : ‖x‖ ≠ 0 := hnormx_pos.ne'
    have hp_norm : ‖((ε : ℝ) / ‖x‖) • x‖ = (ε : ℝ) := by
      calc
        ‖((ε : ℝ) / ‖x‖) • x‖ = |(ε : ℝ) / ‖x‖| * ‖x‖ := norm_smul _ _
        _ = ((ε : ℝ) / ‖x‖) * ‖x‖ := by
          rw [abs_of_pos (div_pos ε.2 hnormx_pos)]
        _ = (ε : ℝ) := by
          rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hnormx_ne, mul_one]
    have hp_inner : ⟪((ε : ℝ) / ‖x‖) • x, x⟫_ℝ = (ε : ℝ) * ‖x‖ := by
      calc
        ⟪((ε : ℝ) / ‖x‖) • x, x⟫_ℝ = ((ε : ℝ) / ‖x‖) * ⟪x, x⟫_ℝ := by
          rw [real_inner_smul_left]
        _ = ((ε : ℝ) / ‖x‖) * ‖x‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        _ = (ε : ℝ) * ‖x‖ := by
          rw [pow_two, div_eq_mul_inv]
          ring_nf
          field_simp [hnormx_ne]
    have hproj :
        ((ε : ℝ) / ‖x‖) • x = Pε x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hB_nonempty hB_closed hB_convex).mpr ?_
      refine ⟨?_, ?_⟩
      · -- The candidate lies on the sphere of radius `ε`, hence in the closed ball.
        simpa [Metric.mem_closedBall, dist_eq_norm, hp_norm]
      · intro y hy
        have hy_norm : ‖y‖ ≤ (ε : ℝ) := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hy
        have hy_inner : ⟪y, x⟫_ℝ ≤ (ε : ℝ) * ‖x‖ := by
          calc
            ⟪y, x⟫_ℝ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
            _ ≤ (ε : ℝ) * ‖x‖ := by
              gcongr
        have hcoef_nonneg : 0 ≤ 1 - (ε : ℝ) / ‖x‖ := by
          have hdiv_lt_one : (ε : ℝ) / ‖x‖ < 1 := by
            exact (div_lt_one hnormx_pos).2 hx
          linarith
        -- The variational inequality characterizes the projector on a closed convex set.
        calc
          ⟪y - ((ε : ℝ) / ‖x‖) • x, x - ((ε : ℝ) / ‖x‖) • x⟫_ℝ
              = (1 - (ε : ℝ) / ‖x‖) * ⟪y - ((ε : ℝ) / ‖x‖) • x, x⟫_ℝ := by
                  rw [show x - ((ε : ℝ) / ‖x‖) • x = (1 - (ε : ℝ) / ‖x‖) • x by
                    calc
                      x - ((ε : ℝ) / ‖x‖) • x = (1 : ℝ) • x - ((ε : ℝ) / ‖x‖) • x := by
                        rw [one_smul]
                      _ = (1 - (ε : ℝ) / ‖x‖) • x := by
                        rw [sub_smul], real_inner_smul_right]
          _ ≤ 0 := by
            refine mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg ?_
            calc
              ⟪y - ((ε : ℝ) / ‖x‖) • x, x⟫_ℝ = ⟪y, x⟫_ℝ - ⟪((ε : ℝ) / ‖x‖) • x, x⟫_ℝ := by
                rw [inner_sub_left]
              _ ≤ 0 := by
                linarith [hy_inner, hp_inner]
    simpa [isChebyshev_closedBall_zero, hx] using hproj.symm
  · have hx_mem : x ∈ Bε := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_not_gt hx
    have hproj : x = Pε x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hB_nonempty hB_closed hB_convex).mpr ?_
      refine ⟨hx_mem, ?_⟩
      intro y hy
      simp
    -- Points already in `B(0; ε)` are fixed by the projector.
    simpa [isChebyshev_closedBall_zero, hx] using hproj.symm

/-- Helper for Example 24.29: outside `B(0; ε)`, the projector rescales the vector to norm
`ε`. -/
private theorem projection_closedBall_zero_eq_radius_div_norm_smul_of_lt_norm {x : H}
    (hx : (ε : ℝ) < ‖x‖) :
    Pε x = ((ε : ℝ) / ‖x‖) • x := by
  -- This is the active branch of the radial clip formula.
  rw [projection_closedBall_zero_eq_radial_clip (ε := ε) (x := x)]
  simp [hx]

/-- Helper for Example 24.29: inside `B(0; ε)`, the projector is the identity. -/
private theorem projection_closedBall_zero_eq_self_of_norm_le {x : H} (hx : ‖x‖ ≤ (ε : ℝ)) :
    Pε x = x := by
  -- This is the inactive branch of the radial clip formula.
  rw [projection_closedBall_zero_eq_radial_clip (ε := ε) (x := x)]
  simp [not_lt_of_ge hx]

/-- Helper for Example 24.29: in the high branch `‖x‖ > γ + ε`, the abstract correction term from
Example 24.28 simplifies to the textbook radial factor `(1 - γ / ‖x‖) x`. -/
private theorem prox_high_branch_closedBall_simplify (γ : PosReal) {x : H}
    (hx : ‖x‖ > (γ : ℝ) + (ε : ℝ)) :
    x + (((γ : ℝ) / Metric.infDist x Bε) • (Pε x - x)) =
      (1 - (γ : ℝ) / ‖x‖) • x := by
  have hεx : (ε : ℝ) < ‖x‖ := by
    have hε_sum : (ε : ℝ) < (γ : ℝ) + (ε : ℝ) := by
      linarith [γ.2]
    exact lt_trans hε_sum hx
  have hnormx_pos : 0 < ‖x‖ := lt_trans ε.2 hεx
  have hnormx_ne : ‖x‖ ≠ 0 := hnormx_pos.ne'
  have hdist_eq : Metric.infDist x Bε = ‖x‖ - (ε : ℝ) := by
    rw [infDist_closedBall_zero_eq_max_sub_radius (ε := ε) x,
      max_eq_left (sub_nonneg.mpr hεx.le)]
  have hdist_ne : ‖x‖ - (ε : ℝ) ≠ 0 := by
    linarith
  have hproj_eq : Pε x = ((ε : ℝ) / ‖x‖) • x :=
    projection_closedBall_zero_eq_radius_div_norm_smul_of_lt_norm (ε := ε) hεx
  -- Replace both the distance and the projection by their radial closed-ball formulas.
  calc
    x + (((γ : ℝ) / Metric.infDist x Bε) • (Pε x - x))
        = x + (((γ : ℝ) / (‖x‖ - (ε : ℝ))) • ((((ε : ℝ) / ‖x‖) - 1) • x)) := by
            rw [hdist_eq, hproj_eq]
            congr 2
            calc
              ((ε : ℝ) / ‖x‖) • x - x = ((ε : ℝ) / ‖x‖) • x - (1 : ℝ) • x := by
                rw [one_smul]
              _ = (((ε : ℝ) / ‖x‖) - 1) • x := by
                rw [sub_smul]
    _ = (1 : ℝ) • x +
          (((γ : ℝ) / (‖x‖ - (ε : ℝ))) * (((ε : ℝ) / ‖x‖) - 1)) • x := by
          rw [smul_smul, one_smul]
    _ = (1 + ((γ : ℝ) / (‖x‖ - (ε : ℝ))) * (((ε : ℝ) / ‖x‖) - 1)) • x := by
          rw [add_smul]
    _ = (1 - (γ : ℝ) / ‖x‖) • x := by
          congr 1
          field_simp [hnormx_ne, hdist_ne]
          ring

/-- Example 24.29 as the closed-ball specialization of the canonical distance-to-set proximity
formula from Example 24.28. -/
theorem prox_epsilonInsensitiveLoss_eq_piecewise_projection (γ : PosReal) (x : H) :
    Prox[γ, epsilonInsensitiveLoss ε, epsilonInsensitiveLoss_mem_gammaZero ε] x =
      if Metric.infDist x Bε > (γ : ℝ) then
        x + (((γ : ℝ) / Metric.infDist x Bε) • (Pε x - x))
      else
        Pε x := by
  have hB_nonempty : Set.Nonempty Bε := closedBall_zero_nonempty ε
  have hB_closed : IsClosed Bε := Metric.isClosed_closedBall
  have hB_convex : Convex ℝ Bε := convex_closedBall (0 : H) (ε : ℝ)
  simpa [epsilonInsensitiveLoss] using
    prox_distanceToSet_eq_piecewise hB_nonempty hB_closed hB_convex γ x

/-- Example 24.29 (1): for `f = max {‖·‖ - ε, 0}`, the proximity operator of `γ f`
is the radial piecewise map from equation `(24.55)`. -/
theorem prox_epsilonInsensitiveLoss_eq (γ : PosReal) (x : H) :
    Prox[γ, epsilonInsensitiveLoss ε, epsilonInsensitiveLoss_mem_gammaZero ε] x =
      if h₁ : ‖x‖ > (γ : ℝ) + (ε : ℝ) then
        (1 - (γ : ℝ) / ‖x‖) • x
      else if h₂ : (ε : ℝ) < ‖x‖ then
        ((ε : ℝ) / ‖x‖) • x
      else
        x := by
  -- Rewrite Example 24.28 using the closed-ball distance/profile formulas from this file.
  rw [prox_epsilonInsensitiveLoss_eq_piecewise_projection (ε := ε) (γ := γ) (x := x)]
  by_cases h₁ : ‖x‖ > (γ : ℝ) + (ε : ℝ)
  · have hεx : (ε : ℝ) < ‖x‖ := by
      have hε_sum : (ε : ℝ) < (γ : ℝ) + (ε : ℝ) := by
        linarith [γ.2]
      exact lt_trans hε_sum h₁
    have hdist_gt : Metric.infDist x Bε > (γ : ℝ) := by
      rw [infDist_closedBall_zero_eq_max_sub_radius (ε := ε) x,
        max_eq_left (sub_nonneg.mpr hεx.le)]
      linarith
    rw [if_pos hdist_gt]
    -- On the high branch, the abstract residual term collapses to the radial shrinkage factor.
    simpa [h₁] using prox_high_branch_closedBall_simplify (ε := ε) (γ := γ) h₁
  · by_cases h₂ : (ε : ℝ) < ‖x‖
    · have hdist_le : Metric.infDist x Bε ≤ (γ : ℝ) := by
        rw [infDist_closedBall_zero_eq_max_sub_radius (ε := ε) x,
          max_eq_left (sub_nonneg.mpr h₂.le)]
        linarith
      rw [if_neg (not_lt.mpr hdist_le)]
      -- In the middle branch, Example 24.28 returns the projector, which is the radial clip.
      simpa [h₁, h₂] using
        projection_closedBall_zero_eq_radius_div_norm_smul_of_lt_norm (ε := ε) h₂
    · have hx_le : ‖x‖ ≤ (ε : ℝ) := le_of_not_gt h₂
      have hx_mem : x ∈ Bε := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx_le
      have hdist_le : Metric.infDist x Bε ≤ (γ : ℝ) := by
        rw [Metric.infDist_zero_of_mem hx_mem]
        exact γ.2.le
      rw [if_neg (not_lt.mpr hdist_le)]
      -- Inside the ball, the projector fixes the point.
      simpa [h₁, h₂] using projection_closedBall_zero_eq_self_of_norm_le (ε := ε) hx_le

end Prox

section Real

/-- Helper for Example 24.29: any scalar radial factor `a / |x|` can be rewritten through
`Real.sign x` once `x ≠ 0`. -/
private theorem div_abs_mul_eq_mul_sign {a x : ℝ} (hx : x ≠ 0) :
    (a / |x|) * x = a * Real.sign x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
    field_simp [hx]
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
    field_simp [hx]

/-- Example 24.29 (2): on `ℝ`, the same formula is Vapnik's `ε`-insensitive loss prox from
equation `(24.56)`. -/
theorem prox_epsilonInsensitiveLoss_real_eq (ε γ : PosReal) (x : ℝ) :
    Prox[γ, epsilonInsensitiveLoss ε, epsilonInsensitiveLoss_mem_gammaZero ε] x =
      if h₁ : |x| > (γ : ℝ) + (ε : ℝ) then
        x - (γ : ℝ) * Real.sign x
      else if h₂ : (ε : ℝ) < |x| then
        (ε : ℝ) * Real.sign x
      else
        x := by
  calc
    Prox[γ, epsilonInsensitiveLoss ε, epsilonInsensitiveLoss_mem_gammaZero ε] x =
        if h₁ : |x| > (γ : ℝ) + (ε : ℝ) then
          (1 - (γ : ℝ) / |x|) * x
        else if h₂ : (ε : ℝ) < |x| then
          ((ε : ℝ) / |x|) * x
        else
          x := by
            -- Specialize the Hilbert-space radial formula to `ℝ`.
            simpa [Real.norm_eq_abs, smul_eq_mul] using
              (prox_epsilonInsensitiveLoss_eq (H := ℝ) (ε := ε) (γ := γ) (x := x))
    _ =
        if h₁ : |x| > (γ : ℝ) + (ε : ℝ) then
          x - (γ : ℝ) * Real.sign x
        else if h₂ : (ε : ℝ) < |x| then
          (ε : ℝ) * Real.sign x
        else
          x := by
            by_cases h₁ : |x| > (γ : ℝ) + (ε : ℝ)
            · simp [h₁]
              have hsum_pos : 0 < (γ : ℝ) + (ε : ℝ) := by
                linarith [γ.2, ε.2]
              have hx_ne : x ≠ 0 := by
                exact abs_ne_zero.mp (ne_of_gt (lt_trans hsum_pos h₁))
              -- Above `γ + ε`, the radial shrinkage factor is `x - γ sign x`.
              calc
                (1 - (γ : ℝ) / |x|) * x = x - ((γ : ℝ) / |x|) * x := by
                  ring
                _ = x - (γ : ℝ) * Real.sign x := by
                  rw [div_abs_mul_eq_mul_sign (a := (γ : ℝ)) hx_ne]
            · simp [h₁]
              by_cases h₂ : (ε : ℝ) < |x|
              · simp [h₂]
                have hx_ne : x ≠ 0 := by
                  exact abs_ne_zero.mp (ne_of_gt (lt_trans ε.2 h₂))
                -- In the middle branch, the clipped radius becomes `ε sign(x)`.
                simpa using div_abs_mul_eq_mul_sign (a := (ε : ℝ)) hx_ne
              · rw [if_neg h₂, if_neg h₂]

end Real

end

end ERealFunction
