import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

-- Semantic recall note: `lean_leansearch` did not surface the thickened-set projection formula,
-- so this item keeps the source-facing `C + closedBall (0) ε` description while exposing the
-- canonical bridge to `Metric.cthickening ε C` and the project-local `P[C, hC]` projector API.

universe u

section

variable {H : Type u} [NormedAddCommGroup H]
variable {C : Set H}

/-- Proposition 29.10 (1): for a nonempty subset `C` of a real Hilbert space and
`D = C + B(0; ε)` with `0 ≤ ε`, the thickened set `D` is nonempty. -/
theorem nonempty_add_closedBall_of_nonempty
    (hC_nonempty : C.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) :
    (C + Metric.closedBall (0 : H) ε : Set H).Nonempty := by
  rcases hC_nonempty with ⟨c, hc⟩
  refine ⟨c, c, hc, 0, ?_, by simp⟩
  simpa [Metric.mem_closedBall] using hε

end

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {C : Set H}

/-- Proposition 29.10 (3): for a convex subset `C` of a real Hilbert space and
`D = C + B(0; ε)`, the thickened set `D` is convex. -/
theorem convex_add_closedBall_of_convex
    (hC_convex : Convex ℝ C) (ε : ℝ) :
    Convex ℝ (C + Metric.closedBall (0 : H) ε : Set H) := by
  simpa using hC_convex.add (convex_closedBall (0 : H) ε)

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

private theorem add_closedBall_eq_cthickening_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (C + Metric.closedBall (0 : H) ε : Set H) = Metric.cthickening ε C := by
  ext x
  constructor
  · rintro ⟨c, hc, z, hz, rfl⟩
    refine Metric.mem_cthickening_of_dist_le (c + z) c ε C hc ?_
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hz
  · intro hx
    let hC_cheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
    have hbest := projectionPoint_isBestApproximation C hC_cheb x
    have hx' : Metric.infDist x C ≤ ε := by
      rw [Metric.mem_cthickening_iff] at hx
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
      simpa [Metric.infDist, ENNReal.toReal_ofReal hε] using hreal
    have hdist : dist x (P[C, hC_cheb] x) ≤ ε := by
      simpa [hbest.2] using hx'
    refine ⟨P[C, hC_cheb] x, projectionPoint_mem C hC_cheb x, x - P[C, hC_cheb] x, ?_,
      by abel_nf⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hdist

/-- Companion bridge for Proposition 29.10: the thickened set `C + B(0; ε)` agrees with the
closed `ε`-thickening `Metric.cthickening ε C` of `C` when `C` is closed and convex. -/
theorem add_closedBall_eq_cthickening_of_isClosed_convex
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {ε : ℝ} (hε : 0 ≤ ε) :
    (C + Metric.closedBall (0 : H) ε : Set H) = Metric.cthickening ε C := by
  by_cases hC_nonempty : C.Nonempty
  · simpa using
      add_closedBall_eq_cthickening_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex hε
  · simp [Set.not_nonempty_iff_eq_empty.mp hC_nonempty]

/-- Proposition 29.10 (2): for a closed convex subset `C` of a real Hilbert space and
`D = C + B(0; ε)`, the thickened set `D` is closed. -/
theorem isClosed_add_closedBall_of_isClosed_convex
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (ε : ℝ) :
    IsClosed (C + Metric.closedBall (0 : H) ε : Set H) := by
  by_cases hε : 0 ≤ ε
  · rw [add_closedBall_eq_cthickening_of_isClosed_convex hC_closed hC_convex hε]
    simpa using (Metric.isClosed_cthickening : IsClosed (Metric.cthickening ε C))
  · rw [Metric.closedBall_eq_empty.2 (lt_of_not_ge hε)]
    simp

/-- Proposition 29.10 companion: the thickened set of a nonempty closed convex set is Chebyshev.
-/
theorem isChebyshev_add_closedBall_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsChebyshev (C + Metric.closedBall (0 : H) ε : Set H) :=
  isChebyshev_of_nonempty_isClosed_convex
    (nonempty_add_closedBall_of_nonempty hC_nonempty hε)
    (isClosed_add_closedBall_of_isClosed_convex hC_closed hC_convex ε)
    (convex_add_closedBall_of_convex hC_convex ε)

section

variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable {ε : ℝ} (hε : 0 < ε)

local notation "D" => (C + Metric.closedBall (0 : H) ε : Set H)
local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
local notation "hD_cheb" =>
  isChebyshev_add_closedBall_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex hε.le
local notation "P_C" => P[C, hC_cheb]

/-- Helper for Proposition 29.10: the scaled residual from `x` to `P_C x` has norm `ε` when
`x` lies outside the `ε`-tube around `C`. -/
private lemma scaledProjectionResidual_norm_eq
    (hε : 0 < ε) {x : H} (houtside : ε < ‖x - P_C x‖) :
    ‖(ε / ‖x - P_C x‖) • (x - P_C x)‖ = ε := by
  -- The strict branch gives a positive denominator, so the scalar factor simplifies directly.
  have hnorm_pos : 0 < ‖x - P_C x‖ := lt_trans hε houtside
  have hscale_nonneg : 0 ≤ ε / ‖x - P_C x‖ := div_nonneg hε.le hnorm_pos.le
  calc
    ‖(ε / ‖x - P_C x‖) • (x - P_C x)‖
        = ‖ε / ‖x - P_C x‖‖ * ‖x - P_C x‖ := norm_smul _ _
    _ = (ε / ‖x - P_C x‖) * ‖x - P_C x‖ := by
        rw [Real.norm_of_nonneg hscale_nonneg]
    _ = ε := by
        field_simp [hnorm_pos.ne']

/-- Helper for Proposition 29.10: the radial truncation from `P_C x` toward `x` lies in
`D = C + Metric.closedBall (0 : H) ε`. -/
private lemma radialProjection_mem_add_closedBall
    (hε : 0 < ε) {x : H} (houtside : ε < ‖x - P_C x‖) :
    P_C x + (ε / ‖x - P_C x‖) • (x - P_C x) ∈ D := by
  -- Use the projection point in `C` together with the scaled residual as the sum witnesses.
  refine ⟨P_C x, projectionPoint_mem C hC_cheb x,
    (ε / ‖x - P_C x‖) • (x - P_C x), ?_, by simp⟩
  have hnorm :
      ‖(ε / ‖x - P_C x‖) • (x - P_C x)‖ = ε :=
    scaledProjectionResidual_norm_eq
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
      (hε := hε) houtside
  simp [Metric.mem_closedBall, dist_eq_norm, hnorm]

/-- Helper for Proposition 29.10: the radial truncation candidate satisfies the projection
variational inequality on `D = C + Metric.closedBall (0 : H) ε`. -/
private lemma radialProjection_inner_le_zero_of_mem_add_closedBall
    (hε : 0 < ε) {x z : H} (houtside : ε < ‖x - P_C x‖) (hz : z ∈ D) :
    ⟪z - (P_C x + (ε / ‖x - P_C x‖) • (x - P_C x)),
      x - (P_C x + (ε / ‖x - P_C x‖) • (x - P_C x))⟫_ℝ ≤ 0 := by
  let p := P_C x
  let r := x - p
  let α : ℝ := ε / ‖r‖
  -- Read the projection inequality on `C` at `p = P_C x`.
  have hp_inner : ∀ c ∈ C, ⟪c - p, r⟫_ℝ ≤ 0 := by
    have hp_char :
        p = projectionPoint C hC_cheb x ↔
          p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 :=
      eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC_cheb hC_convex
    have hp_data := hp_char.mp rfl
    intro c hc
    simpa [p, r] using hp_data.2 c hc
  have hrnorm_pos : 0 < ‖r‖ := by
    dsimp [r, p]
    exact lt_trans hε houtside
  have hα_lt_one : α < 1 := by
    have hε_lt : ε < ‖r‖ := by
      simpa [r, p] using houtside
    exact (div_lt_one hrnorm_pos).2 hε_lt
  have hfactor_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα_lt_one.le
  have hα_mul : α * ‖r‖ ^ 2 = ε * ‖r‖ := by
    calc
      α * ‖r‖ ^ 2 = (ε / ‖r‖) * (‖r‖ * ‖r‖) := by
        simp [α, pow_two]
      _ = ε * ‖r‖ := by
        field_simp [hrnorm_pos.ne']
  rcases hz with ⟨c, hc, b, hb, rfl⟩
  have hb_norm : ‖b‖ ≤ ε := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hb
  -- Control the ball component by Cauchy-Schwarz and the radius bound `‖b‖ ≤ ε`.
  have hb_inner : ⟪b, r⟫_ℝ ≤ ε * ‖r‖ := by
    have hinner_le : ⟪b, r⟫_ℝ ≤ ‖b‖ * ‖r‖ := real_inner_le_norm _ _
    have hmul_le : ‖b‖ * ‖r‖ ≤ ε * ‖r‖ := by
      nlinarith [hb_norm, norm_nonneg r]
    exact le_trans hinner_le hmul_le
  have hball : ⟪b - α • r, r⟫_ℝ ≤ 0 := by
    have hrewrite : ⟪b - α • r, r⟫_ℝ = ⟪b, r⟫_ℝ - ε * ‖r‖ := by
      calc
        ⟪b - α • r, r⟫_ℝ = ⟪b, r⟫_ℝ - ⟪α • r, r⟫_ℝ := by
          rw [inner_sub_left]
        _ = ⟪b, r⟫_ℝ - α * ⟪r, r⟫_ℝ := by
          simp [inner_smul_left]
        _ = ⟪b, r⟫_ℝ - α * ‖r‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        _ = ⟪b, r⟫_ℝ - ε * ‖r‖ := by
          rw [hα_mul]
    rw [hrewrite]
    linarith
  have hcore : ⟪(c - p) + (b - α • r), r⟫_ℝ ≤ 0 := by
    rw [inner_add_left]
    linarith [hp_inner c hc, hball]
  have hsub :
      x - (p + α • r) = (1 - α) • r := by
    have hrewrite : (1 - α) • r = r - α • r := by
      rw [sub_smul, one_smul]
    calc
      x - (p + α • r) = r - α • r := by
        simp [r, p, sub_eq_add_neg, add_assoc, add_comm]
      _ = (1 - α) • r := hrewrite.symm
  have hz_rewrite :
      (c + b) - (p + α • r) = (c - p) + (b - α • r) := by
    abel_nf
  -- After rewriting, the `C`-term is nonpositive and the ball term is bounded by the radius.
  calc
    ⟪(c + b) - (p + α • r), x - (p + α • r)⟫_ℝ
        = ⟪(c - p) + (b - α • r), (1 - α) • r⟫_ℝ := by
            rw [hz_rewrite, hsub]
    _ = (1 - α) * ⟪(c - p) + (b - α • r), r⟫_ℝ := by
          rw [inner_smul_right]
    _ ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg hcore

/-- Proposition 29.10 (4): if `D = C + B(0; ε)` with `ε ∈ ℝ_{++}`, then the metric projection
onto `D` is given by formula `(29.5)`. -/
theorem projectionPoint_add_closedBall_eq
    (x : H) :
    P[D, hD_cheb] x =
      if ‖x - P_C x‖ ≤ ε then
        x
      else
        P_C x + (ε / ‖x - P_C x‖) • (x - P_C x) := by
  have hD_convex : Convex ℝ D := convex_add_closedBall_of_convex hC_convex ε
  by_cases hinside : ‖x - P_C x‖ ≤ ε
  · -- In the easy branch, `x` already lies in the thickened set, so it is its own projection.
    have hx_mem : x ∈ D := by
      rw [add_closedBall_eq_cthickening_of_isClosed_convex hC_closed hC_convex hε.le]
      refine Metric.mem_cthickening_of_dist_le x (P_C x) ε C (projectionPoint_mem C hC_cheb x) ?_
      simpa [dist_eq_norm] using hinside
    have hx_proj : x = P[D, hD_cheb] x := by
      rw [eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hD_cheb hD_convex]
      constructor
      · exact hx_mem
      · intro z hz
        simp
    simpa [hinside] using hx_proj.symm
  · -- In the strict branch, the projection is the radial truncation of `x - P_C x` to norm `ε`.
    have houtside : ε < ‖x - P_C x‖ := lt_of_not_ge hinside
    have hy_proj :
        P_C x + (ε / ‖x - P_C x‖) • (x - P_C x) = P[D, hD_cheb] x := by
      rw [eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hD_cheb hD_convex]
      constructor
      · exact radialProjection_mem_add_closedBall
          (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
          (hε := hε) houtside
      · intro z hz
        exact radialProjection_inner_le_zero_of_mem_add_closedBall
          (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
          (hε := hε) houtside hz
    simpa [hinside] using hy_proj.symm

end

end
