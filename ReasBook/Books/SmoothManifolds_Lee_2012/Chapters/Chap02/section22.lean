import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_2_22 (from Chap02/Sec02_10) -/
open Metric
open scoped ContDiff

variable {r₁ r₂ : ℝ}
variable {n : ℕ}

/-- Helper for Lemma 2.22: away from the origin, a radial reparameterization of a smooth scalar
cutoff is smooth by composition with the norm map. -/
private lemma radial_cutoff_contDiffAt_ne_zero {h : ℝ → ℝ} (hh_smooth : ContDiff ℝ ∞ h)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ h ‖y‖) x := by
  -- Away from `0`, the norm map is smooth, so the radial cutoff is a smooth composition.
  exact hh_smooth.contDiffAt.comp x (contDiffAt_norm (𝕜 := ℝ) hx)

/-- Helper for Lemma 2.22: if the scalar cutoff is identically `1` on `[0, r₁]`, then the radial
cutoff is smooth at the origin because it agrees nearby with the constant function `1`. -/
private lemma radial_cutoff_contDiffAt_zero {h : ℝ → ℝ} (hr₁ : 0 < r₁)
    (hh_one : ∀ ⦃t : ℝ⦄, t ≤ r₁ → h t = 1) :
    ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ h ‖y‖) 0 := by
  -- On the ball of radius `r₁`, the radial function agrees with the constant function `1`.
  have hconst : ContDiffAt ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ)) 0 := contDiffAt_const
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hr₁] with y hy
  have hy_norm : ‖y‖ < r₁ := by
    simpa [mem_ball_zero_iff] using hy
  -- The scalar cutoff is already in its constant region throughout this neighborhood.
  simpa using hh_one hy_norm.le

/-- Helper for Lemma 2.22: membership in the annulus between the two concentric balls is exactly
the pair of norm inequalities needed by the one-variable cutoff. -/
private lemma mem_annulus_iff_norm_bounds {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ ball 0 r₂ \ closedBall 0 r₁ ↔ r₁ < ‖x‖ ∧ ‖x‖ < r₂ := by
  constructor
  · intro hx
    constructor
    · -- Exclusion from the inner closed ball forces the lower norm bound.
      simpa [mem_closedBall_zero_iff, not_le] using hx.2
    · -- Membership in the outer ball gives the upper norm bound.
      simpa [mem_ball_zero_iff] using hx.1
  · intro hx
    constructor
    · -- The upper norm bound puts the point in the outer ball.
      simpa [mem_ball_zero_iff] using hx.2
    · -- The lower norm bound excludes the point from the inner closed ball.
      simpa [mem_closedBall_zero_iff, not_le] using hx.1

/-- Helper for Lemma 2.22: once the scalar cutoff has vanished on `[r₂, ∞)`, the radial cutoff
vanishes outside the ball of radius `r₂`. -/
private lemma radial_cutoff_eq_zero_of_not_mem_ball {h : ℝ → ℝ}
    (hh_zero : ∀ ⦃t : ℝ⦄, r₂ ≤ t → h t = 0) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ ball 0 r₂) : h ‖x‖ = 0 := by
  have hx_norm : r₂ ≤ ‖x‖ := by
    -- Outside the outer ball, the radial variable has already reached the zero region.
    exact not_lt.mp (by simpa [mem_ball_zero_iff] using hx)
  exact hh_zero hx_norm

/-- Lemma 2.22: given positive real numbers `r₁ < r₂`, there exists a smooth function
`H : ℝ^n → ℝ` that is `1` on the closed ball of radius `r₁`, strictly between `0` and `1` on the
annulus between radii `r₁` and `r₂`, and `0` outside the open ball of radius `r₂`.

This follows Lee's radial construction `H x = h ‖x‖` using the one-variable cutoff from
Lemma 2.21. -/
theorem exists_smooth_ball_cutoff (n : ℕ) (hr₁ : 0 < r₁) (hr : r₁ < r₂) :
    ∃ H : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ H ∧
      (∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ closedBall 0 r₁ → H x = 1) ∧
      (∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄,
        x ∈ ball 0 r₂ \ closedBall 0 r₁ → 0 < H x ∧ H x < 1) ∧
      ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∉ ball 0 r₂ → H x = 0 := by
  rcases exists_one_zero_smooth_cutoff (r₁ := r₁) (r₂ := r₂) hr with
    ⟨h, hh_smooth, hh_one, hh_between, hh_zero⟩
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ h ‖x‖
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · -- Split smoothness into the origin and non-origin cases, exactly as in the source proof.
    refine contDiff_iff_contDiffAt.2 ?_
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simpa [H] using radial_cutoff_contDiffAt_zero (n := n) hr₁ hh_one
    · simpa [H] using radial_cutoff_contDiffAt_ne_zero (n := n) hh_smooth hx
  · intro x hx
    -- On the inner closed ball, the radial parameter lies in the `h = 1` region.
    have hx_norm : ‖x‖ ≤ r₁ := by
      simpa [mem_closedBall_zero_iff] using hx
    simpa [H] using hh_one hx_norm
  · intro x hx
    -- Annulus membership translates directly into the open interval where `h` lies in `(0, 1)`.
    have hx_bounds : r₁ < ‖x‖ ∧ ‖x‖ < r₂ := (mem_annulus_iff_norm_bounds (n := n)).1 hx
    simpa [H] using hh_between hx_bounds.1 hx_bounds.2
  · intro x hx
    -- Outside the outer ball, the scalar cutoff has already vanished.
    simpa [H] using radial_cutoff_eq_zero_of_not_mem_ball (n := n) (r₂ := r₂) hh_zero hx
