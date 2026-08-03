import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap29.Definition_29_40

open ERealFunction
open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (C : Set H) (p : ℝ)
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

-- Semantic recall: `lean_leansearch` only surfaced generic orthogonal-projection owners, so this
-- item uses the Chapter 29 differentiable projector formula together with the established metric
-- projection notation `P[C, hC]`.
local notation "P_C" =>
  P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]

/-- The gradient field of `x ↦ d(x, C)^p` away from `C`, extended by `0` on `C`. -/
noncomputable def distancePowerGradient : H → H :=
  let _ : DecidablePred (· ∈ C) := Classical.decPred C
  fun x ↦
    if x ∈ C then
      0
    else
      (p * Metric.infDist x C ^ (p - 2)) • (x - P_C x)

/-- The source-facing differentiable subgradient projector associated with `(d_C^p, 0)`. -/
noncomputable def distancePowerSubgradientProjector : H → H :=
  fun x ↦
    if 0 < Metric.infDist x C ^ p then
      x +
        (((0 : ℝ) - Metric.infDist x C ^ p) /
            ‖distancePowerGradient C p hC_nonempty hC_closed hC_convex x‖ ^ 2) •
          distancePowerGradient C p hC_nonempty hC_closed hC_convex x
    else
      x

/-- Helper for Example 29.43: every point already in `C` is fixed by the metric projection
`P_C`. -/
lemma projectionPoint_eq_self_of_mem
    {x : H} (hx : x ∈ C) :
    P_C x = x := by
  -- A point of `C` is itself a best approximation because its distance to `C` is zero.
  have hx_proj : x = P_C x := by
    refine eq_projectionPoint_of_isBestApproximation C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) ?_
    exact ⟨hx, by simp [Metric.infDist_zero_of_mem hx]⟩
  exact hx_proj.symm

/-- Helper for Example 29.43: the norm of the projection residual is exactly the distance to
`C`. -/
lemma projection_residual_norm_eq_infDist
    (x : H) :
    ‖x - P_C x‖ = Metric.infDist x C := by
  -- The chosen projection point realizes the infimum distance by definition.
  simpa [dist_eq_norm] using
    (projectionPoint_isBestApproximation C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x).2

/-- Helper for Example 29.43: away from `C`, the subgradient-projector formula reduces to the
displayed affine combination of `x` and `P_C x`. -/
lemma distancePowerSubgradientProjector_apply_of_not_mem
    (hp : 1 ≤ p) {x : H} (hx : x ∉ C) :
    distancePowerSubgradientProjector C p hC_nonempty hC_closed hC_convex x =
      (1 - 1 / p) • x + (1 / p) • P_C x := by
  let d : ℝ := Metric.infDist x C
  have hdist_pos : 0 < d := by
    simpa [d] using (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hd_ne : d ≠ 0 := ne_of_gt hdist_pos
  have hdp2_ne : d ^ (p - 2) ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos hdist_pos _)
  have hscalar_pos : 0 < p * d ^ (p - 2) := by
    positivity
  have hgrad :
      distancePowerGradient C p hC_nonempty hC_closed hC_convex x =
        (p * d ^ (p - 2)) • (x - P_C x) := by
    -- Outside `C`, `distancePowerGradient` is exactly the explicit residual field.
    simp [distancePowerGradient, hx, d]
  have hnorm_sq :
      ‖distancePowerGradient C p hC_nonempty hC_closed hC_convex x‖ ^ 2 =
        ((p * d ^ (p - 2)) * d) ^ 2 := by
    -- The projection residual norm rewrites the denominator in terms of `d = infDist x C`.
    have hresid : ‖x - P_C x‖ = d := by
      simpa [d] using
        projection_residual_norm_eq_infDist
          (C := C) (hC_nonempty := hC_nonempty)
          (hC_closed := hC_closed) (hC_convex := hC_convex) x
    rw [hgrad, norm_smul, Real.norm_of_nonneg hscalar_pos.le,
      hresid]
  have hscaled_norm_sq :
      ‖(p * d ^ (p - 2)) • (x - P_C x)‖ ^ 2 =
        ((p * d ^ (p - 2)) * d) ^ 2 := by
    -- Re-express the denominator after unfolding the active branch of the gradient field.
    simpa [hgrad] using hnorm_sq
  have hd_split : d ^ p = d ^ (p - 2) * d ^ (2 : ℝ) := by
    -- This is the scalar identity `d^p = d^(p-2) d^2` used for cancellation.
    calc
      d ^ p = d ^ ((p - 2) + 2) := by congr 1; ring
      _ = d ^ (p - 2) * d ^ (2 : ℝ) := by rw [Real.rpow_add hdist_pos]
  have hcoeff :
      (((0 : ℝ) - d ^ p) / (((p * d ^ (p - 2)) * d) ^ 2)) * (p * d ^ (p - 2)) =
        -(1 / p) := by
    rw [zero_sub, hd_split, Real.rpow_two]
    field_simp [hp_ne, hd_ne, hdp2_ne]
  -- With the scalar coefficient identified, the vector expression is just affine algebra.
  calc
    distancePowerSubgradientProjector C p hC_nonempty hC_closed hC_convex x
        =
      x + ((((0 : ℝ) - d ^ p) / (((p * d ^ (p - 2)) * d) ^ 2)) •
          ((p * d ^ (p - 2)) • (x - P_C x))) := by
        rw [distancePowerSubgradientProjector]
        simp [hgrad, hscaled_norm_sq, d, Real.rpow_pos_of_pos hdist_pos p]
    _ =
      x +
        ((((0 : ℝ) - d ^ p) / (((p * d ^ (p - 2)) * d) ^ 2)) * (p * d ^ (p - 2))) •
          (x - P_C x) := by
            rw [smul_smul]
    _ = x + (-(1 / p)) • (x - P_C x) := by rw [hcoeff]
    _ = x + (-((1 / p) • x) + (1 / p) • P_C x) := by
      simp [sub_eq_add_neg]
    _ = (x + (-(1 / p)) • x) + (1 / p) • P_C x := by
      simp [add_assoc, neg_smul]
    _ = ((1 : ℝ) • x + (-(1 / p)) • x) + (1 / p) • P_C x := by rw [one_smul]
    _ = ((1 : ℝ) + (-(1 / p))) • x + (1 / p) • P_C x := by rw [← add_smul]
    _ = (1 - 1 / p) • x + (1 / p) • P_C x := by ring_nf

/-- Example 29.43: if `C` is a nonempty closed convex subset of a real Hilbert space and
`p ∈ [1, +∞[`, then the subgradient projector onto `C` associated with `(d_C^p, 0)` is
`(1 - 1 / p) Id + (1 / p) P_C`. -/
theorem distancePowerSubgradientProjector_eq_affine_projection (hp : 1 ≤ p) :
    distancePowerSubgradientProjector C p hC_nonempty hC_closed hC_convex =
      fun x ↦ (1 - 1 / p) • x + (1 / p) • P_C x := by
  funext x
  by_cases hx : x ∈ C
  · -- On the zero-level branch, both the projector and the affine formula fix `x`.
    have hx_level :
        x ∈ lowerLevelSet (fun y : H ↦ Metric.infDist y C ^ p).toEReal.asEReal 0 := by
      rw [mem_lowerLevelSet_iff]
      simpa [Function.asEReal_apply, Function.toEReal_apply, Metric.infDist_zero_of_mem hx,
        Real.zero_rpow (by exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp))]
    have hfixed_rhs : (1 - 1 / p) • x + (1 / p) • P_C x = x := by
      calc
        (1 - 1 / p) • x + (1 / p) • P_C x
            = ((1 - 1 / p) + (1 / p)) • x := by
                rw [projectionPoint_eq_self_of_mem
                  (C := C) (hC_nonempty := hC_nonempty)
                  (hC_closed := hC_closed) (hC_convex := hC_convex) hx, ← add_smul]
        _ = (1 : ℝ) • x := by ring_nf
        _ = x := by simp
    calc
      distancePowerSubgradientProjector C p hC_nonempty hC_closed hC_convex x = x := by
        have hfx : Metric.infDist x C ^ p ≤ 0 := by
          simpa [Function.toEReal_apply] using
            (mem_lowerLevelSet_iff (fun y : H ↦ Metric.infDist y C ^ p).toEReal.asEReal 0 x).1
              hx_level
        simp [distancePowerSubgradientProjector, not_lt.mpr hfx]
      _ = (1 - 1 / p) • x + (1 / p) • P_C x := by simpa using hfixed_rhs.symm
  · -- Outside `C`, the explicit residual formula gives the claimed affine combination.
    exact distancePowerSubgradientProjector_apply_of_not_mem
      (C := C) (p := p) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
      (hC_convex := hC_convex) hp hx

/-- If `p ∈ [1, +∞[`, evaluating `distancePowerSubgradientProjector` at `x` gives the displayed
affine combination of `x` and its metric projection onto `C`. -/
@[simp] theorem distancePowerSubgradientProjector_apply (hp : 1 ≤ p) (x : H) :
    distancePowerSubgradientProjector C p hC_nonempty hC_closed hC_convex x =
      (1 - 1 / p) • x + (1 / p) • P_C x := by
  -- The pointwise formula is just the function equality from Example 29.43 evaluated at `x`.
  exact congrArg (fun f : H → H ↦ f x)
    (distancePowerSubgradientProjector_eq_affine_projection
      C p hC_nonempty hC_closed hC_convex hp)

end
