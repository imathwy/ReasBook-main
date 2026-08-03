import BauschkeLean.Chap28.Corollary_28_10
import BauschkeLean.Chap04.Proposition_4_16

open Filter
open InnerProductSpace
open scoped Gradient InnerProductSpace Topology

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 28.11 is the relaxed alternating projection recursion `(28.35)` for two
  nonempty closed convex sets `C` and `D`.
- `core/canonical`: the reusable Chapter 5 owner is `relaxedOperatorIteration`.
- `bridge/view`: the source recursion is the constant-family relaxed iteration attached to the
  alternating projection operator `P_C ∘ P_D`, and the minimizing conclusion is best exposed
  through `Argmin[C] (fun x ↦ Metric.infDist x D).toEReal.asEReal`.
-/

section RelaxedAlternatingProjection

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The alternating projection operator `P_C ∘ P_D` associated to nonempty closed convex sets
`C` and `D`. -/
noncomputable def alternatingProjectionOperator
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (D : Set H) (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) : H → H :=
  P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] ∘
    P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex]

/-- Applying `alternatingProjectionOperator` amounts to projecting onto `D` and then onto `C`. -/
@[simp] theorem alternatingProjectionOperator_apply
    {C : Set H} {hC_nonempty : C.Nonempty} {hC_closed : IsClosed C}
    {hC_convex : Convex ℝ C} {D : Set H} {hD_nonempty : D.Nonempty} {hD_closed : IsClosed D}
    {hD_convex : Convex ℝ D} (x : H) :
    alternatingProjectionOperator
        C hC_nonempty hC_closed hC_convex D hD_nonempty hD_closed hD_convex x =
      P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
        (P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x) :=
  rfl

/-- Helper for Example 28.11: the half squared distance to `D` has gradient
`x - P_D x` at every point. -/
private lemma projectionResidual_inner_mono
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (x y : H) :
    ⟪x - P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x,
        y - x⟫_ℝ ≤
      ⟪y - P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] y,
        y - x⟫_ℝ := by
  let P_D : H → H :=
    P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex]
  let p := P_D x
  let q := P_D y
  have hfirm : ‖q - p‖ ^ 2 ≤ ⟪q - p, y - x⟫_ℝ := by
    simpa [P_D, p, q, real_inner_comm] using
      norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
        (C := D) hD_nonempty hD_closed hD_convex y x
  have hqp_le : ‖q - p‖ ≤ ‖y - x‖ := by
    by_cases hqp : q = p
    · simp [hqp]
    · have hqp_pos : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqp)
      have hcs : ⟪q - p, y - x⟫_ℝ ≤ ‖q - p‖ * ‖y - x‖ := real_inner_le_norm _ _
      nlinarith
  have hinner_le : ⟪q - p, y - x⟫_ℝ ≤ ‖y - x‖ ^ 2 := by
    have hcs : ⟪q - p, y - x⟫_ℝ ≤ ‖q - p‖ * ‖y - x‖ := real_inner_le_norm _ _
    nlinarith
  have hres_nonneg : 0 ≤ ⟪(y - q) - (x - p), y - x⟫_ℝ := by
    have hrew : (y - q) - (x - p) = (y - x) - (q - p) := by
      abel_nf
    rw [hrew, inner_sub_left, real_inner_self_eq_norm_sq]
    nlinarith
  simpa [inner_sub_left] using hres_nonneg

/-- Helper for Example 28.11: the first-order remainder of `(1 / 2) d_D^2` is bounded by a
quadratic error. -/
private lemma halfSqInfDist_remainder_bound
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (x y : H) :
    |((1 / 2 : ℝ) * Metric.infDist y D ^ 2 - (1 / 2 : ℝ) * Metric.infDist x D ^ 2 -
        ⟪x - P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x,
          y - x⟫_ℝ)| ≤
      (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
  let P_D : H → H :=
    P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex]
  let p := P_D x
  let q := P_D y
  have hp_mem : p ∈ D := projectionPoint_mem D _ x
  have hq_mem : q ∈ D := projectionPoint_mem D _ y
  have hdistx : Metric.infDist x D = ‖x - p‖ := by
    simpa [P_D, p, dist_eq_norm] using
      (projectionPoint_isBestApproximation D _ x).2.symm
  have hdisty : Metric.infDist y D = ‖y - q‖ := by
    simpa [P_D, q, dist_eq_norm] using
      (projectionPoint_isBestApproximation D _ y).2.symm
  have hmono :
      ⟪x - p, y - x⟫_ℝ ≤ ⟪y - q, y - x⟫_ℝ := by
    simpa [P_D, p, q] using
      projectionResidual_inner_mono
        (H := H) (D := D) hD_nonempty hD_closed hD_convex x y
  have hupper :
      (1 / 2 : ℝ) * Metric.infDist y D ^ 2 ≤
        (1 / 2 : ℝ) * Metric.infDist x D ^ 2 +
          ⟪x - p, y - x⟫_ℝ +
          (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    have hdisty_le : Metric.infDist y D ≤ ‖y - p‖ := by
      simpa [dist_eq_norm, p] using Metric.infDist_le_dist_of_mem hp_mem
    have hsq_le :
        (1 / 2 : ℝ) * Metric.infDist y D ^ 2 ≤ (1 / 2 : ℝ) * ‖y - p‖ ^ 2 := by
      have hdisty_nonneg : 0 ≤ Metric.infDist y D := Metric.infDist_nonneg (x := y) (s := D)
      nlinarith [hdisty_le, hdisty_nonneg, norm_nonneg (y - p)]
    have hexpand :
        (1 / 2 : ℝ) * ‖y - p‖ ^ 2 =
          (1 / 2 : ℝ) * Metric.infDist x D ^ 2 +
            ⟪x - p, y - x⟫_ℝ +
            (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
      have hdecomp : y - p = (y - x) + (x - p) := by
        abel_nf
      rw [hdecomp, norm_add_sq_real, hdistx, real_inner_comm]
      ring
    nlinarith
  have hlower_q :
      (1 / 2 : ℝ) * Metric.infDist x D ^ 2 ≤
        (1 / 2 : ℝ) * Metric.infDist y D ^ 2 -
          ⟪y - q, y - x⟫_ℝ +
          (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    have hdistx_le : Metric.infDist x D ≤ ‖x - q‖ := by
      simpa [dist_eq_norm, q] using Metric.infDist_le_dist_of_mem hq_mem
    have hsq_le :
        (1 / 2 : ℝ) * Metric.infDist x D ^ 2 ≤ (1 / 2 : ℝ) * ‖x - q‖ ^ 2 := by
      have hdistx_nonneg : 0 ≤ Metric.infDist x D := Metric.infDist_nonneg (x := x) (s := D)
      nlinarith [hdistx_le, hdistx_nonneg, norm_nonneg (x - q)]
    have hexpand :
        (1 / 2 : ℝ) * ‖x - q‖ ^ 2 =
          (1 / 2 : ℝ) * Metric.infDist y D ^ 2 -
            ⟪y - q, y - x⟫_ℝ +
            (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
      have hdecomp : x - q = (y - q) - (y - x) := by
        abel_nf
      rw [hdecomp, norm_sub_sq_real, hdisty]
      ring
    nlinarith
  have hlower :
      (1 / 2 : ℝ) * Metric.infDist x D ^ 2 ≤
        (1 / 2 : ℝ) * Metric.infDist y D ^ 2 -
          ⟪x - p, y - x⟫_ℝ +
          (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    linarith
  refine abs_le.mpr ?_
  constructor
  · nlinarith
  · nlinarith

/-- Helper for Example 28.11: the half squared distance to `D` has gradient
`x - P_D x` at every point. -/
private lemma halfSqInfDist_hasGradientAt_sub_projectionPoint
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (x : H) :
    HasGradientAt
      (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2)
      (x - P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x)
      x := by
  rw [hasGradientAt_iff_tendsto]
  have hbound :
      ∀ y : H,
        ‖y - x‖⁻¹ *
            ‖(1 / 2 : ℝ) * Metric.infDist y D ^ 2 - (1 / 2 : ℝ) * Metric.infDist x D ^ 2 -
                ⟪x -
                    P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex]
                      x, y - x⟫_ℝ‖ ≤
          (1 / 2 : ℝ) * ‖y - x‖ := by
    intro y
    have hrem :
        |((1 / 2 : ℝ) * Metric.infDist y D ^ 2 - (1 / 2 : ℝ) * Metric.infDist x D ^ 2 -
            ⟪x -
                P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x,
              y - x⟫_ℝ)| ≤
          (1 / 2 : ℝ) * ‖y - x‖ ^ 2 :=
      halfSqInfDist_remainder_bound
        (H := H) (D := D) hD_nonempty hD_closed hD_convex x y
    have hrem_norm :
        ‖(1 / 2 : ℝ) * Metric.infDist y D ^ 2 - (1 / 2 : ℝ) * Metric.infDist x D ^ 2 -
            ⟪x -
                P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x,
              y - x⟫_ℝ‖ ≤
          (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
      simpa [Real.norm_eq_abs] using hrem
    by_cases hy : y = x
    · simp [hy]
    · have hnorm_ne : ‖y - x‖ ≠ 0 := by
        exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
      have hmul :
          ‖y - x‖⁻¹ *
              ‖(1 / 2 : ℝ) * Metric.infDist y D ^ 2 - (1 / 2 : ℝ) * Metric.infDist x D ^ 2 -
                  ⟪x -
                      P[D,
                          isChebyshev_of_nonempty_isClosed_convex
                            hD_nonempty hD_closed hD_convex] x,
                    y - x⟫_ℝ‖ ≤
            ‖y - x‖⁻¹ * ((1 / 2 : ℝ) * ‖y - x‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hrem_norm (inv_nonneg.mpr (norm_nonneg _))
      calc
        ‖y - x‖⁻¹ *
            ‖(1 / 2 : ℝ) * Metric.infDist y D ^ 2 - (1 / 2 : ℝ) * Metric.infDist x D ^ 2 -
                ⟪x -
                    P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex]
                      x, y - x⟫_ℝ‖ ≤
            ‖y - x‖⁻¹ * ((1 / 2 : ℝ) * ‖y - x‖ ^ 2) :=
          hmul
        _ = (1 / 2 : ℝ) * ‖y - x‖ := by
          rw [pow_two]
          calc
            ‖y - x‖⁻¹ * ((1 / 2 : ℝ) * (‖y - x‖ * ‖y - x‖)) =
                (1 / 2 : ℝ) * (‖y - x‖⁻¹ * ‖y - x‖) * ‖y - x‖ := by
                  ring
            _ = (1 / 2 : ℝ) * 1 * ‖y - x‖ := by
                  rw [inv_mul_cancel₀ hnorm_ne]
            _ = (1 / 2 : ℝ) * ‖y - x‖ := by
                  ring
  have hnorm :
      Filter.Tendsto (fun y : H ↦ ‖y - x‖) (nhds x) (nhds (0 : ℝ)) := by
    have hcont : Continuous fun y : H ↦ ‖y - x‖ := by
      exact continuous_norm.comp
        (continuous_id.sub (continuous_const : Continuous fun _ : H ↦ x))
    simpa using
      (show Filter.Tendsto (fun y : H ↦ ‖y - x‖) (nhds x) (nhds (‖x - x‖)) from
        (hcont.continuousAt : ContinuousAt (fun y : H ↦ ‖y - x‖) x))
  have hupper :
      Filter.Tendsto (fun y : H ↦ (1 / 2 : ℝ) * ‖y - x‖) (nhds x) (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hnorm)
  exact squeeze_zero
    (fun y ↦ mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    hbound
    hupper

/-- Helper for Example 28.11: the gradient of `(1 / 2) d_D^2` is `Id - P_D`. -/
private theorem gradient_halfSqInfDist_eq_sub_projectionPoint
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    ∇ (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2) =
      fun x : H ↦
        x - P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x := by
  -- Promote the pointwise gradient formula to an equality of gradient fields.
  apply gradient_eq
  intro x
  simpa using
    halfSqInfDist_hasGradientAt_sub_projectionPoint
      (H := H) (D := D) hD_nonempty hD_closed hD_convex x

/-- Helper for Example 28.11: for a nonempty closed convex set `D`, the map
`x ↦ Metric.infDist x D` is convex on `Set.univ`. -/
private lemma infDist_convexOn_univ_of_nonempty_isClosed_convex
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    _root_.ConvexOn ℝ Set.univ (fun y : H ↦ Metric.infDist y D) := by
  let hD_cheb := isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
  let P_D : H → H := P[D, hD_cheb]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hPx : P_D x ∈ D := projectionPoint_mem D hD_cheb x
  have hPy : P_D y ∈ D := projectionPoint_mem D hD_cheb y
  have hcombo_mem : a • P_D x + b • P_D y ∈ D := hD_convex hPx hPy ha hb hab
  have hdistx : Metric.infDist x D = ‖x - P_D x‖ := by
    simpa [P_D, dist_eq_norm] using
      (projectionPoint_isBestApproximation D hD_cheb x).2.symm
  have hdisty : Metric.infDist y D = ‖y - P_D y‖ := by
    simpa [P_D, dist_eq_norm] using
      (projectionPoint_isBestApproximation D hD_cheb y).2.symm
  calc
    Metric.infDist (a • x + b • y) D ≤ dist (a • x + b • y) (a • P_D x + b • P_D y) := by
      exact Metric.infDist_le_dist_of_mem hcombo_mem
    _ = ‖a • (x - P_D x) + b • (y - P_D y)‖ := by
      simp [P_D, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ ‖a • (x - P_D x)‖ + ‖b • (y - P_D y)‖ := norm_add_le _ _
    _ = a * ‖x - P_D x‖ + b * ‖y - P_D y‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ = a * Metric.infDist x D + b * Metric.infDist y D := by
      rw [hdistx, hdisty]

/-- Helper for Example 28.11: `(1 / 2) d_D^2` is convex on the whole Hilbert space. -/
private lemma halfSqInfDist_convexOn_univ
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    _root_.ConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2) := by
  have hdist_conv :
      _root_.ConvexOn ℝ Set.univ (fun y : H ↦ Metric.infDist y D) :=
    infDist_convexOn_univ_of_nonempty_isClosed_convex
      (H := H) (D := D) hD_nonempty hD_closed hD_convex
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hdist :
      Metric.infDist (a • x + b • y) D ≤
        a * Metric.infDist x D + b * Metric.infDist y D := by
    simpa [smul_eq_mul] using hdist_conv.2 (by simp) (by simp) ha hb hab
  have hx_nonneg : 0 ≤ Metric.infDist x D := Metric.infDist_nonneg
  have hy_nonneg : 0 ≤ Metric.infDist y D := Metric.infDist_nonneg
  have hxy_nonneg :
      0 ≤ a * Metric.infDist x D + b * Metric.infDist y D := by
    positivity
  have hdist_sq :
      Metric.infDist (a • x + b • y) D ^ 2 ≤
        (a * Metric.infDist x D + b * Metric.infDist y D) ^ 2 := by
    have hdist_nonneg : 0 ≤ Metric.infDist (a • x + b • y) D :=
      Metric.infDist_nonneg (x := a • x + b • y) (s := D)
    nlinarith
  have hsq :
      Metric.infDist (a • x + b • y) D ^ 2 ≤
        a * Metric.infDist x D ^ 2 + b * Metric.infDist y D ^ 2 := by
    have hweighted_sq :
        (a * Metric.infDist x D + b * Metric.infDist y D) ^ 2 ≤
          a * Metric.infDist x D ^ 2 + b * Metric.infDist y D ^ 2 := by
      have hidentity :
          a * Metric.infDist x D ^ 2 + b * Metric.infDist y D ^ 2 -
              (a * Metric.infDist x D + b * Metric.infDist y D) ^ 2 =
            a * b * (Metric.infDist x D - Metric.infDist y D) ^ 2 := by
        have hb_eq : b = 1 - a := by
          linarith
        rw [hb_eq]
        ring
      have hnonneg :
          0 ≤ a * b * (Metric.infDist x D - Metric.infDist y D) ^ 2 := by
        positivity
      linarith
    exact le_trans hdist_sq hweighted_sq
  -- After squaring the convex distance bound, the scalar factor `1 / 2` preserves convexity.
  calc
    (1 / 2 : ℝ) * Metric.infDist (a • x + b • y) D ^ 2
        ≤ (1 / 2 : ℝ) * (a * Metric.infDist x D ^ 2 + b * Metric.infDist y D ^ 2) := by
          gcongr
    _ = a * ((1 / 2 : ℝ) * Metric.infDist x D ^ 2) +
          b * ((1 / 2 : ℝ) * Metric.infDist y D ^ 2) := by
          ring

/-- Helper for Example 28.11: the gradient of `(1 / 2) d_D^2` is `1`-Lipschitz. -/
private lemma lipschitzWith_one_gradient_halfSqInfDist
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    LipschitzWith 1 (∇ (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2)) := by
  have hresidual :
      LipschitzWith 1
        (fun x : H ↦
          x -
            P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    let p :=
      P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] x
    let q :=
      P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] y
    have hproj : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
      simpa [p, q, real_inner_comm] using
        norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
          (C := D) hD_nonempty hD_closed hD_convex x y
    have hsq : ‖(x - p) - (y - q)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hrew : (x - p) - (y - q) = (x - y) - (p - q) := by
        abel_nf
      rw [hrew]
      nlinarith [norm_sub_sq_real (x - y) (p - q), hproj]
    have hnorm : ‖(x - p) - (y - q)‖ ≤ ‖x - y‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
    simpa [one_mul, dist_eq_norm, p, q] using hnorm
  -- Rewrite the residual map back to the gradient field.
  convert hresidual using 1
  funext x
  rw [gradient_halfSqInfDist_eq_sub_projectionPoint
    (H := H) (D := D) hD_nonempty hD_closed hD_convex]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 28.11: if `D` is bounded, then `(1 / 2) d_D^2` is coercive. -/
private lemma coercive_halfSqInfDist_toEReal_of_isBounded
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_bounded : Bornology.IsBounded D) :
    Coercive ((fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2).toEReal.asEReal) := by
  rcases isBounded_iff_forall_norm_le.mp hD_bounded with ⟨R, hR⟩
  rw [coercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  let S : ℝ := R + max (ξ + 1) 2
  have htail :
      ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop, S ≤ ‖x‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun x : H ↦ ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop).eventually_ge_atTop S
  filter_upwards [htail] with x hx
  have hdist_lower : ‖x‖ - R ≤ Metric.infDist x D := by
    rw [Metric.le_infDist hD_nonempty]
    intro y hyD
    have hy_norm : ‖y‖ ≤ R := hR y hyD
    calc
      ‖x‖ - R ≤ ‖x‖ - ‖y‖ := by linarith
      _ ≤ ‖x - y‖ := by
            have htriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
              calc
                ‖x‖ = ‖(x - y) + y‖ := by abel_nf
                _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
            linarith
      _ = dist x y := by rw [dist_eq_norm]
  have hmax_le : max (ξ + 1) 2 ≤ Metric.infDist x D := by
    dsimp [S] at hx
    linarith
  have hhalf_lower : ξ + 1 ≤ (1 / 2 : ℝ) * Metric.infDist x D ^ 2 := by
    have htwo_le : (2 : ℝ) ≤ Metric.infDist x D := by
      exact le_trans (le_max_right (ξ + 1) 2) hmax_le
    have hdist_nonneg : 0 ≤ Metric.infDist x D := Metric.infDist_nonneg
    have hxi_le : ξ + 1 ≤ Metric.infDist x D := by
      exact le_trans (le_max_left (ξ + 1) 2) hmax_le
    have hdist_le_half_sq : Metric.infDist x D ≤ (1 / 2 : ℝ) * Metric.infDist x D ^ 2 := by
      nlinarith
    exact le_trans hxi_le hdist_le_half_sq
  have hlt_real : ξ < (1 / 2 : ℝ) * Metric.infDist x D ^ 2 := by
    linarith
  have hlt_ereal :
      ((ξ : ℝ) : EReal) <
        ((((1 / 2 : ℝ) * Metric.infDist x D ^ 2 : ℝ) : EReal)) := by
    exact_mod_cast hlt_real
  simpa [Function.toEReal_apply, Function.asEReal_apply] using hlt_ereal

/-- Helper for Example 28.11: the half squared-distance objective has a constrained minimizer as
soon as `C` or `D` is bounded. -/
private theorem argminOn_nonempty_halfSqInfDist_of_bounded_or_boundedTarget
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hbounded : Bornology.IsBounded C ∨ Bornology.IsBounded D) :
    (Argmin[C]
      ((fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2).toEReal.asEReal) : Set H).Nonempty := by
  have hcont : Continuous (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2) := by
    -- The distance map is continuous, hence so is its half squared profile.
    exact continuous_const.mul ((Metric.continuous_infDist_pt D).pow 2)
  have hgammaZero :
      (fun y : H ↦ ((1 / 2 : ℝ) * Metric.infDist y D ^ 2)).toEReal ∈ Γ₀(H) := by
    simpa using
      real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
        (H := H)
        (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2)
        hcont
        (halfSqInfDist_convexOn_univ (H := H) (D := D) hD_nonempty hD_closed hD_convex)
  have hcase :
      Coercive ((fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2).toEReal.asEReal) ∨
        Bornology.IsBounded C := by
    rcases hbounded with hC_bounded | hD_bounded
    · exact Or.inr hC_bounded
    · exact Or.inl <|
        coercive_halfSqInfDist_toEReal_of_isBounded (H := H) (D := D) hD_nonempty hD_bounded
  -- Proposition 11.15 now applies to the smooth owner objective.
  simpa using
    argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded
      (H := H)
      hgammaZero
      hC_closed
      hC_convex
      hC_nonempty
      hcase

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 28.11: minimizing `(1 / 2) d_D^2` over `C` is equivalent to minimizing
`d_D` over `C`. -/
private lemma mem_argminOn_halfSqInfDist_iff_mem_argminOn_infDist
    {C : Set H} {D : Set H} {p : H} :
    p ∈ Argmin[C] ((fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2).toEReal.asEReal) ↔
      p ∈ Argmin[C] ((fun y : H ↦ Metric.infDist y D).toEReal.asEReal) := by
  constructor
  · intro hp
    rcases mem_argminOn_iff.mp hp with ⟨hpC, hpmin⟩
    refine mem_argminOn_iff.mpr ⟨hpC, ?_⟩
    rw [isMinOn_iff] at hpmin ⊢
    intro y hyC
    have hsq :
        (((1 / 2 : ℝ) * Metric.infDist p D ^ 2 : ℝ) : EReal) ≤
          (((1 / 2 : ℝ) * Metric.infDist y D ^ 2 : ℝ) : EReal) := by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using hpmin y hyC
    have hsq_real :
        (1 / 2 : ℝ) * Metric.infDist p D ^ 2 ≤ (1 / 2 : ℝ) * Metric.infDist y D ^ 2 := by
      exact_mod_cast hsq
    have hp_nonneg : 0 ≤ Metric.infDist p D := Metric.infDist_nonneg
    have hy_nonneg : 0 ≤ Metric.infDist y D := Metric.infDist_nonneg
    have hdist_real : Metric.infDist p D ≤ Metric.infDist y D := by
      nlinarith
    simpa [Function.asEReal_apply, Function.toEReal_apply] using
      (show (((Metric.infDist p D : ℝ) : EReal)) ≤ (((Metric.infDist y D : ℝ) : EReal)) from by
        exact_mod_cast hdist_real)
  · intro hp
    rcases mem_argminOn_iff.mp hp with ⟨hpC, hpmin⟩
    refine mem_argminOn_iff.mpr ⟨hpC, ?_⟩
    rw [isMinOn_iff] at hpmin ⊢
    intro y hyC
    have hdist :
        (((Metric.infDist p D : ℝ) : EReal)) ≤ (((Metric.infDist y D : ℝ) : EReal)) := by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using hpmin y hyC
    have hdist_real : Metric.infDist p D ≤ Metric.infDist y D := by
      exact_mod_cast hdist
    have hp_nonneg : 0 ≤ Metric.infDist p D := Metric.infDist_nonneg
    have hy_nonneg : 0 ≤ Metric.infDist y D := Metric.infDist_nonneg
    have hsq_real :
        (1 / 2 : ℝ) * Metric.infDist p D ^ 2 ≤ (1 / 2 : ℝ) * Metric.infDist y D ^ 2 := by
      nlinarith
    have hsq :
        (((1 / 2 : ℝ) * Metric.infDist p D ^ 2 : ℝ) : EReal) ≤
          (((1 / 2 : ℝ) * Metric.infDist y D ^ 2 : ℝ) : EReal) := by
      exact_mod_cast hsq_real
    simpa [Function.asEReal_apply, Function.toEReal_apply] using hsq

/-- Example 28.11: let `C` and `D` be nonempty closed convex subsets of a real Hilbert space, let
`(λ_n)` lie in `[0, 3 / 2]` with `∑ λ_n (3 - 2 λ_n) = +∞`, and suppose that `C` or `D` is
bounded. Then the relaxed alternating projection recursion `(28.35)` converges weakly to a point
of `Argmin[C] (fun x ↦ Metric.infDist x D).toEReal.asEReal`. -/
theorem relaxedAlternatingProjection_exists_weakLimit_mem_argminOn_infDist
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (3 / 2))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (3 - 2 * lam n)))
        atTop atTop)
    (hbounded : Bornology.IsBounded C ∨ Bornology.IsBounded D)
    (x0 : H) :
    let f : H → ℝ := fun x ↦ Metric.infDist x D
    let T :=
      alternatingProjectionOperator
        C hC_nonempty hC_closed hC_convex D hD_nonempty hD_closed hD_convex
    let x := relaxedOperatorIteration (fun _ : ℕ ↦ T) lam x0
    ∃ p ∈ Argmin[C] f.toEReal.asEReal,
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H p)) := by
  dsimp
  let g : H → ℝ := fun y ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2
  let T :=
    alternatingProjectionOperator
      C hC_nonempty hC_closed hC_convex D hD_nonempty hD_closed hD_convex
  let x := relaxedOperatorIteration (fun _ : ℕ ↦ T) lam x0
  let β : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let γ : PosReal := ⟨1, by norm_num⟩
  have hconv : _root_.ConvexOn ℝ Set.univ g := by
    -- The smooth owner is the convex half squared-distance objective.
    simpa [g] using
      halfSqInfDist_convexOn_univ (H := H) (D := D) hD_nonempty hD_closed hD_convex
  have hdiff : Differentiable ℝ g := by
    intro z
    -- Differentiability comes from the explicit pointwise gradient formula.
    exact
      (halfSqInfDist_hasGradientAt_sub_projectionPoint
        (H := H) (D := D) hD_nonempty hD_closed hD_convex z).differentiableAt
  have hgrad_lipschitz :
      LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) (∇ g) := by
    -- Corollary 4.18 gives the `1`-Lipschitz gradient field after identifying `∇ g = Id - P_D`.
    simpa [g, β] using
      lipschitzWith_one_gradient_halfSqInfDist
        (H := H) (D := D) hD_nonempty hD_closed hD_convex
  have hγ_lt : (γ : ℝ) < 2 * (β : ℝ) := by
    norm_num [β, γ]
  have hlam_pg :
      ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (2 - (γ : ℝ) / (2 * (β : ℝ))) := by
    intro n
    rcases hlam n with ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    norm_num [β, γ] at h1 ⊢
    exact h1
  have hdiv_pg :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * ((2 - (γ : ℝ) / (2 * (β : ℝ))) - lam n)))
        atTop atTop := by
    -- The Chapter 28 divergence hypothesis differs from the source one by the factor `1 / 2`.
    convert hdiv.const_mul_atTop (by norm_num : 0 < (1 / 2 : ℝ)) using 1
    ext N
    simp [β, γ, Finset.mul_sum]
    ring
  have hargmin :
      (Argmin[C] g.toEReal.asEReal : Set H).Nonempty :=
    argminOn_nonempty_halfSqInfDist_of_bounded_or_boundedTarget
      (H := H)
      hC_nonempty
      hC_closed
      hC_convex
      hD_nonempty
      hD_closed
      hD_convex
      hbounded
  have hOrbit :
      IsProjectionGradientOrbit
        g
        C
        hC_nonempty
        hC_closed
        hC_convex
        (γ : ℝ)
        lam
        x0
        x := by
    refine ⟨by simp [x], ?_⟩
    intro n
    have hstep :
        x n - (γ : ℝ) • ∇ g (x n) =
          P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] (x n) := by
      -- Rewrite the projected-gradient forward step as the projector onto `D`.
      change
        x n - (γ : ℝ) • ∇ (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y D ^ 2) (x n) =
          P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex] (x n)
      rw [gradient_halfSqInfDist_eq_sub_projectionPoint
        (H := H) (D := D) hD_nonempty hD_closed hD_convex]
      simp [γ]
    have hstep_congr :
        x n +
            lam n •
              (P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
                  (x n - (γ : ℝ) • ∇ g (x n)) -
                x n) =
          x n +
            lam n •
              (P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
                  (P[D, isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex]
                    (x n)) -
                x n) := by
      simpa using congrArg
        (fun z : H ↦
          x n +
            lam n •
              (P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] z -
                x n))
        hstep
    -- The relaxed operator recursion is exactly the projection-gradient orbit with `γ = 1`.
    rw [show x (n + 1) = relaxedOperatorIteration (fun _ : ℕ ↦ T) lam x0 (n + 1) by rfl]
    rw [relaxedOperatorIteration_succ]
    simp only [T, alternatingProjectionOperator_apply]
    simpa [x, T, γ] using hstep_congr.symm
  rcases
      projectionGradient_exists_weakLimit_mem_argminOn
        (C := C)
        (hC_nonempty := hC_nonempty)
        (hC_closed := hC_closed)
        (hC_convex := hC_convex)
        (f := g)
        (β := β)
        (γ := γ)
        (lam := lam)
        (x0 := x0)
        hconv
        hdiff
        hgrad_lipschitz
        hγ_lt
        hlam_pg
        hdiv_pg
        hargmin
        hOrbit
    with ⟨p, hp, hp_tendsto⟩
  have hp_infDist :
      p ∈ Argmin[C] (fun y : H ↦ Metric.infDist y D).toEReal.asEReal := by
    -- The constrained minimizers of `g` are exactly the constrained nearest points to `D`.
    exact
      (mem_argminOn_halfSqInfDist_iff_mem_argminOn_infDist
        (C := C) (D := D)).1 hp
  exact ⟨p, hp_infDist, hp_tendsto⟩

/-- Source-facing reformulation of Example 28.11: the weak limit point minimizes
`x ↦ Metric.infDist x D` over `C`. -/
theorem relaxedAlternatingProjection_exists_weakLimit_minimizing_infDistOn
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) (3 / 2))
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (3 - 2 * lam n)))
        atTop atTop)
    (hbounded : Bornology.IsBounded C ∨ Bornology.IsBounded D)
    (x0 : H) :
    let f : H → ℝ := fun x ↦ Metric.infDist x D
    let T :=
      alternatingProjectionOperator
        C hC_nonempty hC_closed hC_convex D hD_nonempty hD_closed hD_convex
    let x := relaxedOperatorIteration (fun _ : ℕ ↦ T) lam x0
    ∃ p ∈ C,
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H p)) ∧
        ∀ y ∈ C, f p ≤ f y := by
  dsimp
  rcases
      relaxedAlternatingProjection_exists_weakLimit_mem_argminOn_infDist
        (H := H)
        (C := C)
        hC_nonempty
        hC_closed
        hC_convex
        (D := D)
        hD_nonempty
        hD_closed
        hD_convex
        lam
        hlam
        hdiv
        hbounded
        x0
    with ⟨p, hp, hp_tendsto⟩
  rcases mem_argminOn_iff.mp hp with ⟨hpC, hpmin⟩
  refine ⟨p, hpC, hp_tendsto, ?_⟩
  -- Unpack the constrained argmin condition into the source-facing minimizing inequality.
  intro y hyC
  have hmin :
      (((Metric.infDist p D : ℝ) : EReal)) ≤ (((Metric.infDist y D : ℝ) : EReal)) :=
    (isMinOn_iff.mp hpmin) y hyC
  exact_mod_cast hmin

end RelaxedAlternatingProjection

end ERealFunction
