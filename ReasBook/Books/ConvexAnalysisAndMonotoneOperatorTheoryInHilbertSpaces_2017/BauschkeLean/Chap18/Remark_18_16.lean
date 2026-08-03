import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap17.Example_17_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContinuousLinearMap Gradient InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → ℝ} {x : H}

/- Source/core/bridge triage:
- `source-facing`: Remark 18.16 is the explicit affine lower model and quadratic upper model at a
  base point `x`, together with the touching and gradient identities of those two models.
- `core/canonical`: the project owners are Proposition 17.6's
  `gateauxGradient_mem_subdifferential`, the Chapter 17 quadratic owner `q[A]`, clause `(iii)` of
  `frechetDifferentiable_tfae_lipschitz_gradient`, and mathlib's `HasGradientAt`.
- `bridge/view`: the explicit model formulas below are thin companions obtained by unpacking the
  canonical owners at the fixed point `x`.
-/

-- Primitive data for Remark 18.16 are the affine model itself and the chapter-level quadratic
-- owner `q[ContinuousLinearMap.id ℝ H]`; the inequalities, touching identities, and gradient
-- formulas below are derived API.
/-- The affine first-order model in Remark 18.16 of `f` at the base point `x`. -/
def gradientAffineModel (f : H → ℝ) (x : H) : H → ℝ :=
  fun y ↦ f x + ⟪y - x, ∇ f x⟫_ℝ

/- Companion recall: the affine lower-model owner behind Remark 18.16 is exactly Proposition 17.6's
canonical subdifferential-membership theorem for a Gâteaux gradient. -/
recall gateauxGradient_mem_subdifferential

omit [CompleteSpace H] in
/-- Helper for Remark 18 16: viewing a real convex function as `EReal`-valued preserves convexity
on the effective domain. -/
private lemma real_convexOn_toEReal_effectiveDomain
    (hconv : _root_.ConvexOn ℝ Set.univ f) :
    ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A real-valued function stays finite after coercion to `EReal`.
    simp [Function.effectiveDomain_toEReal]
  · -- Hence every effective-domain point is immediate.
    simp [Function.effectiveDomain_toEReal]
  · -- Rewrite the `EReal` convexity inequality back to the real-valued one.
    intro y hy z hz a ha0 ha1
    have hreal :
        f (a • y + (1 - a) • z) ≤ a * f y + (1 - a) * f z := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le)
    change ((f (a • y + (1 - a) • z) : ℝ) : EReal) ≤
      ((a * f y + (1 - a) * f z : ℝ) : EReal)
    exact_mod_cast hreal

/-- Helper for Remark 18 16: a real gradient gives the Gâteaux derivative required by the
extended-real subdifferential owner. -/
private lemma hasGateauxDerivativeAt_toEReal_toReal_of_hasGradientAt
    {g : H → ℝ} {x grad : H} (hgrad : HasGradientAt g grad x) :
    HasGateauxDerivativeAt
      (fun z ↦ (g.toEReal z : EReal).toReal)
      (InnerProductSpace.toDualMap ℝ H grad) x := by
  -- First package the gradient as a Fréchet derivative in the Hilbert-space dual.
  have hFDeriv : HasFDerivAt g (InnerProductSpace.toDual ℝ H grad) x :=
    hgrad.hasFDerivAt
  -- Then convert the resulting whole-space Fréchet derivative into a Gâteaux derivative.
  have hGateaux : HasGateauxDerivativeAt g (InnerProductSpace.toDual ℝ H grad) x :=
    hFDeriv.hasGateauxDerivativeAt
  -- Finally identify the finite `EReal` representative and the `toDualMap` notation.
  simpa [Function.toEReal_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hGateaux

omit [CompleteSpace H] in
/-- Helper for Remark 18 16: the translated quadratic correction vanishes at the base point. -/
private lemma gradient_quadratic_remainder_eq_basePoint {β : ℝ} :
    β * q[(ContinuousLinearMap.id ℝ H)] (x - x) = 0 := by
  -- At `x`, the displacement is zero, so the quadratic term is zero.
  simp [ContinuousLinearMap.quadraticPotential_apply, ContinuousLinearMap.id_apply]

/-- Helper for Remark 18 16: the displayed quadratic model is the canonical
`f x + ⟪y - x, ∇ f x⟫ + (β / 2) ‖x - y‖²` expression from Theorem 18.15(iii). -/
private lemma gradient_quadratic_model_normal_form {β : Set.Ioi (0 : ℝ)} (y : H) :
    gradientAffineModel f x y + (β : ℝ) * q[(ContinuousLinearMap.id ℝ H)] (y - x) =
      f x + ⟪y - x, ∇ f x⟫_ℝ + ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  -- Normalize the quadratic owner `q[id]` into the norm-square formula used by clause `(iii)`.
  rw [gradientAffineModel, ContinuousLinearMap.quadraticPotential_apply,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, norm_sub_rev]
  ring

/-- Helper for Remark 18 16: the translated quadratic correction has zero gradient at the base
point. -/
private lemma hasGradientAt_scaled_shifted_quadraticPotential_zero_at_basePoint {β : ℝ} :
    HasGradientAt (fun y ↦ β * q[(ContinuousLinearMap.id ℝ H)] (y - x)) 0 x := by
  have hsub :
      HasFDerivAt (fun y : H ↦ y + (-x)) (ContinuousLinearMap.id ℝ H) x := by
    -- Translation by a constant does not change the derivative.
    simpa using (ContinuousLinearMap.id ℝ H).hasFDerivAt.add_const (-x)
  have hnorm_sq_zero :
      HasFDerivAt
        (fun y : H ↦ (β / 2 : ℝ) * ‖y‖ ^ (2 : ℕ))
        (0 : H →L[ℝ] ℝ)
        (x + (-x)) := by
    -- At the origin, the norm-square gradient vanishes.
    simpa [pow_two] using
      (hasStrictFDerivAt_norm_sq (0 : H)).hasFDerivAt.const_smul (β / 2 : ℝ)
  have hShiftedNormSq :
      HasFDerivAt
        (fun y : H ↦ (β / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ))
        (0 : H →L[ℝ] ℝ) x := by
    -- Compose the norm-square derivative with the translation `y ↦ y - x`.
    simpa [sub_eq_add_neg] using hnorm_sq_zero.comp x hsub
  have hQuadratic :
      HasFDerivAt
        (fun y ↦ β * q[(ContinuousLinearMap.id ℝ H)] (y - x))
        (0 : H →L[ℝ] ℝ) x := by
    -- Identify the quadratic owner with the translated half-norm-square.
    convert hShiftedNormSq using 1
    ext y
    simp [ContinuousLinearMap.quadraticPotential_apply, ContinuousLinearMap.id_apply]
    ring
  -- At the base point, the derivative linear form is zero, so the gradient is zero.
  simpa using hQuadratic.hasGradientAt

/-- Helper for Remark 18 16: composing `f` with the affine segment from `x` to `y` differentiates
to the gradient paired with the segment direction `y - x`. -/
private lemma hasDerivAt_comp_lineMap
    (hdiff : Differentiable ℝ f) (y : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s))
      ⟪y - x, ∇ f (AffineMap.lineMap x y t)⟫_ℝ t := by
  have hf :
      HasFDerivAt f (InnerProductSpace.toDual ℝ H (∇ f (AffineMap.lineMap x y t)))
        (AffineMap.lineMap x y t) :=
    (hdiff (AffineMap.lineMap x y t)).hasGradientAt.hasFDerivAt
  have hline : HasDerivAt (AffineMap.lineMap x y) (y - x) t :=
    AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)
  have hlineF :
      HasFDerivAt (AffineMap.lineMap x y)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (y - x)) t :=
    hline.hasFDerivAt
  simpa [Function.comp, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    (hf.comp t hlineF).hasDerivAt

-- Proof sketch: specialize the canonical owner `gateauxGradient_mem_subdifferential` to the
-- differentiable convex real-valued function `f`, then unfold subdifferential membership.
/-- Remark 18 16: the affine first-order model at `x` determined by the gradient of `f`
minorizes `f` everywhere. -/
theorem gradient_affine_model_le_of_differentiable_convex
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f) (y : H) :
    gradientAffineModel f x y ≤ f y := by
  have hconv_toEReal :
      ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    real_convexOn_toEReal_effectiveDomain (f := f) hconv
  have hx : x ∈ effectiveDomain f.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hgateaux :
      HasGateauxDerivativeAt
        (fun z ↦ (f.toEReal z : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H (∇ f x)) x :=
    hasGateauxDerivativeAt_toEReal_toReal_of_hasGradientAt
      ((hdiff x).hasGradientAt)
  have hsub : ∇ f x ∈ (∂ f.toEReal) x :=
    gateauxGradient_mem_subdifferential f.toEReal hconv_toEReal hx (∇ f x) hgateaux
  have hsupport :
      (⟪y - x, ∇ f x⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := by
    -- Unpack subdifferential membership at the evaluation point `y`.
    simpa [Function.toEReal_apply] using
      (mem_subdifferential_iff (f := f.toEReal) (x := x) (u := ∇ f x)).1 hsub y
  have hsupport_real : ⟪y - x, ∇ f x⟫_ℝ + f x ≤ f y := by
    exact_mod_cast hsupport
  -- Rewrite the displayed affine model into the supporting-hyperplane inequality.
  simpa [gradientAffineModel, add_comm, add_left_comm, add_assoc] using hsupport_real

-- Proof sketch: restrict `f` to the segment `t ↦ (1 - t) x + t y`, subtract the affine tangent
-- term and the quadratic correction, then show the resulting real function has nonpositive
-- derivative on `[0,1]` using the gradient Lipschitz bound.
/-- The quadratic model at `x` with curvature `β` majorizes `f` everywhere. -/
theorem le_gradient_quadratic_model_of_differentiable_convex_lipschitzGradient
    {β : Set.Ioi (0 : ℝ)}
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hLip : LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f)) (y : H) :
    f y ≤ gradientAffineModel f x y + (β : ℝ) * q[(ContinuousLinearMap.id ℝ H)] (y - x) := by
  let C : ℝ := (β : ℝ) * ‖x - y‖ ^ (2 : ℕ)
  let k : ℝ → ℝ := fun t ↦
    f (AffineMap.lineMap x y t) - t * ⟪y - x, ∇ f x⟫_ℝ - (C / 2) * t ^ (2 : ℕ)
  let _ := hconv
  have hk_deriv :
      ∀ t : ℝ,
        HasDerivAt k
          (⟪y - x, ∇ f (AffineMap.lineMap x y t)⟫_ℝ -
            ⟪y - x, ∇ f x⟫_ℝ - C * t) t := by
    intro t
    have hcomp :
        HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s))
          ⟪y - x, ∇ f (AffineMap.lineMap x y t)⟫_ℝ t :=
      hasDerivAt_comp_lineMap (f := f) (x := x) hdiff y t
    have hlin :
        HasDerivAt (fun s : ℝ ↦ s * ⟪y - x, ∇ f x⟫_ℝ)
          ⟪y - x, ∇ f x⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪y - x, ∇ f x⟫_ℝ
    have hquad :
        HasDerivAt (fun s : ℝ ↦ (C / 2) * s ^ (2 : ℕ)) (C * t) t := by
      have hsq : HasDerivAt (fun s : ℝ ↦ s ^ (2 : ℕ)) (2 * t) t := by
        simpa [pow_two, two_mul] using (hasDerivAt_id t).pow 2
      convert hsq.const_mul (C / 2) using 1
      ring
    have htmp := (hcomp.sub hlin).sub hquad
    convert htmp using 1
  have hk_differentiable : Differentiable ℝ k := by
    intro t
    exact (hk_deriv t).differentiableAt
  have hk_deriv_nonpos :
      ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), deriv k t ≤ 0 := by
    intro t ht
    have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [interior_Icc] using ht
    have ht_nonneg : 0 ≤ t := htIoo.1.le
    have hLip_line :
        ‖∇ f (AffineMap.lineMap x y t) - ∇ f x‖ ≤ (β : ℝ) * ‖AffineMap.lineMap x y t - x‖ := by
      simpa [Real.toNNReal_of_nonneg β.2.le, dist_eq_norm] using
        hLip.dist_le_mul (AffineMap.lineMap x y t) x
    have hline_norm :
        ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
      calc
        ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by
          simp [AffineMap.lineMap_apply_module']
        _ = |t| * ‖y - x‖ := norm_smul t (y - x)
        _ = t * ‖y - x‖ := by rw [abs_of_nonneg ht_nonneg]
    have hgrad_bound :
        ‖∇ f (AffineMap.lineMap x y t) - ∇ f x‖ ≤ (β : ℝ) * (t * ‖y - x‖) := by
      simpa [hline_norm]
        using hLip_line
    have hinner_bound :
        ⟪y - x, ∇ f (AffineMap.lineMap x y t) - ∇ f x⟫_ℝ ≤ C * t := by
      have hinner_le :
          ⟪y - x, ∇ f (AffineMap.lineMap x y t) - ∇ f x⟫_ℝ ≤
            ‖y - x‖ * ‖∇ f (AffineMap.lineMap x y t) - ∇ f x‖ := by
        exact real_inner_le_norm (y - x) (∇ f (AffineMap.lineMap x y t) - ∇ f x)
      have hright :
          ‖y - x‖ * ‖∇ f (AffineMap.lineMap x y t) - ∇ f x‖ ≤ C * t := by
        calc
          ‖y - x‖ * ‖∇ f (AffineMap.lineMap x y t) - ∇ f x‖
              ≤ ‖y - x‖ * ((β : ℝ) * (t * ‖y - x‖)) := by
                exact mul_le_mul_of_nonneg_left hgrad_bound (norm_nonneg (y - x))
          _ = C * t := by
            dsimp [C]
            rw [norm_sub_rev, pow_two]
            ring
      exact hinner_le.trans hright
    have hk_eval :
        deriv k t =
          (⟪y - x, ∇ f (AffineMap.lineMap x y t) - ∇ f x⟫_ℝ - C * t) := by
      have hk' := (hk_deriv t).deriv
      calc
        deriv k t =
            (⟪y - x, ∇ f (AffineMap.lineMap x y t)⟫_ℝ -
              ⟪y - x, ∇ f x⟫_ℝ - C * t) := hk'
        _ = (⟪y - x, ∇ f (AffineMap.lineMap x y t) - ∇ f x⟫_ℝ - C * t) := by
          rw [inner_sub_right]
    rw [hk_eval]
    linarith
  have hk_mono :
      k 1 - k 0 ≤ 0 * (1 - 0) := by
    exact
      (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
        hk_differentiable.continuous.continuousOn
        (hk_differentiable.differentiableOn.mono <| by
          intro t ht
          exact Set.mem_univ t)
        hk_deriv_nonpos 0 (by simp) 1 (by simp) zero_le_one
  have hstandard :
      f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    have hk_zero :
        k 0 = f x := by
      simp [k, C, AffineMap.lineMap_apply_zero]
    have hk_one :
        k 1 = f y - ⟪y - x, ∇ f x⟫_ℝ - ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
      simp [k, C, AffineMap.lineMap_apply_one, pow_two, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
      ring
    rw [hk_one, hk_zero] at hk_mono
    linarith
  calc
    f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := hstandard
    _ = gradientAffineModel f x y + (β : ℝ) * q[(ContinuousLinearMap.id ℝ H)] (y - x) :=
      (gradient_quadratic_model_normal_form (f := f) (x := x) (β := β) y).symm

-- Proof sketch: evaluate the explicit affine formula at `y = x`.
/-- The affine model in Remark 18.16 touches `f` at the base point `x`. -/
@[simp] theorem gradient_affine_model_eq_at_basePoint :
    gradientAffineModel f x x = f x := by
  -- The inner-product term vanishes because the displacement `x - x` is zero.
  simp [gradientAffineModel]

-- Proof sketch: at `y = x`, both `x - x` and the translated `q[id]` correction vanish.
/-- The quadratic model in Remark 18.16 touches `f` at the base point `x`. -/
@[simp] theorem gradient_quadratic_model_eq_at_basePoint {β : ℝ} :
    gradientAffineModel f x x + β * q[(ContinuousLinearMap.id ℝ H)] (x - x) = f x := by
  -- Combine the affine touching identity with the vanishing quadratic remainder.
  rw [gradient_affine_model_eq_at_basePoint, gradient_quadratic_remainder_eq_basePoint, add_zero]

-- Proof sketch: the affine model is a constant plus the linear functional
-- `y ↦ ⟪y, ∇ f x⟫ - ⟪x, ∇ f x⟫`, so its gradient is constantly `∇ f x`.
/-- The affine model in Remark 18.16 has gradient `∇ f x` at the base point. -/
theorem hasGradientAt_gradient_affine_model_at_basePoint :
    HasGradientAt (gradientAffineModel f x) (∇ f x) x := by
  let L : H →L[ℝ] ℝ := InnerProductSpace.toDual ℝ H (∇ f x)
  have hsub :
      HasFDerivAt (fun y : H ↦ y - x) (ContinuousLinearMap.id ℝ H) x := by
    -- Translation does not alter the derivative of the identity map.
    simpa using (ContinuousLinearMap.id ℝ H).hasFDerivAt.sub_const x
  have hinner :
      HasFDerivAt (fun y : H ↦ ⟪y - x, ∇ f x⟫_ℝ) L x := by
    -- Compose the translated identity with the linear functional represented by `∇ f x`.
    simpa [L, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      L.hasFDerivAt.comp x hsub
  have hconst :
      HasFDerivAt (fun _ : H ↦ f x) (0 : H →L[ℝ] ℝ) x := by
    -- Constant terms contribute zero derivative.
    simpa using (hasFDerivAt_const (c := f x) (x := x))
  have hAffine :
      HasFDerivAt (gradientAffineModel f x) L x := by
    -- Add the constant and linear pieces of the affine model.
    simpa [gradientAffineModel, L, zero_add] using hconst.add hinner
  simpa [L, InnerProductSpace.toDual_apply_apply] using hAffine.hasGradientAt

-- Proof sketch: the translated quadratic owner `y ↦ β * q[id] (y - x)` has zero gradient at `x`;
-- add this to the affine-model gradient formula.
/-- The quadratic model in Remark 18.16 has gradient `∇ f x` at the base point. -/
theorem hasGradientAt_gradient_quadratic_model_at_basePoint {β : ℝ} :
    HasGradientAt
      (fun y ↦ gradientAffineModel f x y + β * q[(ContinuousLinearMap.id ℝ H)] (y - x))
      (∇ f x) x := by
  have hAffine :
      HasFDerivAt (gradientAffineModel f x) (InnerProductSpace.toDual ℝ H (∇ f x)) x :=
    hasGradientAt_gradient_affine_model_at_basePoint (f := f) (x := x) |>.hasFDerivAt
  have hQuadratic :
      HasFDerivAt
        (fun y ↦ β * q[(ContinuousLinearMap.id ℝ H)] (y - x))
        (0 : H →L[ℝ] ℝ) x :=
    by
      simpa using
        (hasGradientAt_scaled_shifted_quadraticPotential_zero_at_basePoint (H := H) (x := x)
          (β := β)).hasFDerivAt
  -- Add the affine gradient and the zero gradient of the quadratic remainder.
  simpa using (hAffine.add hQuadratic).hasGradientAt

end StrongerDifferentiabilityNotions

end

end ERealFunction
