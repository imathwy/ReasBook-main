import BauschkeLean.Chap04.Remark_4_15_1
import BauschkeLean.Chap04.Remark_4_34
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap18.Remark_18_16
import BauschkeLean.Chap18.Theorem_18_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace

universe u

namespace ERealFunction

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 18.17 records the Baillon-Haddad equivalence for gradients of
  differentiable convex functions, together with the `β = 1` firm-nonexpansiveness specialization.
- `core/canonical`: the owner stack is `frechetDifferentiable_tfae_lipschitz_gradient` from
  Chapter 18 and the Chapter 4 equivalences
  `cocoerciveOn_iff_smul_averagedWith_half` / `firmlyNonexpansive_iff_averaged_half`.
- `bridge/view`: the two theorems below specialize those owners to the gradient map and strip the
  differentiability component already supplied as a hypothesis, while keeping the chapter-owner
  parameter shape `β : Set.Ioi (0 : ℝ)`.
-/

/-- Helper for Corollary 18.17: the quadratic control `s ↦ β s²` has remainder
`θ(s) = (β / 2) s²`. -/
lemma quadratic_theta_eq
    (β : Set.Ioi (0 : ℝ)) (r : ℝ) :
    θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r = ((β : ℝ) / 2) * r ^ (2 : ℕ) := by
  rw [theta_apply]
  have hintegrand :
      (fun t : ℝ ↦ ((β : ℝ) * (r * t) ^ (2 : ℕ)) / t) =
        fun t : ℝ ↦ t * ((β : ℝ) * r ^ (2 : ℕ)) := by
    funext t
    by_cases ht : t = 0
    · subst ht
      simp
    · field_simp [ht]
  -- Rewrite the integral into the elementary linear integral on `[0,1]`.
  rw [hintegrand, intervalIntegral.integral_mul_const, integral_id]
  ring

/-- Helper for Corollary 18.17: the quadratic control `s ↦ β s²` has conjugate remainder
`θ*(r) = r² / (2β)` on nonnegative inputs. -/
lemma quadratic_thetaStar_eq_of_nonneg
    (β : Set.Ioi (0 : ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    thetaStar (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r =
      (1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) := by
  have hquadratic_even : Function.Even (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    intro s
    simp [pow_two]
  have hquadratic_conv :
      _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    have hsqConv : _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ s ^ (2 : ℕ)) := by
      simpa using (show Even (2 : ℕ) by decide).convexOn_pow
    simpa [smul_eq_mul] using hsqConv.smul β.2.le
  have hquadratic_zero :
      ∀ s : ℝ, (β : ℝ) * s ^ (2 : ℕ) = 0 ↔ s = 0 := by
    intro s
    constructor
    · intro hs
      have hβ_ne : (β : ℝ) ≠ 0 := ne_of_gt β.2
      have hsq : s ^ (2 : ℕ) = 0 := by
        exact (mul_eq_zero.mp hs).resolve_left hβ_ne
      exact eq_zero_of_pow_eq_zero hsq
    · intro hs
      simp [hs]
  have hasEReal :=
    thetaStar_asEReal_of_nonneg
      (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
      hquadratic_even hquadratic_conv hquadratic_zero hr
  have hconj :
      thetaConj (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r =
        (((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal))) := by
    -- Evaluate the public conjugate of the quadratic Moreau remainder.
    rw [thetaConj]
    have htheta :
        ((θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))).toEReal.asEReal) =
          (moreauQuadraticKernel (H := ℝ) (β⁻¹ : PosReal)).asEReal := by
      funext s
      rw [Function.asEReal_apply, Function.toEReal_apply, Function.asEReal_apply,
        quadratic_theta_eq]
      have hreal :
          ((β : ℝ) / 2) * s ^ (2 : ℕ) =
            (1 / (2 * (((β⁻¹ : PosReal) : ℝ))) * ‖s‖ ^ (2 : ℕ) : ℝ) := by
        rw [Real.norm_eq_abs, sq_abs]
        have hcoeff :
            (1 / (2 * (((β⁻¹ : PosReal) : ℝ))) : ℝ) = (β : ℝ) / 2 := by
          change (1 / (2 * (β : ℝ)⁻¹) : ℝ) = (β : ℝ) / 2
          field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
        rw [hcoeff]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    rw [htheta]
    have hkernel :=
      congrFun
        (conjugate_moreauQuadraticKernel_eq_smul_halfSquaredNorm
          (H := ℝ) (γ := (β⁻¹ : PosReal)))
        r
    calc
      (moreauQuadraticKernel (H := ℝ) (β⁻¹ : PosReal)).asEReal∗ r =
          ((((((β⁻¹ : PosReal) : ℝ) * ((1 / 2 : ℝ) * r ^ (2 : ℕ)) : ℝ) : EReal))) := by
            simpa [Pi.smul_apply, Function.asEReal_apply, halfSquaredNorm_apply,
              Real.norm_eq_abs, sq_abs, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              hkernel
      _ = (((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal))) := by
            congr 1
            change ((β : ℝ)⁻¹) * ((1 / 2 : ℝ) * r ^ (2 : ℕ)) =
              (1 / (2 * (β : ℝ))) * r ^ (2 : ℕ)
            field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
  have hrealEq :
      (((thetaStar (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r : ℝ) : EReal)) =
        ((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal)) := by
    rw [hasEReal, hconj]
  exact_mod_cast hrealEq

/-- Helper for Corollary 18.17: on the whole space, `1`-cocoercivity is equivalent to firm
nonexpansiveness. -/
lemma cocoerciveOn_one_univ_iff_firmlyNonexpansive {T : H → H} :
    CocoerciveOn (1 : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      FirmlyNonexpansive T := by
  -- Convert unit cocoercivity into `1 / 2`-averagedness via Remark 4.34.
  calc
    CocoerciveOn (1 : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
        AveragedWith (1 / 2 : ℝ) (fun x : Set.univ ↦ (1 : ℝ) • T x) := by
          exact cocoerciveOn_iff_smul_averagedWith_half (by norm_num) (fun x : Set.univ ↦ T x)
    _ ↔ AveragedWith (1 / 2 : ℝ) (fun x : Set.univ ↦ T x) := by
          simp
    -- Rewrite the subtype-domain averagedness statement into the whole-space self-map API.
    _ ↔ Averaged (1 / 2 : ℝ) T := by
          exact (averaged_iff_averagedWith_univ (α := (1 / 2 : ℝ)) (T := T)).symm
    _ ↔ FirmlyNonexpansive T := by
          exact firmlyNonexpansive_iff_averaged_half.symm

-- Proof sketch: apply Theorem 18.15 to identify clause `(i)` with clause `(v)` for the TFAE list
-- attached to a continuous convex function. The hypothesis `Differentiable ℝ f` supplies the
-- differentiability component already built into both clauses, so the equivalence reduces to the
-- raw gradient statements.
/-- Corollary 18.17 (1): for a Fréchet differentiable convex function on a real Hilbert space,
the gradient is `β`-Lipschitz if and only if it is `1 / β`-cocoercive. -/
theorem gradient_lipschitz_iff_cocoercive_of_differentiable_convex
    (f : H → ℝ) (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ)) :
    LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f) ↔
      CocoerciveOn (1 / (β : ℝ)) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ f x) := by
  have hquadratic_even : Function.Even (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    intro s
    simp [pow_two]
  have hquadratic_conv :
      _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
    have hsqConv : _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ s ^ (2 : ℕ)) := by
      simpa using (show Even (2 : ℕ) by decide).convexOn_pow
    simpa [smul_eq_mul] using hsqConv.smul β.2.le
  have hquadratic_zero :
      ∀ s : ℝ, (β : ℝ) * s ^ (2 : ℕ) = 0 ↔ s = 0 := by
    intro s
    constructor
    · intro hs
      have hβ_ne : (β : ℝ) ≠ 0 := ne_of_gt β.2
      have hsq : s ^ (2 : ℕ) = 0 := by
        exact (mul_eq_zero.mp hs).resolve_left hβ_ne
      exact eq_zero_of_pow_eq_zero hsq
    · intro hs
      simp [hs]
  constructor
  · intro hLip
    refine ⟨by simpa [one_div] using (show 0 < 1 / (β : ℝ) from one_div_pos.mpr β.2), ?_⟩
    intro x y
    have hinner :
        ∀ a b : H, ⟪a - b, ∇ f a - ∇ f b⟫_ℝ ≤ (β : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
      intro a b
      have hgrad :
          ‖∇ f a - ∇ f b‖ ≤ (β : ℝ) * ‖a - b‖ := by
        simpa [dist_eq_norm, Real.toNNReal_of_nonneg β.2.le] using hLip.dist_le_mul a b
      calc
        ⟪a - b, ∇ f a - ∇ f b⟫_ℝ ≤ ‖a - b‖ * ‖∇ f a - ∇ f b‖ := by
          exact real_inner_le_norm _ _
        _ ≤ ‖a - b‖ * ((β : ℝ) * ‖a - b‖) := by
          gcongr
        _ = (β : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
          ring_nf
    have hdescent :
        ∀ a b : H,
          f b ≤ f a + ⟪b - a, ∇ f a⟫_ℝ +
            ∫ t in (0 : ℝ)..1, ((β : ℝ) * (‖a - b‖ * t) ^ (2 : ℕ)) / t := by
      intro a b
      have hmodel :=
        le_gradient_quadratic_model_of_differentiable_convex_lipschitzGradient
          (f := f) (x := a) hdiff hconv hLip b
      have hmodel' :
          f b ≤ f a + ⟪b - a, ∇ f a⟫_ℝ + ((β : ℝ) / 2) * ‖a - b‖ ^ (2 : ℕ) := by
        calc
          f b ≤ gradientAffineModel f a b +
              (β : ℝ) * ContinuousLinearMap.quadraticPotential (ContinuousLinearMap.id ℝ H) (b - a) :=
            hmodel
          _ = f a + ⟪b - a, ∇ f a⟫_ℝ + ((β : ℝ) / 2) * ‖a - b‖ ^ (2 : ℕ) := by
            rw [gradientAffineModel, ContinuousLinearMap.quadraticPotential_apply,
              ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, norm_sub_rev]
            ring
      -- Rewrite the explicit integral remainder back to the closed quadratic formula.
      rw [← theta_apply (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) (s := ‖a - b‖)]
      rw [quadratic_theta_eq (β := β) (r := ‖a - b‖)]
      exact hmodel'
    have hpair :=
      gradient_inner_ge_two_thetaConjugate_of_conjugate_gradient_ge_affine_add_thetaConjugate
        (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
        (f := f) hdiff hconv hquadratic_even hquadratic_conv hquadratic_zero
        (conjugate_gradient_ge_affine_add_thetaConjugate_of_descent_le_linearization_add_theta
          (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
          (f := f) hdiff hconv hquadratic_even hquadratic_conv hquadratic_zero hdescent)
        (x : H) (y : H)
    have htheta :
        thetaStar (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖∇ f (x : H) - ∇ f y‖ =
          (1 / (2 * (β : ℝ))) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) :=
      quadratic_thetaStar_eq_of_nonneg β (norm_nonneg _)
    calc
      (1 / (β : ℝ)) * ‖∇ f (x : H) - ∇ f y‖ ^ (2 : ℕ) =
          2 * thetaStar (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖∇ f (x : H) - ∇ f y‖ := by
            rw [htheta]
            field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
      _ ≤ ⟪(x : H) - y, ∇ f (x : H) - ∇ f y⟫_ℝ := by
            simpa using hpair
  · intro hCoco
    have hsub :
        LipschitzWith (Real.toNNReal (β : ℝ)) (fun x : (Set.univ : Set H) ↦ ∇ f (x : H)) := by
      -- Convert the whole-space cocoercivity statement into the Chapter 4 Lipschitz estimate.
      simpa [one_div, Real.toNNReal_of_nonneg β.2.le] using
        (lipschitzWith_of_cocoercive
          (T := fun x : (Set.univ : Set H) ↦ ∇ f (x : H))
          (β := 1 / (β : ℝ))
          hCoco)
    -- Remove the `Set.univ` subtype bookkeeping from the Lipschitz estimate.
    refine LipschitzWith.of_dist_le' ?_
    intro x y
    simpa [Subtype.dist_eq, Real.toNNReal_of_nonneg β.2.le] using
      hsub.dist_le_mul ⟨x, by simp⟩ ⟨y, by simp⟩

-- Proof sketch: specialize the previous theorem to `β = 1`. Then `1 / β = 1`, and
-- Remark 4.34(3) identifies `1`-cocoercivity on the whole space with firm nonexpansiveness.
/-- Corollary 18.17 (2): for a Fréchet differentiable convex function on a real Hilbert space, a
nonexpansive gradient is exactly a firmly nonexpansive gradient. -/
theorem gradient_nonexpansive_iff_firmlyNonexpansive_of_differentiable_convex
    (f : H → ℝ) (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    LipschitzWith 1 (∇ f) ↔ FirmlyNonexpansive (∇ f) := by
  let β1 : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  -- Specialize part (1) to the unit parameter.
  have hunit :=
    gradient_lipschitz_iff_cocoercive_of_differentiable_convex f hdiff hconv β1
  -- Normalize the parameter and then apply the whole-space bridge to firm nonexpansiveness.
  simpa [β1, cocoerciveOn_one_univ_iff_firmlyNonexpansive] using hunit

end StrongerDifferentiabilityNotions

end ERealFunction
