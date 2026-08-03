import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap04.Remark_4_15_1
import BauschkeLean.Chap05.Example_5_18
import BauschkeLean.Chap12.Remark_12_24
import BauschkeLean.Chap12.Proposition_12_27
import BauschkeLean.Chap12.Proposition_12_28
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.Corollary_13_40
import BauschkeLean.Chap14.Proposition_14_1
import BauschkeLean.Chap14.Proposition_14_2
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap17.Proposition_17_9
import BauschkeLean.Chap18.Theorem_18_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace Pointwise

universe u

namespace ERealFunction

section QuadraticGapContinuity

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Theorem 18 15: the quadratic gap `x ↦ β q(x) - f(x)` is continuous whenever `f`
is continuous. -/
lemma continuous_quadratic_gap
    (f : H → ℝ) (hcont : Continuous f) (β : Set.Ioi (0 : ℝ)) :
    Continuous (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) := by
  -- The quadratic term is continuous, so subtracting the continuous `f` preserves continuity.
  have hquad_cont : Continuous (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ)) := by
    simpa using continuous_const.mul (continuous_norm.pow 2)
  simpa using hquad_cont.sub hcont

end QuadraticGapContinuity

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 18 15: on `Set.univ`, cocoercivity is exactly the ambient pairwise
inequality without subtype bookkeeping. -/
lemma cocoerciveOn_univ_iff {β : ℝ} {T : H → H} :
    CocoerciveOn β (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      0 < β ∧ ∀ x y : H, β * ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪x - y, T x - T y⟫_ℝ := by
  let _ : CompleteSpace H := inferInstance
  constructor
  · intro hT
    refine ⟨hT.1, ?_⟩
    intro x y
    -- Remove the `Set.univ` subtype wrappers from the canonical cocoercivity inequality.
    simpa using hT.2 ⟨x, by simp⟩ ⟨y, by simp⟩
  · rintro ⟨hβ, hineq⟩
    refine ⟨hβ, ?_⟩
    intro x y
    -- Repackage the ambient inequality back into the `Set.univ`-indexed formulation.
    simpa using hineq x y

/-- Helper for Theorem 18 15: adding back the Moreau quadratic kernel to the shifted conjugate
recovers the ordinary Fenchel conjugate of `f`. -/
lemma shifted_conjugate_add_moreauQuadraticKernel_eq_conjugate
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) :
    ((conjugateSubInvHalfSquaredNorm f β + moreauQuadraticKernel β).asEReal) =
      f.toEReal.asEReal∗ := by
  let _ : CompleteSpace H := inferInstance
  ext u
  -- Expand the shifted conjugate and cancel the quadratic correction pointwise.
  rw [Function.asEReal_apply, add_apply, conjugateSubInvHalfSquaredNorm_apply,
    moreauQuadraticKernel_apply]
  exact EReal.sub_add_cancel

/-- Helper for Theorem 18 15: the owner remainder `θ` attached to the quadratic control
`s ↦ β s²` is the expected quadratic `β s² / 2`. -/
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
  -- Rewrite the interval integral to the elementary integral of `t` times a constant.
  rw [hintegrand, intervalIntegral.integral_mul_const, integral_id]
  ring

/-- Helper for Theorem 18 15: on `ℝ`, the quadratic remainder `θ(s ↦ β s²)` is exactly the
reciprocal-parameter Moreau quadratic kernel. -/
lemma theta_quadratic_as_ereal_eq_moreauQuadraticKernel_inv
    (β : Set.Ioi (0 : ℝ)) :
    ((θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))).toEReal.asEReal) =
      (moreauQuadraticKernel (H := ℝ) (β⁻¹ : PosReal)).asEReal := by
  funext r
  -- Route correction: rewrite `θ` by the closed quadratic formula before matching the kernel.
  rw [Function.asEReal_apply, Function.toEReal_apply, Function.asEReal_apply,
    quadratic_theta_eq, moreauQuadraticKernel_apply]
  have hreal :
      ((β : ℝ) / 2) * r ^ (2 : ℕ) =
        (1 / (2 * (((β⁻¹ : PosReal) : ℝ))) * ‖r‖ ^ (2 : ℕ) : ℝ) := by
    rw [Real.norm_eq_abs, sq_abs]
    have hcoeff :
        (1 / (2 * (((β⁻¹ : PosReal) : ℝ))) : ℝ) = (β : ℝ) / 2 := by
      change (1 / (2 * (β : ℝ)⁻¹) : ℝ) = (β : ℝ) / 2
      field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
    rw [hcoeff]
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Theorem 18 15: the quadratic control `s ↦ β s²` has conjugate `r ↦ r² / (2β)` on
the source-facing `thetaConj` owner. -/
lemma quadratic_thetaConj_eq
    (β : Set.Ioi (0 : ℝ)) (r : ℝ) :
    thetaConj (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) r =
      ((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal)) := by
  -- Rewrite `thetaConj` through the reciprocal Moreau kernel and evaluate the public conjugacy.
  rw [thetaConj, theta_quadratic_as_ereal_eq_moreauQuadraticKernel_inv]
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
    _ = ((((1 / (2 * (β : ℝ))) * r ^ (2 : ℕ) : ℝ) : EReal)) := by
          congr 1
          change ((β : ℝ)⁻¹) * ((1 / 2 : ℝ) * r ^ (2 : ℕ)) =
            (1 / (2 * (β : ℝ))) * r ^ (2 : ℕ)
          field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]

/-- Helper for Theorem 18 15: if the quadratic gap `β q - f` is convex, then the shifted
conjugate `f* - β⁻¹ q` belongs to `Γ₀(H)`. -/
lemma conjugateSubInvHalfSquaredNorm_mem_gammaZero_of_halfSquaredNorm_sub_convex
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ))
    (hgap_conv : _root_.ConvexOn ℝ Set.univ
      (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x)) :
    conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H) := by
  let g : H → ℝ := fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x
  have hg_cont : Continuous g := by
    -- Reuse the named continuity bridge for the source-side quadratic gap.
    simpa [g] using continuous_quadratic_gap (f := f) hcont β
  have hgΓ : g.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ g hg_cont hgap_conv
  have hscaled_gamma :
      (fun u : H ↦ ((β : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f β u : EReal)) ∈
        gamma H := by
    -- Proposition 13.29 packages the scaled shifted conjugate as a Fenchel conjugate.
    rw [smul_conjugateSubInvHalfSquaredNorm_eq_conjugate_gap f β rfl hgΓ]
    exact
      conjugate_mem_gamma
        (fun x : H ↦
          ((β : ℝ) : EReal) * (gammaZeroConjugate g.toEReal hgΓ x : EReal) -
            halfSquaredNorm.asEReal x)
  have hh_gamma :
      (fun u : H ↦ (conjugateSubInvHalfSquaredNorm f β u : EReal)) ∈ gamma H := by
    have hscaled_inv :
        (fun u : H ↦
          (((β : ℝ)⁻¹ : EReal) *
            (((β : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f β u : EReal)))) ∈
          gamma H := by
      -- Divide the `Γ(H)` owner by the positive scalar `β`.
      exact const_mul_mem_gamma_of_nonneg hscaled_gamma (inv_nonneg.mpr β.2.le)
    have hcancel :
        (fun u : H ↦
          (((β : ℝ)⁻¹ : EReal) *
            (((β : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f β u : EReal)))) =
          (fun u : H ↦ (conjugateSubInvHalfSquaredNorm f β u : EReal)) := by
      ext u
      have hcoeff : (((β : ℝ)⁻¹ : EReal) * ((β : ℝ) : EReal)) = 1 := by
        rw [← EReal.coe_inv, ← EReal.coe_mul,
          inv_mul_cancel₀ (show (β : ℝ) ≠ 0 from ne_of_gt β.2), EReal.coe_one]
      rw [← mul_assoc, hcoeff, one_mul]
    rw [← hcancel]
    exact hscaled_inv
  have hdom :
      (effectiveDomain (conjugateSubInvHalfSquaredNorm f β)).Nonempty :=
    conjugateSubInvHalfSquaredNorm_effectiveDomain_nonempty f hcont hconv β
  have hproper : IsProper (conjugateSubInvHalfSquaredNorm f β).asEReal := by
    refine ⟨?_, ?_⟩
    · intro x
      exact ne_of_gt (show (⊥ : EReal) < (conjugateSubInvHalfSquaredNorm f β).asEReal x from
        (conjugateSubInvHalfSquaredNorm f β x).2)
    · rcases hdom with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa [effectiveDomain, dom] using hx
  have hrepr :
      conjugateSubInvHalfSquaredNorm f β =
        properIoi (conjugateSubInvHalfSquaredNorm f β).asEReal hproper := by
    funext u
    apply Subtype.ext
    rfl
  -- Repackage the proper `Γ(H)` owner through the canonical `Γ₀(H)` wrapper.
  rw [hrepr]
  exact properIoi_mem_gammaZero_of_mem_gamma hproper hh_gamma

/-- Helper for Theorem 18 15: clause `(viii)`'s second Moreau identity follows from the public
quadratic-gap representation in Proposition 14.2. -/
lemma shifted_conjugate_quadratic_gap_representation
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ)) :
    f.toEReal.asEReal =
      (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal -
        {}^[β] (conjugateSubInvHalfSquaredNorm f β) ∘ ((β : ℝ) • ·) := by
  have hfΓ : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  funext x
  have hgap :=
    congrFun
      (halfSquaredNorm_sub_eq_moreauEnvelope_conjugateSubInvHalfSquaredNorm_comp_smul
        (f := f) (γ := β) hfΓ)
      x
  have hgap' :
      ({}^[β] (conjugateSubInvHalfSquaredNorm f β)) ((β : ℝ) • x) =
        (((((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x : ℝ)) : EReal) := by
    -- Collapse the finite-valued quadratic gap to a single real cast before rewriting it.
    simpa [sub_eq_add_neg, ← EReal.coe_sub] using hgap.symm
  have hkernel :
      ((((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) =
        (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal x := by
    -- Route correction: evaluate the reciprocal-parameter kernel directly instead of transporting
    -- the coefficient through ad hoc `EReal` subtraction identities.
    rw [Function.asEReal_apply, moreauQuadraticKernel_apply]
    congr 1
    change ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) = (1 / (2 * (β : ℝ)⁻¹)) * ‖x‖ ^ (2 : ℕ)
    have hcoeff : (1 / (2 * (β : ℝ)⁻¹) : ℝ) = (β : ℝ) / 2 := by
      field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
    rw [hcoeff]
  have hreal :
      f x =
        ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - (((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) := by
    ring
  have hrealE :
      (f x : EReal) =
        (((((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) -
          (((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) : ℝ)) : EReal) :=
    congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  -- Rewrite the target pointwise formula through the exact quadratic-gap identity from
  -- Proposition 14.2 and then normalize the quadratic term to the Moreau kernel.
  change (f x : EReal) =
    (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal x -
      ({}^[β] (conjugateSubInvHalfSquaredNorm f β) ∘ ((β : ℝ) • ·)) x
  rw [Function.comp_apply, ← hkernel, hgap']
  rw [← EReal.coe_sub]
  exact hrealE

/-- Helper for Theorem 18 15: the reciprocal Moreau-envelope representation in clause `(viii)`.
After the Chapter 9 duplicate-declaration repair, Proposition 14.1 applies directly to the
shifted conjugate `h = f* - β⁻¹ q`, whose quadratic correction is exactly `f*`; conjugating once
more then recovers `f` by Fenchel--Moreau. -/
lemma shifted_conjugate_first_moreau_representation
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ))
    (hgamma : conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H)) :
    f.toEReal.asEReal =
      {}^[(β⁻¹ : PosReal)]((conjugateSubInvHalfSquaredNorm f β).asEReal∗) := by
  have hfΓ : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  have howner :
      ((conjugateSubInvHalfSquaredNorm f β).asEReal +
          ((((β⁻¹ : PosReal) : ℝ) : EReal) • halfSquaredNorm.asEReal)) =
        f.toEReal.asEReal∗ := by
    -- Route correction: identify the quadratic correction from Proposition 14.1 with the
    -- textbook `β⁻¹ q` term before appealing to the existing shifted-conjugate identity.
    ext u
    rw [Pi.add_apply, Function.asEReal_apply]
    have hreal :
        ((((((β⁻¹ : PosReal) : ℝ) : EReal) • halfSquaredNorm.asEReal) u)) =
          (moreauQuadraticKernel β u : EReal) := by
      rw [Pi.smul_apply, Function.asEReal_apply, halfSquaredNorm_apply,
        smul_eq_mul]
      calc
        ((((β⁻¹ : PosReal) : ℝ) : EReal) * ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal))) =
            ((((β⁻¹ : PosReal) : ℝ) * ((‖u‖ ^ (2 : ℕ)) / 2) : ℝ) : EReal) := by
              rw [← EReal.coe_mul]
        _ = (moreauQuadraticKernel β u : EReal) := by
              rw [moreauQuadraticKernel_apply]
              congr 1
              have hβ0 : (β : ℝ) ≠ 0 := ne_of_gt β.2
              calc
                ((β : ℝ)⁻¹ * ((‖u‖ ^ (2 : ℕ)) / 2) : ℝ)
                    = ((β : ℝ)⁻¹ * ‖u‖ ^ (2 : ℕ)) / 2 := by ring
                _ = (1 / (2 * (β : ℝ))) * ‖u‖ ^ (2 : ℕ) := by
                      field_simp [hβ0]
    calc
      ((conjugateSubInvHalfSquaredNorm f β u : EReal) +
          ((((((β⁻¹ : PosReal) : ℝ) : EReal) • halfSquaredNorm.asEReal) u)))
          = ((conjugateSubInvHalfSquaredNorm f β u : EReal) +
              (moreauQuadraticKernel β u : EReal)) := by
                rw [hreal]
      _ = f.toEReal.asEReal∗ u := by
            simpa [Function.asEReal_apply] using
              congrFun (shifted_conjugate_add_moreauQuadraticKernel_eq_conjugate f β) u
  have hmoreau_owner :=
    conjugate_add_scaledQuadratic_eq_moreauEnvelope_gammaZeroConjugate
      (f := conjugateSubInvHalfSquaredNorm f β) (hf := hgamma) (γ := (β⁻¹ : PosReal))
  have hmoreau :
      f.toEReal.asEReal∗∗ =
        {}^[(β⁻¹ : PosReal)] (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma) := by
    -- Rewrite the owner theorem with the exact left-hand side `f*` identified above.
    calc
      f.toEReal.asEReal∗∗ =
          (((conjugateSubInvHalfSquaredNorm f β).asEReal +
              ((((β⁻¹ : PosReal) : ℝ) : EReal) • halfSquaredNorm.asEReal))∗) := by
                rw [howner]
      _ =
          {}^[(β⁻¹ : PosReal)] (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma) :=
        hmoreau_owner
  -- Fenchel--Moreau turns the biconjugate of the original finite convex function back into `f`.
  calc
    f.toEReal.asEReal = f.toEReal.asEReal∗∗ := by
      symm
      exact biconjugate_eq_of_mem_gammaZero hfΓ
    _ =
        {}^[(β⁻¹ : PosReal)] (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma) :=
      hmoreau
    _ = {}^[(β⁻¹ : PosReal)]((conjugateSubInvHalfSquaredNorm f β).asEReal∗) := by
      -- The packaged `Γ₀(H)` conjugate is pointwise the ambient Fenchel conjugate.
      rfl

/-- Helper for Theorem 18 15: the quadratic gap `x ↦ β q(x) - f x` has gradient
`x ↦ β • x - ∇ f x` whenever `f` is Fréchet differentiable. -/
lemma quadratic_gap_hasGradientAt
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (hdiff : Differentiable ℝ f) (x : H) :
    HasGradientAt (fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y)
      ((β : ℝ) • x - ∇ f x) x := by
  -- Differentiate the quadratic term through the norm-square Fréchet derivative formula.
  rw [hasGradientAt_iff_hasFDerivAt]
  have hnormsq :
      HasFDerivAt (fun y : H ↦ ‖y‖ ^ (2 : ℕ))
        (2 • innerSL ℝ x) x := by
    simpa using
      (HasFDerivAt.norm_sq (x := x)
        (f := fun y : H ↦ y) (f' := ContinuousLinearMap.id ℝ H) (hasFDerivAt_id x))
  have hquad :
      HasFDerivAt (fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ))
        (((β : ℝ) / 2) • (2 • innerSL ℝ x)) x := by
    simpa [smul_eq_mul] using hnormsq.const_smul ((β : ℝ) / 2)
  have hf :
      HasFDerivAt f (InnerProductSpace.toDual ℝ H (∇ f x)) x :=
    (hdiff x).hasGradientAt.hasFDerivAt
  -- Subtract the gradient of `f` from the gradient of the quadratic term.
  convert hquad.sub hf using 2
  ext y
  simp [ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply, sub_eq_add_neg]
  ring

/-- Helper for Theorem 18 15: on the full effective domain of the quadratic gap, the canonical
`gradientWithin` field agrees with the explicit gradient `x ↦ β • x - ∇ f x`. -/
lemma gradientWithin_quadratic_gap_toEReal_eq
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (hdiff : Differentiable ℝ f) (x : H) :
    gradientWithin
      (fun z : H ↦
        (((fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y).toEReal z : EReal).toReal))
      (effectiveDomain
        ((fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y).toEReal))
      x =
      (β : ℝ) • x - ∇ f x := by
  let g : H → ℝ := fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y
  have hdiff_g :
      DifferentiableOn ℝ (fun z : H ↦ ((g.toEReal z : EReal).toReal)) (effectiveDomain g.toEReal) :=
    by
      intro z hz
      -- The explicit global gradient of the quadratic gap gives differentiability on `Set.univ`.
      simpa [g, Function.toEReal_apply] using
        (quadratic_gap_hasGradientAt f β hdiff z).differentiableAt.differentiableWithinAt
  have hcanonical :
      HasGradientWithinAt
        (fun z : H ↦ ((g.toEReal z : EReal).toReal))
        (gradientWithin
          (fun z : H ↦ ((g.toEReal z : EReal).toReal))
          (effectiveDomain g.toEReal)
          x)
        (effectiveDomain g.toEReal)
        x :=
    (hdiff_g x (by simp [g, Function.effectiveDomain_toEReal])).hasGradientWithinAt
  have hexplicit :
      HasGradientWithinAt
        (fun z : H ↦ ((g.toEReal z : EReal).toReal))
        ((β : ℝ) • x - ∇ f x)
        (effectiveDomain g.toEReal)
        x := by
    -- The explicit `HasGradientAt` formula specializes to the within-gradient on `Set.univ`.
    simpa [g, Function.effectiveDomain_toEReal, Function.toEReal_apply] using
      ((hasGradientWithinAt_univ :
        HasGradientWithinAt g ((β : ℝ) • x - ∇ f x) Set.univ x ↔
          HasGradientAt g ((β : ℝ) • x - ∇ f x) x).2
        (quadratic_gap_hasGradientAt f β hdiff x))
  have hUnique : UniqueDiffWithinAt ℝ (effectiveDomain g.toEReal) x := by
    simp [Function.effectiveDomain_toEReal]
  have hEq :
      InnerProductSpace.toDual ℝ H
          (gradientWithin
            (fun z : H ↦ ((g.toEReal z : EReal).toReal))
            (effectiveDomain g.toEReal)
            x) =
        InnerProductSpace.toDual ℝ H (((β : ℝ) • x - ∇ f x)) :=
    hUnique.eq hcanonical.hasFDerivWithinAt hexplicit.hasFDerivWithinAt
  exact (InnerProductSpace.toDual ℝ H).injective hEq

/-- Helper for Theorem 18 15: the monotonicity pairing for the quadratic-gap gradient field
`x ↦ β • x - ∇ f x` normalizes to the scalar expression from clause `(ii)`. -/
lemma quadratic_gap_monotonicity_pairing_eq
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (x y : H) :
    ((InnerProductSpace.toDual ℝ H ((β : ℝ) • x - ∇ f x) -
        InnerProductSpace.toDual ℝ H ((β : ℝ) • y - ∇ f y))
        (x - y)) =
      (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) - ⟪x - y, ∇ f x - ∇ f y⟫_ℝ := by
  let d : H := x - y
  have hxy : ⟪x, d⟫_ℝ - ⟪y, d⟫_ℝ = ⟪x - y, d⟫_ℝ := by
    rw [← inner_sub_left]
  have hgrad : ⟪∇ f x, d⟫_ℝ - ⟪∇ f y, d⟫_ℝ = ⟪∇ f x - ∇ f y, d⟫_ℝ := by
    rw [← inner_sub_left]
  -- Expand the `toDual` pairing and then collect the quadratic and gradient contributions.
  calc
    ((InnerProductSpace.toDual ℝ H ((β : ℝ) • x - ∇ f x) -
        InnerProductSpace.toDual ℝ H ((β : ℝ) • y - ∇ f y))
        (x - y)) =
      ⟪(β : ℝ) • x - ∇ f x, x - y⟫_ℝ - ⟪(β : ℝ) • y - ∇ f y, x - y⟫_ℝ := by
        rw [ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply,
          InnerProductSpace.toDual_apply_apply]
    _ = (β : ℝ) * ⟪x, d⟫_ℝ - ⟪∇ f x, d⟫_ℝ - ((β : ℝ) * ⟪y, d⟫_ℝ - ⟪∇ f y, d⟫_ℝ) := by
      simp [d, inner_sub_left, real_inner_smul_left]
    _ = (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) - ⟪x - y, ∇ f x - ∇ f y⟫_ℝ := by
      calc
        (β : ℝ) * ⟪x, x - y⟫_ℝ - ⟪∇ f x, x - y⟫_ℝ - ((β : ℝ) * ⟪y, x - y⟫_ℝ - ⟪∇ f y, x - y⟫_ℝ)
            = (β : ℝ) * (⟪x, x - y⟫_ℝ - ⟪y, x - y⟫_ℝ) -
                (⟪∇ f x, x - y⟫_ℝ - ⟪∇ f y, x - y⟫_ℝ) := by
                  ring
        _ = (β : ℝ) * ⟪x - y, x - y⟫_ℝ - ⟪∇ f x - ∇ f y, x - y⟫_ℝ := by
              rw [hxy, hgrad]
        _ = (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) - ⟪x - y, ∇ f x - ∇ f y⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq, real_inner_comm]

/-- Helper for Theorem 18 15: the pointwise quadratic upper bound on `∇ f` makes the quadratic
gap `x ↦ β q(x) - f x` convex on all of `H`. -/
lemma quadratic_gap_convex_of_gradient_upper_bound
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (hdiff : Differentiable ℝ f)
    (hinner :
      ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ (β : ℝ) * ‖x - y‖ ^ (2 : ℕ)) :
    _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) := by
  let g : H → ℝ := fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x
  have hdiff_g :
      DifferentiableOn ℝ (fun z : H ↦ ((g.toEReal z : EReal).toReal)) (effectiveDomain g.toEReal) :=
    by
      intro z hz
      -- The explicit global gradient of the quadratic gap gives differentiability everywhere.
      simpa [g, Function.toEReal_apply] using
        (quadratic_gap_hasGradientAt f β hdiff z).differentiableAt.differentiableWithinAt
  have hmono :
      GateauxDerivativeMonotoneOn
        (fun x ↦
          InnerProductSpace.toDual ℝ H
            (gradientWithin
              (fun z ↦ ((g.toEReal z : EReal).toReal))
              (effectiveDomain g.toEReal)
              x))
        (effectiveDomain g.toEReal) := by
    intro x hx y hy
    have hxgrad := gradientWithin_quadratic_gap_toEReal_eq (f := f) (β := β) hdiff x
    have hygrad := gradientWithin_quadratic_gap_toEReal_eq (f := f) (β := β) hdiff y
    change 0 ≤
      (⟪gradientWithin
            (fun z ↦ ((g.toEReal z : EReal).toReal))
            (effectiveDomain g.toEReal)
            x, x - y⟫_ℝ -
        ⟪gradientWithin
            (fun z ↦ ((g.toEReal z : EReal).toReal))
            (effectiveDomain g.toEReal)
            y, x - y⟫_ℝ)
    have hpair :
        (⟪gradientWithin
              (fun z ↦ ((g.toEReal z : EReal).toReal))
              (effectiveDomain g.toEReal)
              x, x - y⟫_ℝ -
          ⟪gradientWithin
              (fun z ↦ ((g.toEReal z : EReal).toReal))
              (effectiveDomain g.toEReal)
              y, x - y⟫_ℝ) =
          (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) - ⟪x - y, ∇ f x - ∇ f y⟫_ℝ := by
      rw [hxgrad, hygrad]
      have hpair' :=
        quadratic_gap_monotonicity_pairing_eq (f := f) (β := β) (x := x) (y := y)
      simpa [inner_sub_left, real_inner_smul_left] using hpair'
    -- Rewrite the canonical pairing into the scalar gap controlled by clause `(ii)`.
    rw [hpair]
    exact sub_nonneg.mpr (hinner x y)
  have hconv_toEReal :
      ConvexOn g.toEReal (effectiveDomain g.toEReal) :=
    convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
      g.toEReal
      (by simp [Function.effectiveDomain_toEReal])
      (by simp [Function.effectiveDomain_toEReal])
      (by
        simpa [Function.effectiveDomain_toEReal] using
          (convex_univ : Convex ℝ (Set.univ : Set H)))
      hdiff_g
      (Or.inl hmono)
  -- Convert the convexity result back from the everywhere-finite `toEReal` owner.
  simpa [g, Function.effectiveDomain_toEReal, Function.toEReal_apply] using
    (ConvexOn.toReal_convexOn_effectiveDomain hconv_toEReal)

/-- Helper for Theorem 18 15: a finite Moreau-envelope representation of `f` forces the
conjugate-side owner `(f* - β⁻¹ q)^*` to be proper. -/
lemma shifted_conjugate_conjugate_isProper_of_moreau_representation
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ))
    (hmoreau : f.toEReal.asEReal =
      {}^[(β⁻¹ : PosReal)]((conjugateSubInvHalfSquaredNorm f β).asEReal∗)) :
    IsProper ((conjugateSubInvHalfSquaredNorm f β).asEReal∗) := by
  let hstar : H → EReal := (conjugateSubInvHalfSquaredNorm f β).asEReal∗
  have hdom_nonempty :
      (effectiveDomain (conjugateSubInvHalfSquaredNorm f β)).Nonempty :=
    conjugateSubInvHalfSquaredNorm_effectiveDomain_nonempty f hcont hconv β
  refine ⟨?_, ?_⟩
  · intro x
    exact conjugate_ne_bot_of_effectiveDomain_nonempty hdom_nonempty x
  · by_contra hdom_empty
    have hall_top : ∀ x : H, hstar x = ⊤ := by
      intro x
      exact (not_mem_dom_iff hstar x).mp (by
        intro hx
        exact hdom_empty ⟨x, hx⟩)
    have henv_top :
        ({}^[(β⁻¹ : PosReal)] hstar) (0 : H) = ⊤ := by
      -- If the conjugate-side owner were `+∞` everywhere, then so would its Moreau envelope.
      rw [moreauEnvelope_apply, iInf_eq_top]
      intro x
      rw [hall_top x]
      exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    have hzero := congrFun hmoreau (0 : H)
    have htop : (f (0 : H) : EReal) = ⊤ := by
      calc
        (f (0 : H) : EReal) = ({}^[(β⁻¹ : PosReal)] hstar) (0 : H) := by
          simpa [hstar, Function.asEReal_apply, Function.toEReal_apply] using hzero
        _ = ⊤ := henv_top
    exact (EReal.coe_ne_top (f (0 : H))) htop

/-- Helper for Theorem 18 15: the Moreau envelope of a `Γ₀(H)` owner is finite at every point. -/
lemma moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    ({}^[γ] g) x ≠ ⊤ ∧ ({}^[γ] g) x ≠ ⊥ := by
  let p := Prox[γ, g, hg] x
  have hpdom : p ∈ effectiveDomain g := by
    simpa [p] using scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero g hg x γ
  have hgp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hpdom)
  have hgp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g p : EReal) from (g p).2)
  have hmoreau :
      ({}^[γ] g) x =
        (g p : EReal) +
          ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    -- Evaluate the Moreau envelope at the scaled proximal point.
    simpa [p] using moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero g hg γ x
  constructor
  · rw [hmoreau]
    exact EReal.add_ne_top hgp_top (EReal.coe_ne_top _)
  · rw [hmoreau]
    exact (EReal.add_ne_bot_iff.2 ⟨hgp_bot, EReal.coe_ne_bot _⟩)

/-- Helper for Theorem 18 15: evaluating the Moreau envelope at the proximal point centered at
`x` gives the quadratic upper tangent estimate at `x`. -/
lemma moreauEnvelope_toReal_sub_le_residual_inner_add_quadratic_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) (x y : H) :
    (({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal ≤
      ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ +
        (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
  let p := Prox[γ, g, hg] x
  have hpdom : p ∈ effectiveDomain g := by
    simpa [p] using scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero g hg x γ
  have hgp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hpdom)
  have hgp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g p : EReal) from (g p).2)
  have henvy_fin :
      ({}^[γ] g) y ≠ ⊤ ∧ ({}^[γ] g) y ≠ ⊥ :=
    moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero_local g hg γ y
  have hmajor :
      ({}^[γ] g) y ≤
        (g p : EReal) +
          ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal)) := by
    -- Evaluate the defining infimum at the proximal point attached to `x`.
    simpa [moreauEnvelope_apply, p] using
      (iInf_le
        (fun z : H ↦
          (g z : EReal) +
            ((((1 / (2 * (γ : ℝ))) * ‖y - z‖ ^ 2 : ℝ) : EReal)))
        p)
  have hmajor_real :
      (({}^[γ] g) y).toReal ≤
        (g p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 := by
    have hsum_top :
        (g p : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal)) ≠ ⊤ := by
      exact EReal.add_ne_top hgp_top (EReal.coe_ne_top _)
    have hsum_real :
        ((g p : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal))).toReal =
          (g p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 := by
      rw [EReal.toReal_add hgp_top hgp_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      rw [EReal.toReal_coe]
    calc
      (({}^[γ] g) y).toReal ≤
          ((g p : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal))).toReal :=
        EReal.toReal_le_toReal hmajor henvy_fin.2 hsum_top
      _ = (g p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 :=
        hsum_real
  have henvx :
      (({}^[γ] g) x).toReal =
        (g p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖x - p‖ ^ 2 := by
    have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
    have hmoreau :
        ({}^[γ] g) x =
          (g p : EReal) +
            ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      simpa [p] using moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero g hg γ x
    rw [hmoreau, EReal.toReal_add hgp_top hgp_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    have hdiv :
        ‖x - p‖ ^ 2 / (2 * (γ : ℝ)) = (1 / (2 * (γ : ℝ))) * ‖x - p‖ ^ 2 := by
      field_simp [hγ_ne]
    rw [hdiv, EReal.toReal_coe]
  have hsplit : y - p = (x - p) + (y - x) := by
    abel_nf
  have hnorm :
      ‖y - p‖ ^ 2 = ‖x - p‖ ^ 2 + 2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real]
  have hstep :
      (({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal ≤
        (1 / (2 * (γ : ℝ))) *
          (2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2) := by
    have hstep' :
        (({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal ≤
          (1 / (2 * (γ : ℝ))) * (‖y - p‖ ^ 2 - ‖x - p‖ ^ 2) := by
      linarith [hmajor_real, henvx]
    have hnorm' :
        ‖y - p‖ ^ 2 - ‖x - p‖ ^ 2 = 2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
      linarith [hnorm]
    simpa [hnorm'] using hstep'
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  have hcoeff :
      (1 / (2 * (γ : ℝ))) * (2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2) =
        ⟪(γ : ℝ)⁻¹ • (x - p), y - x⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
    rw [real_inner_smul_left]
    field_simp [hγ_ne]
  calc
    (({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal ≤
        (1 / (2 * (γ : ℝ))) * (2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2) :=
      hstep
    _ =
        ⟪(γ : ℝ)⁻¹ • (x - p), y - x⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 :=
      hcoeff

/-- Helper for Theorem 18 15: swapping the upper tangent estimate gives the companion lower
estimate involving the residual at `y`. -/
lemma residual_inner_sub_le_moreauEnvelope_toReal_sub_add_quadratic_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) (x y : H) :
    ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, g, hg] y), y - x⟫_ℝ -
        (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 ≤
      (({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal := by
  have hswap :
      (({}^[γ] g) x).toReal - (({}^[γ] g) y).toReal ≤
        ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, g, hg] y), x - y⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 :=
    moreauEnvelope_toReal_sub_le_residual_inner_add_quadratic_local g hg γ y x
  have hsub : x - y = -(y - x) := by
    abel_nf
  have hinner :
      ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, g, hg] y), x - y⟫_ℝ =
        -⟪(γ : ℝ)⁻¹ • (y - Prox[γ, g, hg] y), y - x⟫_ℝ := by
    rw [hsub, inner_neg_right]
  have hswap' :
      (({}^[γ] g) x).toReal - (({}^[γ] g) y).toReal ≤
        -⟪(γ : ℝ)⁻¹ • (y - Prox[γ, g, hg] y), y - x⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
    simpa [hinner, norm_sub_rev] using hswap
  nlinarith [hswap']

/-- Helper for Theorem 18 15: the scaled residual map `Id - Prox_{γ g}` is firmly nonexpansive. -/
lemma scaled_proximityOperator_firmlyNonexpansive_of_mem_gammaZero_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) :
    FirmlyNonexpansive (fun x : H ↦ Prox[γ, g, hg] x) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  let p := Prox[γ, g, hg] x
  let q := Prox[γ, g, hg] y
  let hγg : γ • g ∈ Γ₀(H) := smul_mem_gammaZero g hg γ
  have hp : IsProxPoint (γ • g) x p := by
    simpa [p, scaledProximityOperator] using
      proximityOperator_isProxPoint
        (γ • g)
        (hasUniqueProxPoint_of_mem_gammaZero (γ • g) hγg)
        x
  have hq : IsProxPoint (γ • g) y q := by
    simpa [q, scaledProximityOperator] using
      proximityOperator_isProxPoint
        (γ • g)
        (hasUniqueProxPoint_of_mem_gammaZero (γ • g) hγg)
        y
  have hp_dom : p ∈ effectiveDomain g :=
    scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero g hg x γ
  have hq_dom : q ∈ effectiveDomain g :=
    scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero g hg y γ
  have hgp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hgp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (g p).2
  have hgq_top : (g q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq_dom)
  have hgq_bot : (g q : EReal) ≠ ⊥ := by
    exact ne_of_gt (g q).2
  have hp_scaled_top : ((γ • g) p : EReal) ≠ ⊤ := by
    rw [posReal_smul_apply, EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
        Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hgp_top⟩
  have hp_scaled_bot : ((γ • g) p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < ((γ • g) p : EReal) from ((γ • g) p).2)
  have hq_scaled_top : ((γ • g) q : EReal) ≠ ⊤ := by
    rw [posReal_smul_apply, EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
        Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hgq_top⟩
  have hq_scaled_bot : ((γ • g) q : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < ((γ • g) q : EReal) from ((γ • g) q).2)
  have hpq_ereal := (isProxPoint_iff_forall_inner_add_le (γ • g) hγg.2 x p).mp hp q
  have hpq :
      ⟪q - p, x - p⟫_ℝ + (γ : ℝ) * (g p : EReal).toReal ≤
        (γ : ℝ) * (g q : EReal).toReal := by
    have hcast :
        (((⟪q - p, x - p⟫_ℝ + (γ : ℝ) * (g p : EReal).toReal : ℝ) : EReal)) ≤
          ((((γ : ℝ) * (g q : EReal).toReal : ℝ) : EReal)) := by
      simpa [posReal_smul_apply, EReal.coe_toReal hgp_top hgp_bot,
        EReal.coe_toReal hgq_top hgq_bot, EReal.coe_add, EReal.coe_mul] using hpq_ereal
    exact_mod_cast hcast
  have hqp_ereal := (isProxPoint_iff_forall_inner_add_le (γ • g) hγg.2 y q).mp hq p
  have hqp :
      ⟪p - q, y - q⟫_ℝ + (γ : ℝ) * (g q : EReal).toReal ≤
        (γ : ℝ) * (g p : EReal).toReal := by
    have hcast :
        (((⟪p - q, y - q⟫_ℝ + (γ : ℝ) * (g q : EReal).toReal : ℝ) : EReal)) ≤
          ((((γ : ℝ) * (g p : EReal).toReal : ℝ) : EReal)) := by
      simpa [posReal_smul_apply, EReal.coe_toReal hgp_top hgp_bot,
        EReal.coe_toReal hgq_top hgq_bot, EReal.coe_add, EReal.coe_mul] using hqp_ereal
    exact_mod_cast hcast
  have hsum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    linarith
  let d : H := p - q
  have hsub : y - q - (x - p) = d - (x - y) := by
    dsimp [d]
    abel_nf
  have hqpd : q - p = -d := by
    dsimp [d]
    abel_nf
  have hrewrite :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ =
        ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ
          = inner ℝ (-d) (x - p) + inner ℝ d (y - q) := by
              rw [hqpd]
      _ = -inner ℝ d (x - p) + inner ℝ d (y - q) := by
            simp
      _ = inner ℝ d (y - q) - inner ℝ d (x - p) := by
            ring_nf
      _ = inner ℝ d ((y - q) - (x - p)) := by
            symm
            rw [inner_sub_right]
      _ = inner ℝ d (d - (x - y)) := by
            rw [hsub]
      _ = inner ℝ d d - inner ℝ d (x - y) := by
            rw [inner_sub_right]
      _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
            rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hsum
  have hfinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (x - y) := by
    linarith
  simpa [d] using hfinal

/-- Helper for Theorem 18 15: the scaled residual map `Id - Prox_{γ g}` is firmly nonexpansive. -/
lemma scaled_residual_firmlyNonexpansive_of_mem_gammaZero_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) :
    FirmlyNonexpansive (fun x : H ↦ x - Prox[γ, g, hg] x) := by
  have hfirm :
      FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ Prox[γ, g, hg] x) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using
      scaled_proximityOperator_firmlyNonexpansive_of_mem_gammaZero_local g hg γ
  rw [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ]
  simpa [residualMap] using
    (firmlyNonexpansiveOn_residualMap_iff
      (Set.univ : Set H) (fun x : Set.univ ↦ Prox[γ, g, hg] x)).2 hfirm

/-- Helper for Theorem 18 15: firm nonexpansiveness of the scaled residual map yields the basic
monotonicity pairing needed in the Moreau remainder estimate. -/
lemma scaled_residual_inner_nonneg_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) (x y : H) :
    0 ≤ ⟪(y - Prox[γ, g, hg] y) - (x - Prox[γ, g, hg] x), y - x⟫_ℝ := by
  have hfirm :
      FirmlyNonexpansive (fun z : H ↦ z - Prox[γ, g, hg] z) :=
    scaled_residual_firmlyNonexpansive_of_mem_gammaZero_local g hg γ
  have hineq :
      ‖((y - Prox[γ, g, hg] y) - (x - Prox[γ, g, hg] x))‖ ^ 2 ≤
        ⟪(y - Prox[γ, g, hg] y) - (x - Prox[γ, g, hg] x), y - x⟫_ℝ := by
    simpa using (firmlyNonexpansive_iff_norm_sq_le_inner.mp hfirm) y x
  exact le_trans (sq_nonneg _) hineq

/-- Helper for Theorem 18 15: after scaling by `γ⁻¹`, residual monotonicity becomes the linear
comparison needed in the Moreau remainder estimate. -/
lemma scaled_residual_inner_mono_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) (x y : H) :
    ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ ≤
      ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, g, hg] y), y - x⟫_ℝ := by
  have hres :
      0 ≤ ⟪(y - Prox[γ, g, hg] y) - (x - Prox[γ, g, hg] x), y - x⟫_ℝ :=
    scaled_residual_inner_nonneg_local g hg γ x y
  have hbase :
      0 ≤
        ⟪y - Prox[γ, g, hg] y, y - x⟫_ℝ -
          ⟪x - Prox[γ, g, hg] x, y - x⟫_ℝ := by
    simpa [inner_sub_left] using hres
  have hscaled :
      0 ≤
        (γ : ℝ)⁻¹ *
          (⟪y - Prox[γ, g, hg] y, y - x⟫_ℝ -
            ⟪x - Prox[γ, g, hg] x, y - x⟫_ℝ) := by
    exact mul_nonneg (inv_nonneg.mpr γ.2.le) hbase
  have hdiff :
      0 ≤
        ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, g, hg] y), y - x⟫_ℝ -
          ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ := by
    rw [real_inner_smul_left, real_inner_smul_left]
    simpa [mul_sub] using hscaled
  linarith

/-- Helper for Theorem 18 15: the Moreau-envelope remainder after subtracting the linear term at
`x` is controlled by the quadratic error `‖h‖² / (2γ)`. -/
lemma moreauEnvelope_toReal_remainder_bound_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) (x h : H) :
    |(({}^[γ] g) (x + h)).toReal - (({}^[γ] g) x).toReal -
        ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), h⟫_ℝ| ≤
      (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
  let gradx := (γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x)
  let delta := (({}^[γ] g) (x + h)).toReal - (({}^[γ] g) x).toReal
  have hupper :
      delta ≤ ⟪gradx, h⟫_ℝ + (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
    simpa [gradx, delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      moreauEnvelope_toReal_sub_le_residual_inner_add_quadratic_local g hg γ x (x + h)
  have hlower_y :
      ⟪(γ : ℝ)⁻¹ • ((x + h) - Prox[γ, g, hg] (x + h)), h⟫_ℝ -
          (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 ≤
        delta := by
    simpa [delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      residual_inner_sub_le_moreauEnvelope_toReal_sub_add_quadratic_local g hg γ x (x + h)
  have hmono :
      ⟪gradx, h⟫_ℝ ≤ ⟪(γ : ℝ)⁻¹ • ((x + h) - Prox[γ, g, hg] (x + h)), h⟫_ℝ := by
    -- Compare the residual at `x` with the residual at `x + h` via firm nonexpansiveness.
    simpa [gradx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      scaled_residual_inner_mono_local g hg γ x (x + h)
  have hlower :
      ⟪gradx, h⟫_ℝ - (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 ≤ delta := by
    exact le_trans (sub_le_sub_right hmono _) hlower_y
  have hquad_nonneg : 0 ≤ (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
    have hcoeff_nonneg : 0 ≤ 1 / (2 * (γ : ℝ)) := by
      have hden_nonneg : 0 ≤ 2 * (γ : ℝ) := by
        nlinarith [γ.2]
      exact one_div_nonneg.mpr hden_nonneg
    exact mul_nonneg hcoeff_nonneg (sq_nonneg ‖h‖)
  have habs :
      |delta - ⟪gradx, h⟫_ℝ| ≤ (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
    refine abs_le.mpr ?_
    constructor
    · nlinarith [hlower, hquad_nonneg]
    · nlinarith [hupper, hquad_nonneg]
  simpa [gradx, delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using habs

/-- Helper for Theorem 18 15: the real-valued `γ`-Moreau envelope of a `Γ₀(H)` owner has pointwise
gradient `γ⁻¹ • (Id - Prox_{γ g})`. -/
lemma moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    HasGradientAt (fun y : H ↦ (({}^[γ] g) y).toReal)
      ((γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x)) x := by
  rw [hasGradientAt_iff_tendsto]
  have hbound :
      ∀ y : H,
        ‖y - x‖⁻¹ *
            ‖(({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal -
                ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ‖ ≤
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ := by
    intro y
    have hyx : x + (y - x) = y := by
      abel_nf
    have hrem :
        |(({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal -
            ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ| ≤
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
      simpa [hyx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        moreauEnvelope_toReal_remainder_bound_local g hg γ x (y - x)
    have hrem_norm :
        ‖(({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal -
            ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ‖ ≤
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
      simpa [Real.norm_eq_abs] using hrem
    by_cases hy : y = x
    · simp [hy]
    · have hnorm_ne : ‖y - x‖ ≠ 0 := by
        exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
      have hmul :
          ‖y - x‖⁻¹ *
              ‖(({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal -
                  ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ‖ ≤
            ‖y - x‖⁻¹ * ((1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hrem_norm (inv_nonneg.mpr (norm_nonneg _))
      calc
        ‖y - x‖⁻¹ *
            ‖(({}^[γ] g) y).toReal - (({}^[γ] g) x).toReal -
                ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x), y - x⟫_ℝ‖ ≤
            ‖y - x‖⁻¹ * ((1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2) :=
          hmul
        _ = (1 / (2 * (γ : ℝ))) * ‖y - x‖ := by
          rw [pow_two]
          calc
            ‖y - x‖⁻¹ * ((1 / (2 * (γ : ℝ))) * (‖y - x‖ * ‖y - x‖)) =
                (1 / (2 * (γ : ℝ))) * (‖y - x‖⁻¹ * ‖y - x‖) * ‖y - x‖ := by
                  ring
            _ = (1 / (2 * (γ : ℝ))) * 1 * ‖y - x‖ := by
                  rw [inv_mul_cancel₀ hnorm_ne]
            _ = (1 / (2 * (γ : ℝ))) * ‖y - x‖ := by
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
      Filter.Tendsto (fun y : H ↦ (1 / (2 * (γ : ℝ))) * ‖y - x‖)
        (nhds x) (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hnorm)
  exact squeeze_zero
    (fun y ↦ mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    hbound
    hupper

/-- Helper for Theorem 18 15: the gradient of the real-valued `γ`-Moreau envelope is the scaled
residual `γ⁻¹ • (Id - Prox_{γ g})`. -/
lemma gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) :
    ∇ (fun y : H ↦ (({}^[γ] g) y).toReal) =
      fun x ↦ (γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x) :=
  gradient_eq <|
    moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero_local g hg γ

/-- Helper for Theorem 18 15: the gradient field of the real-valued `γ`-Moreau envelope is
`γ⁻¹`-Lipschitz. -/
lemma lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (γ : PosReal) :
    LipschitzWith (Real.toNNReal ((γ : ℝ)⁻¹))
      (∇ (fun y : H ↦ (({}^[γ] g) y).toReal)) := by
  rw [gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero_local
    g hg γ]
  have hres :
      LipschitzWith 1 (fun x : H ↦ x - Prox[γ, g, hg] x) := by
    exact
      lipschitzWith_one_of_firmlyNonexpansive <|
        scaled_residual_firmlyNonexpansive_of_mem_gammaZero_local g hg γ
  have hscaled :
      LipschitzWith (‖(γ : ℝ)⁻¹‖₊ * 1)
        (fun x : H ↦ (γ : ℝ)⁻¹ • (x - Prox[γ, g, hg] x)) :=
    (lipschitzWith_smul ((γ : ℝ)⁻¹)).comp hres
  simpa [Real.toNNReal_eq_nnnorm_of_nonneg (inv_nonneg.mpr γ.2.le)] using hscaled

/-- Helper for Theorem 18 15: every subgradient of a `Γ₀(H)` owner becomes a subgradient of its
packaged Fenchel conjugate at the same dual point. -/
lemma mem_subdifferential_gammaZeroConjugate_of_mem_subdifferential_local
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) {p u : H} (hu : u ∈ (∂ g) p) :
    p ∈ (∂ (gammaZeroConjugate g hg)) u := by
  let _ : CompleteSpace H := inferInstance
  have hp_subdom : p ∈ SetValuedOperator.dom (∂ g) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  have hp_dom : p ∈ effectiveDomain g := by
    exact subdifferential_domain_subset_effectiveDomain g hg.2.nonempty hp_subdom
  have hp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (g p).2
  have hu_halfspace :
      ∀ y ∈ effectiveDomain g,
        ⟪y - p, u⟫_ℝ ≤ (g y : EReal).toReal - (g p : EReal).toReal := by
    rw [subdifferential_eq_iInter_affine_halfspaces g p hp_dom] at hu
    exact Set.mem_iInter₂.mp hu
  have hconj_upper :
      (gammaZeroConjugate g hg u : EReal) ≤
        (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) := by
    rw [gammaZeroConjugate_apply, conjugate_eq_sSup_image_dom]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy_dom : y ∈ effectiveDomain g := by
      simpa [effectiveDomain, dom] using hy
    have hy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
    have hy_bot : (g y : EReal) ≠ ⊥ := ne_of_gt (g y).2
    have hreal :
        ⟪y, u⟫_ℝ - (g y : EReal).toReal ≤
          ⟪p, u⟫_ℝ - (g p : EReal).toReal := by
      have hy_le := hu_halfspace y hy_dom
      have hinner : ⟪y - p, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪p, u⟫_ℝ := by
        simpa using inner_sub_left y p u
      nlinarith
    have hy_defect :
        (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal g x) y =
          (((⟪y, u⟫_ℝ - (g y : EReal).toReal : ℝ) : EReal)) := by
      change ((⟪y, u⟫_ℝ : EReal) - (g y : EReal)) =
        (((⟪y, u⟫_ℝ - (g y : EReal).toReal : ℝ) : EReal))
      rw [← EReal.coe_toReal hy_top hy_bot, EReal.coe_sub]
      simp
    rw [hy_defect]
    exact_mod_cast hreal
  have hconj_lower :
      (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) ≤
        (gammaZeroConjugate g hg u : EReal) := by
    have hp_mem_dom : p ∈ dom (g : H → EReal) := by
      simpa [effectiveDomain, dom] using hp_dom
    rw [gammaZeroConjugate_apply, conjugate_eq_sSup_image_dom]
    have hp_defect :
        (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) =
          (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal g x) p := by
      change (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) =
        ((⟪p, u⟫_ℝ : EReal) - (g p : EReal))
      rw [← EReal.coe_toReal hp_top hp_bot, EReal.coe_sub]
      simp
    rw [hp_defect]
    exact le_sSup (Set.mem_image_of_mem
      (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal g x) hp_mem_dom)
  have hconj_eq :
      (gammaZeroConjugate g hg u : EReal) =
        (((⟪p, u⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) :=
    le_antisymm hconj_upper hconj_lower
  -- Reinsert the Fenchel--Young equality into the subgradient inequality for the conjugate.
  rw [mem_subdifferential_iff]
  intro y
  have hfy :
      ((⟪p, y⟫_ℝ : ℝ) : EReal) ≤ (g p : EReal) + (gammaZeroConjugate g hg y : EReal) := by
    simpa [gammaZeroConjugate_apply, add_comm] using
      fenchel_young_inequality (f := (g : H → EReal)) (isProper_of_mem_gammaZero hg) p y
  calc
    (⟪y - u, p⟫_ℝ : EReal) + (gammaZeroConjugate g hg u : EReal) =
        (((⟪p, y⟫_ℝ - (g p : EReal).toReal : ℝ) : EReal)) := by
          rw [hconj_eq, ← EReal.coe_add]
          congr 1
          rw [inner_sub_left, real_inner_comm u p, real_inner_comm p y]
          ring
    _ = ((⟪p, y⟫_ℝ : ℝ) : EReal) - (g p : EReal) := by
          rw [← EReal.coe_toReal hp_top hp_bot, EReal.coe_sub]
          simp
    _ ≤ (gammaZeroConjugate g hg y : EReal) := by
          exact (EReal.sub_le_iff_le_add (.inl hp_bot) (.inl hp_top)).2 <| by
            simpa [add_comm] using hfy

/-- Helper for Theorem 18 15: the reciprocal-parameter scaled proximal point of the Fenchel
conjugate is the scaled residual of the primal scaled proximal point. -/
lemma conjugate_scaledProx_eq_inv_smul_sub_scaledProx_local
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    Prox[(γ⁻¹ : PosReal), gammaZeroConjugate f hf, gammaZeroConjugate_mem_gammaZero hf]
        ((γ : ℝ)⁻¹ • x) =
      (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x) := by
  let p := Prox[γ, f, hf] x
  let pStar := (γ : ℝ)⁻¹ • (x - p)
  have hprox :
      x - p ∈ (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) p := by
    -- Read the scaled proximal point as a subgradient inclusion for `γ • f`.
    simpa [p, scaledProximityOperator] using
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := (γ • f : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero f hf γ)
        (x := x)
        (p := p)).1 rfl
  have hsub :
      pStar ∈ (∂ f) p := by
    -- Undo the positive scalar on the subdifferential side.
    rw [subdifferential_posReal_smul_eq_smul (f := f) (γ := γ)] at hprox
    change x - p ∈ (γ : ℝ) • ((∂ f) p) at hprox
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hprox
    simpa [pStar, smul_smul, mul_inv_cancel₀ γ.2.ne'] using hprox
  have hconj :
      p ∈ (∂ (gammaZeroConjugate f hf)) pStar := by
    -- Transport the primal subgradient to the conjugate side.
    exact mem_subdifferential_gammaZeroConjugate_of_mem_subdifferential_local f hf hsub
  have hscaledConj :
      (γ : ℝ)⁻¹ • p ∈
        (∂ (((γ⁻¹ : PosReal) • (gammaZeroConjugate f hf) : H → Set.Ioi (⊥ : EReal)))) pStar := by
    -- Scale the conjugate subgradient by the reciprocal parameter.
    rw [subdifferential_posReal_smul_eq_smul (f := gammaZeroConjugate f hf)
      (γ := (γ⁻¹ : PosReal))]
    change (γ : ℝ)⁻¹ • p ∈ ((γ : ℝ)⁻¹) • ((∂ (gammaZeroConjugate f hf)) pStar)
    exact Set.smul_mem_smul_set hconj
  have hpStar :
      pStar =
        Prox[(γ⁻¹ : PosReal), gammaZeroConjugate f hf, gammaZeroConjugate_mem_gammaZero hf]
          ((γ : ℝ)⁻¹ • x) := by
    -- The reciprocal subgradient inclusion characterizes the conjugate proximal point.
    have hpStar_raw :
        pStar =
          Prox[((γ⁻¹ : PosReal) • (gammaZeroConjugate f hf)),
            smul_mem_gammaZero (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf)
              (γ⁻¹ : PosReal)] ((γ : ℝ)⁻¹ • x) := by
      apply (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := (((γ⁻¹ : PosReal) • (gammaZeroConjugate f hf) : H → Set.Ioi (⊥ : EReal))))
        (hf := smul_mem_gammaZero (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf)
          (γ⁻¹ : PosReal))
        (x := (γ : ℝ)⁻¹ • x)
        (p := pStar)).2
      simpa [p, pStar, sub_eq_add_neg, smul_sub, smul_smul, inv_mul_cancel₀ γ.2.ne',
        add_assoc, add_left_comm, add_comm] using hscaledConj
    simpa [scaledProximityOperator] using hpStar_raw
  exact hpStar.symm

/-- Helper for Theorem 18 15: Moreau's decomposition written directly with the packaged conjugate
owner instead of the Chapter 14 notation wrapper. -/
lemma id_eq_scaledProximityOperator_add_scaledProximityOperator_conjugate_local
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    id =
      Prox[γ, f, hf] +
        (γ : ℝ) •
          (fun x ↦
            Prox[(γ⁻¹ : PosReal), gammaZeroConjugate f hf, gammaZeroConjugate_mem_gammaZero hf]
              ((γ : ℝ)⁻¹ • x)) := by
  funext x
  let p := Prox[γ, f, hf] x
  have hproxStar :=
    conjugate_scaledProx_eq_inv_smul_sub_scaledProx_local (f := f) (hf := hf) (γ := γ) x
  have hres :
      (γ : ℝ) •
          (Prox[(γ⁻¹ : PosReal), gammaZeroConjugate f hf, gammaZeroConjugate_mem_gammaZero hf]
            ((γ : ℝ)⁻¹ • x)) = x - p := by
    rw [hproxStar]
    simp [p, smul_smul, mul_inv_cancel₀ γ.2.ne']
  -- Rearrange the reciprocal proximal identity into the source-facing Moreau decomposition.
  calc
    id x = x := rfl
    _ = p +
        (γ : ℝ) •
          (Prox[(γ⁻¹ : PosReal), gammaZeroConjugate f hf, gammaZeroConjugate_mem_gammaZero hf]
            ((γ : ℝ)⁻¹ • x)) := by
          rw [hres]
          abel_nf
    _ =
        (Prox[γ, f, hf] +
          (γ : ℝ) •
            (fun y ↦
              Prox[(γ⁻¹ : PosReal), gammaZeroConjugate f hf, gammaZeroConjugate_mem_gammaZero hf]
                ((γ : ℝ)⁻¹ • y))) x := by
          rfl

/-- Helper for Theorem 18 15: once the shifted conjugate lies in `Γ₀(H)`, Proposition 12.30 and
Moreau's decomposition identify `∇ f` with the primal and dual proximal formulas from clause
`(ix)`. -/
lemma shifted_conjugate_prox_formulas_of_mem_gammaZero
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ))
    (hgamma : conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H)) :
    (∇ f =
      fun x : H ↦
        Prox[β, conjugateSubInvHalfSquaredNorm f β, hgamma] ((β : ℝ) • x)) ∧
      ∇ f =
        fun x : H ↦
          (β : ℝ) •
            (x -
              Prox[(β⁻¹ : PosReal),
                gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma,
                gammaZeroConjugate_mem_gammaZero hgamma] x) := by
  let g := gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma
  have hmoreau :=
    shifted_conjugate_first_moreau_representation f hcont hconv β hgamma
  have hmoreau_real : f = fun x : H ↦ (({}^[(β⁻¹ : PosReal)] g) x).toReal := by
    funext x
    have hx : (f x : EReal) =
        ({}^[(β⁻¹ : PosReal)]((conjugateSubInvHalfSquaredNorm f β).asEReal∗)) x := by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using congrFun hmoreau x
    have hx' : (f x : EReal) = ({}^[(β⁻¹ : PosReal)] g) x := by
      simpa [g] using hx
    simpa [Function.toEReal_apply] using congrArg EReal.toReal hx'
  have hβinv : (((β⁻¹ : PosReal) : ℝ)⁻¹) = (β : ℝ) := by
    change ((β : ℝ)⁻¹)⁻¹ = (β : ℝ)
    exact inv_inv (β : ℝ)
  have hmoreau_grad :=
    gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero_local
      g
      (gammaZeroConjugate_mem_gammaZero hgamma)
      (β⁻¹ : PosReal)
  have hdual :
      ∇ f =
        fun x : H ↦
          (β : ℝ) •
            (x -
              Prox[(β⁻¹ : PosReal), g, gammaZeroConjugate_mem_gammaZero hgamma] x) := by
    funext x
    have hgrad :
        ∇ (fun y : H ↦ (({}^[(β⁻¹ : PosReal)] g) y).toReal) x =
          (β : ℝ) •
            (x -
              Prox[(β⁻¹ : PosReal),
                g,
                gammaZeroConjugate_mem_gammaZero hgamma] x) := by
      simpa [g, hβinv] using congrFun hmoreau_grad x
    -- Rewrite only the Moreau-envelope side pointwise to avoid
    -- dependent transport through `hgamma`.
    simpa [hmoreau_real] using hgrad
  have hprimal :
      ∇ f =
        fun x : H ↦
          Prox[β, conjugateSubInvHalfSquaredNorm f β, hgamma] ((β : ℝ) • x) := by
    funext x
    have hdecomp :=
      congrFun
        (id_eq_scaledProximityOperator_add_scaledProximityOperator_conjugate_local
          (f := conjugateSubInvHalfSquaredNorm f β) (hf := hgamma) (γ := β))
        ((β : ℝ) • x)
    have hdecomp' :
        (β : ℝ) • x =
          Prox[β, conjugateSubInvHalfSquaredNorm f β, hgamma] ((β : ℝ) • x) +
            (β : ℝ) •
              Prox[(β⁻¹ : PosReal), g, gammaZeroConjugate_mem_gammaZero hgamma] x := by
      simpa [g, smul_smul, inv_mul_cancel₀ (show (β : ℝ) ≠ 0 from ne_of_gt β.2), one_smul]
        using hdecomp
    have hdualx := congrFun hdual x
    calc
      ∇ f x =
          (β : ℝ) • x -
            (β : ℝ) • Prox[(β⁻¹ : PosReal), g, gammaZeroConjugate_mem_gammaZero hgamma] x := by
              simpa [smul_sub] using hdualx
      _ = Prox[β, conjugateSubInvHalfSquaredNorm f β, hgamma] ((β : ℝ) • x) := by
            exact (sub_eq_iff_eq_add).2 hdecomp'
  exact ⟨hprimal, by simpa [g] using hdual⟩

-- Proof sketch: specialize Corollary 18.14 to the case `p = 1` to obtain the equivalence of
-- clauses `(i)` through `(v)`. Then use Proposition 4.4 and Proposition 17.7 to identify
-- cocoercivity with convexity of `β q - f`, Proposition 14.2 for `(vi) ↔ (vii)`, Corollary 13.38
-- together with Proposition 14.1 and Theorem 14.3 for `(vii) → (viii) → (ix)`, and finally
-- Proposition 12.30 to recover clause `(i)` from `(ix)`.
/-- Theorem 18 15: for a continuous convex function `f : H → ℝ`, a positive parameter `β`, and
`h = f* - β⁻¹ q` with `q(x) = ‖x‖² / 2`, the standard smoothness, descent, cocoercivity,
convexity, and proximal formulations of `β`-Lipschitz differentiability are equivalent. -/
theorem frechetDifferentiable_tfae_lipschitz_gradient
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ)) :
    List.TFAE
      [ Differentiable ℝ f ∧ LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f),
        Differentiable ℝ f ∧
          ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ (β : ℝ) * ‖x - y‖ ^ (2 : ℕ),
        Differentiable ℝ f ∧
          ∀ x y : H,
            f y ≤
              f x + ⟪y - x, ∇ f x⟫_ℝ + ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ),
        Differentiable ℝ f ∧
          ∀ x y : H,
            conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (∇ f y) ≥
              conjugate (fun z : H ↦ ((f z : ℝ) : EReal)) (∇ f x) +
                ((⟪x, ∇ f y - ∇ f x⟫_ℝ : ℝ) : EReal) +
                  ((((1 / (2 * (β : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal)),
        Differentiable ℝ f ∧
          CocoerciveOn (1 / (β : ℝ)) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ f x),
        _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x),
        ConvexOn (conjugateSubInvHalfSquaredNorm f β)
          (effectiveDomain (conjugateSubInvHalfSquaredNorm f β)),
        f.toEReal.asEReal =
          {}^[(β⁻¹ : PosReal)]((conjugateSubInvHalfSquaredNorm f β).asEReal∗) ∧
          f.toEReal.asEReal =
            (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal -
              {}^[β] (conjugateSubInvHalfSquaredNorm f β) ∘ ((β : ℝ) • ·),
        conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H) ∧
          (∀ hgamma : conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H),
            ∇ f =
              fun x : H ↦
                Prox[β, conjugateSubInvHalfSquaredNorm f β, hgamma] ((β : ℝ) • x)) ∧
          ∀ hgamma : conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H),
            ∇ f =
              fun x : H ↦
                (β : ℝ) •
                  (x -
                    Prox[(β⁻¹ : PosReal),
                      gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma,
                      gammaZeroConjugate_mem_gammaZero hgamma] x) ] :=
  by
    -- Route correction: the checked-in `Corollary_18_14` owner is broken in this workspace, so
    -- this retry keeps the source-faithful front chain local: `(i) → (ii) → (iii) → (iv) → (v)`,
    -- then reuses the compile-safe endpoint `(v) → (i)` and the exact Chapter 14 bridge
    -- `(vi) ↔ (vii)`.
    tfae_have 1 → 2 := by
      rintro ⟨hdiff, hLip⟩
      refine ⟨hdiff, ?_⟩
      intro x y
      have hgrad :
          ‖∇ f x - ∇ f y‖ ≤ (β : ℝ) * ‖x - y‖ := by
        -- Unpack the Lipschitz estimate for the gradient into an ambient norm inequality.
        simpa [dist_eq_norm, Real.toNNReal_of_nonneg β.2.le] using hLip.dist_le_mul x y
      calc
        ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ ‖x - y‖ * ‖∇ f x - ∇ f y‖ := by
          exact real_inner_le_norm _ _
        _ ≤ ‖x - y‖ * ((β : ℝ) * ‖x - y‖) := by
          gcongr
        _ = (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) := by
          ring_nf
    tfae_have 2 → 3 := by
      rintro ⟨hdiff, hinner⟩
      refine ⟨hdiff, ?_⟩
      intro x y
      have hgrad : ∀ z : H, HasGradientAt f (∇ f z) z := fun z ↦ (hdiff z).hasGradientAt
      have hdescent :=
        descent_le_linearization_add_theta_of_gradient_inner_le_phi
          (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
          (f := f) (gradf := ∇ f) hgrad hinner x y
      have htheta_integral :
          ∫ t in (0 : ℝ)..1, ((β : ℝ) * (‖x - y‖ * t) ^ (2 : ℕ)) / t =
            ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
        calc
          ∫ t in (0 : ℝ)..1, ((β : ℝ) * (‖x - y‖ * t) ^ (2 : ℕ)) / t =
              θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖x - y‖ := by
                rw [theta_apply]
          _ = ((β : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) :=
            quadratic_theta_eq (β := β) (r := ‖x - y‖)
      -- Replace the abstract remainder `θ` by its quadratic closed form.
      simpa [htheta_integral] using hdescent
    tfae_have 3 → 4 := by
      rintro ⟨hdiff, hdescent⟩
      refine ⟨hdiff, ?_⟩
      intro x y
      have hquadratic_even : Function.Even (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) := by
        intro s
        simp
      have hdescent_theta :
          ∀ x y : H,
            f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ +
              θ (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖x - y‖ := by
        intro x y
        -- Repackage clause `(iii)` into the exact `θ`-surface used by Theorem 18.13.
        have hxy := hdescent x y
        rw [← quadratic_theta_eq (β := β) (r := ‖x - y‖)] at hxy
        simpa using hxy
      have hconj :=
        conjugate_gradient_ge_affine_add_thetaConjugate_of_descent_le_linearization_add_theta
          (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
          (f := f) (gradf := ∇ f) hquadratic_even hdescent_theta x y
      -- Evaluate the abstract quadratic conjugate in the exact coefficient used by clause `(iv)`.
      simpa [Function.asEReal_apply, Function.toEReal_apply,
        quadratic_thetaConj_eq (β := β) (r := ‖∇ f x - ∇ f y‖)] using hconj
    tfae_have 4 → 5 := by
      rintro ⟨hdiff, hconj⟩
      refine ⟨hdiff, ?_⟩
      refine (cocoerciveOn_univ_iff (H := H) (T := ∇ f)).2 ⟨?_, ?_⟩
      · -- The target cocoercivity parameter is the reciprocal positive scalar `β⁻¹`.
        simpa [one_div] using (show 0 < 1 / (β : ℝ) from one_div_pos.mpr β.2)
      · intro x y
        have hconj_theta :
            ∀ x y : H,
              f.toEReal.asEReal∗ (∇ f y) ≥
                f.toEReal.asEReal∗ (∇ f x) +
                  (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
                    thetaConj (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖∇ f x - ∇ f y‖ := by
          intro x y
          -- Re-express clause `(iv)` in the abstract `thetaConj` surface from Theorem 18.13.
          simpa [Function.asEReal_apply, Function.toEReal_apply,
            quadratic_thetaConj_eq (β := β) (r := ‖∇ f x - ∇ f y‖)] using hconj x y
        have hinner :=
          gradient_inner_ge_two_thetaConjugate_of_conjugate_gradient_ge_affine_add_thetaConjugate
            (φ := fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ))
            (f := f) (gradf := ∇ f) hconj_theta x y
        have hcoeff :
            ((((1 / (β : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal)) =
              (2 : EReal) *
                thetaConj (fun s : ℝ ↦ (β : ℝ) * s ^ (2 : ℕ)) ‖∇ f x - ∇ f y‖ := by
          have htwo : (2 : EReal) = ((2 : ℝ) : EReal) := by
            rfl
          rw [quadratic_thetaConj_eq (β := β) (r := ‖∇ f x - ∇ f y‖), htwo, ← EReal.coe_mul]
          congr 1
          change (1 / (β : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) =
            2 * ((1 / (2 * (β : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ))
          field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
        have hereal :
            ((((1 / (β : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
              ((⟪x - y, ∇ f x - ∇ f y⟫_ℝ : ℝ) : EReal) := by
          -- Replace `2 θ*` by the explicit quadratic coefficient `β⁻¹`.
          rw [hcoeff]
          simpa using hinner
        exact_mod_cast hereal
    tfae_have 5 → 1 := by
      rintro ⟨hdiff, hcoco⟩
      refine ⟨hdiff, ?_⟩
      have hsub :
          LipschitzWith (Real.toNNReal (β : ℝ))
            (fun x : (Set.univ : Set H) ↦ ∇ f (x : H)) := by
        -- The Chapter 4 owner gives the subtype-valued Lipschitz estimate on `Set.univ`.
        simpa [one_div, Real.toNNReal_of_nonneg β.2.le] using
          (lipschitzWith_of_cocoercive
            (T := fun x : (Set.univ : Set H) ↦ ∇ f (x : H))
            (β := 1 / (β : ℝ))
            ((cocoerciveOn_univ_iff (H := H) (T := ∇ f)).2 ⟨by
              simpa [one_div] using (show 0 < 1 / (β : ℝ) from one_div_pos.mpr β.2),
                fun x y ↦ by
                  have hcoco' := (cocoerciveOn_univ_iff (H := H) (T := ∇ f)).1 hcoco
                  simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hcoco'.2 x y⟩))
      -- The Chapter 4 owner turns `β⁻¹`-cocoercivity back into a `β`-Lipschitz bound.
      refine LipschitzWith.of_dist_le' ?_
      intro x y
      simpa [Subtype.dist_eq, Real.toNNReal_of_nonneg β.2.le] using
        hsub.dist_le_mul ⟨x, by simp⟩ ⟨y, by simp⟩
    tfae_have 6 ↔ 7 := by
      -- Proposition 14.2 is exactly the shifted-quadratic / shifted-conjugate convexity bridge.
      simpa using
        (conjugateSubInvHalfSquaredNorm_convex_iff_halfSquaredNorm_sub_convex
          (f := f) hcont hconv β).symm
    tfae_have 2 → 6 := by
      rintro ⟨hdiff, hinner⟩
      -- Proposition 17.9 upgrades the monotone quadratic-gap gradient to convexity of `β q - f`.
      exact quadratic_gap_convex_of_gradient_upper_bound f β hdiff hinner
    tfae_have 7 → 8 := by
      intro hshift_conv
      -- Upgrade clause `(vii)` to `Γ₀(H)` and then invoke the Chapter 14 Moreau identities.
      have hgamma :
          conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H) :=
        conjugateSubInvHalfSquaredNorm_mem_gammaZero_of_halfSquaredNorm_sub_convex
          f hcont hconv β <|
          (conjugateSubInvHalfSquaredNorm_convex_iff_halfSquaredNorm_sub_convex
            (f := f) hcont hconv β).mp hshift_conv
      exact
        ⟨shifted_conjugate_first_moreau_representation f hcont hconv β hgamma,
          shifted_conjugate_quadratic_gap_representation f hcont hconv β⟩
    tfae_have 7 → 9 := by
      intro hshift_conv
      have hgamma :
          conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H) :=
        conjugateSubInvHalfSquaredNorm_mem_gammaZero_of_halfSquaredNorm_sub_convex
          f hcont hconv β <|
          (conjugateSubInvHalfSquaredNorm_convex_iff_halfSquaredNorm_sub_convex
            (f := f) hcont hconv β).mp hshift_conv
      -- Clause `(ix)` is exactly the proximal API extracted from the `Γ₀(H)` owner.
      refine ⟨hgamma, ?_, ?_⟩
      · intro hgamma'
        exact
          (shifted_conjugate_prox_formulas_of_mem_gammaZero f hcont hconv β hgamma').1
      · intro hgamma'
        exact
          (shifted_conjugate_prox_formulas_of_mem_gammaZero f hcont hconv β hgamma').2
    tfae_have 8 → 1 := by
      rintro ⟨hmoreau, _⟩
      let hstar : H → EReal := (conjugateSubInvHalfSquaredNorm f β).asEReal∗
      have hproper : IsProper hstar :=
        shifted_conjugate_conjugate_isProper_of_moreau_representation f hcont hconv β hmoreau
      let g : H → Set.Ioi (⊥ : EReal) := properIoi hstar hproper
      have hgamma : g ∈ Γ₀(H) := by
        -- Package the proper conjugate owner back into `Γ₀(H)`.
        exact
          properIoi_mem_gammaZero_of_mem_gamma hproper
            (conjugate_mem_gamma ((conjugateSubInvHalfSquaredNorm f β).asEReal))
      have hmoreau_owner : {}^[(β⁻¹ : PosReal)] g = {}^[(β⁻¹ : PosReal)] hstar := by
        funext x
        -- The packaged owner and the raw conjugate have the same `EReal` values pointwise.
        rw [moreauEnvelope_apply, moreauEnvelope_apply]
        congr with y
      have hmoreau_real : f = fun x : H ↦ (({}^[(β⁻¹ : PosReal)] g) x).toReal := by
        funext x
        have hx : (f x : EReal) = ({}^[(β⁻¹ : PosReal)] hstar) x := by
          simpa [hstar, Function.asEReal_apply, Function.toEReal_apply] using
            congrFun hmoreau x
        have hx' : (f x : EReal) = ({}^[(β⁻¹ : PosReal)] g) x := by
          calc
            (f x : EReal) = ({}^[(β⁻¹ : PosReal)] hstar) x := hx
            _ = ({}^[(β⁻¹ : PosReal)] g) x := by
              simpa using (congrFun hmoreau_owner x).symm
        simpa [Function.toEReal_apply] using congrArg EReal.toReal hx'
      refine ⟨?_, ?_⟩
      · rw [hmoreau_real]
        intro x
        -- The local Moreau-gradient theorem gives differentiability at every point.
        exact
          (moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero_local
            g hgamma (β⁻¹ : PosReal) x).differentiableAt
      · rw [hmoreau_real]
        have hβinv : (((β⁻¹ : PosReal) : ℝ)⁻¹) = (β : ℝ) := by
          change ((β : ℝ)⁻¹)⁻¹ = (β : ℝ)
          exact inv_inv (β : ℝ)
        -- The local Moreau Lipschitz theorem matches the target coefficient after simplifying
        -- the reciprocal parameter.
        simpa [hβinv, Real.toNNReal_of_nonneg β.2.le] using
          (lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero_local
            g hgamma (β⁻¹ : PosReal))
    tfae_have 9 → 7 := by
      rintro ⟨hgamma, _, _⟩
      -- Clause `(ix)` already carries the `Γ₀(H)` owner, so recover convexity on the effective
      -- domain through the canonical Chapter 14 bridge.
      exact
        convexOn_effectiveDomain_of_mem_gamma
          (conjugateSubInvHalfSquaredNorm_effectiveDomain_nonempty f hcont hconv β)
          (asEReal_mem_gamma_of_mem_gammaZero hgamma)
    tfae_finish

end StrongerDifferentiabilityNotions

end ERealFunction
