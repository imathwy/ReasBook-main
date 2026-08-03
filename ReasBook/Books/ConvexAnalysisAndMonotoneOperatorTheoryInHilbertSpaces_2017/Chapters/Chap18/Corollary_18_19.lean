import Mathlib
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap08.Corollary_8_40
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.Proposition_12_30
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap14.Proposition_14_1
import BauschkeLean.Chap14.Proposition_14_2
import BauschkeLean.Chap17.Proposition_17_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction Gradient InnerProductSpace Pointwise

universe u

namespace ERealFunction

section MoreauCharacterizationOfSmoothConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 18.19: if the quadratic gap `β q - f` is convex, then the shifted
conjugate `f* - β⁻¹ q` belongs to `Γ₀(H)`. -/
lemma conjugateSubInvHalfSquaredNorm_mem_gammaZero_of_halfSquaredNorm_sub_convex
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ))
    (hgap_conv : _root_.ConvexOn ℝ Set.univ
      (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x)) :
    conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H) := by
  let g : H → ℝ := fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x
  have hg_cont : Continuous g := by
    have hquad_cont : Continuous (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ)) := by
      simpa using continuous_const.mul (continuous_norm.pow 2)
    simpa [g] using hquad_cont.sub hcont
  have hgΓ : g.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ g hg_cont hgap_conv
  have hscaled_gamma :
      (fun u : H ↦ ((β : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f β u : EReal)) ∈
        gamma H := by
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
  rw [hrepr]
  exact properIoi_mem_gammaZero_of_mem_gamma hproper hh_gamma

/-- Helper for Corollary 18.19: Proposition 14.2 gives the quadratic-gap Moreau representation
of `f` once `f` is packaged in `Γ₀(H)`. -/
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
    simpa [sub_eq_add_neg, ← EReal.coe_sub] using hgap.symm
  have hkernel :
      ((((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) =
        (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal x := by
    rw [Function.asEReal_apply, moreauQuadraticKernel_apply]
    congr 1
    change ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) = (1 / (2 * (β : ℝ)⁻¹)) * ‖x‖ ^ (2 : ℕ)
    have hcoeff : (1 / (2 * (β : ℝ)⁻¹) : ℝ) = (β : ℝ) / 2 := by
      field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
    rw [hcoeff]
  calc
    (f.toEReal.asEReal x : EReal) =
        ((((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) -
          ({}^[β] (conjugateSubInvHalfSquaredNorm f β)) ((β : ℝ) • x) := by
            rw [hgap', ← EReal.coe_sub]
            norm_num
    _ =
        (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal x -
          ({}^[β] (conjugateSubInvHalfSquaredNorm f β)) ((β : ℝ) • x) := by
            rw [hkernel]

/-- Helper for Corollary 18.19: once the shifted conjugate lies in `Γ₀(H)`, Proposition 14.1
identifies `f` with the reciprocal-parameter Moreau envelope of its conjugate. -/
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
    ext u
    rw [Pi.add_apply, Function.asEReal_apply]
    have hreal :
        ((((((β⁻¹ : PosReal) : ℝ) : EReal) • halfSquaredNorm.asEReal) u)) =
          (moreauQuadraticKernel β u : EReal) := by
      rw [Pi.smul_apply, Function.asEReal_apply, halfSquaredNorm_apply, smul_eq_mul]
      calc
        ((((β⁻¹ : PosReal) : ℝ) : EReal) * ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal))) =
            ((((β⁻¹ : PosReal) : ℝ) * ((‖u‖ ^ (2 : ℕ)) / 2) : ℝ) : EReal) := by
              rw [← EReal.coe_mul]
        _ = (moreauQuadraticKernel β u : EReal) := by
              rw [moreauQuadraticKernel_apply]
              congr 1
              have hβ0 : (β : ℝ) ≠ 0 := ne_of_gt β.2
              calc
                ((β : ℝ)⁻¹ * ((‖u‖ ^ (2 : ℕ)) / 2) : ℝ) =
                    ((β : ℝ)⁻¹ * ‖u‖ ^ (2 : ℕ)) / 2 := by ring
                _ = (1 / (2 * (β : ℝ))) * ‖u‖ ^ (2 : ℕ) := by
                      field_simp [hβ0]
    calc
      ((conjugateSubInvHalfSquaredNorm f β u : EReal) +
          ((((((β⁻¹ : PosReal) : ℝ) : EReal) • halfSquaredNorm.asEReal) u))) =
          ((conjugateSubInvHalfSquaredNorm f β u : EReal) +
            (moreauQuadraticKernel β u : EReal)) := by
              rw [hreal]
      _ = f.toEReal.asEReal∗ u := by
            rw [conjugateSubInvHalfSquaredNorm_apply]
            exact EReal.sub_add_cancel
  have hmoreau_owner :=
    conjugate_add_scaledQuadratic_eq_moreauEnvelope_gammaZeroConjugate
      (f := conjugateSubInvHalfSquaredNorm f β) (hf := hgamma) (γ := (β⁻¹ : PosReal))
  have hmoreau :
      f.toEReal.asEReal∗∗ =
        {}^[(β⁻¹ : PosReal)] (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma) := by
    calc
      f.toEReal.asEReal∗∗ =
          (((conjugateSubInvHalfSquaredNorm f β).asEReal +
              ((((β⁻¹ : PosReal) : ℝ) : EReal) • halfSquaredNorm.asEReal))∗) := by
                rw [howner]
      _ =
          {}^[(β⁻¹ : PosReal)] (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma) :=
        hmoreau_owner
  calc
    f.toEReal.asEReal = f.toEReal.asEReal∗∗ := by
      symm
      exact biconjugate_eq_of_mem_gammaZero hfΓ
    _ =
        {}^[(β⁻¹ : PosReal)] (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hgamma) :=
      hmoreau
    _ = {}^[(β⁻¹ : PosReal)]((conjugateSubInvHalfSquaredNorm f β).asEReal∗) := by
      rfl

/-- Helper for Corollary 18.19: the quadratic gap `x ↦ β q(x) - f x` has gradient
`x ↦ β • x - ∇ f x` when `f` is Fréchet differentiable. -/
lemma quadratic_gap_hasGradientAt
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (hdiff : Differentiable ℝ f) (x : H) :
    HasGradientAt (fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y)
      ((β : ℝ) • x - ∇ f x) x := by
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
  convert hquad.sub hf using 2
  ext y
  simp [ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply, sub_eq_add_neg]
  ring

/-- Helper for Corollary 18.19: the canonical `gradientWithin` field of the quadratic gap agrees
with the explicit gradient `x ↦ β • x - ∇ f x`. -/
lemma gradientWithin_quadratic_gap_toEReal_eq
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (hdiff : Differentiable ℝ f) (x : H) :
    gradientWithin
      (fun z : H ↦
        (((fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y).toEReal z : EReal).toReal))
      (effectiveDomain ((fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y).toEReal))
      x =
      (β : ℝ) • x - ∇ f x := by
  let g : H → ℝ := fun y : H ↦ ((β : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y
  have hdiff_g :
      DifferentiableOn ℝ (fun z : H ↦ ((g.toEReal z : EReal).toReal)) (effectiveDomain g.toEReal) :=
    by
      intro z hz
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

/-- Helper for Corollary 18.19: the monotonicity pairing of the quadratic-gap gradient field
reduces to the scalar gap `β ‖x - y‖² - ⟪x - y, ∇ f x - ∇ f y⟫`. -/
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
        (β : ℝ) * ⟪x, x - y⟫_ℝ - ⟪∇ f x, x - y⟫_ℝ -
            ((β : ℝ) * ⟪y, x - y⟫_ℝ - ⟪∇ f y, x - y⟫_ℝ) =
          (β : ℝ) * (⟪x, x - y⟫_ℝ - ⟪y, x - y⟫_ℝ) -
            (⟪∇ f x, x - y⟫_ℝ - ⟪∇ f y, x - y⟫_ℝ) := by
              ring
        _ = (β : ℝ) * ⟪x - y, x - y⟫_ℝ - ⟪∇ f x - ∇ f y, x - y⟫_ℝ := by
              rw [hxy, hgrad]
        _ = (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) - ⟪x - y, ∇ f x - ∇ f y⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq, real_inner_comm]

/-- Helper for Corollary 18.19: the quadratic upper bound on `∇ f` forces the quadratic gap
`x ↦ β q(x) - f x` to be convex on all of `H`. -/
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
  simpa [g, Function.effectiveDomain_toEReal, Function.toEReal_apply] using
    (ConvexOn.toReal_convexOn_effectiveDomain hconv_toEReal)

/-- Helper for Corollary 18.19: a Moreau-envelope representation forces the conjugate-side owner
to be proper, which is exactly what Proposition 12.30 needs. -/
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

/-- Corollary 18.19: for `f ∈ Γ₀(H)` viewed through its real-valued representative and
`β ∈ ℝ_{++}`, `f` is Fréchet differentiable on `H` with `β`-Lipschitz gradient if and only if
`f` is the `β⁻¹`-Moreau envelope of the shifted conjugate `f^* - β⁻¹ q`, equivalently
`f = q / β - {}^[β] (f^* - β⁻¹ q) ∘ (β • ·)`, where `q(x) = ‖x‖² / 2`. -/
theorem differentiable_lipschitzGradient_iff_moreauEnvelope_eq_of_mem_gammaZero
    (f : H → ℝ) (hf : f.toEReal ∈ Γ₀(H)) (β : Set.Ioi (0 : ℝ)) :
    (Differentiable ℝ f ∧ LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f)) ↔
      f.toEReal.asEReal =
          {}^[(β⁻¹ : PosReal)]((conjugateSubInvHalfSquaredNorm f β).asEReal∗) ∧
        f.toEReal.asEReal =
          (moreauQuadraticKernel (β⁻¹ : PosReal)).asEReal -
            {}^[β] (conjugateSubInvHalfSquaredNorm f β) ∘ ((β : ℝ) • ·) := by
  have hconv : _root_.ConvexOn ℝ Set.univ f := by
    simpa [Function.effectiveDomain_toEReal] using hf.2.toReal_convexOn_effectiveDomain
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    have hx_local :
        x ∈
          {x : H |
            ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f.toEReal ∧
              ContinuousAt (fun y : H ↦ (f.toEReal y : EReal).toReal) x} := by
      rw [continuous_points_eq_interior_effectiveDomain_of_lowerSemicontinuous
        (g := f.toEReal) hf]
      simp [Function.effectiveDomain_toEReal]
    rcases hx_local with ⟨ρ, hρ, -, hxcont⟩
    simpa [Function.toEReal_apply] using hxcont
  constructor
  · rintro ⟨hdiff, hLip⟩
    have hinner :
        ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) := by
      intro x y
      have hgrad :
          ‖∇ f x - ∇ f y‖ ≤ (β : ℝ) * ‖x - y‖ := by
        simpa [dist_eq_norm, Real.toNNReal_of_nonneg β.2.le] using hLip.dist_le_mul x y
      calc
        ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ ‖x - y‖ * ‖∇ f x - ∇ f y‖ := by
          exact real_inner_le_norm _ _
        _ ≤ ‖x - y‖ * ((β : ℝ) * ‖x - y‖) := by
          gcongr
        _ = (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) := by
          ring_nf
    have hgap_conv :
        _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) :=
      quadratic_gap_convex_of_gradient_upper_bound f β hdiff hinner
    have hgamma :
        conjugateSubInvHalfSquaredNorm f β ∈ Γ₀(H) :=
      conjugateSubInvHalfSquaredNorm_mem_gammaZero_of_halfSquaredNorm_sub_convex
        f hcont hconv β hgap_conv
    refine ⟨?_, ?_⟩
    · exact shifted_conjugate_first_moreau_representation f hcont hconv β hgamma
    · exact shifted_conjugate_quadratic_gap_representation f hcont hconv β
  · rintro ⟨hmoreau, _⟩
    let hstar : H → EReal := (conjugateSubInvHalfSquaredNorm f β).asEReal∗
    have hproper : IsProper hstar :=
      shifted_conjugate_conjugate_isProper_of_moreau_representation f hcont hconv β hmoreau
    let g : H → Set.Ioi (⊥ : EReal) := properIoi hstar hproper
    have hgamma : g ∈ Γ₀(H) := by
      exact
        properIoi_mem_gammaZero_of_mem_gamma hproper
          (conjugate_mem_gamma ((conjugateSubInvHalfSquaredNorm f β).asEReal))
    have hmoreau_owner : {}^[(β⁻¹ : PosReal)] g = {}^[(β⁻¹ : PosReal)] hstar := by
      funext x
      rw [moreauEnvelope_apply, moreauEnvelope_apply]
      congr with y
    have hmoreau_real : f = fun x : H ↦ (({}^[(β⁻¹ : PosReal)] g) x).toReal := by
      funext x
      have hx : (f x : EReal) = ({}^[(β⁻¹ : PosReal)] hstar) x := by
        simpa [hstar, Function.asEReal_apply, Function.toEReal_apply] using congrFun hmoreau x
      have hx' : (f x : EReal) = ({}^[(β⁻¹ : PosReal)] g) x := by
        calc
          (f x : EReal) = ({}^[(β⁻¹ : PosReal)] hstar) x := hx
          _ = ({}^[(β⁻¹ : PosReal)] g) x := by
              simpa using (congrFun hmoreau_owner x).symm
      simpa [Function.toEReal_apply] using congrArg EReal.toReal hx'
    refine ⟨?_, ?_⟩
    · rw [hmoreau_real]
      intro x
      exact
        (moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
          g (β⁻¹ : PosReal) hgamma x).differentiableAt
    · rw [hmoreau_real]
      have hβinv : (((β⁻¹ : PosReal) : ℝ)⁻¹) = (β : ℝ) := by
        change ((β : ℝ)⁻¹)⁻¹ = (β : ℝ)
        exact inv_inv (β : ℝ)
      simpa [hβinv, Real.toNNReal_of_nonneg β.2.le] using
        (lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero
          g (β⁻¹ : PosReal) hgamma)

end MoreauCharacterizationOfSmoothConvexFunctions

end ERealFunction
