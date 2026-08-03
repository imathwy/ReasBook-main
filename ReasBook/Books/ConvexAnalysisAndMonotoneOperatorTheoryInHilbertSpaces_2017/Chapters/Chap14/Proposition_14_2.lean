import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap08.Example_8_10
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Proposition_12_11
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.Definition_12_20_Core
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Example_13_4
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Proposition_13_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: `conjugate f u` is already strictly above `-∞`, and subtracting a finite real
-- quadratic term preserves that lower bound in `EReal`.
/-- Subtracting the finite quadratic term `γ⁻¹ ‖u‖² / 2` from the conjugate of a real-valued
function still yields an `]-∞,+∞]`-valued function. -/
theorem conjugate_sub_invHalfSquaredNorm_gt_bot
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) (u : H) :
    ⊥ < f.toEReal.asEReal∗ u - moreauQuadraticKernel γ u := by
  -- The Fenchel conjugate of a finite-valued function is never `-∞`.
  refine bot_lt_iff_ne_bot.mpr ?_
  have hconj : f.toEReal.asEReal∗ u ≠ ⊥ := by
    exact conjugate_ne_bot_of_effectiveDomain_nonempty (by simp) u
  have hkernel : (moreauQuadraticKernel γ u : EReal) ≠ ⊤ := by
    simpa using
      (EReal.coe_ne_top (((1 / (2 * (γ : ℝ))) * ‖u‖ ^ (2 : ℕ) : ℝ)))
  change f.toEReal.asEReal∗ u + -↑(moreauQuadraticKernel γ u) ≠ ⊥
  rw [EReal.add_ne_bot_iff]
  constructor
  · exact hconj
  · intro hneg
    exact hkernel (EReal.neg_eq_bot_iff.mp hneg)

/-- The shifted conjugate `f* - γ⁻¹ q`, packaged through the canonical Moreau quadratic kernel
as an `]-∞,+∞]`-valued function. -/
noncomputable def conjugateSubInvHalfSquaredNorm
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) : H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨f.toEReal.asEReal∗ u - moreauQuadraticKernel γ u,
      conjugate_sub_invHalfSquaredNorm_gt_bot f γ u⟩

/-- Coercing `conjugateSubInvHalfSquaredNorm f γ` to `EReal` recovers the canonical expression
`f.toEReal.asEReal∗ - moreauQuadraticKernel γ`. -/
@[simp] theorem conjugateSubInvHalfSquaredNorm_apply
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) (u : H) :
    (conjugateSubInvHalfSquaredNorm f γ u : EReal) =
      f.toEReal.asEReal∗ u - moreauQuadraticKernel γ u :=
  rfl

end Conjugation

section ConjugationComplete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 14 2: the shifted conjugate has nonempty effective domain because the
Fenchel conjugate of `f` is already packaged as a `Γ₀(H)` function with nonempty effective
domain. -/
lemma conjugateSubInvHalfSquaredNorm_effectiveDomain_nonempty
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (γ : Set.Ioi (0 : ℝ)) :
    (effectiveDomain (conjugateSubInvHalfSquaredNorm f γ)).Nonempty := by
  -- Package `f` as a `Γ₀(H)` object so that its conjugate has nonempty domain.
  have hfΓ : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  have hproper_f : IsProper f.toEReal.asEReal := isProper_of_mem_gammaZero hfΓ
  have hgamma_f : f.toEReal.asEReal ∈ gamma H := asEReal_mem_gamma_of_mem_gammaZero hfΓ
  rcases (conjugate_is_proper_of_mem_gamma hproper_f hgamma_f).2 with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  -- Subtracting the finite quadratic kernel preserves finiteness above at that point.
  rw [mem_effectiveDomain_iff, lt_top_iff_ne_top, conjugateSubInvHalfSquaredNorm_apply,
    sub_eq_add_neg]
  have hconj_bot : f.toEReal.asEReal∗ u ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty (by simp) u
  have hconj_top : f.toEReal.asEReal∗ u ≠ ⊤ := lt_top_iff_ne_top.mp hu
  have hkernel_top : (moreauQuadraticKernel γ u : EReal) ≠ ⊤ := by
    simpa using
      (EReal.coe_ne_top (((1 / (2 * (γ : ℝ))) * ‖u‖ ^ (2 : ℕ) : ℝ)))
  have hkernel_bot : (moreauQuadraticKernel γ u : EReal) ≠ ⊥ := by
    simpa using
      (EReal.coe_ne_bot (((1 / (2 * (γ : ℝ))) * ‖u‖ ^ (2 : ℕ) : ℝ)))
  have hneg_bot : (-↑(moreauQuadraticKernel γ u) : EReal) ≠ ⊥ := by
    intro hneg
    exact hkernel_top (EReal.neg_eq_bot_iff.mp hneg)
  have hneg_top : (-↑(moreauQuadraticKernel γ u) : EReal) ≠ ⊤ := by
    intro hneg
    exact hkernel_bot (EReal.neg_eq_top_iff.mp hneg)
  exact (EReal.add_ne_top_iff_ne_top₂ hconj_bot hneg_bot).2 ⟨hconj_top, hneg_top⟩

section

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 2: multiplying the Moreau quadratic kernel by `γ` recovers the
standard quadratic `q(x) = ‖x‖² / 2`. -/
private lemma scaled_moreauQuadraticKernel_eq_halfSquaredNorm
    (γ : Set.Ioi (0 : ℝ)) (u : H) :
    ((γ : ℝ) : EReal) * (moreauQuadraticKernel γ u : EReal) = halfSquaredNorm.asEReal u := by
  -- Rewrite both kernels as real casts so the scalar normalization happens in `ℝ`.
  rw [Function.asEReal_apply, moreauQuadraticKernel_apply, halfSquaredNorm_apply, EReal.coe_mul]
  have hγ0 : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  have hreal : (γ : ℝ) * ((1 / (2 * (γ : ℝ))) * ‖u‖ ^ 2) = (‖u‖ ^ 2) / 2 := by
    field_simp [hγ0]
  -- The real coefficients simplify to the unit-parameter quadratic coefficient `1 / 2`.
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

end

/-- Helper for Proposition 14 2: evaluating Example 13.4 at the shifted conjugate gives the
pointwise identity `{}^[γ](f* - γ⁻¹ q)(γx) = γ q(x) - f(x)`. -/
private lemma moreauEnvelope_shifted_conjugate_value_eq_quadratic_gap
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) (hfΓ : f.toEReal ∈ Γ₀(H)) (x : H) :
    ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) ((γ : ℝ) • x) =
      ((((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x : ℝ) : EReal) := by
  let m : EReal := ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) ((γ : ℝ) • x)
  have hsum :
      ((conjugateSubInvHalfSquaredNorm f γ + moreauQuadraticKernel γ).asEReal) =
        f.toEReal.asEReal∗ := by
    ext u
    -- Adding back the quadratic kernel recovers the Fenchel conjugate of `f`.
    rw [Function.asEReal_apply, add_apply, conjugateSubInvHalfSquaredNorm_apply,
      moreauQuadraticKernel_apply]
    exact EReal.sub_add_cancel
  have hraw :
      f.toEReal.asEReal∗∗ x =
        ((((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) - m := by
    -- Route correction: rewrite Example 13.4 pointwise before transporting the biconjugate.
    simpa [hsum] using
      conjugate_regularized_value_eq_scaledQuadratic_sub_moreauEnvelope
        (φ := conjugateSubInvHalfSquaredNorm f γ) (γ := γ) x
  have hbiconj :
      f.toEReal.asEReal∗∗ x = (f x : EReal) := by
    -- Fenchel--Moreau collapses the biconjugate because `f.toEReal ∈ Γ₀(H)`.
    simpa [Function.asEReal_apply, Function.toEReal_apply] using
      congrFun (biconjugate_eq_of_mem_gammaZero hfΓ) x
  have hraw' : (f x : EReal) = ((((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) - m := by
    exact hbiconj.symm.trans hraw
  have hm_top : m ≠ ⊤ := by
    intro hm_top
    rw [hm_top] at hraw'
    simp at hraw'
  have hm_bot : m ≠ ⊥ := by
    intro hm_bot
    rw [sub_eq_add_neg, hm_bot, EReal.neg_bot] at hraw'
    have hquad_ne_bot :
        ((((γ : ℝ) / 2 : ℝ) : EReal) * (((‖x‖ : ℝ) : EReal) ^ (2 : ℕ))) ≠ ⊥ := by
      simpa [EReal.coe_mul] using
        (EReal.coe_ne_bot (((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ))
    have hraw_top : (f x : EReal) = ⊤ := by
      calc
        (f x : EReal) =
            ((((γ : ℝ) / 2 : ℝ) : EReal) * (((‖x‖ : ℝ) : EReal) ^ (2 : ℕ))) + ⊤ := by
              simpa [EReal.coe_mul] using hraw'
        _ = ⊤ := EReal.add_top_of_ne_bot hquad_ne_bot
    exact (EReal.coe_ne_top (f x)) hraw_top
  have hraw_real :
      f x = ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - m.toReal := by
    have hrawE :
        (f x : EReal) =
          (((((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) - m := by
      simpa using hraw'
    have hquad_top :
        (((((γ : ℝ) / 2 : ℝ) : EReal) * ((‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) : EReal) ≠ ⊤ := by
      simpa [EReal.coe_mul] using
        (EReal.coe_ne_top (((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ))
    have hquad_bot :
        (((((γ : ℝ) / 2 : ℝ) : EReal) * ((‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) : EReal) ≠ ⊥ := by
      simpa [EReal.coe_mul] using
        (EReal.coe_ne_bot (((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ))
    have htoReal' :
        f x =
          (((((γ : ℝ) / 2 : ℝ) : EReal) * ((‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) - m).toReal := by
      simpa [EReal.coe_mul] using congrArg EReal.toReal hrawE
    rw [EReal.toReal_sub hquad_top hquad_bot hm_top hm_bot] at htoReal'
    simpa using htoReal'
  have hm_real : m.toReal = ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x := by
    linarith
  -- The Moreau-envelope value is finite, so the target follows by recovering it from `toReal`.
  change m = ((((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x : ℝ) : EReal)
  rw [← EReal.coe_toReal hm_top hm_bot]
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hm_real

/-- Helper for Proposition 14 2: Example 13.4 rewrites `γ q - f` as the `γ`-Moreau envelope of
the shifted conjugate composed with the homothety `x ↦ γ • x`. -/
lemma halfSquaredNorm_sub_eq_moreauEnvelope_conjugateSubInvHalfSquaredNorm_comp_smul
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) (hfΓ : f.toEReal ∈ Γ₀(H)) :
    (fun x : H ↦ ((((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) - (f x : EReal)) =
      fun x : H ↦ ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) ((γ : ℝ) • x) := by
  funext x
  -- Use the pointwise Example 13.4 transport and then read the result from left to right.
  simpa using (moreauEnvelope_shifted_conjugate_value_eq_quadratic_gap f γ hfΓ x).symm

section

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 2: the quadratic gap `x ↦ γ q(x) - f x` is continuous whenever
`f` is continuous. -/
private lemma continuous_quadratic_gap
    (f : H → ℝ) (hcont : Continuous f) (γ : Set.Ioi (0 : ℝ)) :
    Continuous (fun x : H ↦ ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) := by
  -- The quadratic term is continuous, so subtracting the continuous `f` preserves continuity.
  have hquad_cont : Continuous (fun x : H ↦ ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ)) := by
    simpa using continuous_const.mul (continuous_norm.pow 2)
  simpa using hquad_cont.sub hcont

end

/-- Helper for Proposition 14 2: the shifted conjugate, scaled by `γ`, is the Fenchel conjugate
appearing in Proposition 13.29 for `g := γ q - f`. -/
lemma smul_conjugateSubInvHalfSquaredNorm_eq_conjugate_gap
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ))
    {g : H → ℝ} (hg : g = fun x : H ↦ ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x)
    (hgΓ : Function.toEReal g ∈ Γ₀(H)) :
    (fun u : H ↦ ((γ : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f γ u : EReal)) =
      (fun x : H ↦
        ((γ : ℝ) : EReal) * (gammaZeroConjugate (Function.toEReal g) hgΓ x : EReal) -
          halfSquaredNorm.asEReal x)∗ := by
  ext u
  have hgap :
      (fun v : H ↦
        ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
          (gammaZeroConjugate (Function.toEReal g) hgΓ).asEReal∗ v) =
        f.toEReal.asEReal := by
    ext v
    have hconjv :
        (gammaZeroConjugate (Function.toEReal g) hgΓ).asEReal∗ v =
          g.toEReal.asEReal∗∗ v := by
      rfl
    have hbiconjv : g.toEReal.asEReal∗∗ v = (g v : EReal) := by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using
        congrFun (biconjugate_eq_of_mem_gammaZero hgΓ) v
    -- Replace the inner biconjugate by `g`, then simplify `γ q - g` back to `f`.
    rw [Function.asEReal_apply, hconjv, hbiconjv, hg, halfSquaredNorm_apply, ← EReal.coe_mul,
      ← EReal.coe_sub]
    have hreal :
        (γ : ℝ) * ((‖v‖ ^ 2) / 2) - (((γ : ℝ) / 2) * ‖v‖ ^ (2 : ℕ) - f v) = f v := by
      ring
    simpa [Function.asEReal_apply, Function.toEReal_apply] using
      congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  have hprop :=
    congrFun
      (conjugate_smul_sub_halfSquaredNorm_eq
        (f := gammaZeroConjugate (Function.toEReal g) hgΓ) (γ := γ)
        (hproper := isProper_of_mem_gammaZero (gammaZeroConjugate_mem_gammaZero hgΓ)))
      u
  have hgap_conj :
      (fun v : H ↦
        ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
          (gammaZeroConjugate (Function.toEReal g) hgΓ).asEReal∗ v)∗ =
        f.toEReal.asEReal∗ := by
    rw [hgap]
  calc
    ((γ : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f γ u : EReal)
        = ((γ : ℝ) : EReal) * f.toEReal.asEReal∗ u - halfSquaredNorm.asEReal u := by
            have hγ_nonneg : (0 : EReal) ≤ ((γ : ℝ) : EReal) := by
              exact_mod_cast γ.2.le
            have hγ_ne_top : ((γ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top (γ : ℝ)
            -- Distribute the scalar using the positive-coefficient `EReal` distributivity lemma.
            rw [conjugateSubInvHalfSquaredNorm_apply, sub_eq_add_neg]
            rw [EReal.left_distrib_of_nonneg_of_ne_top hγ_nonneg hγ_ne_top, mul_neg]
            rw [scaled_moreauQuadraticKernel_eq_halfSquaredNorm, sub_eq_add_neg]
    _ =
        ((fun x : H ↦
          ((γ : ℝ) : EReal) * (gammaZeroConjugate (Function.toEReal g) hgΓ x : EReal) -
            halfSquaredNorm.asEReal x)∗) u := by
          -- Proposition 13.29 identifies the scaled shifted conjugate with the target conjugate.
          have hprop' := hprop
          rw [hgap_conj] at hprop'
          exact hprop'.symm

section

omit [CompleteSpace H] in
/-- Helper for Proposition 14 2: a `γ(H)` member whose effective domain is nonempty is convex on
its effective domain in the source-facing Chapter 8 sense. -/
lemma convexOn_effectiveDomain_of_mem_gamma
    {φ : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain φ).Nonempty)
    (hγ : φ.asEReal ∈ gamma H) :
    ConvexOn φ (effectiveDomain φ) := by
  -- Upgrade the raw `gamma H` owner to `Γ₀(H)` via the proper packaging of `φ.asEReal`.
  have hproper : IsProper φ.asEReal := by
    refine ⟨?_, ?_⟩
    · intro x
      exact ne_of_gt (show (⊥ : EReal) < φ.asEReal x from (φ x).2)
    · simpa [effectiveDomain, dom] using hdom
  have hΓ : properIoi φ.asEReal hproper ∈ Γ₀(H) :=
    properIoi_mem_gammaZero_of_mem_gamma hproper hγ
  have hrepr : φ = properIoi φ.asEReal hproper := by
    funext x
    apply Subtype.ext
    rfl
  rw [hrepr]
  exact (mem_gammaZero_iff.mp hΓ).2

end

-- Proof sketch: for `(i) → (ii)`, apply the Fenchel--Moreau identities from Chapter 13 to the
-- convex function `f* - γ⁻¹ q` and identify `γ q - f` with a Moreau-envelope expression, whose
-- convexity follows from Proposition 12.15. For `(ii) → (i)`, write `f = γ q - g` with `g`
-- convex, use Proposition 13.29 to rewrite `f* - γ⁻¹ q` as a positive multiple of a conjugate,
-- and conclude by convexity of Fenchel conjugates.
/-- Proposition 14 2: for a continuous convex real-valued function `f` on a real Hilbert space and
`γ ∈ ℝ_{++}`, the shifted conjugate `f* - γ⁻¹ q` with `q(x) = ‖x‖² / 2` is convex if and only if
`γ q - f` is convex. -/
theorem conjugateSubInvHalfSquaredNorm_convex_iff_halfSquaredNorm_sub_convex
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (γ : Set.Ioi (0 : ℝ)) :
    ConvexOn (conjugateSubInvHalfSquaredNorm f γ)
      (effectiveDomain (conjugateSubInvHalfSquaredNorm f γ)) ↔
      _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) := by
  let g : H → ℝ := fun x ↦ ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x
  have hfΓ : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  constructor
  · intro hshift
    let pTwo : Set.Ici (1 : ℝ) := ⟨(2 : ℝ), by norm_num⟩
    have hpTwo : (1 : ℝ) < pTwo := by
      change (1 : ℝ) < (2 : ℝ)
      norm_num
    have hkernel_eq :
        normPowerKernel (H := H) pTwo γ = moreauQuadraticKernel γ := by
      ext x
      have hγ0 : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
      have hreal :
          ‖x‖ ^ (2 : ℕ) / ((γ : ℝ) * 2) = (1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 := by
        field_simp [hγ0]
      simpa [pTwo, normPowerKernel_apply, moreauQuadraticKernel_apply, Real.rpow_natCast] using
        congrArg (fun r : ℝ ↦ (r : EReal)) hreal
    have hkernelΓ : moreauQuadraticKernel γ ∈ Γ₀(H) := by
      -- Package the quadratic kernel through the existing `p = 2` owner from Chapter 12.
      simpa [hkernel_eq] using
        normPowerKernel_mem_gammaZero (H := H) pTwo γ hpTwo
    have hmoreau_epi :
        Convex ℝ (epigraph ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ))) := by
      -- The Moreau envelope is an infimal convolution of two convex source functions.
      change Convex ℝ
        (epigraph ((conjugateSubInvHalfSquaredNorm f γ) □ (moreauQuadraticKernel γ)))
      exact
        convex_epigraph_infimalConvolution
          (conjugateSubInvHalfSquaredNorm f γ)
          (moreauQuadraticKernel γ)
          hshift
          (mem_gammaZero_iff.mp hkernelΓ).2
    have hmoreau_jensen :=
      (convex_epigraph_iff_jensen_on_dom ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ))).1
        hmoreau_epi
    rw [convexOn_iff_forall_pos]
    constructor
    · exact convex_univ
    · intro x _ y _ a b ha hb hab
      have ha_lt_one : a < 1 := by
        linarith
      have hb_eq : b = 1 - a := by
        linarith
      have hx_dom :
          (γ : ℝ) • x ∈ dom ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) := by
        rw [mem_dom_iff]
        rw [moreauEnvelope_shifted_conjugate_value_eq_quadratic_gap f γ hfΓ x]
        exact EReal.coe_lt_top _
      have hy_dom :
          (γ : ℝ) • y ∈ dom ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) := by
        rw [mem_dom_iff]
        rw [moreauEnvelope_shifted_conjugate_value_eq_quadratic_gap f γ hfΓ y]
        exact EReal.coe_lt_top _
      have hineq0 :
          ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ))
              (a • ((γ : ℝ) • x) + (1 - a) • ((γ : ℝ) • y)) ≤
            (a : EReal) * ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) ((γ : ℝ) • x) +
              (((1 - a : ℝ) : EReal) *
                ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) ((γ : ℝ) • y)) := by
        exact hmoreau_jensen hx_dom hy_dom ha ha_lt_one
      have hineq :
          ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ))
              ((γ : ℝ) • (a • x + b • y)) ≤
            (a : EReal) * ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) ((γ : ℝ) • x) +
              ((b : EReal) * ({}^[γ] (conjugateSubInvHalfSquaredNorm f γ)) ((γ : ℝ) • y)) := by
        simpa [hb_eq, smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hineq0
      have hineq_real :
          (((g (a • x + b • y) : ℝ) : EReal)) ≤
            (((a * g x + b * g y : ℝ) : EReal)) := by
        -- Route correction: rewrite the Jensen inequality only after transporting the three
        -- Moreau-envelope values pointwise through Example 13.4.
        rw [moreauEnvelope_shifted_conjugate_value_eq_quadratic_gap f γ hfΓ (a • x + b • y),
          moreauEnvelope_shifted_conjugate_value_eq_quadratic_gap f γ hfΓ x,
          moreauEnvelope_shifted_conjugate_value_eq_quadratic_gap f γ hfΓ y] at hineq
        simpa [g, EReal.coe_mul, EReal.coe_add] using hineq
      exact_mod_cast hineq_real
  · intro hgap_conv
    have hg_cont : Continuous g := by
      -- Reuse the named continuity bridge for the source-side quadratic gap.
      simpa [g] using continuous_quadratic_gap f hcont γ
    have hgΓ : g.toEReal ∈ Γ₀(H) :=
      real_toEReal_mem_gammaZero_of_continuous_convexOn_univ g hg_cont hgap_conv
    have hscaled_gamma :
        (fun u : H ↦ ((γ : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f γ u : EReal)) ∈
          gamma H := by
      have hscaled_repr :=
        smul_conjugateSubInvHalfSquaredNorm_eq_conjugate_gap f γ rfl hgΓ
      -- Proposition 13.29 packages the scaled shifted conjugate as a Fenchel conjugate.
      rw [hscaled_repr]
      exact
        conjugate_mem_gamma
          (fun x : H ↦
            ((γ : ℝ) : EReal) * (gammaZeroConjugate g.toEReal hgΓ x : EReal) -
              halfSquaredNorm.asEReal x)
    have hh_gamma :
        (fun u : H ↦ (conjugateSubInvHalfSquaredNorm f γ u : EReal)) ∈ gamma H := by
      have hscaled_inv :
          (fun u : H ↦
            (((γ : ℝ)⁻¹ : EReal) *
              (((γ : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f γ u : EReal)))) ∈
              gamma H := by
        exact const_mul_mem_gamma_of_nonneg hscaled_gamma (inv_nonneg.mpr γ.2.le)
      have hcancel :
          (fun u : H ↦
            (((γ : ℝ)⁻¹ : EReal) *
              (((γ : ℝ) : EReal) * (conjugateSubInvHalfSquaredNorm f γ u : EReal)))) =
            (fun u : H ↦ (conjugateSubInvHalfSquaredNorm f γ u : EReal)) := by
        ext u
        have hcoeff : (((γ : ℝ)⁻¹ : EReal) * ((γ : ℝ) : EReal)) = 1 := by
          rw [← EReal.coe_inv, ← EReal.coe_mul,
            inv_mul_cancel₀ (show (γ : ℝ) ≠ 0 from ne_of_gt γ.2),
            EReal.coe_one]
        rw [← mul_assoc, hcoeff, one_mul]
      -- Divide the `gamma` owner by the positive scalar `γ`.
      rw [← hcancel]
      exact hscaled_inv
    exact
      convexOn_effectiveDomain_of_mem_gamma
        (conjugateSubInvHalfSquaredNorm_effectiveDomain_nonempty f hcont hconv γ)
        hh_gamma

end ConjugationComplete

end ERealFunction
