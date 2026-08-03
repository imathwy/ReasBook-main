import Mathlib
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap14.Proposition_14_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace translate

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Theorem 14 17: the negative inner-product linear functional is a convex lower
semicontinuous `EReal`-valued function. -/
lemma linear_neg_inner_mem_gamma (u : H) :
    (fun x : H ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) ∈ Γ(H) := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The functional is affine, so Jensen's inequality is an equality.
    intro x y a ha0 ha1
    apply le_of_eq
    have hreal :
        -⟪a • x + (1 - a) • y, u⟫_ℝ =
          a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      ring
    rw [show (1 - a : EReal) = ((1 - a : ℝ) : EReal) by norm_num, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  · -- Continuity of the inner product yields lower semicontinuity after coercion to `EReal`.
    simpa [Function.comp] using
      (continuous_coe_real_ereal.comp
        ((continuous_id.inner continuous_const).neg)).lowerSemicontinuous

omit [CompleteSpace H] in
/-- Helper for Theorem 14 17: the everywhere-finite perturbation `x ↦ -⟪x,u⟫` belongs to
`Γ₀(H)` via the canonical coercion to `]-∞,+∞]`. -/
lemma linear_neg_inner_toEReal_mem_gammaZero (u : H) :
    (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) := by
  -- Repackage the `Γ(H)` statement through `toEReal`.
  exact
    toEReal_mem_gammaZero_of_mem_gamma (H := H) (f := fun x : H ↦ -⟪x, u⟫_ℝ)
      (linear_neg_inner_mem_gamma (H := H) u)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 14 17: translating by `-u` moves the interior-domain condition at `0`
exactly to the point `u`. -/
lemma zero_mem_interior_dom_translate_neg_iff (g : H → EReal) (u : H) :
    (0 : H) ∈ interior (dom (τ (-u) g)) ↔ u ∈ interior (dom g) := by
  have hdom :
      dom (τ (-u) g) = (Homeomorph.addRight u) ⁻¹' dom g := by
    -- Translating by `-u` is precomposition with the right-translation `x ↦ x + u`.
    ext x
    simp [dom, translate_apply, sub_eq_add_neg, add_comm]
  have hpre :
      (Homeomorph.addRight u) ⁻¹' interior (dom g) =
        interior ((Homeomorph.addRight u) ⁻¹' dom g) := by
    simpa using (Homeomorph.preimage_interior (Homeomorph.addRight u) (dom g))
  constructor
  · intro hzero
    -- Rewrite the translated domain as a preimage, then evaluate at the origin.
    have hzero' : (0 : H) ∈ (Homeomorph.addRight u) ⁻¹' interior (dom g) := by
      rw [hpre]
      simpa [hdom] using hzero
    simpa using hzero'
  · intro hu
    -- The same homeomorphism transports interior membership back to the translated domain.
    have hzero' : (0 : H) ∈ (Homeomorph.addRight u) ⁻¹' interior (dom g) := by
      simpa using hu
    rw [hpre] at hzero'
    simpa [hdom] using hzero'

-- Proof sketch: Proposition 14.16 identifies coercivity of an element of `Γ₀(H)` with
-- membership of `0` in the interior of the domain of its Fenchel conjugate. Apply this to the
-- linear perturbation `x ↦ f x - ⟪x, u⟫`, then use Proposition 13.23 (iii) with zero translation
-- and constant term to rewrite its conjugate as the translate
-- `v ↦ f^*(v + u)`, which moves the interior-domain condition from `0` to `u`.
/-- Theorem 14 17: the Moreau--Rockafellar coercivity criterion says that for `f ∈ Γ₀(H)` and
`u ∈ H`, the linear perturbation `x ↦ f x - ⟪x, u⟫` is coercive exactly when `u` lies in the
interior of the domain of the Fenchel conjugate `f*`. -/
theorem coercive_sub_inner_iff_mem_interior_dom_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    Coercive (f.asEReal - fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) ↔
      u ∈ interior (dom f.asEReal∗) := by
  let perturbation : H → Set.Ioi (⊥ : EReal) :=
    f + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal
  have hlinear : (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) :=
    linear_neg_inner_toEReal_mem_gammaZero (H := H) u
  have hdom_inter :
      (effectiveDomain f ∩ effectiveDomain ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal)).Nonempty := by
    -- The linear term is finite everywhere, so any effective-domain point of `f` works.
    rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp [hx]
  have hpert : perturbation ∈ Γ₀(H) := by
    -- Package the linear perturbation as a sum of two `Γ₀(H)` functions.
    simpa [perturbation] using pointwiseAdd_mem_gammaZero
      f ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) hf hlinear hdom_inter
  have hcoercive_iff_zero :
      Coercive perturbation.asEReal ↔
        (0 : H) ∈ interior (dom perturbation.asEReal∗) :=
    List.TFAE.out
      (coercive_tfae_lowerLevelSet_asymptoticSlope_affineLowerBound_conjugate perturbation hpert)
      0 5
  have hconj :
      perturbation.asEReal∗ = τ (-u) (f.asEReal∗) := by
    -- Proposition 13.23(iii) identifies the perturbation conjugate with the translated conjugate.
    ext w
    simpa [perturbation, translate_apply, Function.toEReal_apply, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm, inner_neg_right] using
      congrFun
        (conjugate_translate_add_inner_add_const (f := f.asEReal) (y := 0) (v := -u) (β := 0))
        w
  have hzero_iff_u :
      (0 : H) ∈ interior (dom perturbation.asEReal∗) ↔
        u ∈ interior (dom f.asEReal∗) := by
    -- After the conjugate rewrite, the interior-domain condition is just transport by translation.
    rw [hconj]
    exact zero_mem_interior_dom_translate_neg_iff (g := f.asEReal∗) u
  -- The packaged perturbation is exactly the raw function `x ↦ f x - ⟪x,u⟫`.
  simpa [perturbation, Function.toEReal_apply, sub_eq_add_neg, inner_neg_right] using
    hcoercive_iff_zero.trans hzero_iff_u

end Conjugation

end ERealFunction
