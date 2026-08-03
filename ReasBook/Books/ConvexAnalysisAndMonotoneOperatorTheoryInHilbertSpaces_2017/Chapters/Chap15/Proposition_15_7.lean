import Mathlib
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap12.Proposition_12_14
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap14.Proposition_14_15
import BauschkeLean.Chap14.Proposition_14_16
import BauschkeLean.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace translate

universe u

namespace ERealFunction

section AttouchBrezisTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: `InfimalConvolutionRegularity` is the proposition-specific five-branch
  regularity predicate from Proposition 15.7.
- `core/canonical`: the derived conclusions should land in the existing owners
  `infimalConvolution.Exact` and `IsProper (f □ g) ∧ (f □ g) ∈ gamma H`,
  using the Chapter 12, 14, and 15 regularity criteria rather than
  introducing a second exactness/properness wrapper.
- `bridge/view`: the five source clauses are kept literally here, and the derived API below routes
  them to the chapter owners.
-/
/-- The five source regularity alternatives from Proposition 15.7 that force exactness and
proper convexity of the infimal convolution `f □ g`. Clause (ii) uses the reflected owner
`g.asERealᵛ`. -/
def InfimalConvolutionRegularity
    (f g : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ((0 : H) ∈
      sri (dom f.asEReal∗ - dom g.asEReal∗)) ∨
    (Coercive (f.asEReal + g.asERealᵛ) ∧
      (0 : H) ∈ sri (dom f.asEReal - dom g.asERealᵛ)) ∨
    (Coercive f.asEReal ∧ BddBelow (range g)) ∨
    dom f.asEReal∗ = univ ∨
    Supercoercive f.asEReal

namespace InfimalConvolutionRegularity

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: `0 ∈ sri (dom f - dom g)` forces the two effective domains to
intersect. -/
lemma effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (effectiveDomain f ∩ effectiveDomain g).Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, ?_⟩
  simpa [sub_eq_zero.mp hxy] using hy

/-
Keep completeness out of scope here so the helper does not pick up an unused section variable.
-/
omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: the Attouch--Brézis strong-relative-interior hypothesis implies
that the pointwise sum again belongs to `Γ₀(H)`. -/
theorem pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    f + g ∈ Γ₀(H) :=
  pointwiseAdd_mem_gammaZero f g hf hg
    (effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain f g hsri)

/-- Helper for Proposition 15 7: the affine tilt of an `EReal`-valued function by the linear term
`x ↦ -⟪x, u⟫`. -/
private noncomputable def affineTiltEReal (φ : H → EReal) (u : H) : H → EReal :=
  fun x ↦ φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal))

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: evaluating the affine tilt exposes the added linear term. -/
@[simp] private theorem affineTiltEReal_apply
    (φ : H → EReal) (u x : H) :
    affineTiltEReal φ u x = φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal)) :=
  rfl

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: affine tilting a `Γ₀(H)` function preserves properness. -/
private theorem affine_tilt_isProper
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    IsProper (affineTiltEReal f.asEReal u) := by
  have htilt_eq_coe :
      ∀ ⦃x : H⦄, x ∈ effectiveDomain f →
        affineTiltEReal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
    intro x hx
    have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  constructor
  · intro x
    by_cases hx : x ∈ effectiveDomain f
    · rw [htilt_eq_coe hx]
      exact EReal.coe_ne_bot _
    · have hx_top : f.asEReal x = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
      rw [affineTiltEReal, hx_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
      simp
  · rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_dom_iff, htilt_eq_coe hx]
    simpa using (EReal.coe_lt_top (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ)))

/-- Helper for Proposition 15 7: package the affine tilt back into the `Set.Ioi (⊥ : EReal)`
codomain used by the chapter API. -/
private noncomputable abbrev affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (affineTiltEReal f.asEReal u) (affine_tilt_isProper f hf u)

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: coercing the packaged affine tilt back to `EReal` recovers the
raw tilted function. -/
@[simp] private theorem affineTiltIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u x : H) :
    (affineTiltIoi f hf u x : EReal) = affineTiltEReal f.asEReal u x := by
  rfl

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: the packaged affine tilt of a `Γ₀(H)` function still lies in
`Γ₀(H)`. -/
private theorem affine_tilt_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    affineTiltIoi f hf u ∈ Γ₀(H) := by
  have hlinear_gamma :
      (fun x : H ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) ∈ Γ(H) := by
    rw [mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      change (((-(⟪a • x + (1 - a) • y, u⟫_ℝ) : ℝ) : EReal)) ≤
        (a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
          (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))
      have hreal :
          -(⟪a • x + (1 - a) • y, u⟫_ℝ) =
            a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      have hsub : (1 - (a : EReal)) = (((1 - a : ℝ)) : EReal) := by
        norm_num
      rw [hreal, hsub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    · simpa using
        (continuous_coe_real_ereal.comp
          ((continuous_id.inner continuous_const).neg)).lowerSemicontinuous
  have htilt_gamma : affineTiltEReal f.asEReal u ∈ Γ(H) := by
    have hf_gamma : f.asEReal ∈ Γ(H) := asEReal_mem_gamma_of_mem_gammaZero hf
    rw [mem_gamma_iff] at hf_gamma hlinear_gamma ⊢
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      have haE_nonneg : (0 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha0
      have hbE_nonneg : (0 : EReal) ≤ (1 - a : EReal) := by
        exact_mod_cast sub_nonneg.mpr ha1
      have haE_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
      have hbE_ne_top : (1 - a : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - a)
      calc
        affineTiltEReal f.asEReal u (a • x + (1 - a) • y)
            ≤ ((a : EReal) * f.asEReal x + (1 - a : EReal) * f.asEReal y) +
                ((a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
                  (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))) := by
              simpa [affineTiltEReal] using
                add_le_add (hf_gamma.1 ha0 ha1) (hlinear_gamma.1 ha0 ha1)
        _ = (a : EReal) * affineTiltEReal f.asEReal u x +
              (1 - a : EReal) * affineTiltEReal f.asEReal u y := by
              simp [affineTiltEReal,
                EReal.left_distrib_of_nonneg_of_ne_top haE_nonneg haE_ne_top,
                EReal.left_distrib_of_nonneg_of_ne_top hbE_nonneg hbE_ne_top,
                add_assoc, add_left_comm]
    · rw [lowerSemicontinuous_iff_le_liminf]
      intro x
      calc
        affineTiltEReal f.asEReal u x
            ≤ Filter.liminf f.asEReal (nhds x) +
                Filter.liminf (fun y : H ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal))) (nhds x) := by
              simpa [affineTiltEReal] using
                add_le_add (hf_gamma.2.le_liminf x) (hlinear_gamma.2.le_liminf x)
        _ ≤ Filter.liminf (affineTiltEReal f.asEReal u) (nhds x) := by
              simpa [affineTiltEReal] using
                (EReal.le_liminf_add :
                  Filter.liminf f.asEReal (nhds x) +
                      Filter.liminf
                        (fun y : H ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                        (nhds x) ≤
                    Filter.liminf
                      (fun y : H ↦
                        f.asEReal y + (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                      (nhds x))
  exact properIoi_mem_gammaZero_of_mem_gamma (affine_tilt_isProper f hf u) htilt_gamma

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: affine tilting does not change the effective domain. -/
private theorem effectiveDomain_affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    effectiveDomain (affineTiltIoi f hf u) = effectiveDomain f := by
  ext x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hvalue :
        affineTiltEReal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
      rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
      simp [sub_eq_add_neg]
    rw [affineTiltIoi_apply, hvalue]
    constructor
    · intro _
      exact mem_effectiveDomain_iff.mp hx
    · intro _
      exact EReal.coe_lt_top _
  · rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hx_top : f.asEReal x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    rw [affineTiltIoi_apply, affineTiltEReal, hx_top,
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
    simp [hx_top]

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: evaluating a conjugate at the origin rewrites it as the negative
of the indexed infimum. -/
private theorem conjugate_zero_eq_neg_iInf_local
    (φ : H → EReal) :
    φ∗ 0 = - (⨅ x : H, φ x) := by
  calc
    φ∗ 0 = ⨆ x : H, -φ x := by
      simp [conjugate_apply]
    _ = - (⨅ x : H, φ x) := by
      have hneg : (-(⨅ x : H, φ x) : EReal) = ⨆ x : H, -φ x := by
        exact OrderIso.map_iInf EReal.negOrderIso (fun x : H ↦ φ x)
      rw [hneg]

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: Fenchel conjugation of the packaged affine tilt translates the
conjugate by `-u`. -/
private theorem conjugate_affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    (affineTiltIoi f hf u).asEReal∗ = τ (-u) (f.asEReal∗) := by
  ext v
  have hconj :=
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := f.asEReal) (y := (0 : H)) (v := -u) (β := 0))
      v
  simpa [Function.asEReal_apply, affineTiltEReal, Pi.add_apply, add_assoc] using hconj

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: the identity-map composite primal objective for the tilted pair
is the affine tilt of the pointwise sum `f + g`. -/
private theorem compositePrimalObjective_id_affineTilt_eq
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    compositePrimalObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) =
      affineTiltEReal ((f + g).asEReal) u := by
  funext x
  simp [compositePrimalObjective, primalObjective, affineTiltEReal, add_assoc, add_left_comm]

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: negating the tilted composite primal optimal value recovers the
conjugate of `f + g` at `u`. -/
private theorem neg_compositePrimalOptimalValue_id_affineTilt_eq_conjugate_pointwiseAdd
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    -compositePrimalOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) =
      (f + g).asEReal∗ u := by
  have hzero :
      (affineTiltEReal ((f + g).asEReal) u)∗ 0 =
        -compositePrimalOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) := by
    rw [← compositePrimalObjective_id_affineTilt_eq f g hf u]
    rw [conjugate_zero_eq_neg_iInf_local, compositePrimalOptimalValue_def, sInf_range]
  calc
    -compositePrimalOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) =
        (affineTiltEReal ((f + g).asEReal) u)∗ 0 := by
          exact hzero.symm
    _ = (τ (-u) ((f + g).asEReal∗)) 0 := by
          have hconj :=
            congrFun
              (conjugate_translate_add_inner_add_const
                (f := (f + g).asEReal) (y := (0 : H)) (v := -u) (β := 0))
              0
          simpa [affineTiltEReal, Pi.add_apply, add_assoc] using hconj
    _ = (f + g).asEReal∗ u := by
          simp [translate_apply]

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: affine tilting preserves the Attouch--Brézis
strong-relative-interior hypothesis for the identity-map composite problem. -/
private theorem zero_mem_sri_sub_image_effectiveDomain_affineTiltIoi
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) (u : H) :
    (0 : H) ∈
      sri
        (effectiveDomain (affineTiltIoi f hf u) -
          (ContinuousLinearMap.id ℝ H) '' effectiveDomain g) := by
  simpa [effectiveDomain_affineTiltIoi] using hsri

/-- Helper for Proposition 15 7: the tilted composite dual optimal value at `u` is exactly the
slice `(f^* □ g^*)(u)`. -/
private theorem compositeDualOptimalValue_id_affineTilt_eq_infimalConvolution_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    compositeDualOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) =
      (f.asEReal∗ □ g.asEReal∗) u := by
  rw [compositeDualOptimalValue_def, infimalConvolution_apply]
  change
    (⨅ v : H,
      compositeDualObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) v) =
      ⨅ y : H, f.asEReal∗ y + g.asEReal∗ (u - y)
  calc
    (⨅ v : H,
      compositeDualObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) v) =
        ⨅ v : H, g.asEReal∗ (-v) + f.asEReal∗ (u + v) := by
          refine iInf_congr fun v => ?_
          rw [compositeDualObjective_apply, conjugate_affineTiltIoi]
          simp [translate_apply, sub_eq_add_neg, add_comm]
    _ = ⨅ y : H, f.asEReal∗ y + g.asEReal∗ (u - y) := by
          exact (Equiv.addRight u).iInf_congr fun y => by
            simp [sub_eq_add_neg, add_comm]

/-- Helper for Proposition 15 7: Theorem 15.23 also gives a dual minimizer for the identity-map
affine-tilt composite problem. -/
private theorem exists_argmin_id_affine_tilt
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (u : H)
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    ∃ v ∈
        Argmin (compositeDualObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H)),
      compositePrimalOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) =
        -(compositeDualObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) v) := by
  have htilt : affineTiltIoi f hf u ∈ Γ₀(H) := affine_tilt_mem_gammaZero f hf u
  have hsri_tilt :
      (0 : H) ∈
        sri
          (effectiveDomain (affineTiltIoi f hf u) -
            (ContinuousLinearMap.id ℝ H) '' effectiveDomain g) :=
    zero_mem_sri_sub_image_effectiveDomain_affineTiltIoi f g hf hsri u
  exact
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      g
      hg
      (affineTiltIoi f hf u)
      htilt
      (ContinuousLinearMap.id ℝ H)
      hsri_tilt

/-- Helper for Proposition 15 7: the same affine-tilt identity-map composite problem satisfies
strong duality. -/
private theorem id_affine_tilt_strong_duality
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (u : H)
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    compositePrimalOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) =
      -compositeDualOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) := by
  obtain ⟨v, hvArg, hvEq⟩ := exists_argmin_id_affine_tilt f g hf hg u hsri
  have hvValue :
      compositeDualObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) v =
        compositeDualOptimalValue g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) := by
    simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hvArg)
  rw [hvValue] at hvEq
  exact hvEq

/-- Helper for Proposition 15 7: under the Attouch--Brézis hypothesis, the conjugate of the
pointwise sum is the infimal convolution of the conjugates. -/
theorem conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ := by
  ext u
  let tilt := affineTiltIoi f hf u
  have hstrong :
      compositePrimalOptimalValue g tilt (ContinuousLinearMap.id ℝ H) =
        -compositeDualOptimalValue g tilt (ContinuousLinearMap.id ℝ H) :=
    by simpa [tilt] using id_affine_tilt_strong_duality f g hf hg u hsri
  calc
    (f + g).asEReal∗ u =
        -compositePrimalOptimalValue g tilt (ContinuousLinearMap.id ℝ H) := by
          simpa [tilt] using
            (neg_compositePrimalOptimalValue_id_affineTilt_eq_conjugate_pointwiseAdd
              f g hf u).symm
    _ = compositeDualOptimalValue g tilt (ContinuousLinearMap.id ℝ H) := by
          simpa using congrArg Neg.neg hstrong
    _ = (f.asEReal∗ □ g.asEReal∗) u := by
          simpa [tilt] using
            compositeDualOptimalValue_id_affineTilt_eq_infimalConvolution_conjugates f g hf u

/-- Helper for Proposition 15 7: the Attouch--Brézis hypothesis yields exactness of the infimal
convolution of the canonical `Γ₀(H)`-valued conjugates. -/
theorem infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    infimalConvolution.Exact (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) := by
  intro u _hu
  let tilt := affineTiltIoi f hf u
  obtain ⟨v, hvArgRaw, _⟩ := exists_argmin_id_affine_tilt f g hf hg u hsri
  have hvArg : v ∈ Argmin (compositeDualObjective g tilt (ContinuousLinearMap.id ℝ H)) := by
    simpa [tilt] using hvArgRaw
  have hdual_value :
      compositeDualObjective g tilt (ContinuousLinearMap.id ℝ H) v =
        compositeDualOptimalValue g tilt (ContinuousLinearMap.id ℝ H) := by
    simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hvArg)
  refine ⟨u + v, ?_⟩
  calc
    ((gammaZeroConjugate f hf □ gammaZeroConjugate g hg) u : EReal) =
        compositeDualOptimalValue g tilt (ContinuousLinearMap.id ℝ H) := by
          simpa [tilt] using
            (compositeDualOptimalValue_id_affineTilt_eq_infimalConvolution_conjugates
              f g hf u).symm
    _ = compositeDualObjective g tilt (ContinuousLinearMap.id ℝ H) v := hdual_value.symm
    _ = g.asEReal∗ (-v) + (τ (-u) (f.asEReal∗)) v := by
          rw [compositeDualObjective_apply, conjugate_affineTiltIoi]
          simp
    _ = (gammaZeroConjugate f hf (u + v) : EReal) +
          (gammaZeroConjugate g hg (u - (u + v)) : EReal) := by
          simp [translate_apply, sub_eq_add_neg, add_comm]

/-- Helper for Proposition 15 7: a point in the ordinary interior of a convex set belongs to its
strong relative interior. -/
lemma mem_sri_of_mem_interior_of_convex {C : Set H} (hC_convex : Convex ℝ C) {x : H}
    (hx : x ∈ interior C) :
    x ∈ sri C := by
  -- Nonempty interior identifies `sri` with the ordinary interior for convex sets.
  rw [← interior_eq_strongRelativeInterior_of_convex_nonempty_interior hC_convex ⟨x, hx⟩]
  exact hx

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: reflecting a `Γ₀(H)` function through the origin preserves
membership in `Γ₀(H)`. -/
lemma reverse_mem_gammaZero_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) :
    Function.reverse g ∈ Γ₀(H) := by
  -- Reflection is precomposition with the negation linear isometry.
  let e : H ≃L[ℝ] H := ContinuousLinearEquiv.neg ℝ
  simpa [Function.comp, e, Function.reverse] using
    (mem_gammaZero_comp_continuousLinearEquiv hg e)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 15 7: reflecting an `]-∞,+∞]`-valued function negates its effective
domain. -/
lemma effectiveDomain_reverse_eq_neg_effectiveDomain
    (g : H → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (Function.reverse g) = -effectiveDomain g := by
  -- Finite values of the reflected function occur exactly at the negated original domain points.
  ext x
  simp [effectiveDomain]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 15 7: reflecting an `EReal`-valued function negates its domain. -/
lemma dom_reverse_eq_neg_dom
    (φ : H → EReal) :
    dom (φᵛ) = -dom φ := by
  -- Reflection preserves finiteness after negating the argument.
  ext x
  simp [dom, ERealFunction.reverse_apply, Set.mem_neg]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 15 7: if the right-hand set is nonempty, then subtracting it from the
whole space leaves the whole space unchanged. -/
lemma univ_sub_eq_univ_of_nonempty {S : Set H} (hS : S.Nonempty) :
    (Set.univ : Set H) - S = Set.univ := by
  ext x
  constructor
  · intro _hx
    simp
  · intro _hx
    rcases hS with ⟨y, hy⟩
    refine Set.mem_sub.mpr ⟨x + y, by simp, y, hy, ?_⟩
    abel

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 15 7: for `]-∞,+∞]`-valued summands that never take the value `-∞`,
the domain of the infimal convolution is the Minkowski sum of the effective domains. -/
lemma dom_infimalConvolution_eq_effectiveDomain_add
    (f g : H → Set.Ioi (⊥ : EReal)) :
    dom (f □ g) = effectiveDomain f + effectiveDomain g := by
  ext x
  constructor
  · intro hx
    -- Outside the Minkowski sum, every decomposition forces one summand to be `⊤`.
    by_contra hxsum
    rw [mem_dom_iff_ne_top, infimalConvolution_apply] at hx
    have htop : (⨅ y : H, (f y : EReal) + (g (x - y) : EReal)) = ⊤ := by
      refine iInf_eq_top.2 ?_
      intro y
      by_cases hy : y ∈ effectiveDomain f
      · have hxy : x - y ∉ effectiveDomain g := by
          intro hxy
          have hdecomp : y + (x - y) = x := by
            simp
          exact hxsum <| Set.mem_add.2 ⟨y, hy, x - y, hxy, hdecomp⟩
        have hgy_top : (g (x - y) : EReal) = ⊤ := by
          rw [mem_effectiveDomain_iff] at hxy
          exact le_antisymm le_top (not_lt.mp hxy)
        rw [hgy_top]
        exact EReal.add_top_of_ne_bot (ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2))
      · have hfy_top : (f y : EReal) = ⊤ := by
          rw [mem_effectiveDomain_iff] at hy
          exact le_antisymm le_top (not_lt.mp hy)
        rw [hfy_top]
        exact EReal.top_add_of_ne_bot
          (ne_of_gt (show (⊥ : EReal) < (g (x - y) : EReal) from (g (x - y)).2))
    exact hx htop
  · intro hx
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hxyz⟩
    -- A finite decomposition bounds the defining infimum by a finite value.
    rw [mem_dom_iff_ne_top, infimalConvolution_apply]
    refine ne_of_lt <| lt_of_le_of_lt
      (iInf_le (fun t : H ↦ (f t : EReal) + (g (x - t) : EReal)) y) ?_
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hz_top : (g z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hsum_lt : (f y : EReal) + (g z : EReal) < ⊤ :=
      EReal.add_lt_top hy_top hz_top
    have hx_sub : x - y = z := by
      rw [← hxyz]
      abel
    simpa [hx_sub] using hsum_lt

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: the domain of `f* □ (g*)ᵛ` is exactly
`dom f* - dom g*`. -/
lemma dom_infimalConvolution_reflected_conjugates_eq_sub
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    dom (f.asEReal∗ □ (g.asEReal∗)ᵛ) = dom f.asEReal∗ - dom g.asEReal∗ := by
  -- First identify the infimal-convolution domain with the Minkowski sum of the packaged domains.
  calc
    dom (f.asEReal∗ □ (g.asEReal∗)ᵛ)
        = effectiveDomain (f∗[hf]) + effectiveDomain (Function.reverse (g∗[hg])) := by
            simpa [gammaZeroConjugate_apply] using
              (
                dom_infimalConvolution_eq_effectiveDomain_add
                  (f∗[hf]) (Function.reverse (g∗[hg])))
    _ = effectiveDomain (f∗[hf]) - effectiveDomain (g∗[hg]) := by
          rw [effectiveDomain_reverse_eq_neg_effectiveDomain]
          ext x
          constructor
          · intro hx
            rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
            refine Set.mem_sub.mpr ⟨y, hy, -z, ?_, by abel⟩
            simpa [Set.mem_neg] using hz
          · intro hx
            rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, rfl⟩
            refine Set.mem_add.mpr ⟨y, hy, -z, ?_, by abel⟩
            simpa [Set.mem_neg] using hz
    _ = dom f.asEReal∗ - dom g.asEReal∗ := by
          ext x
          constructor
          · intro hx
            rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, rfl⟩
            refine Set.mem_sub.mpr ⟨y, ?_, z, ?_, rfl⟩
            · simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hy
            · simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hz
          · intro hx
            rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, rfl⟩
            refine Set.mem_sub.mpr ⟨y, ?_, z, ?_, rfl⟩
            · simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hy
            · simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hz

omit [CompleteSpace H] in
/-- Helper for Proposition 15 7: a lower bound on `g` makes the conjugate finite at `0`. -/
lemma zero_mem_dom_conjugate_of_bddBelow_range
    (g : H → Set.Ioi (⊥ : EReal)) (hg_bdd : BddBelow (Set.range g)) :
    (0 : H) ∈ dom g.asEReal∗ := by
  rcases hg_bdd with ⟨η, hη⟩
  -- At the origin the conjugate is the negative infimum, so a lower bound rules out `+∞`.
  rw [mem_dom_iff]
  have hzero :
      g.asEReal∗ 0 = - (⨅ x : H, (g x : EReal)) := by
    calc
      g.asEReal∗ 0 = ⨆ x : H, -((g x : EReal)) := by
        simp [conjugate_apply]
      _ = - (⨅ x : H, (g x : EReal)) := by
        have hneg : (-(⨅ x : H, (g x : EReal)) : EReal) = ⨆ x : H, -((g x : EReal)) := by
          exact OrderIso.map_iInf EReal.negOrderIso (fun x : H ↦ (g x : EReal))
        rw [hneg]
  rw [hzero]
  have hη_le : (η : EReal) ≤ ⨅ x : H, (g x : EReal) := by
    refine le_iInf fun x ↦ ?_
    exact hη ⟨x, rfl⟩
  have hiInf_ne_bot : (⨅ x : H, (g x : EReal)) ≠ ⊥ := by
    intro hbot
    have : (η : EReal) ≤ (⊥ : EReal) := by simpa [hbot] using hη_le
    exact not_le_of_gt η.2 this
  simp [lt_top_iff_ne_top, hiInf_ne_bot]

/-- Helper for Proposition 15 7: every regularity branch yields the Attouch--Brézis
strong-relative-interior hypothesis on the conjugate domains. -/
lemma zero_mem_sri_sub_effectiveDomain_gammaZeroConjugates_of_regularity
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hreg : InfimalConvolutionRegularity f g) :
    (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - effectiveDomain (g∗[hg])) := by
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hgConj : g∗[hg] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hg
  have hconv_sub :
      Convex ℝ (effectiveDomain (f∗[hf]) - effectiveDomain (g∗[hg])) :=
    hfConj.2.convex_effectiveDomain.sub hgConj.2.convex_effectiveDomain
  rcases hreg with hsri | hreg
  · -- Clause (i) is already the desired dual-side `sri` hypothesis.
    simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hsri
  rcases hreg with ⟨hcoercive_sum, hsri_primal⟩ | hreg
  · let gv : H → Set.Ioi (⊥ : EReal) := Function.reverse g
    have hgRev : gv ∈ Γ₀(H) := reverse_mem_gammaZero_of_mem_gammaZero hg
    have hsumGamma : f + gv ∈ Γ₀(H) :=
      pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f gv hf hgRev <| by
        simpa [effectiveDomain, dom] using hsri_primal
    have htfae :
        List.TFAE
          [Coercive (f + gv).asEReal,
            ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet (f + gv).asEReal ξ),
            ((0 : ℝ) : EReal) <
              Filter.liminf (fun x : H ↦ (f + gv).asEReal x / ‖x‖)
                (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop),
            ∃ α : Set.Ioi (0 : ℝ), ∃ β : ℝ,
              (scaledNormKernelOfPos α).asEReal +
                (fun _ : H ↦ (β : EReal)) ≤
                  (f + gv).asEReal,
            ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ,
              ∀ u : H, u ∈ Metric.closedBall (0 : H) (ε : ℝ) →
                (f + gv).asEReal∗ u ≤ (γ : EReal),
            (0 : H) ∈ interior (dom (f + gv).asEReal∗)] :=
      coercive_tfae_lowerLevelSet_asymptoticSlope_affineLowerBound_conjugate (f + gv) hsumGamma
    have hzero_int_sum :
        (0 : H) ∈ interior (dom (f + gv).asEReal∗) :=
      (List.TFAE.out htfae 0 5).1 <| by
        simpa [Function.asEReal, Function.reverse_apply] using hcoercive_sum
    have hsum_conj :
        (f + gv).asEReal∗ = f.asEReal∗ □ gv.asEReal∗ := by
      exact
        conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
          f
          gv
          hf
          hgRev
          (by simpa [effectiveDomain, dom] using hsri_primal)
    have hconj_eq :
        (f + gv).asEReal∗ = f.asEReal∗ □ (g.asEReal∗)ᵛ := by
      calc
        (f + gv).asEReal∗ = f.asEReal∗ □ gv.asEReal∗ := by
          simpa [gammaZeroConjugate_apply] using hsum_conj
        _ = f.asEReal∗ □ (g.asEReal∗)ᵛ := by
          rw [show gv.asEReal∗ = (g.asEReal∗)ᵛ by
            simpa [Function.asEReal, Function.reverse_apply] using
              (conjugate_precompose_neg g.asEReal)]
    have hdom_eq :
        dom (f.asEReal∗ □ (g.asEReal∗)ᵛ) = dom (f + gv).asEReal∗ := by
      simp [hconj_eq]
    have hzero_int_sub :
        (0 : H) ∈ interior (dom f.asEReal∗ - dom g.asEReal∗) := by
      rw [← dom_infimalConvolution_reflected_conjugates_eq_sub f g hf hg, hdom_eq]
      exact hzero_int_sum
    exact mem_sri_of_mem_interior_of_convex
      (by simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hconv_sub)
      hzero_int_sub
  rcases hreg with ⟨hcoercive_f, hg_bdd⟩ | hreg
  · have htfae :
        List.TFAE
          [Coercive f.asEReal,
            ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f.asEReal ξ),
            ((0 : ℝ) : EReal) <
              Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
                (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop),
            ∃ α : Set.Ioi (0 : ℝ), ∃ β : ℝ,
              (scaledNormKernelOfPos α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal,
            ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ,
              ∀ u : H, u ∈ Metric.closedBall (0 : H) (ε : ℝ) →
                f.asEReal∗ u ≤ (γ : EReal),
            (0 : H) ∈ interior (dom f.asEReal∗)] :=
      coercive_tfae_lowerLevelSet_asymptoticSlope_affineLowerBound_conjugate f hf
    have hzero_int_f : (0 : H) ∈ interior (dom f.asEReal∗) :=
      (List.TFAE.out htfae 0 5).1 hcoercive_f
    have hzero_dom_g : (0 : H) ∈ dom g.asEReal∗ :=
      zero_mem_dom_conjugate_of_bddBelow_range g hg_bdd
    have hsubset :
        dom f.asEReal∗ ⊆ dom f.asEReal∗ - dom g.asEReal∗ := by
      intro x hx
      exact Set.mem_sub.mpr ⟨x, hx, 0, hzero_dom_g, by simp⟩
    have hzero_int_sub : (0 : H) ∈ interior (dom f.asEReal∗ - dom g.asEReal∗) := by
      exact interior_mono hsubset hzero_int_f
    exact mem_sri_of_mem_interior_of_convex
      (by simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hconv_sub)
      hzero_int_sub
  rcases hreg with hdom_univ | hsuper
  · have hdom_nonempty : (dom g.asEReal∗).Nonempty := by
      simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hgConj.2.nonempty
    have hsub_univ : dom f.asEReal∗ - dom g.asEReal∗ = (Set.univ : Set H) := by
      rw [hdom_univ]
      exact univ_sub_eq_univ_of_nonempty hdom_nonempty
    have hzero_int_sub : (0 : H) ∈ interior (dom f.asEReal∗ - dom g.asEReal∗) := by
      rw [hsub_univ]
      simp
    exact mem_sri_of_mem_interior_of_convex
      (by simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hconv_sub)
      hzero_int_sub
  · have hdom_univ :
        dom f.asEReal∗ = Set.univ := by
      exact dom_conjugate_eq_univ_of_conjugate_boundedOnEveryBoundedSet f
        ((supercoercive_iff_conjugate_boundedOnEveryBoundedSet f hf).mp hsuper)
    have hdom_nonempty : (dom g.asEReal∗).Nonempty := by
      simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hgConj.2.nonempty
    have hsub_univ : dom f.asEReal∗ - dom g.asEReal∗ = (Set.univ : Set H) := by
      rw [hdom_univ]
      exact univ_sub_eq_univ_of_nonempty hdom_nonempty
    have hzero_int_sub : (0 : H) ∈ interior (dom f.asEReal∗ - dom g.asEReal∗) := by
      rw [hsub_univ]
      simp
    exact mem_sri_of_mem_interior_of_convex
      (by simpa [effectiveDomain, dom, gammaZeroConjugate_apply] using hconv_sub)
      hzero_int_sub

-- Proof sketch: use the fifth disjunct in the definition of
-- `InfimalConvolutionRegularity`.
omit [CompleteSpace H] in
/-- Supercoercivity of the left summand is one of the regularity alternatives in
`InfimalConvolutionRegularity`. -/
theorem of_supercoercive
    (f g : H → Set.Ioi (⊥ : EReal))
    (hsuper : Supercoercive f.asEReal) :
    InfimalConvolutionRegularity f g := by
  -- Select the fifth branch of the source regularity predicate.
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr hsuper

-- Proof sketch: apply the Attouch--Brezis exactness statement on the dual side under clause (i).
-- Clause (ii) reduces to clause (i) by Proposition 14.16 after identifying the reflected domain
-- difference, while clauses (iii)--(v) imply the needed dual regularity through Propositions 14.15
-- and 14.16.
/-- Proposition 15 7 (1): under any of the five source regularity alternatives, the infimal
convolution `f □ g` is exact. -/
theorem exact
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hreg : InfimalConvolutionRegularity f g) :
    infimalConvolution.Exact f g := by
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hgConj : g∗[hg] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hg
  -- Route the source regularity predicate to the canonical dual-side `sri` hypothesis.
  have hsri :
      (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - effectiveDomain (g∗[hg])) :=
    zero_mem_sri_sub_effectiveDomain_gammaZeroConjugates_of_regularity f g hf hg hreg
  -- Exactness now follows from the owner theorem on the conjugate pair, then by biconjugation.
  have hExactConj :
      infimalConvolution.Exact (f∗[hf]∗[hfConj]) (g∗[hg]∗[hgConj]) :=
    infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
      (f∗[hf]) (g∗[hg]) hfConj hgConj hsri
  have hfBi : f∗[hf]∗[hfConj] = f := by
    funext x
    apply Subtype.ext
    simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hf) x
  have hgBi : g∗[hg]∗[hgConj] = g := by
    funext x
    apply Subtype.ext
    simpa [gammaZeroConjugate_apply] using congrFun (biconjugate_eq_of_mem_gammaZero hg) x
  simpa [hfBi, hgBi] using hExactConj

-- Proof sketch: combine exactness from Proposition 15.7 (1) with the Attouch--Brezis
-- identification of `f □ g` as a conjugate of a pointwise sum on the dual side. Theorem 15.3 and
-- Fenchel--Moreau then give lower semicontinuity and convexity, and properness is recovered from
-- the same dual representation.
/-- Proposition 15 7 (2): under the same regularity alternatives, the infimal convolution `f □ g`
is proper, convex, and lower semicontinuous. In the project's unbundled API, this is expressed as
`IsProper (f □ g)` together with membership of `f □ g` in `γ(H)`,
which is the canonical form of `f □ g ∈ Γ₀(H)` before repackaging
into `]-∞,+∞]`-valued form. -/
theorem isProper_and_mem_gamma
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hreg : InfimalConvolutionRegularity f g) :
    IsProper (f □ g) ∧ (f □ g) ∈ gamma H := by
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hgConj : g∗[hg] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hg
  have hsri :
      (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - effectiveDomain (g∗[hg])) :=
    zero_mem_sri_sub_effectiveDomain_gammaZeroConjugates_of_regularity f g hf hg hreg
  -- The dual sum belongs to `Γ₀(H)` by the Attouch--Brézis pointwise-add owner theorem.
  have hsum : f∗[hf] + g∗[hg] ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
      (f∗[hf]) (g∗[hg]) hfConj hgConj hsri
  have hrepr : ((f∗[hf] + g∗[hg]).asEReal)∗ = (f □ g) := by
    have hfBi : (f∗[hf]).asEReal∗ = f.asEReal := by
      simpa [gammaZeroConjugate_apply] using biconjugate_eq_of_mem_gammaZero hf
    have hgBi : (g∗[hg]).asEReal∗ = g.asEReal := by
      simpa [gammaZeroConjugate_apply] using biconjugate_eq_of_mem_gammaZero hg
    have hdual_conj :
        ((f∗[hf] + g∗[hg]).asEReal)∗ =
          (f∗[hf]).asEReal∗ □ (g∗[hg]).asEReal∗ := by
      exact
        conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
          (f∗[hf])
          (g∗[hg])
          hfConj
          hgConj
          hsri
    -- Theorem 15.3 rewrites the conjugate of the dual sum as the primal infimal convolution.
    calc
      ((f∗[hf] + g∗[hg]).asEReal)∗
          = (f∗[hf]).asEReal∗ □ (g∗[hg]).asEReal∗ := by
              simpa using hdual_conj
      _ = f.asEReal □ g.asEReal := by
            rw [hfBi, hgBi]
      _ = f □ g := rfl
  have hproper_conj : IsProper (((f∗[hf] + g∗[hg]).asEReal)∗) :=
    conjugate_is_proper_of_mem_gamma
      (isProper_of_mem_gammaZero hsum)
      (asEReal_mem_gamma_of_mem_gammaZero hsum)
  have hgamma_conj : ((f∗[hf] + g∗[hg]).asEReal)∗ ∈ gamma H :=
    conjugate_mem_gamma ((f∗[hf] + g∗[hg]).asEReal)
  constructor
  · -- Properness transports across the dual representation of `f □ g`.
    rw [← hrepr]
    exact hproper_conj
  · -- The same representation transports `gamma`-membership.
    rw [← hrepr]
    exact hgamma_conj

end InfimalConvolutionRegularity

end AttouchBrezisTheorem

end ERealFunction
