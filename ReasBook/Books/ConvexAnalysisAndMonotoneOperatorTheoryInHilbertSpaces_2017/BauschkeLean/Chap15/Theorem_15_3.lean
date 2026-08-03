import Mathlib
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap15.Proposition_15_13

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace translate

noncomputable section

universe u

namespace ERealFunction

section PointwiseAddRegularity

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] [SequentialSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

omit [SequentialSpace H] in
-- Proof sketch: membership in `sri (effectiveDomain f - effectiveDomain g)` implies membership in
-- `effectiveDomain f - effectiveDomain g`, so `0 = x - y` for some `x ∈ effectiveDomain f` and
-- `y ∈ effectiveDomain g`; hence `x = y`, and the effective domains intersect.
private theorem effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (effectiveDomain f ∩ effectiveDomain g).Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, ?_⟩
  simpa [sub_eq_zero.mp hxy] using hy

-- Proof sketch: use the previous domain-intersection lemma and the canonical Chapter 9 owner
-- `pointwiseAdd_mem_gammaZero`.
/-- Theorem 15 3: (Attouch--Brézis) if `f, g ∈ Γ₀(H)` and
`0 ∈ sri (effectiveDomain f - effectiveDomain g)`, then `f + g ∈ Γ₀(H)`. -/
theorem pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    f + g ∈ Γ₀(H) :=
  pointwiseAdd_mem_gammaZero f g hf hg
    (effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain f g hsri)

end PointwiseAddRegularity

section AttouchBrezisTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 15 3: the affine tilt of an `EReal`-valued function by the linear term
`x ↦ -⟪x, u⟫`. -/
private def affineTiltEReal (φ : H → EReal) (u : H) : H → EReal :=
  fun x ↦ φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal))

omit [CompleteSpace H] in
/-- Helper for Theorem 15 3: evaluating the affine tilt exposes the added linear term. -/
@[simp] private theorem affineTiltEReal_apply
    (φ : H → EReal) (u x : H) :
    affineTiltEReal φ u x = φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal)) :=
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 15 3: affine tilting a `Γ₀` function by `x ↦ -⟪x,u⟫` preserves properness.
-/
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

/-- Helper for Theorem 15 3: package the affine tilt back into the `Set.Ioi (⊥ : EReal)` codomain
expected by the Chapter 15 owner theorem. -/
private noncomputable abbrev affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (affineTiltEReal f.asEReal u) (affine_tilt_isProper f hf u)

omit [CompleteSpace H] in
/-- Helper for Theorem 15 3: coercing the packaged affine tilt back to `EReal` recovers the raw
tilted function. -/
@[simp] private theorem affineTiltIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u x : H) :
    (affineTiltIoi f hf u x : EReal) = affineTiltEReal f.asEReal u x := by
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 15 3: the packaged affine tilt of a `Γ₀` function again belongs to
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
/-- Helper for Theorem 15 3: affine tilting does not change the effective domain. -/
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
/-- Helper for Theorem 15 3: evaluating a conjugate at the origin rewrites it as the negative of
the indexed infimum. -/
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
/-- Helper for Theorem 15 3: Fenchel conjugation of the packaged affine tilt translates the
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
/-- Helper for Theorem 15 3: the identity-map composite primal objective for the tilted pair is
the affine tilt of the pointwise sum `f + g`. -/
private theorem compositePrimalObjective_id_affineTilt_eq
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    compositePrimalObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) =
      affineTiltEReal ((f + g).asEReal) u := by
  funext x
  simp [compositePrimalObjective, primalObjective, affineTiltEReal, add_assoc, add_left_comm]

omit [CompleteSpace H] in
/-- Helper for Theorem 15 3: negating the tilted composite primal optimal value recovers the
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
                (f := ((f + g).asEReal)) (y := (0 : H)) (v := -u) (β := 0))
              0
          simpa [affineTiltEReal, Pi.add_apply, add_assoc] using hconj
    _ = (f + g).asEReal∗ u := by
          simp [translate_apply]

omit [CompleteSpace H] in
/-- Helper for Theorem 15 3: affine tilting preserves the Attouch--Brézis strong-relative-interior
regularity hypothesis for the identity-map composite problem. -/
private theorem zero_mem_sri_sub_image_effectiveDomain_affineTiltIoi
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) (u : H) :
    (0 : H) ∈
      sri
        (effectiveDomain (affineTiltIoi f hf u) -
          (ContinuousLinearMap.id ℝ H) '' effectiveDomain g) := by
  simpa [effectiveDomain_affineTiltIoi] using hsri

/-- Helper for Theorem 15 3: the tilted composite dual optimal value at `u` is exactly the
infimal-convolution slice `(f^* □ g^*)(u)`. -/
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
      compositeDualObjective g (affineTiltIoi f hf u) (ContinuousLinearMap.id ℝ H) v)
        = ⨅ v : H, g.asEReal∗ (-v) + f.asEReal∗ (u + v) := by
            refine iInf_congr fun v => ?_
            rw [compositeDualObjective_apply, conjugate_affineTiltIoi]
            simp [translate_apply, sub_eq_add_neg, add_comm]
    _ = ⨅ y : H, f.asEReal∗ y + g.asEReal∗ (u - y) := by
          exact (Equiv.addRight u).iInf_congr fun y => by
            simp [sub_eq_add_neg, add_comm]

/-- Helper for Theorem 15 3: negating a minimizer of `fenchelDualObjective f g` yields a minimizer
of the identity composite dual objective with the summands swapped. -/
private theorem neg_mem_argmin_compositeDualObjective_id_of_mem_argmin_fenchelDualObjective
    (f g : H → Set.Ioi (⊥ : EReal)) {v : H}
    (hvArg : v ∈ Argmin (fenchelDualObjective f g)) :
    -v ∈ Argmin (compositeDualObjective g f (ContinuousLinearMap.id ℝ H)) := by
  rw [mem_argmin_iff, isMinOn_univ_iff]
  have hvmin : IsMinOn (fenchelDualObjective f g) Set.univ v := (mem_argmin_iff).mp hvArg
  intro z
  have hvz : fenchelDualObjective f g v ≤ fenchelDualObjective f g (-z) :=
    (isMinOn_univ_iff.mp hvmin) (-z)
  simpa [compositeDualObjective_apply, fenchelDualObjective_apply, add_comm] using hvz

-- Proof sketch: follow the Attouch--Brézis affine-tilt reduction and apply Theorem 15.23 to the
-- identity-map composite problem.
/-- Theorem 15.3: (Attouch--Brézis) if `f, g ∈ Γ₀(H)` and
`0 ∈ sri (effectiveDomain f - effectiveDomain g)`, then the Fenchel conjugate of `f + g` is
`f^* □ g^*`. -/
theorem conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ := by
  ext u
  let tilt := affineTiltIoi f hf u
  have htilt : tilt ∈ Γ₀(H) := affine_tilt_mem_gammaZero f hf u
  have hsri_tilt :
      (0 : H) ∈
        sri (effectiveDomain tilt - (ContinuousLinearMap.id ℝ H) '' effectiveDomain g) :=
    zero_mem_sri_sub_image_effectiveDomain_affineTiltIoi f g hf hsri u
  have hsri_tilt' : (0 : H) ∈ sri (effectiveDomain tilt - effectiveDomain g) := by
    simpa using hsri_tilt
  obtain ⟨w, hwArgFenchel, hwEqFenchel⟩ := (
exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain
      tilt g htilt hg hsri_tilt')
  have hwArg :
      -w ∈ Argmin (compositeDualObjective g tilt (ContinuousLinearMap.id ℝ H)) :=
    neg_mem_argmin_compositeDualObjective_id_of_mem_argmin_fenchelDualObjective
      tilt g hwArgFenchel
  have hwValue :
      compositeDualObjective g tilt (ContinuousLinearMap.id ℝ H) (-w) =
        compositeDualOptimalValue g tilt (ContinuousLinearMap.id ℝ H) := by
    simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hwArg)
  have hstrong :
      compositePrimalOptimalValue g tilt (ContinuousLinearMap.id ℝ H) =
        -compositeDualOptimalValue g tilt (ContinuousLinearMap.id ℝ H) :=
    by
      calc
        compositePrimalOptimalValue g tilt (ContinuousLinearMap.id ℝ H) =
            primalOptimalValue g tilt := by
              simp [compositePrimalOptimalValue]
        _ = primalOptimalValue tilt g := by
              rw [primalOptimalValue_eq_iInf_primalObjective,
                primalOptimalValue_eq_iInf_primalObjective]
              simp [add_comm]
        _ = -(fenchelDualObjective tilt g w) := hwEqFenchel
        _ = -(compositeDualObjective g tilt (ContinuousLinearMap.id ℝ H) (-w)) := by
              simp [compositeDualObjective_apply, fenchelDualObjective_apply, add_comm]
        _ = -compositeDualOptimalValue g tilt (ContinuousLinearMap.id ℝ H) := by
              rw [hwValue]
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

-- Proof sketch: use the same affine-tilt reduction and the minimizing dual vector from
-- Theorem 15.23 to produce an exact infimal-convolution witness.
/-- Theorem 15.3: (Attouch--Brézis) under the same hypothesis, the infimal convolution of the
canonical `Γ₀(H)`-valued Fenchel conjugates is exact. -/
theorem infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    infimalConvolution.Exact (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) := by
  intro u _hu
  let tilt := affineTiltIoi f hf u
  have htilt : tilt ∈ Γ₀(H) := affine_tilt_mem_gammaZero f hf u
  have hsri_tilt :
      (0 : H) ∈
        sri (effectiveDomain tilt - (ContinuousLinearMap.id ℝ H) '' effectiveDomain g) :=
    zero_mem_sri_sub_image_effectiveDomain_affineTiltIoi f g hf hsri u
  have hsri_tilt' : (0 : H) ∈ sri (effectiveDomain tilt - effectiveDomain g) := by
    simpa using hsri_tilt
  obtain ⟨w, hwArgFenchel, _hwEqFenchel⟩ := (
exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain
      tilt g htilt hg hsri_tilt')
  let v := -w
  have hvArg : v ∈ Argmin (compositeDualObjective g tilt (ContinuousLinearMap.id ℝ H)) := by
    simpa [v] using
      neg_mem_argmin_compositeDualObjective_id_of_mem_argmin_fenchelDualObjective
        tilt g hwArgFenchel
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

end AttouchBrezisTheorem

end ERealFunction
