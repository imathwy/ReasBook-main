import Mathlib
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap15.Fact_15_25
import BauschkeLean.Chap15.Proposition_15_26
import BauschkeLean.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace translate

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 15.27 is the chapter's conjugation identity and attained infimum
  formula under the three textbook regularity branches:
  (i) `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`;
  (ii) `K` is finite-dimensional, `g` is polyhedral, and
  `effectiveDomain g ∩ ri (L '' effectiveDomain f) ≠ ∅`;
  (iii) `H` and `K` are finite-dimensional, both `f` and `g` are polyhedral, and
  `effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`.
- `core/canonical`: the owner objects are `compositePrimalObjective`, `compositeDualObjective`,
  `compositeDualOptimalValue`, and the dual infimal convolution
  `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)`.
- `bridge/view`: Theorem 15.23 and Fact 15.25 are the branch-specific attainment engines for the
  owner dual objective, while `shiftedCompositeDualObjective f g L u` is only the fiberwise
  translated minimand whose infimum at `u` computes the owner dual infimal convolution. In the
  zero-shift case, downstream files should use `compositeDualObjective f g L` directly.
-/

/-- The dual minimization functional from formula `(15.43)` at a fixed dual point `u`. This is
the source-facing fiberwise view of the owner dual infimal convolution
`f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)` at `u`. -/
def shiftedCompositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) : K → EReal :=
  fun v ↦
    f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v

/-- Evaluating `shiftedCompositeDualObjective` gives the explicit minimand
`f^*(u - L^* v) + g^*(v)`. -/
@[simp] theorem shiftedCompositeDualObjective_apply
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) (v : K) :
    shiftedCompositeDualObjective f g L u v =
      f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v := rfl

/-- At `u = 0`, the shifted dual minimand is exactly the owner dual objective from
Definition 15.19. -/
@[simp] theorem shiftedCompositeDualObjective_zero
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    shiftedCompositeDualObjective f g L 0 = compositeDualObjective f g L := by
  funext v
  simp [shiftedCompositeDualObjective, compositeDualObjective]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 15 27: the regularity hypotheses imply
`effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`. -/
private theorem effectiveDomain_inter_image_nonempty_of_regular
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty := by
  rcases hregular with hsri | hpoly | hpoly
  · rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
    rcases Set.mem_sub.mp hzero with ⟨y, hy, z, hz, hyz⟩
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨y, hy, ?_⟩
    exact ⟨x, hx, (sub_eq_zero.mp hyz).symm⟩
  · rcases hpoly.2.2 with ⟨y, hy, hyri⟩
    exact ⟨y, hy, (Set.mem_relativeInterior_iff.mp hyri).1⟩
  · exact hpoly.2.2.2.2

/-- Helper for Theorem 15 27: the affine tilt of an `EReal`-valued function by the linear
functional `x ↦ -⟪x, u⟫`. -/
private def affineTiltEReal (φ : H → EReal) (u : H) : H → EReal :=
  fun x ↦ φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal))

omit [CompleteSpace H] in
/-- Helper for Theorem 15 27: evaluating the affine tilt exposes the added linear term. -/
@[simp] private theorem affineTiltEReal_apply
    (φ : H → EReal) (u x : H) :
    affineTiltEReal φ u x = φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal)) :=
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 15 27: affine tilting a `Γ₀(H)` function preserves properness. -/
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

/-- Helper for Theorem 15 27: package the affine tilt back into the `]-∞,+∞]` codomain expected
by the Chapter 15 owners. -/
private noncomputable abbrev affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (affineTiltEReal f.asEReal u) (affine_tilt_isProper f hf u)

omit [CompleteSpace H] in
/-- Helper for Theorem 15 27: coercing the packaged affine tilt back to `EReal` recovers the raw
tilt. -/
@[simp] private theorem affineTiltIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u x : H) :
    (affineTiltIoi f hf u x : EReal) = affineTiltEReal f.asEReal u x := by
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 15 27: the packaged affine tilt of a `Γ₀(H)` function again belongs to
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
/-- Helper for Theorem 15 27: affine tilting does not change the effective domain. -/
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
/-- Helper for Theorem 15 27: evaluating a conjugate at the origin rewrites it as the negative of
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
/-- Helper for Theorem 15 27: Fenchel conjugation of the affine tilt translates the conjugate by
`-u`. -/
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

/-- Helper for Theorem 15 27: preimages of polyhedral sets under continuous linear maps are
polyhedral. -/
private theorem Set.IsPolyhedral.preimage_continuousLinearMap
    {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {C : Set F} (hC : C.IsPolyhedral) (A : E →L[ℝ] F) :
    (A ⁻¹' C).IsPolyhedral := by
  classical
  rcases hC with ⟨t, rfl⟩
  refine ⟨t.image (fun p : (F →L[ℝ] ℝ) × ℝ ↦ (p.1.comp A, p.2)), ?_⟩
  ext x
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_closedHalfspace_iff] at hx ⊢
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    simpa using hx p hp
  · intro hx
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_closedHalfspace_iff] at hx ⊢
    intro p hp
    have hp' :
        (p.1.comp A, p.2) ∈
          t.image (fun q : (F →L[ℝ] ℝ) × ℝ ↦ (q.1.comp A, q.2)) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    simpa using hx _ hp'

/-- Helper for Theorem 15 27: the epigraph shear sending `(x, t)` to
`(x, t + ⟪x, u⟫)` transports the original epigraph to the tilted one. -/
private def epigraphShearMap (u : H) : (H × ℝ) →L[ℝ] H × ℝ :=
  (ContinuousLinearMap.fst ℝ H ℝ).prod
    ((innerSL ℝ u).comp (ContinuousLinearMap.fst ℝ H ℝ) + ContinuousLinearMap.snd ℝ H ℝ)

omit [CompleteSpace H] in
/-- Helper for Theorem 15 27: evaluating the epigraph shear exposes the affine ordinate shift. -/
@[simp] private theorem epigraphShearMap_apply
    (u : H) (p : H × ℝ) :
    epigraphShearMap u p = (p.1, p.2 + ⟪p.1, u⟫_ℝ) := by
  ext <;> simp [epigraphShearMap, real_inner_comm, add_comm]

omit [CompleteSpace H] in
/-- Helper for Theorem 15 27: the epigraph of the affine tilt is the preimage of the original
epigraph under the epigraph shear. -/
private theorem epigraph_affineTiltEReal_eq_preimage
    (φ : H → EReal) (u : H) :
    epigraph (affineTiltEReal φ u) = (epigraphShearMap u) ⁻¹' epigraph φ := by
  ext p
  rcases p with ⟨x, t⟩
  rw [Set.mem_preimage, mem_epigraph_iff, mem_epigraph_iff]
  simpa [affineTiltEReal, epigraphShearMap_apply, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    (EReal.sub_le_iff_le_add
      (a := φ x)
      (b := ((⟪x, u⟫_ℝ : ℝ) : EReal))
      (c := (t : EReal))
      (.inr (EReal.coe_ne_top _))
      (.inr (EReal.coe_ne_bot _)))

omit [CompleteSpace H] in
/-- Helper for Theorem 15 27: affine tilting preserves polyhedrality. -/
private theorem polyhedral_affineTiltEReal
    {φ : H → EReal} (u : H) (hpoly : Polyhedral φ) :
    Polyhedral (affineTiltEReal φ u) := by
  have hpoly_epi : (epigraph φ).IsPolyhedral := by
    simpa [polyhedral_iff] using hpoly
  rw [polyhedral_iff]
  rw [epigraph_affineTiltEReal_eq_preimage]
  exact
    Set.IsPolyhedral.preimage_continuousLinearMap
      (C := epigraph φ) hpoly_epi (epigraphShearMap u)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 15 27: tilting the primal objective commutes with the composite owner. -/
private theorem tilted_compositePrimalObjective_eq_affineTilt
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (u : H) :
    compositePrimalObjective (affineTiltIoi f hf u) g L =
      affineTiltEReal (compositePrimalObjective f g L) u := by
  funext x
  rw [compositePrimalObjective_apply, affineTiltIoi_apply, affineTiltEReal]
  simp [compositePrimalObjective_apply, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 15 27: the tilted dual objective is exactly the shifted minimand from
formula `(15.43)`. -/
private theorem tilted_compositeDualObjective_eq_shiftedCompositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (u : H) :
    compositeDualObjective (affineTiltIoi f hf u) g L =
      shiftedCompositeDualObjective f g L u := by
  funext v
  rw [compositeDualObjective_apply, shiftedCompositeDualObjective_apply,
    conjugate_affineTiltIoi f hf u]
  simp [translate_apply, sub_eq_add_neg, add_comm]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 15 27: negating the tilted composite primal optimal value recovers the
conjugate of the original composite primal objective at `u`. -/
private theorem neg_tilted_compositePrimalOptimalValue_eq_conjugate_comp
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (u : H) :
    -compositePrimalOptimalValue (affineTiltIoi f hf u) g L =
      (compositePrimalObjective f g L)∗ u := by
  have hzero :
      (affineTiltEReal (compositePrimalObjective f g L) u)∗ 0 =
        -compositePrimalOptimalValue (affineTiltIoi f hf u) g L := by
    rw [← tilted_compositePrimalObjective_eq_affineTilt f hf g L u]
    rw [conjugate_zero_eq_neg_iInf_local, compositePrimalOptimalValue_def, sInf_range]
  calc
    -compositePrimalOptimalValue (affineTiltIoi f hf u) g L =
        (affineTiltEReal (compositePrimalObjective f g L) u)∗ 0 := by
          exact hzero.symm
    _ = (τ (-u) ((compositePrimalObjective f g L)∗)) 0 := by
          have hconj :=
            congrFun
              (conjugate_translate_add_inner_add_const
                (f := compositePrimalObjective f g L)
                (y := (0 : H)) (v := -u) (β := 0))
              0
          simpa [affineTiltEReal, Pi.add_apply, add_assoc] using hconj
    _ = (compositePrimalObjective f g L)∗ u := by
          simp [translate_apply]

/-- Helper for Theorem 15 27: the minimization formula `(15.43)` is attained under the stated
regularity assumptions. -/
private theorem exists_mem_argmin_shiftedCompositeDualObjective_eq_conjugate_addComp_of_regular_aux
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty))
    (u : H) :
    ∃ v ∈ Argmin (shiftedCompositeDualObjective f g L u),
      (compositePrimalObjective f g L)∗ u =
        shiftedCompositeDualObjective f g L u v := by
  let tilt := affineTiltIoi f hf u
  have htilt : tilt ∈ Γ₀(H) := affine_tilt_mem_gammaZero f hf u
  rcases hregular with hsri | hpoly | hpoly
  · obtain ⟨v, hvArg, hvEq⟩ :=
      exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
        (f := tilt) (hf := htilt) (g := g) (hg := hg) (L := L) (by
          simpa [tilt, effectiveDomain_affineTiltIoi f hf u] using hsri)
    have hshift :
        compositeDualObjective tilt g L = shiftedCompositeDualObjective f g L u := by
      simpa [tilt] using
        tilted_compositeDualObjective_eq_shiftedCompositeDualObjective f hf g L u
    have hshift' :
        tilt.asEReal∗ᵛ ∘ L.adjoint + g.asEReal∗ =
          shiftedCompositeDualObjective f g L u := by
      simpa [compositeDualObjective_eq_add_reflectedConjugates] using hshift
    have hvArg' : v ∈ Argmin (shiftedCompositeDualObjective f g L u) := by
      simpa [hshift'] using hvArg
    have hvShift :
        compositeDualObjective tilt g L v = shiftedCompositeDualObjective f g L u v := by
      simpa [hshift] using congrArg (fun ψ : K → EReal ↦ ψ v) hshift
    refine ⟨v, ?_, ?_⟩
    · exact hvArg'
    · have hneg := congrArg Neg.neg hvEq
      calc
        (compositePrimalObjective f g L)∗ u =
            compositeDualObjective tilt g L v := by
              simpa
                [tilt, neg_tilted_compositePrimalOptimalValue_eq_conjugate_comp f hf g L u] using
                hneg
        _ = shiftedCompositeDualObjective f g L u v := hvShift
  · rcases hpoly with ⟨hK, hg_polyhedral, hnonempty⟩
    letI : FiniteDimensional ℝ K := hK
    obtain ⟨v, hvArg, hvEq⟩ :=
      exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regularity
        (f := tilt) (hf := htilt) (g := g) (hg := hg) (L := L)
        (hg_polyhedral := hg_polyhedral) (Or.inl (by
          simpa [tilt, effectiveDomain_affineTiltIoi f hf u] using hnonempty))
    have hshift :
        compositeDualObjective tilt g L = shiftedCompositeDualObjective f g L u := by
      simpa [tilt] using
        tilted_compositeDualObjective_eq_shiftedCompositeDualObjective f hf g L u
    have hshift' :
        tilt.asEReal∗ᵛ ∘ L.adjoint + g.asEReal∗ =
          shiftedCompositeDualObjective f g L u := by
      simpa [compositeDualObjective_eq_add_reflectedConjugates] using hshift
    have hvArg' : v ∈ Argmin (shiftedCompositeDualObjective f g L u) := by
      simpa [hshift'] using hvArg
    have hvShift :
        compositeDualObjective tilt g L v = shiftedCompositeDualObjective f g L u v := by
      simpa [hshift] using congrArg (fun ψ : K → EReal ↦ ψ v) hshift
    refine ⟨v, ?_, ?_⟩
    · exact hvArg'
    · have hneg := congrArg Neg.neg hvEq
      calc
        (compositePrimalObjective f g L)∗ u =
            compositeDualObjective tilt g L v := by
              simpa
                [tilt, neg_tilted_compositePrimalOptimalValue_eq_conjugate_comp f hf g L u] using
                hneg
        _ = shiftedCompositeDualObjective f g L u v := hvShift
  · rcases hpoly with ⟨hK, hg_polyhedral, hH, hf_polyhedral, hnonempty⟩
    letI : FiniteDimensional ℝ K := hK
    letI : FiniteDimensional ℝ H := hH
    have htilt_polyhedral : Polyhedral tilt.asEReal := by
      simpa [tilt, affineTiltIoi_apply] using polyhedral_affineTiltEReal (u := u) hf_polyhedral
    obtain ⟨v, hvArg, hvEq⟩ :=
      exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regularity
        (f := tilt) (hf := htilt) (g := g) (hg := hg) (L := L)
        (hg_polyhedral := hg_polyhedral) (Or.inr ⟨hH, htilt_polyhedral, by
          simpa [tilt, effectiveDomain_affineTiltIoi f hf u] using hnonempty⟩)
    have hshift :
        compositeDualObjective tilt g L = shiftedCompositeDualObjective f g L u := by
      simpa [tilt] using
        tilted_compositeDualObjective_eq_shiftedCompositeDualObjective f hf g L u
    have hshift' :
        tilt.asEReal∗ᵛ ∘ L.adjoint + g.asEReal∗ =
          shiftedCompositeDualObjective f g L u := by
      simpa [compositeDualObjective_eq_add_reflectedConjugates] using hshift
    have hvArg' : v ∈ Argmin (shiftedCompositeDualObjective f g L u) := by
      simpa [hshift'] using hvArg
    have hvShift :
        compositeDualObjective tilt g L v = shiftedCompositeDualObjective f g L u v := by
      simpa [hshift] using congrArg (fun ψ : K → EReal ↦ ψ v) hshift
    refine ⟨v, ?_, ?_⟩
    · exact hvArg'
    · have hneg := congrArg Neg.neg hvEq
      calc
        (compositePrimalObjective f g L)∗ u =
            compositeDualObjective tilt g L v := by
              simpa
                [tilt, neg_tilted_compositePrimalOptimalValue_eq_conjugate_comp f hf g L u] using
                hneg
        _ = shiftedCompositeDualObjective f g L u v := hvShift

/-- Helper for Theorem 15 27: evaluating the attained minimum rewrites the conjugate value as the
infimum of the shifted dual range. -/
private theorem conjugate_addComp_eq_sInf_range_shiftedCompositeDualObjective_of_regular_aux
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty))
    (u : H) :
    (compositePrimalObjective f g L)∗ u =
      sInf (Set.range (shiftedCompositeDualObjective f g L u)) := by
  obtain ⟨v, hvArg, hvEq⟩ :=
    exists_mem_argmin_shiftedCompositeDualObjective_eq_conjugate_addComp_of_regular_aux
      f hf g hg L hregular u
  have hvValue :
      shiftedCompositeDualObjective f g L u v =
        sInf (Set.range (shiftedCompositeDualObjective f g L u)) :=
    (mem_argmin_iff_eq_sInf).1 hvArg
  exact hvEq.trans hvValue

set_option maxHeartbeats 800000 in
-- The regularity proof expands several nested infimum and conjugation rewrites, so it needs a
-- larger heartbeat budget to elaborate reliably.
/-- Helper for Theorem 15 27: the regularity hypotheses identify the composite conjugate with the
dual infimal convolution. -/
private theorem conjugate_addComp_eq_dualInfimalConvolution_of_regular_aux
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (compositePrimalObjective f g L)∗ =
      f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗) := by
  let F : H → EReal := f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)
  have hdom :
      (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty :=
    effectiveDomain_inter_image_nonempty_of_regular f g L hregular
  ext u
  have hconj :
      (compositePrimalObjective f g L)∗ u = F∗∗ u := by
    simpa [F] using
      congrFun
        (conjugate_pointwiseAddComp_eq_biconjugate_dualInfimalConvolution
          f hf g hg L hdom)
        u
  have hvalue :
      (compositePrimalObjective f g L)∗ u =
        sInf (Set.range (shiftedCompositeDualObjective f g L u)) :=
    conjugate_addComp_eq_sInf_range_shiftedCompositeDualObjective_of_regular_aux
      f hf g hg L hregular u
  have hF_le :
      F u ≤ sInf (Set.range (shiftedCompositeDualObjective f g L u)) := by
    refine le_sInf ?_
    rintro _ ⟨v, rfl⟩
    change (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)) u ≤
      shiftedCompositeDualObjective f g L u v
    rw [infimalConvolution_apply]
    refine le_trans
      (iInf_le
        (fun y : H ↦ f.asEReal∗ y + (L.adjoint ▷ g.asEReal∗) (u - y))
        (u - L.adjoint v))
      ?_
    have hfiber :
        (L.adjoint ▷ g.asEReal∗) (L.adjoint v) ≤ g.asEReal∗ v := by
      rw [show
          (L.adjoint ▷ g.asEReal∗) (L.adjoint v) =
            sInf ((fun x ↦ g.asEReal∗ x) '' ((L.adjoint) ⁻¹' {L.adjoint v})) by
            simpa using
              infimalPostcomposition_apply
                (L := L.adjoint) (f := g.asEReal∗) (y := L.adjoint v)]
      exact sInf_le ⟨v, by simp, rfl⟩
    have huv : u - (u - L.adjoint v) = L.adjoint v := by
      abel
    calc
      f.asEReal∗ (u - L.adjoint v) + (L.adjoint ▷ g.asEReal∗) (u - (u - L.adjoint v))
          = f.asEReal∗ (u - L.adjoint v) + (L.adjoint ▷ g.asEReal∗) (L.adjoint v) := by
              rw [huv]
      _ ≤ f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v :=
            add_le_add_right hfiber (f.asEReal∗ (u - L.adjoint v))
      _ = shiftedCompositeDualObjective f g L u v := by
            rw [shiftedCompositeDualObjective_apply]
  have hsInf_le_F :
      sInf (Set.range (shiftedCompositeDualObjective f g L u)) ≤ F u := by
    calc
      sInf (Set.range (shiftedCompositeDualObjective f g L u)) =
          (compositePrimalObjective f g L)∗ u := hvalue.symm
      _ = F∗∗ u := hconj
      _ ≤ F u := biconjugate_le F u
  calc
    (compositePrimalObjective f g L)∗ u =
        sInf (Set.range (shiftedCompositeDualObjective f g L u)) := hvalue
    _ = F u := le_antisymm hsInf_le_F hF_le

variable
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty))

-- Proof sketch: combine Proposition 15.26 with the source-facing regularity split. Branch `(i)`
-- uses Theorem 15.23, while branches `(ii)` and `(iii)` route through Fact 15.25.
include hf hg hregular in
/-- Theorem 15 27: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, and
either (i) `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`, or (ii) `K` is
finite-dimensional, `g` is polyhedral, and `effectiveDomain g ∩ ri (L '' effectiveDomain f)` is
nonempty, or (iii) `H` and `K` are finite-dimensional, `f` and `g` are polyhedral, and
`effectiveDomain g ∩ L '' effectiveDomain f` is nonempty, then
`(compositePrimalObjective f g L)∗ = f^* □ (L^* ▷ g^*)`. -/
theorem conjugate_addComp_eq_dualInfimalConvolution_of_regular
    :
    (compositePrimalObjective f g L)∗ =
      f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗) := by
  exact
    conjugate_addComp_eq_dualInfimalConvolution_of_regular_aux
      f hf g hg L hregular

-- Proof sketch: evaluate Theorem 15.27 at `u` and rewrite the infimal postcomposition along
-- `L.adjoint` fiberwise. This turns the infimal convolution formula into the displayed infimum
-- over `v : K` of `f^*(u - L^* v) + g^*(v)`.
include hf hg hregular in
/-- Evaluating the composite conjugation formula at `u` yields the infimum form of `(15.43)`. -/
theorem conjugate_addComp_eq_sInf_range_shiftedCompositeDualObjective_of_regular
    (u : H) :
    (compositePrimalObjective f g L)∗ u =
      sInf (Set.range (shiftedCompositeDualObjective f g L u)) := by
  exact
    conjugate_addComp_eq_sInf_range_shiftedCompositeDualObjective_of_regular_aux
      f hf g hg L hregular u

-- Proof sketch: fix `u` and tilt the primal objective by the affine functional
-- `x ↦ -⟪x, u⟫_ℝ`. The same regularity branch split remains available for the tilted problem, so
-- Theorem 15.23 or Fact 15.25 yields a minimizer `v` of the dual objective; rewriting that dual
-- objective gives exactly `shiftedCompositeDualObjective f g L u`.
include hf hg hregular in
/-- The explicit minimization formula `(15.43)` is attained at some `v`, so the conjugate value is
the minimum of `v ↦ f^*(u - L^* v) + g^*(v)`. -/
theorem exists_mem_argmin_shiftedCompositeDualObjective_eq_conjugate_addComp_of_regular
    (u : H) :
    ∃ v ∈ Argmin (shiftedCompositeDualObjective f g L u),
      (compositePrimalObjective f g L)∗ u =
        shiftedCompositeDualObjective f g L u v := by
  exact
    exists_mem_argmin_shiftedCompositeDualObjective_eq_conjugate_addComp_of_regular_aux
      f hf g hg L hregular u

end FenchelRockafellarDuality

end ERealFunction
