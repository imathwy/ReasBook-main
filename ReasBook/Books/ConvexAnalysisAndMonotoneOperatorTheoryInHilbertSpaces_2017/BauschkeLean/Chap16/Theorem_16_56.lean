import Mathlib
import BauschkeLean.Chap01.Theorem_1_29
import BauschkeLean.Chap06.Corollary_6_15
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap01.Text_1_0_6
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap11.Proposition_11_5
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Theorem_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: on `ℝ`, the inner product is ordinary multiplication. -/
lemma real_inner_eq_mul_scalar (s t : ℝ) :
    inner ℝ s t = s * t := by
  -- Rewrite the scalar inner product through the `RCLike` formula and simplify.
  calc
    inner ℝ s t = (starRingEnd ℝ) s * t := RCLike.inner_apply' s t
    _ = s * t := by simp

/-- Helper for Theorem 16 56: a point of `line[ℝ, x0, x1]` is exactly a translated point of the
range of `toSpanSingleton ℝ (x1 - x0)`. -/
lemma mem_line_iff_exists_toSpanSingleton
    {x0 x1 y : H} :
    y ∈ (line[ℝ, x0, x1] : Set H) ↔
      ∃ t : ℝ,
        y = x0 + ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t := by
  constructor
  · intro hy
    -- Reparameterize the affine-line witness through the concrete chord map.
    rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    -- Then rewrite the line map into the translated `toSpanSingleton` form used later.
    simp [AffineMap.lineMap_apply_module', add_comm]
  · rintro ⟨t, rfl⟩
    -- Convert the translated linear parameterization back to the canonical affine-line witness.
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ?_
    refine ⟨t, ?_⟩
    simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 16 56: the scalar line parameterization is the translated linear trace
through `toSpanSingleton ℝ (x1 - x0)`. -/
lemma lineMap_eq_add_toSpanSingleton
    (x0 x1 : H) (t : ℝ) :
    AffineMap.lineMap x0 x1 t =
      x0 + ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t := by
  -- Expand the affine line map into the base point plus the chord direction.
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 16 56: subtracting `{z}` after translating the effective domain by `x0`
is the same as subtracting `{x0 + z}` from the original effective domain. -/
lemma translated_effectiveDomain_sub_singleton_eq
    {f : H → Set.Ioi (⊥ : EReal)} (x0 z : H) :
    effectiveDomain (fun w : H ↦ f (x0 + w)) - ({z} : Set H) =
      effectiveDomain f - ({x0 + z} : Set H) := by
  -- Route correction: normalize the translated domain to a literal singleton difference first,
  -- so the later `ri` transport is a direct rewrite rather than nested `Set.mem_sub` juggling.
  ext w
  constructor
  · intro hw
    rcases Set.mem_sub.mp hw with ⟨u, hu, v, hv, huv⟩
    have hvz : v = z := Set.mem_singleton_iff.mp hv
    subst v
    refine Set.mem_sub.mpr ⟨x0 + u, ?_, x0 + z, by simp, ?_⟩
    · -- The translated-domain witness becomes an original-domain witness by evaluation.
      simpa [mem_effectiveDomain_iff] using hu
    · -- Both set differences encode the same translated chord variable.
      calc
        (x0 + u) - (x0 + z) = u - z := by abel
        _ = w := huv
  · intro hw
    rcases Set.mem_sub.mp hw with ⟨y, hy, v, hv, hwv⟩
    have hvz : v = x0 + z := Set.mem_singleton_iff.mp hv
    subst v
    refine Set.mem_sub.mpr ?_
    refine ⟨y - x0, ?_, z, by simp, ?_⟩
    · -- Repackage the original-domain witness into the translated owner by evaluation again.
      rw [mem_effectiveDomain_iff] at hy ⊢
      simpa using hy
    · calc
        (y - x0) - z = y - (x0 + z) := by abel
        _ = w := hwv

/-- Helper for Theorem 16 56: translating the effective domain by `x0` also translates its
relative interior. -/
lemma mem_relativeInterior_precompose_add_const_iff
    [FiniteDimensional ℝ H]
    {f : H → Set.Ioi (⊥ : EReal)} {x0 z : H} :
    z ∈ ri (effectiveDomain (fun w : H ↦ f (x0 + w))) ↔
      x0 + z ∈ ri (effectiveDomain f) := by
  -- Rewrite both relative-interior memberships to the cone/span criterion, then transport the
  -- translated singleton difference through the canonical set rewrite above.
  rw [Set.mem_relativeInterior_iff, Set.mem_relativeInterior_iff]
  constructor
  · rintro ⟨hz_dom, hz_cone_span⟩
    refine ⟨?_, ?_⟩
    · -- First unwrap translated domain membership into the original coordinate.
      rw [mem_effectiveDomain_iff] at hz_dom ⊢
      simpa using hz_dom
    · -- Then rewrite the translated difference owner into the original singleton difference.
      simpa [translated_effectiveDomain_sub_singleton_eq (f := f) x0 z] using hz_cone_span
  · rintro ⟨hz_dom, hz_cone_span⟩
    refine ⟨?_, ?_⟩
    · -- Package the original domain witness back into the translated effective-domain owner.
      rw [mem_effectiveDomain_iff] at hz_dom ⊢
      simpa using hz_dom
    · -- The cone/span equality is the same equality after the singleton-difference rewrite.
      simpa [translated_effectiveDomain_sub_singleton_eq (f := f) x0 z] using hz_cone_span

/-- Helper for Theorem 16 56: translating the effective domain by `x0` also translates its
ordinary interior. -/
lemma mem_interior_precompose_add_const_iff
    {f : H → Set.Ioi (⊥ : EReal)} {x0 z : H} :
    z ∈ interior (effectiveDomain (fun w : H ↦ f (x0 + w))) ↔
      x0 + z ∈ interior (effectiveDomain f) := by
  have hdom :
      effectiveDomain (fun w : H ↦ f (x0 + w)) =
        (Homeomorph.addLeft x0) ⁻¹' effectiveDomain f := by
    ext w
    simp [mem_effectiveDomain_iff]
  have hpre :
      (Homeomorph.addLeft x0) ⁻¹' interior (effectiveDomain f) =
        interior ((Homeomorph.addLeft x0) ⁻¹' effectiveDomain f) := by
    simpa using (Homeomorph.preimage_interior (Homeomorph.addLeft x0) (effectiveDomain f))
  constructor
  · intro hz
    -- Rewrite the translated effective domain as the preimage under the translation homeomorphism.
    have hz_int :
        z ∈ (Homeomorph.addLeft x0) ⁻¹' interior (effectiveDomain f) := by
      rw [hpre]
      simpa [hdom] using hz
    -- Evaluate the preimage membership at `z`.
    simpa using hz_int
  · intro hz
    have hz_pre :
        z ∈ (Homeomorph.addLeft x0) ⁻¹' interior (effectiveDomain f) := by
      simpa using hz
    have hz_int :
        z ∈ interior ((Homeomorph.addLeft x0) ⁻¹' effectiveDomain f) := by
      rw [← hpre]
      exact hz_pre
    -- Return to the translated effective domain owner used in this file.
    simpa [hdom] using hz_int

/-- Helper for Theorem 16 56: translating `effectiveDomain f` by `-x0` and subtracting the chord
range is exactly the same owner as subtracting the affine line through `x0` and `x1`. -/
lemma translated_effectiveDomain_sub_range_eq_line_difference
    {f : H → Set.Ioi (⊥ : EReal)} (x0 x1 : H) :
    effectiveDomain (fun z : H ↦ f (x0 + z)) -
        Set.range (ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0)) =
      effectiveDomain f - (line[ℝ, x0, x1] : Set H) := by
  -- Route correction: isolate the translated set-owner rewrite before the `sri` proof, so branch
  -- `(i)` becomes a direct `simpa` instead of repeating the same `Set.mem_sub` transport later.
  ext w
  constructor
  · intro hw
    rcases Set.mem_sub.mp hw with ⟨u, hu, v, hv, huv⟩
    rcases hv with ⟨t, rfl⟩
    refine Set.mem_sub.mpr ?_
    refine ⟨x0 + u, ?_, x0 + ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t, ?_, ?_⟩
    · -- The translated-domain witness is already a point of the original effective domain.
      simpa [mem_effectiveDomain_iff] using hu
    · -- The affine line is the translated range of `toSpanSingleton`.
      exact
        (mem_line_iff_exists_toSpanSingleton (x0 := x0) (x1 := x1)
          (y := x0 + ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t)).2 ⟨t, rfl⟩
    · -- Both difference owners encode the same translated chord variable.
      calc
        (x0 + u) - (x0 + ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t)
            = u - ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t := by
                abel
        _ = w := huv
  · intro hw
    rcases Set.mem_sub.mp hw with ⟨y, hy, z, hz, hyz⟩
    rcases
        (mem_line_iff_exists_toSpanSingleton (x0 := x0) (x1 := x1) (y := z)).1 hz with
      ⟨t, rfl⟩
    refine Set.mem_sub.mpr ?_
    refine
      ⟨y - x0, ?_, ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t, ⟨t, rfl⟩, ?_⟩
    · -- Re-express original effective-domain membership in translated coordinates.
      rw [mem_effectiveDomain_iff] at hy ⊢
      simpa using hy
    · -- Undoing the translation recovers the original difference witness.
      calc
        (y - x0) - ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t
            = y - (x0 + ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0) t) := by
                abel
        _ = w := hyz

/-- Helper for Theorem 16 56: an interior point of the left set and a point of the right set
produce an interior neighborhood of the origin in the Minkowski difference. -/
lemma zero_mem_interior_sub_of_mem_interior_left_mem_right {A D : Set H} {y : H}
    (hyD : y ∈ interior D) (hyA : y ∈ A) :
    (0 : H) ∈ interior (D - A) := by
  -- Translate the interior ball at `y` back to the origin while keeping the right witness fixed.
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hyD) with ⟨ε, hε, hball⟩
  have hsubset : Metric.ball (0 : H) ε ⊆ D - A := by
    intro z hz
    refine Set.mem_sub.mpr ?_
    refine ⟨y + z, hball ?_, y, hyA, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm, dist_comm, sub_eq_add_neg, add_assoc] using hz
    · abel
  refine mem_interior_iff_mem_nhds.mpr ?_
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) hε) hsubset

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: the linear functional `x ↦ -⟪x, u⟫`, packaged through `toEReal`,
belongs to `Γ₀(H)`. -/
lemma negative_inner_toEReal_mem_gammaZero (u : H) :
    (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · have hcont :
        Continuous (fun x : H ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) := by
      simpa using continuous_coe_real_ereal.comp ((continuous_id.inner continuous_const).neg)
    exact hcont.lowerSemicontinuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · refine ⟨0, ?_⟩
      simp
    · intro x _hx y _hy a ha0 ha1
      have hreal :
          -⟪a • x + (1 - a) • y, u⟫_ℝ =
            a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      have hcast :
          (((-⟪a • x + (1 - a) • y, u⟫_ℝ : ℝ) : EReal)) =
            (((a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
      simpa [Function.toEReal_apply, EReal.coe_add, EReal.coe_mul] using le_of_eq hcast

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: the effective domain of `x ↦ -⟪x, u⟫` is all of `H`. -/
lemma effectiveDomain_negative_inner_toEReal (u : H) :
    effectiveDomain ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) = Set.univ := by
  ext x
  simp

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: at the matching point `w = -u`, the conjugate of
`x ↦ -⟪x, u⟫` vanishes. -/
lemma conjugate_negative_inner_toEReal_apply_eq_zero
    (u w : H) (hw : w = -u) :
    (((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal).asEReal)∗ w = 0 := by
  let f : H → Set.Ioi (⊥ : EReal) := (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal
  rw [conjugate_apply]
  subst hw
  simp [Function.toEReal_apply]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: off the matching point `w = -u`, the conjugate of
`x ↦ -⟪x, u⟫` is `⊤`. -/
lemma conjugate_negative_inner_toEReal_apply_eq_top
    (u w : H) (hw : w ≠ -u) :
    (((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal).asEReal)∗ w = ⊤ := by
  let f : H → Set.Ioi (⊥ : EReal) := (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal
  rw [conjugate_apply]
  have hwu_ne : w + u ≠ 0 := by
    simpa [eq_neg_iff_add_eq_zero] using hw
  have hnorm_sq_pos : 0 < ‖w + u‖ ^ 2 := by
    have hnorm_pos : 0 < ‖w + u‖ := norm_pos_iff.mpr hwu_ne
    nlinarith
  rw [EReal.eq_top_iff_forall_lt]
  intro a
  let x : H := (((a + 1) / ‖w + u‖ ^ 2) : ℝ) • (w + u)
  have hreal :
      ⟪x, w⟫_ℝ - (-⟪x, u⟫_ℝ) = a + 1 := by
    calc
      ⟪x, w⟫_ℝ - (-⟪x, u⟫_ℝ) = ⟪x, w + u⟫_ℝ := by
        rw [inner_add_right]
        ring
      _ = (((a + 1) / ‖w + u‖ ^ 2) : ℝ) * ‖w + u‖ ^ 2 := by
        simpa [x, smul_add, real_inner_self_eq_norm_sq] using
          (real_inner_smul_left (w + u) (w + u) (((a + 1) / ‖w + u‖ ^ 2) : ℝ))
      _ = a + 1 := by
        field_simp [hnorm_sq_pos.ne']
  have hx_defect :
      (((⟪x, w⟫_ℝ : ℝ) : EReal) - (f x : EReal)) =
        ((a + 1 : ℝ) : EReal) := by
    simpa [f, Function.toEReal_apply, sub_eq_add_neg] using
      congrArg (fun r : ℝ ↦ (r : EReal)) hreal
  have ha_lt_defect :
      ((a : ℝ) : EReal) < (((⟪x, w⟫_ℝ : ℝ) : EReal) - (f x : EReal)) := by
    rw [hx_defect]
    exact_mod_cast lt_add_of_pos_right a zero_lt_one
  rw [lt_iSup_iff]
  exact ⟨x, by simpa using ha_lt_defect⟩

/-- Helper for Theorem 16 56: for the linear tilt `x ↦ -⟪x, u⟫`, the Chapter 15 dual owner is
the conjugate of `g` restricted to the fiber `L.adjoint v = u`. -/
lemma compositeDualObjective_negative_inner_toEReal_apply
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (u : H) (v : K) (hLv : L.adjoint v = u) :
    compositeDualObjective ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) g L v = g.asEReal∗ v := by
  rw [compositeDualObjective_apply]
  have hneg : -(L.adjoint v) = -u := by
    simpa using congrArg Neg.neg hLv
  rw [conjugate_negative_inner_toEReal_apply_eq_zero (u := u) (w := -(L.adjoint v)) hneg]
  simp

/-- Helper for Theorem 16 56: away from the fiber `L.adjoint v = u`, the linear-tilted
composite dual objective is `⊤`. -/
lemma compositeDualObjective_negative_inner_toEReal_apply_eq_top
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (u : H) (v : K) (hLv : L.adjoint v ≠ u) :
    compositeDualObjective ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) g L v = ⊤ := by
  rw [compositeDualObjective_apply]
  have hneg : -(L.adjoint v) ≠ -u := by
    intro hneg_eq
    apply hLv
    simpa using congrArg Neg.neg hneg_eq
  have hg_ne_bot : g.asEReal∗ v ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty v
  rw [conjugate_negative_inner_toEReal_apply_eq_top (u := u) (w := -(L.adjoint v)) hneg]
  rw [EReal.top_add_of_ne_bot hg_ne_bot]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: `0 ∈ sri (effectiveDomain g - range L)` forces the range of `L`
to meet the effective domain of `g`. -/
lemma range_inter_effectiveDomain_nonempty_of_zero_mem_sri_sub_range
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L)) :
    (Set.range L ∩ effectiveDomain g).Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨y, hy, z, hz, hyz⟩
  rcases hz with ⟨x, rfl⟩
  refine ⟨y, ?_, hy⟩
  simpa [sub_eq_zero.mp hyz]

/-- Helper for Theorem 16 56: under the `sri` branch, the adjoint infimal postcomposition of the
Fenchel conjugate is exact on every finite fiber. -/
lemma infimalPostcomposition_adjoint_conjugate_exact_of_zero_mem_sri_sub_range
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L)) :
    infimalPostcomposition.Exact L.adjoint (g∗[hg]) := by
  intro u hu_dom
  let f : H → Set.Ioi (⊥ : EReal) := (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal
  have hf : f ∈ Γ₀(H) := negative_inner_toEReal_mem_gammaZero (u := u)
  obtain ⟨v, hvArg, _⟩ :=
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      f hf g hg L <| by
        simpa [f, effectiveDomain_negative_inner_toEReal] using hsri
  rw [mem_argmin_iff, isMinOn_univ_iff] at hvArg
  have hu_lt : (L.adjoint ▷ g∗[hg]) u < ⊤ := by
    rw [mem_dom_iff] at hu_dom
    exact hu_dom
  have hu_lt' :
      sInf (((fun x ↦ ((g∗[hg] x : Set.Ioi (⊥ : EReal)) : EReal)) '' (L.adjoint ⁻¹' {u}))) < ⊤ := by
    simpa [infimalPostcomposition_apply] using hu_lt
  obtain ⟨_, ⟨w, hw_fiber, rfl⟩, hw_lt_top⟩ := sInf_lt_iff.mp hu_lt'
  have hwEq : L.adjoint w = u := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hw_fiber
  have hwDual_eq :
      compositeDualObjective f g L w = g.asEReal∗ w := by
    exact compositeDualObjective_negative_inner_toEReal_apply g L u w hwEq
  have hwDual_lt : compositeDualObjective f g L w < ⊤ := by
    rw [hwDual_eq]
    simpa [gammaZeroConjugate_apply] using hw_lt_top
  have hvDual_lt : compositeDualObjective f g L v < ⊤ := by
    exact lt_of_le_of_lt (hvArg w) hwDual_lt
  have hLv : L.adjoint v = u := by
    by_contra hne
    have hvDual_eq_top : compositeDualObjective f g L v = ⊤ := by
      simpa [f, hne] using
        compositeDualObjective_negative_inner_toEReal_apply_eq_top g hg L u v hne
    rw [hvDual_eq_top] at hvDual_lt
    exact (lt_irrefl (⊤ : EReal)) hvDual_lt
  refine (infimalPostcomposition.exactAt_iff_exists_eq L.adjoint (g∗[hg]) u).2 ?_
  refine ⟨hu_dom, v, hLv, ?_⟩
  have hupper : (L.adjoint ▷ g∗[hg]) u ≤ (g∗[hg] v : EReal) := by
    change
      sInf (((fun x ↦ ((g∗[hg] x : Set.Ioi (⊥ : EReal)) : EReal)) '' (L.adjoint ⁻¹' {u}))) ≤
        (g∗[hg] v : EReal)
    refine sInf_le ?_
    exact ⟨v, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hLv, rfl⟩
  have hlower : (g∗[hg] v : EReal) ≤ (L.adjoint ▷ g∗[hg]) u := by
    change
      (g∗[hg] v : EReal) ≤
        sInf (((fun x ↦ ((g∗[hg] x : Set.Ioi (⊥ : EReal)) : EReal)) '' (L.adjoint ⁻¹' {u})))
    refine le_sInf ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzEq : L.adjoint z = u := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hz
    have hvDual_eq :
        compositeDualObjective f g L v = g.asEReal∗ v := by
      exact compositeDualObjective_negative_inner_toEReal_apply g L u v hLv
    have hzDual_eq :
        compositeDualObjective f g L z = g.asEReal∗ z := by
      exact compositeDualObjective_negative_inner_toEReal_apply g L u z hzEq
    have hle : g.asEReal∗ v ≤ g.asEReal∗ z := by
      calc
        g.asEReal∗ v = compositeDualObjective f g L v := hvDual_eq.symm
        _ ≤ compositeDualObjective f g L z := hvArg z
        _ = g.asEReal∗ z := hzDual_eq
    simpa [gammaZeroConjugate_apply] using hle
  exact le_antisymm hupper hlower

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: for a function with nonempty effective domain, subgradient
membership is equivalent to Fenchel--Young equality. -/
lemma mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (x : H) (hdom : (effectiveDomain f).Nonempty) (u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  have hproper : IsProper f.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (f y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  constructor
  · intro hu
    have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    have hx : x ∈ effectiveDomain f :=
      subdifferential_domain_subset_effectiveDomain f hdom hx_dom
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hu_halfspace :
        ∀ y ∈ effectiveDomain f,
          ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hu
      exact hu
    have hdefect_le :
        ∀ y : H,
          ((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal) ≤
            ((⟪x, u⟫_ℝ : ℝ) : EReal) - (f x : EReal) := by
      intro y
      by_cases hy : y ∈ effectiveDomain f
      · have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
        have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
        have hinner_sub :
            ⟪y - x, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ := by
          simp [sub_eq_add_neg, inner_add_left]
        have hdefect_real :
            ⟪y, u⟫_ℝ - (f y : EReal).toReal ≤ ⟪x, u⟫_ℝ - (f x : EReal).toReal := by
          linarith [hu_halfspace y hy, hinner_sub]
        have hy_toReal :
            ((((f y : EReal).toReal : ℝ) : EReal)) = (f y : EReal) :=
          EReal.coe_toReal hy_top hy_bot
        have hx_toReal :
            ((((f x : EReal).toReal : ℝ) : EReal)) = (f x : EReal) :=
          EReal.coe_toReal hfx_top hfx_bot
        have hdefect_ereal :
            (((⟪y, u⟫_ℝ - (f y : EReal).toReal : ℝ) : EReal)) ≤
              (((⟪x, u⟫_ℝ - (f x : EReal).toReal : ℝ) : EReal)) :=
          EReal.coe_le_coe_iff.mpr hdefect_real
        simpa [EReal.coe_sub, hy_toReal, hx_toReal] using hdefect_ereal
      · have hy_top : (f y : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
        rw [hy_top, EReal.sub_top]
        exact bot_le
    have hconj_le : f.asEReal∗ u ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x := by
      rw [conjugate_apply]
      exact iSup_le hdefect_le
    have hsum_le : (f x : EReal) + f.asEReal∗ u ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      simpa [add_comm] using
        (EReal.le_sub_iff_add_le (Or.inl hfx_bot) (Or.inl hfx_top)).1 hconj_le
    have hfy_le :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + f.asEReal∗ u := by
      simpa using fenchel_young_inequality hproper x u
    exact le_antisymm hsum_le hfy_le
  · intro hEq
    have hconj_bot : f.asEReal∗ u ≠ ⊥ :=
      conjugate_ne_bot_of_isProper hproper u
    have hfx_top : (f x : EReal) ≠ ⊤ := by
      intro hx_top
      have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
        rw [hx_top]
        exact EReal.top_add_of_ne_bot hconj_bot
      exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)
    have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hconj_top : f.asEReal∗ u ≠ ⊤ := by
      intro hu_top
      have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
        rw [hu_top]
        exact EReal.add_top_of_ne_bot hfx_bot
      exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)
    have hx : x ∈ effectiveDomain f := by
      rw [mem_effectiveDomain_iff]
      exact lt_of_le_of_ne le_top hfx_top
    have hEq_real : (f x : EReal).toReal + (f.asEReal∗ u).toReal = ⟪x, u⟫_ℝ := by
      have hEq' := hEq
      rw [← EReal.coe_toReal hfx_top hfx_bot,
        ← EReal.coe_toReal hconj_top hconj_bot, ← EReal.coe_add] at hEq'
      exact EReal.coe_eq_coe_iff.mp hEq'
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂]
    intro y hy
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
    have hfy :
        ((⟪y, u⟫_ℝ : ℝ) : EReal) ≤ (f y : EReal) + f.asEReal∗ u := by
      simpa using fenchel_young_inequality hproper y u
    have hfy_real : ⟪y, u⟫_ℝ ≤ (f y : EReal).toReal + (f.asEReal∗ u).toReal := by
      have hfy' := hfy
      rw [← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_toReal hconj_top hconj_bot, ← EReal.coe_add] at hfy'
      exact EReal.coe_le_coe_iff.mp hfy'
    have hinner_sub :
        ⟪y - x, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ := by
      simp [sub_eq_add_neg, inner_add_left]
    have hineq :
        ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      linarith [hfy_real, hEq_real]
    simpa [hinner_sub] using hineq

/-- Helper for Theorem 16 56: under the `sri` branch, every subgradient of `g ∘ L`
already lies in the adjoint image `L^*(∂ g)(L x)`. -/
lemma mem_adjointImage_of_mem_subdifferential_comp_under_zero_mem_sri_range
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L))
    {x u : H} (hu : u ∈ (∂ (g ∘ L)) x) :
    u ∈ ContinuousLinearMap.adjointImageSubdifferential L g x := by
  have hdom : (Set.range L ∩ effectiveDomain g).Nonempty :=
    range_inter_effectiveDomain_nonempty_of_zero_mem_sri_sub_range (g := g) (L := L) hsri
  have hcomp_dom : (effectiveDomain (g ∘ L)).Nonempty := by
    rcases hdom with ⟨y, hy_range, hy_dom⟩
    rcases hy_range with ⟨x0, rfl⟩
    refine ⟨x0, ?_⟩
    simpa [mem_effectiveDomain_iff] using hy_dom
  have hu_eq :
      (g (L x) : EReal) + (g ∘ L).asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    exact
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        (f := g ∘ L) x hcomp_dom u).1 hu
  have hcomp_eq : (g ∘ L).asEReal∗ u = (L.adjoint ▷ g.asEReal∗) u := by
    simpa [Function.asEReal_apply] using
      congrFun (conjugate_comp_eq_adjointInfimalPostcomposition (g := g) (hg := hg) (L := L) hdom) u
  have hu_finite : (L.adjoint ▷ g.asEReal∗) u < ⊤ := by
    have htop : (g ∘ L).asEReal∗ u ≠ ⊤ := by
      intro htop
      have hsum : (g (L x) : EReal) + (g ∘ L).asEReal∗ u = ⊤ := by
        rw [htop, EReal.add_top_of_ne_bot (ne_of_gt (g (L x)).2)]
      exact EReal.coe_ne_top _ (hu_eq.symm.trans hsum)
    rw [← hcomp_eq]
    exact lt_top_iff_ne_top.mpr htop
  have hu_dom : u ∈ dom (L.adjoint ▷ g∗[hg]) := by
    rw [mem_dom_iff]
    simpa [infimalPostcomposition_apply, gammaZeroConjugate_apply] using hu_finite
  obtain ⟨_, v, hLv, huvalue⟩ :=
    (infimalPostcomposition.exactAt_iff_exists_eq L.adjoint (g∗[hg]) u).1
      (infimalPostcomposition_adjoint_conjugate_exact_of_zero_mem_sri_sub_range
        (g := g) (hg := hg) (L := L) hsri hu_dom)
  have hinner_real : ⟪x, u⟫_ℝ = ⟪L x, v⟫_ℝ := by
    simpa [hLv] using (ContinuousLinearMap.adjoint_inner_right L x v)
  have hinner : ((⟪x, u⟫_ℝ : ℝ) : EReal) = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := by
    exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner_real
  have huvalue' : (L.adjoint ▷ g.asEReal∗) u = g.asEReal∗ v := by
    simpa [infimalPostcomposition_apply, gammaZeroConjugate_apply] using huvalue
  have hgy :
      (g (L x) : EReal) + g.asEReal∗ v = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := by
    calc
      (g (L x) : EReal) + g.asEReal∗ v = (g (L x) : EReal) + (L.adjoint ▷ g.asEReal∗) u := by
        rw [huvalue'.symm]
      _ = (g (L x) : EReal) + (g ∘ L).asEReal∗ u := by
        rw [← hcomp_eq]
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hu_eq
      _ = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := hinner
  have hv_dom : (effectiveDomain g).Nonempty := hg.2.nonempty
  have hv : v ∈ (∂ g) (L x) := by
    exact
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        (f := g) (L x) hv_dom v).2 hgy
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
  exact ⟨v, hv, hLv⟩

/-- Helper for Theorem 16 56: the scalar linear tilt `s ↦ -m s`, viewed through `toEReal`,
belongs to `Γ₀(ℝ)`. -/
lemma neg_mul_toEReal_mem_gammaZero (m : ℝ) :
    (fun s : ℝ ↦ -m * s).toEReal ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity comes from continuity of the scalar linear map.
    have hcont : Continuous (fun s : ℝ ↦ (((-m * s : ℝ) : EReal))) := by
      simpa using continuous_coe_real_ereal.comp ((continuous_const.mul continuous_id).neg)
    exact hcont.lowerSemicontinuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The tilt is finite everywhere, so in particular at `0`.
      refine ⟨0, by simp⟩
    · intro s _hs t _ht a ha0 ha1
      have hreal :
          -m * (a * s + (1 - a) * t) =
            a * (-m * s) + (1 - a) * (-m * t) := by
        ring
      have hcast :
          (((-m * (a * s + (1 - a) * t) : ℝ) : EReal)) =
            (((a * (-m * s) + (1 - a) * (-m * t) : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
      simpa [Function.toEReal_apply, EReal.coe_add, EReal.coe_mul] using le_of_eq hcast

/-- Helper for Theorem 16 56: the everywhere-zero finite scalar function has singleton
subdifferential `{0}` at every base point. -/
lemma subdifferential_zero_toEReal_apply_real (t : ℝ) :
    (∂ ((fun _ : ℝ ↦ (0 : ℝ)).toEReal)) t = ({0} : Set ℝ) := by
  ext u
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
    have hzero_t :
        (((fun _ : ℝ ↦ (0 : ℝ)).toEReal t : Set.Ioi (⊥ : EReal)) : EReal) = 0 := by
      simp [Function.toEReal_apply]
    have hzero_tu :
        (((fun _ : ℝ ↦ (0 : ℝ)).toEReal (t + u) : Set.Ioi (⊥ : EReal)) : EReal) = 0 := by
      simp [Function.toEReal_apply]
    have htest0 := hu (t + u)
    have hsqE : (((u * u : ℝ)) : EReal) ≤ 0 := by
      calc
        (((u * u : ℝ)) : EReal)
            = (⟪t + u - t, u⟫_ℝ : EReal) +
                (((fun _ : ℝ ↦ (0 : ℝ)).toEReal t : Set.Ioi (⊥ : EReal)) : EReal) := by
                    have hreal : u * u = ⟪t + u - t, u⟫_ℝ + 0 := by
                      rw [real_inner_eq_mul_scalar]
                      ring
                    exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
        _ ≤ (((fun _ : ℝ ↦ (0 : ℝ)).toEReal (t + u) : Set.Ioi (⊥ : EReal)) : EReal) := htest0
        _ = 0 := hzero_tu
    have hsq : u * u ≤ 0 := by
      exact_mod_cast hsqE
    have hu_zero : u = 0 := by
      nlinarith [sq_nonneg u, hsq]
    simp [hu_zero]
  · intro hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    intro y
    have heq :
        (⟪y - t, (0 : ℝ)⟫_ℝ : EReal) +
            (((fun _ : ℝ ↦ (0 : ℝ)).toEReal t : Set.Ioi (⊥ : EReal)) : EReal) =
          (((fun _ : ℝ ↦ (0 : ℝ)).toEReal y : Set.Ioi (⊥ : EReal)) : EReal) := by
      simp [Function.toEReal_apply]
    exact le_of_eq heq

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: translating a `Γ₀(H)` function by `x0` preserves `Γ₀(H)`. -/
lemma precompose_add_const_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (x0 : H) :
    (fun z : H ↦ f (x0 + z)) ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · -- Lower semicontinuity is stable under composition with the translation map.
    simpa [Function.comp] using hf.1.comp (continuous_const.add continuous_id)
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- Translate an effective-domain witness back by `-x0`.
      rcases hf.2.nonempty with ⟨y, hy⟩
      refine ⟨y - x0, ?_⟩
      rw [mem_effectiveDomain_iff]
      simpa [sub_eq_add_neg, add_assoc] using hy
    · intro z hz w hw a ha0 ha1
      have hz' : x0 + z ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using hz
      have hw' : x0 + w ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using hw
      have hcombo :
          x0 + (a • z + (1 - a) • w) = a • (x0 + z) + (1 - a) • (x0 + w) := by
        calc
          x0 + (a • z + (1 - a) • w)
              = (a + (1 - a)) • x0 + (a • z + (1 - a) • w) := by
                  simp
          _ = a • x0 + (1 - a) • x0 + (a • z + (1 - a) • w) := by
                rw [add_smul]
          _ = a • x0 + (a • z + ((1 - a) • x0 + (1 - a) • w)) := by
                abel
          _ = a • (x0 + z) + (1 - a) • (x0 + w) := by
                simp [smul_add, add_assoc]
      -- Re-express the translated convex combination in the original coordinates.
      simpa [hcombo] using hf.2.ineq hz' hw' ha0 ha1

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: translating the argument shifts the subdifferential base point but
leaves the subgradient vector unchanged. -/
lemma mem_subdifferential_precompose_add_const_iff
    {f : H → Set.Ioi (⊥ : EReal)} (x0 z u : H) :
    u ∈ (∂ fun w : H ↦ f (x0 + w)) z ↔ u ∈ (∂ f) (x0 + z) := by
  constructor
  · intro hu
    rw [mem_subdifferential_iff] at hu ⊢
    intro y
    -- Shift the test point back by `x0` so the translated and original inequalities match.
    have hshift : y - (x0 + z) = y - x0 - z := by
      abel
    simpa [hshift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu (y - x0)
  · intro hu
    rw [mem_subdifferential_iff] at hu ⊢
    intro y
    -- Translate the test point forward by `x0` to recover the original subgradient inequality.
    have hshift : x0 + y - (x0 + z) = y - z := by
      abel
    simpa [hshift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu (x0 + y)

/-- Helper for Theorem 16 56: the regularity hypothesis on the affine line yields the canonical
owner hypothesis `0 ∈ sri (effectiveDomain g - Set.range L)` for the translated-linear model. -/
lemma zero_mem_sri_translated_domain_sub_range_of_segment_regularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x0 x1 : H}
    (hregular :
      (0 : H) ∈ sri (effectiveDomain f - (line[ℝ, x0, x1] : Set H)) ∨
        ((line[ℝ, x0, x1] : Set H) ∩ interior (effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧
          ((line[ℝ, x0, x1] : Set H) ∩ ri (effectiveDomain f)).Nonempty)) :
    let g : H → Set.Ioi (⊥ : EReal) := fun z ↦ f (x0 + z)
    let L : ℝ →L[ℝ] H := ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0)
    (0 : H) ∈ sri (effectiveDomain g - Set.range L) := by
  dsimp
  let g : H → Set.Ioi (⊥ : EReal) := fun z ↦ f (x0 + z)
  let L : ℝ →L[ℝ] H := ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0)
  have hg : g ∈ Γ₀(H) := by
    -- The translated function stays in `Γ₀(H)`, so its effective domain is convex.
    simpa [g] using precompose_add_const_mem_gammaZero hf x0
  have hL_range : Set.range L = (L.range : Set H) := by
    ext y
    rfl
  have hL_convex : Convex ℝ (Set.range L) := by
    -- The chord owner on the right is a linear range, hence convex.
    rw [hL_range]
    exact L.range.convex
  have hsub_convex : Convex ℝ (effectiveDomain g - Set.range L) :=
    hg.2.convex_effectiveDomain.sub hL_convex
  rcases hregular with hsri | hinter | hri
  · -- Branch `(i)`: after normalizing the owner set, the hypothesis is already the desired one.
    simpa [g, L, translated_effectiveDomain_sub_range_eq_line_difference (f := f) x0 x1] using hsri
  · rcases hinter with ⟨y, hyline, hyint⟩
    rcases
        (mem_line_iff_exists_toSpanSingleton (x0 := x0) (x1 := x1) (y := y)).1 hyline with
      ⟨t, rfl⟩
    have ht_range :
        L t ∈ Set.range L := by
      exact ⟨t, rfl⟩
    have ht_int :
        L t ∈ interior (effectiveDomain g) := by
      -- Transport the interior witness through the translation `z ↦ x0 + z`.
      exact
        (mem_interior_precompose_add_const_iff
          (f := f) (x0 := x0) (z := L t)).2 <| by
            simpa [g, L]
    have h0_int : (0 : H) ∈ interior (effectiveDomain g - Set.range L) :=
      zero_mem_interior_sub_of_mem_interior_left_mem_right ht_int ht_range
    -- Nonempty interior identifies `interior` with `sri` for this convex difference owner.
    rw [← interior_eq_strongRelativeInterior_of_convex_nonempty_interior hsub_convex ⟨0, h0_int⟩]
    exact h0_int
  · rcases hri with ⟨hfd, hri_nonempty⟩
    letI : FiniteDimensional ℝ H := hfd
    rcases hri_nonempty with ⟨y, hyline, hyri⟩
    rcases
        (mem_line_iff_exists_toSpanSingleton (x0 := x0) (x1 := x1) (y := y)).1 hyline with
      ⟨t, rfl⟩
    have ht_range :
        L t ∈ Set.range L := by
      exact ⟨t, rfl⟩
    have ht_ri_dom :
        L t ∈ ri (effectiveDomain g) := by
      -- Transport the relative-interior witness through the same translation.
      exact
        (mem_relativeInterior_precompose_add_const_iff
          (f := f) (x0 := x0) (z := L t)).2 <| by
            simpa [g, L]
    have ht_ri_range :
        L t ∈ ri (Set.range L) := by
      -- A linear range is a submodule, so its relative interior is itself.
      rw [hL_range]
      simpa [relativeInterior_submodule_eq_self] using
        (show L t ∈ (L.range : Set H) from ⟨t, rfl⟩)
    have h0_ri : (0 : H) ∈ ri (effectiveDomain g - Set.range L) := by
      -- In finite dimension, the relative interior of a difference is the difference of the
      -- relative interiors.
      rw [relativeInterior_sub_eq_sub_relativeInterior_of_finiteDimensional
        (effectiveDomain g) (Set.range L) hg.2.nonempty ⟨0, ⟨0, by simp [L]⟩⟩
        hg.2.convex_effectiveDomain hL_convex]
      exact Set.mem_sub.mpr ⟨L t, ht_ri_dom, L t, ht_ri_range, sub_self (L t)⟩
    -- In finite dimension, `sri` and `ri` agree for convex sets.
    rw [strongRelativeInterior_eq_relativeInterior_of_finiteDimensional hsub_convex]
    exact h0_ri

/-- Helper for Theorem 16 56: the real secant slope rewrites back to the endpoint difference once
both endpoint values are finite. -/
lemma secant_slope_cast_eq_endpoint_difference
    {ψ : ℝ → Set.Ioi (⊥ : EReal)}
    (hψ0 : 0 ∈ effectiveDomain ψ) (hψ1 : 1 ∈ effectiveDomain ψ)
    (m : ℝ) (hm : m = (ψ 1 : EReal).toReal - (ψ 0 : EReal).toReal) :
    ((m : ℝ) : EReal) = (ψ 1 : EReal) - (ψ 0 : EReal) := by
  -- Rewrite both finite endpoint values through `toReal`, then the secant slope is literal
  -- subtraction in `ℝ`.
  subst m
  have hψ0_top : (ψ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hψ0)
  have hψ0_bot : (ψ 0 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (ψ 0 : EReal) from (ψ 0).2)
  have hψ1_top : (ψ 1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hψ1)
  have hψ1_bot : (ψ 1 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (ψ 1 : EReal) from (ψ 1).2)
  calc
    ((((ψ 1 : EReal).toReal - (ψ 0 : EReal).toReal : ℝ)) : EReal)
        = (((ψ 1 : EReal).toReal : ℝ) : EReal) - (((ψ 0 : EReal).toReal : ℝ) : EReal) := by
            rw [EReal.coe_sub]
    _ = (ψ 1 : EReal) - (ψ 0 : EReal) := by
          rw [EReal.coe_toReal hψ1_top hψ1_bot, EReal.coe_toReal hψ0_top hψ0_bot]

/-- Helper for Theorem 16 56: tilting a scalar `Γ₀(ℝ)` function by a finite affine map keeps the
result in `Γ₀(ℝ)`. -/
lemma secant_tilt_mem_gammaZero
    {ψ : ℝ → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(ℝ)) (m : ℝ)
    (hψ0 : 0 ∈ effectiveDomain ψ) :
    ψ + (fun s : ℝ ↦ -m * s).toEReal ∈ Γ₀(ℝ) := by
  -- The linear tilt is a `Γ₀` summand with full effective domain, so pointwise addition applies.
  have htilt : (fun s : ℝ ↦ -m * s).toEReal ∈ Γ₀(ℝ) :=
    neg_mul_toEReal_mem_gammaZero m
  have htilt0 : 0 ∈ effectiveDomain ((fun s : ℝ ↦ -m * s).toEReal) := by
    simp
  have hdom : (effectiveDomain ψ ∩ effectiveDomain ((fun s : ℝ ↦ -m * s).toEReal)).Nonempty := by
    exact ⟨0, hψ0, htilt0⟩
  exact pointwiseAdd_mem_gammaZero ψ ((fun s : ℝ ↦ -m * s).toEReal) hψ htilt hdom

/-- Helper for Theorem 16 56: if a scalar `Γ₀(ℝ)` function has equal endpoint values on
`[0,1]`, then it has a minimizer in the open interval `]0,1[`. -/
lemma exists_interior_isMinOn_Icc_of_mem_gammaZero_of_eq_endpoints
    {η : ℝ → Set.Ioi (⊥ : EReal)} (hη : η ∈ Γ₀(ℝ))
    (hη_dom : Set.Icc (0 : ℝ) 1 ⊆ effectiveDomain η)
    (hη_end : η 0 = η 1) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, IsMinOn η.asEReal (Set.Icc (0 : ℝ) 1) t := by
  -- First take a constrained minimizer on the compact interval.
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simp
  have hdom_nonempty :
      (Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | η.asEReal x < ⊤}).Nonempty := by
    exact ⟨0, hzero_mem, hη_dom hzero_mem⟩
  obtain ⟨t0, ht0_Icc, ht0_min⟩ :=
    lowerSemicontinuous_exists_isMinOn_of_isCompact hη.1 isCompact_Icc hdom_nonempty
  by_cases ht0_Ioo : t0 ∈ Set.Ioo (0 : ℝ) 1
  · exact ⟨t0, ht0_Ioo, ht0_min⟩
  · -- If the compact minimizer lands on the boundary, convexity and equal endpoint values move it
    -- to the midpoint.
    have ht0_eq : t0 = 0 ∨ t0 = 1 := by
      rcases ht0_Icc with ⟨ht0_nonneg, ht0_le_one⟩
      by_contra ht0_ne
      apply ht0_Ioo
      constructor
      · have ht0_pos : 0 < t0 := by
          by_contra ht0_not_pos
          have ht0_le_zero : t0 ≤ 0 := le_of_not_gt ht0_not_pos
          apply ht0_ne
          left
          linarith
        exact ht0_pos
      · have ht0_lt_one : t0 < 1 := by
          by_contra ht0_not_lt
          have h_one_le_t0 : 1 ≤ t0 := le_of_not_gt ht0_not_lt
          apply ht0_ne
          right
          linarith
        exact ht0_lt_one
    have hone_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      simp
    have hhalf_mem_Icc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hhalf_mem_Ioo : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hη0_dom : 0 ∈ effectiveDomain η := hη_dom hzero_mem
    have hη1_dom : 1 ∈ effectiveDomain η := hη_dom hone_mem
    have ht0_dom : t0 ∈ effectiveDomain η := hη_dom ht0_Icc
    have hhalf_dom : (1 / 2 : ℝ) ∈ effectiveDomain η := hη_dom hhalf_mem_Icc
    have hη0_top : (η 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hη0_dom)
    have hη0_bot : (η 0 : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (η 0 : EReal) from (η 0).2)
    have hη1_top : (η 1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hη1_dom)
    have hη1_bot : (η 1 : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (η 1 : EReal) from (η 1).2)
    have ht0_top : (η t0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ht0_dom)
    have ht0_bot : (η t0 : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (η t0 : EReal) from (η t0).2)
    have hhalf_top : (η (1 / 2 : ℝ) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hhalf_dom)
    have hhalf_bot : (η (1 / 2 : ℝ) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (η (1 / 2 : ℝ) : EReal) from (η (1 / 2)).2)
    have hη01_toReal : (η 0 : EReal).toReal = (η 1 : EReal).toReal := by
      exact
        (EReal.toReal_eq_toReal hη0_top hη0_bot hη1_top hη1_bot).2 <|
          congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) hη_end
    have hhalf_le_left_real :
        (η (1 / 2 : ℝ) : EReal).toReal ≤ (η 0 : EReal).toReal := by
      have hconv_mid :
          (η (1 / 2 : ℝ) : EReal).toReal ≤
            (1 / 2 : ℝ) * (η 1 : EReal).toReal + (1 / 2 : ℝ) * (η 0 : EReal).toReal := by
        -- Jensen convexity at the midpoint gives the average-endpoint upper bound.
        simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (hη.2.toReal_convexOn_effectiveDomain).2
            hη1_dom hη0_dom
            (show 0 ≤ (1 / 2 : ℝ) by norm_num)
            (show 0 ≤ (1 / 2 : ℝ) by norm_num)
            (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      linarith
    have hhalf_le_right_real :
        (η (1 / 2 : ℝ) : EReal).toReal ≤ (η 1 : EReal).toReal := by
      have hconv_mid :
          (η (1 / 2 : ℝ) : EReal).toReal ≤
            (1 / 2 : ℝ) * (η 1 : EReal).toReal + (1 / 2 : ℝ) * (η 0 : EReal).toReal := by
        -- The same midpoint inequality also controls the right endpoint after rewriting values.
        simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (hη.2.toReal_convexOn_effectiveDomain).2
            hη1_dom hη0_dom
            (show 0 ≤ (1 / 2 : ℝ) by norm_num)
            (show 0 ≤ (1 / 2 : ℝ) by norm_num)
            (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      linarith
    have hhalf_le_t0_real :
        (η (1 / 2 : ℝ) : EReal).toReal ≤ (η t0 : EReal).toReal := by
      rcases ht0_eq with rfl | rfl
      · simpa using hhalf_le_left_real
      · simpa using hhalf_le_right_real
    have hhalf_le_t0 :
        (η (1 / 2 : ℝ) : EReal) ≤ (η t0 : EReal) := by
      calc
        (η (1 / 2 : ℝ) : EReal) = (((η (1 / 2 : ℝ) : EReal).toReal : ℝ) : EReal) := by
          exact (EReal.coe_toReal hhalf_top hhalf_bot).symm
        _ ≤ (((η t0 : EReal).toReal : ℝ) : EReal) := by
          exact EReal.coe_le_coe hhalf_le_t0_real
        _ = (η t0 : EReal) := by
          exact EReal.coe_toReal ht0_top ht0_bot
    have hhalf_min : IsMinOn η.asEReal (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
      rw [isMinOn_iff]
      intro z hz
      exact le_trans hhalf_le_t0 ((isMinOn_iff.mp ht0_min) z hz)
    exact ⟨1 / 2, hhalf_mem_Ioo, hhalf_min⟩

/-- Helper for Theorem 16 56: zero belongs to the subdifferential of the secant-tilted function
exactly when the secant slope belongs to the original subdifferential. -/
lemma zero_mem_subdifferential_secant_tilt_iff
    {ψ : ℝ → Set.Ioi (⊥ : EReal)} {t m : ℝ}
    (ht : t ∈ effectiveDomain ψ) :
    (0 : ℝ) ∈ (∂ (ψ + (fun s : ℝ ↦ -m * s).toEReal)) t ↔ m ∈ (∂ ψ) t := by
  let η : ℝ → Set.Ioi (⊥ : EReal) := ψ + (fun s : ℝ ↦ -m * s).toEReal
  have hψt_top : (ψ t : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ht)
  have hψt_bot : (ψ t : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (ψ t : EReal) from (ψ t).2)
  have hψt_cast :
      ((((ψ t : EReal).toReal : ℝ) : EReal)) = (ψ t : EReal) :=
    EReal.coe_toReal hψt_top hψt_bot
  have hψt_val : (ψ t : EReal) = ((((ψ t : EReal).toReal : ℝ) : EReal)) :=
    hψt_cast.symm
  have hη_eq :
      (η t : EReal) = (((ψ t : EReal).toReal - m * t : ℝ) : EReal) := by
    calc
      (η t : EReal) = (ψ t : EReal) + (((-m * t : ℝ)) : EReal) := by
        simp [η, Function.toEReal_apply]
      _ = ((((ψ t : EReal).toReal : ℝ) : EReal)) + (((-m * t : ℝ)) : EReal) := by
            simpa using congrArg (fun z : EReal ↦ z + (((-m * t : ℝ)) : EReal)) hψt_val
      _ = (((ψ t : EReal).toReal - m * t : ℝ) : EReal) := by
            simpa [sub_eq_add_neg] using
              (EReal.coe_add ((ψ t : EReal).toReal) (-m * t)).symm
  constructor
  · intro hu
    rw [mem_subdifferential_iff] at hu ⊢
    intro y
    by_cases hy : y ∈ effectiveDomain ψ
    · have hψy_top : (ψ y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
      have hψy_bot : (ψ y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (ψ y : EReal) from (ψ y).2)
      have hψy_cast :
          ((((ψ y : EReal).toReal : ℝ) : EReal)) = (ψ y : EReal) :=
        EReal.coe_toReal hψy_top hψy_bot
      have hψy_val : (ψ y : EReal) = ((((ψ y : EReal).toReal : ℝ) : EReal)) :=
        hψy_cast.symm
      have hηy_eq :
          (η y : EReal) = (((ψ y : EReal).toReal - m * y : ℝ) : EReal) := by
        calc
          (η y : EReal) = (ψ y : EReal) + (((-m * y : ℝ)) : EReal) := by
            simp [η, Function.toEReal_apply]
          _ = ((((ψ y : EReal).toReal : ℝ) : EReal)) + (((-m * y : ℝ)) : EReal) := by
                simpa using congrArg (fun z : EReal ↦ z + (((-m * y : ℝ)) : EReal)) hψy_val
          _ = (((ψ y : EReal).toReal - m * y : ℝ) : EReal) := by
                simpa [sub_eq_add_neg] using
                  (EReal.coe_add ((ψ y : EReal).toReal) (-m * y)).symm
      have hu_real :
          (ψ t : EReal).toReal - m * t ≤ (ψ y : EReal).toReal - m * y := by
        have hη_le : (η t : EReal) ≤ (η y : EReal) := by
          simpa [η] using hu y
        rw [hη_eq, hηy_eq] at hη_le
        exact EReal.coe_le_coe_iff.mp hη_le
      have htarget_real :
          (y - t) * m + (ψ t : EReal).toReal ≤ (ψ y : EReal).toReal := by
        have haux :
            ((ψ t : EReal).toReal - m * t) + m * y ≤
              ((ψ y : EReal).toReal - m * y) + m * y := by
          exact add_le_add_left hu_real (m * y)
        ring_nf at haux ⊢
        exact haux
      calc
        (⟪y - t, m⟫_ℝ : EReal) + (ψ t : EReal)
            = ((((y - t) * m + (ψ t : EReal).toReal : ℝ)) : EReal) := by
                calc
                  (⟪y - t, m⟫_ℝ : EReal) + (ψ t : EReal)
                      = (((y - t) * m : ℝ) : EReal) +
                          ((((ψ t : EReal).toReal : ℝ) : EReal)) := by
                            rw [real_inner_eq_mul_scalar]
                            simpa using
                              congrArg
                                (fun z : EReal ↦ (((y - t) * m : ℝ) : EReal) + z)
                                hψt_cast.symm
                  _ = ((((y - t) * m + (ψ t : EReal).toReal : ℝ)) : EReal) := by
                        simpa [add_comm] using
                          (EReal.coe_add ((y - t) * m) ((ψ t : EReal).toReal)).symm
        _ ≤ (((ψ y : EReal).toReal : ℝ) : EReal) := by
              exact EReal.coe_le_coe htarget_real
        _ = (ψ y : EReal) := by
              exact hψy_cast
    · -- Outside the effective domain, the target value is `⊤`, so the affine minorant inequality
      -- is automatic.
      have hψy_top : (ψ y : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
      change (⟪y - t, m⟫_ℝ : EReal) + (ψ t : EReal) ≤ (ψ y : EReal)
      rw [hψy_top]
      exact le_top
  · intro hu
    rw [mem_subdifferential_iff] at hu ⊢
    intro y
    by_cases hy : y ∈ effectiveDomain ψ
    · have hψy_top : (ψ y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
      have hψy_bot : (ψ y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (ψ y : EReal) from (ψ y).2)
      have hψy_cast :
          ((((ψ y : EReal).toReal : ℝ) : EReal)) = (ψ y : EReal) :=
        EReal.coe_toReal hψy_top hψy_bot
      have hψy_val : (ψ y : EReal) = ((((ψ y : EReal).toReal : ℝ) : EReal)) :=
        hψy_cast.symm
      have hu_real :
          (y - t) * m + (ψ t : EReal).toReal ≤ (ψ y : EReal).toReal := by
        have hu_realized :
            ((((y - t) * m + (ψ t : EReal).toReal : ℝ)) : EReal) ≤
              (((ψ y : EReal).toReal : ℝ) : EReal) := by
          calc
            ((((y - t) * m + (ψ t : EReal).toReal : ℝ)) : EReal)
                = (⟪y - t, m⟫_ℝ : EReal) + (ψ t : EReal) := by
                    calc
                      ((((y - t) * m + (ψ t : EReal).toReal : ℝ)) : EReal)
                          = (((y - t) * m : ℝ) : EReal) +
                              ((((ψ t : EReal).toReal : ℝ) : EReal)) := by
                                  simpa [add_comm] using
                                    (EReal.coe_add ((y - t) * m) ((ψ t : EReal).toReal)).symm
                      _ = (⟪y - t, m⟫_ℝ : EReal) + (ψ t : EReal) := by
                            rw [real_inner_eq_mul_scalar]
                            simpa using
                              congrArg
                                (fun z : EReal ↦ (((y - t) * m : ℝ) : EReal) + z)
                                hψt_cast
            _ ≤ (ψ y : EReal) := by
                  simpa using hu y
            _ = (((ψ y : EReal).toReal : ℝ) : EReal) := by
                  exact hψy_cast.symm
        exact EReal.coe_le_coe_iff.mp hu_realized
      have htarget_real :
          (ψ t : EReal).toReal - m * t ≤ (ψ y : EReal).toReal - m * y := by
        have haux :
            ((y - t) * m + (ψ t : EReal).toReal) + (-m * y) ≤
              (ψ y : EReal).toReal + (-m * y) := by
          exact add_le_add_left hu_real (-m * y)
        ring_nf at haux ⊢
        exact haux
      have hηy_eq :
          (η y : EReal) = (((ψ y : EReal).toReal - m * y : ℝ) : EReal) := by
        calc
          (η y : EReal) = (ψ y : EReal) + (((-m * y : ℝ)) : EReal) := by
            simp [η, Function.toEReal_apply]
          _ = ((((ψ y : EReal).toReal : ℝ) : EReal)) + (((-m * y : ℝ)) : EReal) := by
                simpa using congrArg (fun z : EReal ↦ z + (((-m * y : ℝ)) : EReal)) hψy_val
          _ = (((ψ y : EReal).toReal - m * y : ℝ) : EReal) := by
                simpa [sub_eq_add_neg] using
                  (EReal.coe_add ((ψ y : EReal).toReal) (-m * y)).symm
      calc
        (⟪y - t, (0 : ℝ)⟫_ℝ : EReal) + (η t : EReal)
            = (((ψ t : EReal).toReal - m * t : ℝ) : EReal) := by
                simpa [η] using hη_eq
        _ ≤ (((ψ y : EReal).toReal - m * y : ℝ) : EReal) := by
              exact EReal.coe_le_coe htarget_real
        _ = (η y : EReal) := by
              exact hηy_eq.symm
    · -- Outside the effective domain of `ψ`, the tilted objective is also `⊤`.
      have hψy_top : (ψ y : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
      have hy_tilt_top : (η y : EReal) = ⊤ := by
        calc
          (η y : EReal) = (ψ y : EReal) + (((-m * y : ℝ)) : EReal) := by
            simp [η, Function.toEReal_apply]
          _ = (⊤ : EReal) + (((-m * y : ℝ)) : EReal) := by
                rw [hψy_top]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-m * y))]
      change (⟪y - t, (0 : ℝ)⟫_ℝ : EReal) + (η t : EReal) ≤ (η y : EReal)
      rw [hy_tilt_top]
      exact le_top

lemma exists_scalar_subgradient_eq_secant_slope_on_unit_interval
    {ψ : ℝ → Set.Ioi (⊥ : EReal)} (hψ_gamma : ψ ∈ Γ₀(ℝ))
    (hψ_dom : Set.Icc (0 : ℝ) 1 ⊆ effectiveDomain ψ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ a ∈ (∂ ψ) t,
      (ψ 1 : EReal) - (ψ 0 : EReal) = ((a : ℝ) : EReal) := by
  let m : ℝ := (ψ 1 : EReal).toReal - (ψ 0 : EReal).toReal
  let η : ℝ → Set.Ioi (⊥ : EReal) := ψ + (fun s : ℝ ↦ -m * s).toEReal
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simp
  have hone_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simp
  have hψ0_dom : 0 ∈ effectiveDomain ψ := hψ_dom hzero_mem
  have hψ1_dom : 1 ∈ effectiveDomain ψ := hψ_dom hone_mem
  have hη_gamma : η ∈ Γ₀(ℝ) := by
    -- The secant tilt stays inside `Γ₀(ℝ)`.
    simpa [η] using secant_tilt_mem_gammaZero hψ_gamma m hψ0_dom
  have hη_dom : Set.Icc (0 : ℝ) 1 ⊆ effectiveDomain η := by
    -- The tilt is finite everywhere, so the interval domain is unchanged.
    intro s hs
    have hs_tilt : s ∈ effectiveDomain ((fun r : ℝ ↦ -m * r).toEReal) := by
      simp
    exact
      (mem_effectiveDomain_pointwiseAdd_iff ψ ((fun r : ℝ ↦ -m * r).toEReal) s).2
        ⟨hψ_dom hs, hs_tilt⟩
  have hψ0_top : (ψ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hψ0_dom)
  have hψ0_bot : (ψ 0 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (ψ 0 : EReal) from (ψ 0).2)
  have hψ1_top : (ψ 1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hψ1_dom)
  have hψ1_bot : (ψ 1 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (ψ 1 : EReal) from (ψ 1).2)
  have hη_end : η 0 = η 1 := by
    -- The secant tilt normalizes the endpoint values.
    apply Subtype.ext
    calc
      (η 0 : EReal) = (((ψ 0 : EReal).toReal : ℝ) : EReal) := by
        calc
          (η 0 : EReal) = (ψ 0 : EReal) + (((-m * (0 : ℝ) : ℝ)) : EReal) := by
              simp [η, Function.toEReal_apply]
          _ = (ψ 0 : EReal) := by simp
          _ = (((ψ 0 : EReal).toReal : ℝ) : EReal) := by
                exact (EReal.coe_toReal hψ0_top hψ0_bot).symm
      _ = (((ψ 1 : EReal).toReal - m : ℝ) : EReal) := by
            have hsecant_real : (ψ 0 : EReal).toReal = (ψ 1 : EReal).toReal - m := by
              dsimp [m]
              ring
            exact congrArg (fun r : ℝ ↦ (r : EReal)) hsecant_real
      _ = (η 1 : EReal) := by
            calc
              ((((ψ 1 : EReal).toReal - m : ℝ)) : EReal)
                  = (((ψ 1 : EReal).toReal : ℝ) : EReal) +
                      (((-m : ℝ)) : EReal) := by
                        simpa [sub_eq_add_neg] using
                          (EReal.coe_add ((ψ 1 : EReal).toReal) (-m)).symm
              _ = (ψ 1 : EReal) + (((-m : ℝ)) : EReal) := by
                    rw [EReal.coe_toReal hψ1_top hψ1_bot]
              _ = (ψ 1 : EReal) + (((-m * (1 : ℝ) : ℝ)) : EReal) := by simp
              _ = (η 1 : EReal) := by
                    simp [η, Function.toEReal_apply]
  obtain ⟨t, ht_Ioo, ht_minOn⟩ :=
    -- The tilted objective attains a minimum at an interior point of `[0,1]`.
    exists_interior_isMinOn_Icc_of_mem_gammaZero_of_eq_endpoints hη_gamma hη_dom hη_end
  have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_Ioo.1.le, ht_Ioo.2.le⟩
  have ht_dom : t ∈ effectiveDomain η := hη_dom ht_Icc
  have ht_dom_ψ : t ∈ effectiveDomain ψ := hψ_dom ht_Icc
  have ht_argminOn : t ∈ Argmin[Set.Icc (0 : ℝ) 1] η.asEReal := by
    -- Package the interior interval minimizer as a constrained argmin witness.
    exact (mem_argminOn_iff).2 ⟨ht_Icc, ht_minOn⟩
  have ht_interior : t ∈ interior (Set.Icc (0 : ℝ) 1) := by
    -- On `ℝ`, the interior of the closed unit interval is the open interval.
    simpa [interior_Icc] using ht_Ioo
  have ht_argmin : t ∈ Argmin η.asEReal := by
    -- Proposition 11.5 globalizes the constrained interior minimizer.
    exact
      mem_argmin_of_mem_argminOn_of_mem_interior_of_convexOn_effectiveDomain
        η hη_gamma.2 ht_dom ht_argminOn ht_interior
  have hzero_sub : (0 : ℝ) ∈ (∂ η) t := by
    -- Fermat's rule turns the global minimizer of `η` into a zero of `∂ η`.
    rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff] at ht_argmin
    exact ht_argmin
  have hm_sub : m ∈ (∂ ψ) t := by
    -- Undo the affine tilt inside the scalar subdifferential.
    exact
      (zero_mem_subdifferential_secant_tilt_iff (ψ := ψ) (t := t) (m := m) ht_dom_ψ).1 <| by
        simpa [η] using hzero_sub
  have hm_cast :
      ((m : ℝ) : EReal) = (ψ 1 : EReal) - (ψ 0 : EReal) :=
    secant_slope_cast_eq_endpoint_difference hψ0_dom hψ1_dom m rfl
  exact ⟨t, ht_Ioo, m, hm_sub, hm_cast.symm⟩

/-- Helper for Theorem 16 56: a scalar subgradient along the translated chord lifts to an ambient
subgradient whose adjoint image is the same slope. -/
lemma lift_scalar_trace_subgradient_to_ambient_segment_subgradient
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x0 x1 : H}
    (hregular :
      (0 : H) ∈ sri (effectiveDomain f - (line[ℝ, x0, x1] : Set H)) ∨
        ((line[ℝ, x0, x1] : Set H) ∩ interior (effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧
          ((line[ℝ, x0, x1] : Set H) ∩ ri (effectiveDomain f)).Nonempty))
    {t a : ℝ}
    (ha : a ∈ (∂ (fun s : ℝ ↦ f (AffineMap.lineMap x0 x1 s))) t) :
    ∃ u ∈ (∂ f) (AffineMap.lineMap x0 x1 t),
      ((a : ℝ) : EReal) = (⟪x1 - x0, u⟫_ℝ : EReal) := by
  let g : H → Set.Ioi (⊥ : EReal) := fun z ↦ f (x0 + z)
  let L : ℝ →L[ℝ] H := ContinuousLinearMap.toSpanSingleton ℝ (x1 - x0)
  have hg : g ∈ Γ₀(H) := by
    -- The translated ambient model stays in `Γ₀(H)`.
    simpa [g] using precompose_add_const_mem_gammaZero hf x0
  have hsri :
      (0 : H) ∈ sri (effectiveDomain g - Set.range L) := by
    -- Route correction: use the theorem-local `sri` bridge before invoking the adjoint-image lift.
    simpa [g, L] using
      zero_mem_sri_translated_domain_sub_range_of_segment_regularity
        (f := f) (hf := hf) (x0 := x0) (x1 := x1) hregular
  have htrace_eq : (fun s : ℝ ↦ f (AffineMap.lineMap x0 x1 s)) = g ∘ L := by
    -- Normalize the chord trace to the translated linear model `g ∘ L`.
    funext s
    simp [g, L, Function.comp, lineMap_eq_add_toSpanSingleton]
  have ha_comp : a ∈ (∂ (g ∘ L)) t := by
    -- Re-express the scalar subgradient on the affine trace as one on the linearized composite.
    simpa [htrace_eq] using ha
  have ha_image :
      a ∈ ContinuousLinearMap.adjointImageSubdifferential L g t := by
    -- The `sri` chain-rule inclusion produces an adjoint-image witness in the ambient space.
    exact
      mem_adjointImage_of_mem_subdifferential_comp_under_zero_mem_sri_range
        (g := g) (hg := hg) (L := L) hsri ha_comp
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image] at ha_image
  rcases ha_image with ⟨uAmbient, huAmbient, hAdjoint⟩
  have hu :
      uAmbient ∈ (∂ f) (AffineMap.lineMap x0 x1 t) := by
    -- Translate the ambient subgradient on `g` back to the original function `f`.
    have hu_shift :
        uAmbient ∈ (∂ f) (x0 + L t) :=
      (mem_subdifferential_precompose_add_const_iff
        (f := f) x0 (L t) uAmbient).1 huAmbient
    simpa [L, lineMap_eq_add_toSpanSingleton] using hu_shift
  have hinner_real : a = ⟪x1 - x0, uAmbient⟫_ℝ := by
    -- Evaluate the adjoint identity at `1` to turn the scalar adjoint equation
    -- into an inner product.
    simpa [hAdjoint, L, real_inner_eq_mul_scalar] using
      (ContinuousLinearMap.adjoint_inner_right L (1 : ℝ) uAmbient)
  have hau : ((a : ℝ) : EReal) = (⟪x1 - x0, uAmbient⟫_ℝ : EReal) := by
    exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner_real
  exact ⟨uAmbient, hu, hau⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 16 56: translating by `x0` shifts the effective domain by `-{x0}`. -/
lemma effectiveDomain_precompose_add_const_eq
    {f : H → Set.Ioi (⊥ : EReal)} (x0 : H) :
    effectiveDomain (fun z : H ↦ f (x0 + z)) = effectiveDomain f - ({x0} : Set H) := by
  ext z
  constructor
  · intro hz
    -- Turn domain membership of the translated function into a set-difference witness.
    refine Set.mem_sub.mpr ?_
    refine ⟨x0 + z, ?_, x0, by simp, ?_⟩
    · simpa [mem_effectiveDomain_iff] using hz
    · simp [sub_eq_add_neg, add_assoc]
  · intro hz
    rcases Set.mem_sub.mp hz with ⟨y, hy, x, hx, hzx⟩
    -- The singleton witness identifies the translated point with an original domain point.
    simp only [Set.mem_singleton_iff] at hx
    subst x
    have hyz : x0 + z = y := by
      have hyz' : y = x0 + z := by
        simpa [sub_eq_add_neg, add_assoc] using congrArg (fun v : H ↦ x0 + v) hzx
      exact hyz'.symm
    rw [mem_effectiveDomain_iff]
    simpa [hyz] using hy

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: restricting a `Γ₀(H)` function to a chord that starts in the
effective domain yields a scalar `Γ₀(ℝ)` trace. -/
lemma lineMap_trace_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x0 x1 : H}
    (hx0 : x0 ∈ effectiveDomain f) :
    (fun t : ℝ ↦ f (AffineMap.lineMap x0 x1 t)) ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · -- Lower semicontinuity is stable under the continuous affine trace map.
    simpa [Function.comp] using hf.1.comp (AffineMap.lineMap_continuous (p := x0) (q := x1))
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The left endpoint gives an explicit point in the scalar effective domain.
      refine ⟨0, ?_⟩
      rw [mem_effectiveDomain_iff]
      simpa using hx0
    · intro s hs t ht a ha0 ha1
      have hs' : AffineMap.lineMap x0 x1 s ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using hs
      have ht' : AffineMap.lineMap x0 x1 t ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using ht
      have hparam : AffineMap.lineMap t s a = a * s + (1 - a) * t := by
        simp [AffineMap.lineMap_apply_module, smul_eq_mul, add_comm]
      have hline :
          AffineMap.lineMap x0 x1 (a * s + (1 - a) * t) =
            a • AffineMap.lineMap x0 x1 s + (1 - a) • AffineMap.lineMap x0 x1 t := by
        calc
          AffineMap.lineMap x0 x1 (a * s + (1 - a) * t)
              = AffineMap.lineMap x0 x1 (AffineMap.lineMap t s a) := by
                  rw [hparam]
          _ = AffineMap.lineMap (AffineMap.lineMap x0 x1 t) (AffineMap.lineMap x0 x1 s) a := by
                simpa using (AffineMap.lineMap x0 x1).apply_lineMap t s a
          _ = a • AffineMap.lineMap x0 x1 s + (1 - a) • AffineMap.lineMap x0 x1 t := by
                rw [AffineMap.lineMap_apply_module]
                abel
      -- The trace map is affine, so convexity of `f` transports directly to the scalar trace.
      simpa [hline, smul_eq_mul] using hf.2.ineq hs' ht' ha0 ha1

omit [CompleteSpace H] in
/-- Helper for Theorem 16 56: if both endpoints lie in the effective domain, then the whole scalar
parameter interval `[0,1]` stays in the effective domain of the line trace. -/
lemma unitInterval_subset_effectiveDomain_lineMap_trace
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x0 x1 : H}
    (hx0 : x0 ∈ effectiveDomain f) (hx1 : x1 ∈ effectiveDomain f) :
    Set.Icc (0 : ℝ) 1 ⊆ effectiveDomain (fun t : ℝ ↦ f (AffineMap.lineMap x0 x1 t)) := by
  intro t ht
  -- Convexity of the effective domain keeps the entire chord inside `effectiveDomain f`.
  have ht' : AffineMap.lineMap x0 x1 t ∈ effectiveDomain f := by
    exact hf.2.convex_effectiveDomain.lineMap_mem hx0 hx1 ht
  simpa [mem_effectiveDomain_iff] using ht'

/- Source/core/bridge triage:
- `source-facing`: Theorem 16.56 is the textbook segment mean-value statement for subgradients.
- `core/canonical`: the owner objects are `∂ f`, `effectiveDomain f`, `openSegment ℝ x0 x1`,
  and the affine line through the endpoints, represented canonically by `line[ℝ, x0, x1]`.
- `bridge/view`: the regularity hypothesis is stated directly on that canonical line owner rather
  than through a repeated raw `affineSpan ℝ ({x0, x1} : Set H)` expression.
-/
-- Proof sketch: restrict `f` to the affine line through `x0` and `x1` via
-- `t ↦ f (AffineMap.lineMap x0 x1 t)`. The three regularity branches ensure that this one-variable
-- restriction belongs to `Γ₀(ℝ)` and has the required continuity on `[0,1]`. Apply the
-- one-dimensional minimizer argument to the auxiliary function used in the textbook proof, obtain
-- `t ∈ (0,1)` with `0 ∈ ∂h(t)`, and then rewrite `∂h(t)` through the subdifferential chain rule
-- to produce a point `x ∈ ]x0,x1[` and a subgradient `u ∈ (∂ f) x` realizing the endpoint value
-- difference.
/-- Theorem 16 56: if `f ∈ Γ₀(H)`, if `x₀` and `x₁` belong to `effectiveDomain f`, and if one of
the following holds, with the affine line `aff{x₀,x₁}` represented by the canonical owner
`line[ℝ, x₀, x₁]`: (i) `0 ∈ sri (effectiveDomain f - aff{x₀,x₁})`; (ii) `aff{x₀,x₁}` meets
`interior (effectiveDomain f)`; or (iii) `H` is finite-dimensional and `aff{x₀,x₁}` meets
`ri (effectiveDomain f)`, then the endpoint value difference `f x₁ - f x₀` is the inner product
of `x₁ - x₀` with some subgradient of `f` at a point of `]x₀,x₁[`. -/
theorem exists_subgradient_on_openSegment_eq_endpoint_value_difference_of_segment_regularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x0 x1 : H}
    (hx0 : x0 ∈ effectiveDomain f) (hx1 : x1 ∈ effectiveDomain f)
    (hregular :
      (0 : H) ∈ sri (effectiveDomain f - (line[ℝ, x0, x1] : Set H)) ∨
        ((line[ℝ, x0, x1] : Set H) ∩ interior (effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧
          ((line[ℝ, x0, x1] : Set H) ∩ ri (effectiveDomain f)).Nonempty)) :
    ∃ x ∈ openSegment ℝ x0 x1, ∃ u ∈ (∂ f) x,
      (f x1 : EReal) - (f x0 : EReal) = (⟪x1 - x0, u⟫_ℝ : EReal) := by
  let ψ : ℝ → Set.Ioi (⊥ : EReal) := fun t ↦ f (AffineMap.lineMap x0 x1 t)
  have hψ_gamma : ψ ∈ Γ₀(ℝ) := by
    -- Then package the scalar trace along the chord from `x0` to `x1`.
    simpa [ψ] using lineMap_trace_mem_gammaZero hf hx0
  have hψ_dom :
      Set.Icc (0 : ℝ) 1 ⊆ effectiveDomain ψ := by
    -- The endpoint domain hypotheses keep the whole unit parameter segment in the trace domain.
    simpa [ψ] using unitInterval_subset_effectiveDomain_lineMap_trace hf hx0 hx1
  have hψ0 : ψ 0 = f x0 := by
    -- Record the left endpoint value of the scalar trace.
    simp [ψ]
  have hψ1 : ψ 1 = f x1 := by
    -- Record the right endpoint value of the scalar trace.
    simp [ψ]
  obtain ⟨t, ht, a, ha, hsecant⟩ :=
    -- First solve the one-dimensional secant-slope problem on the scalar trace.
    exists_scalar_subgradient_eq_secant_slope_on_unit_interval hψ_gamma hψ_dom
  obtain ⟨u, hu, hau⟩ :=
    -- Then lift that scalar subgradient back to the ambient space along the affine chord.
    lift_scalar_trace_subgradient_to_ambient_segment_subgradient
      (hf := hf) (x0 := x0) (x1 := x1) hregular ha
  refine ⟨AffineMap.lineMap x0 x1 t, ?_, u, hu, ?_⟩
  · -- Parameters in `Ioo (0,1)` give points of the open segment.
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  · -- Replace the scalar secant slope by the ambient inner product witness.
    calc
      (f x1 : EReal) - (f x0 : EReal) = (ψ 1 : EReal) - (ψ 0 : EReal) := by
        simp [hψ0, hψ1]
      _ = ((a : ℝ) : EReal) := hsecant
      _ = (⟪x1 - x0, u⟫_ℝ : EReal) := hau

end SubdifferentialCalculus

end ERealFunction
