import Mathlib
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Fact_15_25
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

open ContinuousLinearMap

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

local notation "existsArgminCompositeDualObjectiveOfSri" =>
exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain

local notation "existsArgminCompositeDualObjectiveOfPolyhedral" =>
exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regularity

omit [CompleteSpace H] in
/-- Helper for Corollary 16 53: the linear functional `x ↦ -⟪x, u⟫` packaged through
`Function.toEReal` belongs to `Γ₀(H)`. -/
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
      simp only [Function.toEReal_apply, EReal.coe_neg, mul_neg, ge_iff_le]
      have hcast :
          (((-⟪a • x + (1 - a) • y, u⟫_ℝ : ℝ) : EReal)) =
            (((a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
      simpa [EReal.coe_add, EReal.coe_mul] using le_of_eq hcast

omit [CompleteSpace H] in
/-- Helper for Corollary 16 53: the effective domain of `x ↦ -⟪x, u⟫` is all of `H`. -/
lemma effectiveDomain_negative_inner_toEReal (u : H) :
    effectiveDomain ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) = Set.univ := by
  ext x
  simp

omit [CompleteSpace H] in
/-- Helper for Corollary 16 53: at the matching point `w = -u`, the conjugate of
`x ↦ -⟪x, u⟫` vanishes. -/
lemma conjugate_negative_inner_toEReal_apply_eq_zero
    (u w : H) (hw : w = -u) :
    (((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal).asEReal)∗ w = 0 := by
  let f : H → Set.Ioi (⊥ : EReal) := (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal
  rw [conjugate_apply]
  subst hw
  simp [Function.toEReal_apply]

omit [CompleteSpace H] in
/-- Helper for Corollary 16 53: off the matching point `w = -u`, the conjugate of
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

/-- Helper for Corollary 16 53: for the linear tilt `x ↦ -⟪x, u⟫`, the Chapter 15 dual owner is
the conjugate of `g` restricted to the fiber `L.adjoint v = u`. -/
lemma compositeDualObjective_negative_inner_toEReal_apply
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (u : H) (v : K) (hLv : L.adjoint v = u) :
    compositeDualObjective ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) g L v = g.asEReal∗ v := by
  rw [compositeDualObjective_apply]
  have hneg : -(L.adjoint v) = -u := by simpa using congrArg Neg.neg hLv
  rw [conjugate_negative_inner_toEReal_apply_eq_zero (u := u) (w := -(L.adjoint v)) hneg]
  simp

/-- Helper for Corollary 16 53: away from the fiber `L.adjoint v = u`, the linear-tilted
composite dual objective is `⊤`. -/
lemma compositeDualObjective_negative_inner_toEReal_apply_eq_top
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

/-- Helper for Corollary 16 53: a minimizer of the linear-tilted composite dual objective
attains the adjoint-fiber infimum defining `L.adjoint ▷ g∗` at `u`. -/
lemma infimalPostcomposition_adjoint_conjugate_exact_of_regular
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - Set.range L) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ Set.range L).Nonempty)) :
    infimalPostcomposition.Exact L.adjoint (g∗[hg]) := by
  intro u hu_dom
  let f : H → Set.Ioi (⊥ : EReal) := (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal
  have hf : f ∈ Γ₀(H) := negative_inner_toEReal_mem_gammaZero (u := u)
  obtain ⟨v, hvArg, _⟩ :=
    match hregular with
    | Or.inl hsri =>
        existsArgminCompositeDualObjectiveOfSri f hf g hg L (by
          simpa [f, effectiveDomain_negative_inner_toEReal] using hsri)
    | Or.inr hpoly =>
        letI : FiniteDimensional ℝ K := hpoly.1
        existsArgminCompositeDualObjectiveOfPolyhedral f hf g hg L hpoly.2.1 <| by
          left
          rcases hpoly.2.2 with ⟨y, hyg, hyL⟩
          have hyri : y ∈ ri (L.range : Set K) := by
            simpa [relativeInterior_submodule_eq_self] using hyL
          refine ⟨y, hyg, ?_⟩
          simpa [f, effectiveDomain_negative_inner_toEReal] using hyri
  rw [mem_argmin_iff, isMinOn_univ_iff] at hvArg
  have hu_lt :
      (L.adjoint ▷ g∗[hg]) u < ⊤ := by
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

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 16 53: `0 ∈ sri (effectiveDomain g - range L)` forces the range of `L`
to meet the effective domain of `g`. -/
lemma range_inter_effectiveDomain_nonempty_of_zero_mem_sri_sub
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L)) :
    (Set.range L ∩ effectiveDomain g).Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨x, hx, y, hy, hxy⟩
  rcases hy with ⟨z, rfl⟩
  refine ⟨x, ?_, hx⟩
  simp [sub_eq_zero.mp hxy]

/-- Helper for Corollary 16 53: the subdifferential of a constant `]-∞,+∞]`-valued function is
the singleton `{0}` at every base point. -/
lemma subdifferential_const_eq_singleton_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : Set.Ioi (⊥ : EReal)) (hc : (c : EReal) < ⊤) (x : E) :
    (∂ fun _ : E ↦ c) x = ({0} : Set E) := by
  ext u
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
    have htest : (⟪(x + u) - x, u⟫_ℝ : EReal) + (c : EReal) ≤ (c : EReal) := by
      simpa using hu (x + u)
    have hc_top : (c : EReal) ≠ ⊤ := ne_of_lt hc
    have hc_bot : (c : EReal) ≠ ⊥ := ne_of_gt c.2
    have htest' :
        (((‖u‖ ^ 2 + (c : EReal).toReal : ℝ) : EReal)) ≤ (c : EReal) := by
      rw [EReal.coe_add, EReal.coe_toReal hc_top hc_bot]
      simpa [real_inner_self_eq_norm_sq] using htest
    have hsq : (‖u‖ ^ 2 : ℝ) ≤ 0 := by
      have hrealE :
          (((‖u‖ ^ 2 + (c : EReal).toReal : ℝ) : EReal)) ≤
            (((c : EReal).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_toReal hc_top hc_bot] using htest'
      have hreal : ‖u‖ ^ 2 + (c : EReal).toReal ≤ (c : EReal).toReal := by
        exact_mod_cast hrealE
      linarith
    have hnorm : ‖u‖ = 0 := by
      nlinarith [sq_nonneg ‖u‖, hsq]
    exact Set.mem_singleton_iff.mpr (norm_eq_zero.mp hnorm)
  · intro hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    intro z
    simp

omit [CompleteSpace H] in
/-- Helper for Corollary 16 53: the subdifferential of the everywhere-zero finite function is the
singleton `{0}` at every point. -/
lemma subdifferential_zero_toEReal_apply (x : H) :
    (∂ ((fun _ : H ↦ (0 : ℝ)).toEReal)) x = ({0} : Set H) := by
  have hzero_lt_top :
      ((((fun _ : H ↦ (0 : ℝ)).toEReal x : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) := by
    simp [Function.toEReal_apply]
  simpa [Function.toEReal_apply] using
    subdifferential_const_eq_singleton_zero
      (c := (fun _ : H ↦ (0 : ℝ)).toEReal x)
      (hc := hzero_lt_top)
      x

/-- Helper for Corollary 16 53: the zero-function subdifferential term disappears from the
pointwise Minkowski sum with `adjointImageSubdifferential`. -/
lemma subdifferential_zero_toEReal_add_adjointImage_eq
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    (∂ ((fun _ : H ↦ (0 : ℝ)).toEReal)) + adjointImageSubdifferential L g =
      adjointImageSubdifferential L g := by
  ext x u
  change u ∈ (∂ ((fun _ : H ↦ (0 : ℝ)).toEReal)) x + adjointImageSubdifferential L g x ↔
    u ∈ adjointImageSubdifferential L g x
  rw [subdifferential_zero_toEReal_apply (x := x)]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases Set.mem_singleton_iff.mp ha with rfl
    have hbu : b = u := by
      simpa using hab
    rw [← hbu]
    exact hb
  · intro hu
    have hzero : (0 : H) ∈ ({0} : Set H) := by
      simp
    have hsum : (0 : H) + u = u := by
      simp
    exact ⟨0, hzero, u, hu, hsum⟩

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 16 53: adding the everywhere-zero finite function does not change the
composite `g ∘ L`. -/
lemma zero_toEReal_add_comp_eq
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    ((fun _ : H ↦ (0 : ℝ)).toEReal) + g ∘ L = g ∘ L := by
  funext x
  apply Subtype.ext
  simp [Function.toEReal_apply]

/-- Helper for Corollary 16 53: any subgradient of `g ∘ L` lifts through `L.adjoint` under the
regularity hypotheses of Corollary 16 53. -/
lemma exists_subgradient_of_mem_subdifferential_comp_of_regular
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - Set.range L) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ Set.range L).Nonempty))
    {x u : H} (hu : u ∈ (∂ (g ∘ L)) x) :
    ∃ v ∈ (∂ g) (L x), L.adjoint v = u := by
  have hu_eq :
      (g (L x) : EReal) + (g ∘ L).asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    exact
      (mem_subdifferential_iff_fenchel_young_eq (f := g ∘ L) x u).1 hu
  have hdom : (Set.range L ∩ effectiveDomain g).Nonempty := by
    rcases hregular with hsri | hpoly
    · exact range_inter_effectiveDomain_nonempty_of_zero_mem_sri_sub (g := g) (L := L) hsri
    · simpa [Set.inter_comm] using hpoly.2.2
  have hcomp_eq : (g ∘ L).asEReal∗ u = (L.adjoint ▷ g.asEReal∗) u := by
    simpa [Function.asEReal_apply] using
      congrFun (conjugate_comp_eq_adjointInfimalPostcomposition (g := g) (L := L) hdom) u
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
  obtain ⟨_, ⟨v, hLv, huvalue⟩⟩ :=
    -- Route correction: reuse the Chapter 15 exactness owner theorem rather than duplicating it
    -- locally in this file.
    (infimalPostcomposition.exactAt_iff_exists_eq L.adjoint (g∗[hg]) u).1
      (infimalPostcomposition_adjoint_conjugate_exact_of_regular
        (g := g) (hg := hg) (L := L) hregular hu_dom)
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
  have hv : v ∈ (∂ g) (L x) := by
    exact
      (mem_subdifferential_iff_fenchel_young_eq (f := g) (L x) v).2 hgy
  exact ⟨v, hv, hLv⟩

/-- Helper for Corollary 16 53: every element of `adjointImageSubdifferential L g x` is already a
subgradient of `g ∘ L` at `x` by the zero-function specialization of the additive chain rule. -/
lemma mem_subdifferential_comp_of_mem_adjointImage
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    {x u : H} (hu : u ∈ adjointImageSubdifferential L g x) :
    u ∈ (∂ (g ∘ L)) x := by
  have hu_add :
      u ∈ (∂ ((fun _ : H ↦ (0 : ℝ)).toEReal)) x +
          adjointImageSubdifferential L g x := by
    rw [ContinuousLinearMap.adjointImageSubdifferential_apply] at hu
    rcases hu with ⟨v, hv, rfl⟩
    refine ⟨0, ?_, L.adjoint v, ?_, by simp⟩
    · simp [subdifferential_zero_toEReal_apply]
    · rw [ContinuousLinearMap.adjointImageSubdifferential_apply]
      exact ⟨v, hv, rfl⟩
  have hu_comp :
      u ∈ (∂ (((fun _ : H ↦ (0 : ℝ)).toEReal) + g ∘ L)) x :=
    -- Apply the additive chain-rule inclusion before collapsing the zero summand.
    subdifferential_add_adjoint_image_subset_subdifferential_add_comp
      ((fun _ : H ↦ (0 : ℝ)).toEReal) g L x hu_add
  have hadd :
      ((fun _ : H ↦ (0 : ℝ)).toEReal) + g ∘ L = g ∘ L :=
    zero_toEReal_add_comp_eq (g := g) (L := L)
  simpa [hadd] using hu_comp

/-- Corollary 16 53: if `g ∈ Γ₀(K)` and either (i)
`0 ∈ sri (effectiveDomain g - Set.range L)` or (ii) `K` is finite-dimensional, `g` has
polyhedral epigraph, and `effectiveDomain g` meets `Set.range L`, then
`∂ (g ∘ L) = L^* ∘ (∂ g) ∘ L`, realized as `adjointImageSubdifferential L g`. -/
theorem subdifferential_comp_eq_adjoint_image_of_regular
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - Set.range L) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ Set.range L).Nonempty)) :
    ∂ (g ∘ L) = adjointImageSubdifferential L g := by
  ext x u
  constructor
  · intro hu
    obtain ⟨v, hv, hLv⟩ :=
      exists_subgradient_of_mem_subdifferential_comp_of_regular
        (g := g) (hg := hg) (L := L) hregular hu
    rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
    exact ⟨v, hv, hLv⟩
  · intro hu
    -- Use the zero-function specialization of the additive chain rule for the reverse inclusion.
    exact mem_subdifferential_comp_of_mem_adjointImage (g := g) (L := L) hu

end SubdifferentialCalculus

end ERealFunction
