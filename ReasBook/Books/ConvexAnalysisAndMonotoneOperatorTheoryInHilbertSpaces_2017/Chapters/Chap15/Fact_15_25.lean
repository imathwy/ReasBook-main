import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap15.Corollary_15_8
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Definition_15_24_1
import BauschkeLean.Chap15.Proposition_15_24
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap27.Proposition_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Keep the helper independent of the ambient completeness assumptions, since it only unpacks set
membership in the source regularity split.
-/
omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Fact 15 25: the source-facing polyhedral regularity alternatives already imply the
basic domain-intersection hypothesis `effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`. -/
private theorem effectiveDomain_inter_image_nonempty_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty := by
  -- In branch `(i)`, relative-interior membership already gives membership in the image set.
  rcases hregular with hri | hpoly
  · rcases hri with ⟨y, hyg, hyri⟩
    exact ⟨y, hyg, (Set.mem_relativeInterior_iff.mp hyri).1⟩
  · -- Branch `(ii)` contains the required nonemptiness explicitly.
    exact hpoly.2.2

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Fact 15 25: the source-facing polyhedral regularity alternatives also give the
range/effective-domain intersection needed for the Chapter 13 composition-conjugation bridge. -/
private theorem range_inter_effectiveDomain_nonempty_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (Set.range L ∩ effectiveDomain g).Nonempty := by
  -- Convert the image witness from the previous helper into a range witness for `L`.
  rcases effectiveDomain_inter_image_nonempty_of_polyhedral_regularity f g L hregular with
    ⟨y, hyg, hyimage⟩
  rcases hyimage with ⟨x, _, rfl⟩
  exact ⟨L x, ⟨x, rfl⟩, hyg⟩

omit [CompleteSpace K] in
/-- Helper for Fact 15 25: the same range/effective-domain witness puts `g ∘ L` in `Γ₀(H)`. -/
private theorem comp_mem_gammaZero_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    g ∘ L ∈ Γ₀(H) := by
  -- First recover a point of `range L ∩ effectiveDomain g`, then apply the Chapter 15 owner.
  have hrange : (Set.range L ∩ effectiveDomain g).Nonempty :=
    range_inter_effectiveDomain_nonempty_of_polyhedral_regularity
      (f := f) (g := g) (L := L) hregular
  exact
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
      g hg L hrange

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Fact 15 25: the source-facing polyhedral regularity alternatives also give a point
of `effectiveDomain (g ∘ L)`. -/
private theorem effectiveDomain_comp_nonempty_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (effectiveDomain (g ∘ L)).Nonempty := by
  -- Turn the range witness into an actual primal point `x` with `g (L x) < ⊤`.
  rcases range_inter_effectiveDomain_nonempty_of_polyhedral_regularity
      (f := f) (g := g) (L := L) hregular with ⟨y, hyL, hyg⟩
  rcases hyL with ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  simpa [Function.comp, mem_effectiveDomain_iff] using hyg

/-- Helper for Fact 15 25: the ordinary dual objective for the pair `(f, g ∘ L)` is exactly the
same-space owner `fenchelDualObjective f (g ∘ L)`. -/
private theorem pointwiseDualObjective_eq_fenchelDualObjective_comp
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    (fun z : H ↦ f.asEReal∗ (-z) + ((g.asEReal ∘ L)∗ z)) =
      fenchelDualObjective f (g ∘ L) := by
  -- Freeze the ordinary dual minimand in the canonical same-space notation.
  funext z
  rw [fenchelDualObjective_apply]
  have hcomp : g.asEReal ∘ L = (g ∘ L).asEReal := by
    funext x
    rfl
  rw [hcomp]

omit [CompleteSpace H] in
/-- Helper for Fact 15 25: the linear tilt `x ↦ -⟪x, u⟫` already belongs to `Γ₀(H)`. This is the
source-facing special case used later to turn dual minimizers into exact adjoint-fiber witnesses.
-/
private theorem negative_inner_toEReal_mem_gammaZero
    (u : H) :
    (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity comes from continuity of the linear functional `x ↦ -⟪x, u⟫`.
    have hcont :
        Continuous (fun x : H ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) := by
      simpa using continuous_coe_real_ereal.comp ((continuous_id.inner continuous_const).neg)
    exact hcont.lowerSemicontinuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The tilt is finite everywhere, so in particular at the origin.
      refine ⟨0, ?_⟩
      simp
    · -- Jensen convexity is exactly linearity of the inner product in the first argument.
      intro x _hx y _hy a ha0 ha1
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
/-- Helper for Fact 15 25: the linear tilt `x ↦ -⟪x, u⟫` has full effective domain. -/
private theorem effectiveDomain_negative_inner_toEReal
    (u : H) :
    effectiveDomain ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) = Set.univ := by
  ext x
  simp

omit [CompleteSpace H] in
/-- Helper for Fact 15 25: at the matching point `w = -u`, the conjugate of the linear tilt
vanishes. -/
private theorem conjugate_negative_inner_toEReal_apply_eq_zero
    (u w : H) (hw : w = -u) :
    (((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal).asEReal)∗ w = 0 := by
  rw [conjugate_apply]
  subst hw
  simp [Function.toEReal_apply]

omit [CompleteSpace H] in
/-- Helper for Fact 15 25: away from the matching point `w = -u`, the conjugate of the linear
tilt is `⊤`. -/
private theorem conjugate_negative_inner_toEReal_apply_eq_top
    (u w : H) (hw : w ≠ -u) :
    (((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal).asEReal)∗ w = ⊤ := by
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
      (((⟪x, w⟫_ℝ : ℝ) : EReal) -
          ((((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) x : Set.Ioi (⊥ : EReal)) : EReal)) =
        ((a + 1 : ℝ) : EReal) := by
    simpa [Function.toEReal_apply, sub_eq_add_neg] using
      congrArg (fun r : ℝ ↦ (r : EReal)) hreal
  have ha_lt_defect :
      ((a : ℝ) : EReal) <
        (((⟪x, w⟫_ℝ : ℝ) : EReal) -
          ((((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) x : Set.Ioi (⊥ : EReal)) : EReal)) := by
    rw [hx_defect]
    exact_mod_cast lt_add_of_pos_right a zero_lt_one
  rw [lt_iSup_iff]
  exact ⟨x, by simpa using ha_lt_defect⟩

/-- Helper for Fact 15 25: on the exact adjoint fiber `L.adjoint v = u`, the composite dual
objective for the linear tilt collapses to `g^*(v)`. -/
private theorem compositeDualObjective_negative_inner_toEReal_apply
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (u : H) (v : K) (hLv : L.adjoint v = u) :
    compositeDualObjective ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) g L v = g.asEReal∗ v := by
  -- Route correction: this keeps the linear-tilt specialization concrete, instead of unfolding
  -- the entire dual objective again inside the later exactness proof.
  rw [compositeDualObjective_apply]
  have hneg : -(L.adjoint v) = -u := by
    simpa using congrArg Neg.neg hLv
  rw [conjugate_negative_inner_toEReal_apply_eq_zero (u := u) (w := -(L.adjoint v)) hneg]
  simp

/-- Helper for Fact 15 25: away from the exact adjoint fiber `L.adjoint v = u`, the same linear
tilt forces the composite dual objective to be `⊤`. -/
private theorem compositeDualObjective_negative_inner_toEReal_apply_eq_top
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
  -- The linear tilt conjugate is `⊤` off the matching point, so the whole dual value is `⊤`.
  rw [conjugate_negative_inner_toEReal_apply_eq_top (u := u) (w := -(L.adjoint v)) hneg]
  rw [EReal.top_add_of_ne_bot hg_ne_bot]

/-
Source/core/bridge triage:
- `source-facing`: Fact 15.25 is the attainment statement under the textbook polyhedral
  regularity alternatives:
  `K` finite-dimensional, `g` polyhedral, and either
  `effectiveDomain g ∩ ri (L '' effectiveDomain f) ≠ ∅` or
  `H` finite-dimensional, `f` polyhedral, and
  `effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`.
- `core/canonical`: the owner objects are the Chapter 15 declarations
  `compositePrimalOptimalValue`, `compositeDualObjective`, and `compositeDualOptimalValue` from
  Definition 15.19.
- `bridge/view`: Proposition 15.24 and Theorem 15.23 provide one proof route to this fact, but
  Fact 15.25 itself remains the source-facing polyhedral alternative rather than an `sri` bridge.
-/

/-- Helper for Fact 15 25: packaging a proper `EReal`-valued function with `properIoi` does not
change its effective domain. -/
private theorem effectiveDomain_properIoi_eq_dom
    {X : Type*} {F : X → EReal} (hproper : IsProper F) :
    effectiveDomain (properIoi F hproper) = dom F := by
  ext x
  rw [mem_effectiveDomain_iff, mem_dom_iff, properIoi_apply]

/-- Helper for Fact 15 25: adding a finite real constant commutes with an indexed infimum in
`EReal`. -/
private theorem iInf_add_real_const_local
    {ι : Sort*} (Φ : ι → EReal) (c : ℝ) :
    (⨅ i, Φ i + ((c : ℝ) : EReal)) = (⨅ i, Φ i) + ((c : ℝ) : EReal) := by
  -- Push the constant through the infimum by proving both lattice inequalities explicitly.
  have hright :
      (⨅ i, Φ i) + ((c : ℝ) : EReal) ≤ (⨅ i, Φ i + ((c : ℝ) : EReal)) := by
    refine le_iInf fun i ↦ ?_
    exact add_le_add (iInf_le Φ i) le_rfl
  have hleft_sub :
      (⨅ i, Φ i + ((c : ℝ) : EReal)) - ((c : ℝ) : EReal) ≤ (⨅ i, Φ i) := by
    refine le_iInf fun i ↦ ?_
    exact
      (EReal.sub_le_iff_le_add
        (Or.inl (EReal.coe_ne_bot c))
        (Or.inl (EReal.coe_ne_top c))).2
        (iInf_le (fun i ↦ Φ i + ((c : ℝ) : EReal)) i)
  have hleft :
      (⨅ i, Φ i + ((c : ℝ) : EReal)) ≤ (⨅ i, Φ i) + ((c : ℝ) : EReal) := by
    exact
      (EReal.sub_le_iff_le_add
        (Or.inl (EReal.coe_ne_bot c))
        (Or.inl (EReal.coe_ne_top c))).1 hleft_sub
  exact le_antisymm hleft hright

/-- Helper for Fact 15 25: evaluating `L ▷ f` at an image point is bounded above by the value of
`f` at that fiber point. -/
private theorem infimalPostcomposition_le_apply_of_map_eq_local
    (f : H → Set.Ioi (⊥ : EReal))
    (L : H → K) (x : H) :
    (L ▷ f) (L x) ≤ (f x : EReal) := by
  -- The defining infimum is bounded above by every value attained on the fiber.
  simpa using
    (sInf_le ⟨x, by simp, rfl⟩ :
      sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' ({L x} : Set K))) ≤ (f x : EReal))

/-- Helper for Fact 15 25: once `L ▷ f` is packaged as a proper `]-∞,+∞]`-valued function, the
composite primal optimal value is exactly the same-space primal optimal value for the pair
`(L ▷ f, g)` on `K`. -/
private theorem compositePrimalOptimalValue_eq_primalOptimalValue_infimalPostcomposition
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hproper : IsProper (L ▷ f)) :
    compositePrimalOptimalValue f g L =
      primalOptimalValue (properIoi (L ▷ f) hproper) g := by
  -- Rewrite both owners as indexed infima and compare them by restricting to fibers and images.
  rw [compositePrimalOptimalValue, primalOptimalValue_eq_iInf_primalObjective,
    primalOptimalValue_eq_iInf_primalObjective]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun y ↦ ?_
    by_cases hyDom : y ∈ dom (L ▷ f)
    · -- On a genuine fiber, the composite infimum is bounded by the fiberwise infimum plus `g y`.
      by_cases hyg : y ∈ effectiveDomain g
      · obtain ⟨x₀, hx₀Dom, hx₀Map⟩ : ∃ x₀ ∈ effectiveDomain f, L x₀ = y := by
          rw [dom_infimalPostcomposition] at hyDom
          rcases hyDom with ⟨x₀, hx₀Dom, rfl⟩
          exact ⟨x₀, hx₀Dom, rfl⟩
        have hcomposite_le_fiber :
            (⨅ x : H, compositePrimalObjective f g L x) ≤
              ⨅ x : {x // L x = y}, (f x.1 : EReal) + (g y : EReal) := by
          refine le_iInf fun x ↦ ?_
          simpa [compositePrimalObjective_apply, x.property] using
            (iInf_le (fun x : H ↦ compositePrimalObjective f g L x) x.1)
        have hgy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hyg)
        have hgy_bot : (g y : EReal) ≠ ⊥ := ne_of_gt (g y).2
        have hgy_coe :
            (((g y : EReal).toReal : ℝ) : EReal) = (g y : EReal) := by
          exact EReal.coe_toReal hgy_top hgy_bot
        -- Normalize the fiber infimum back to the packaged same-space primal objective.
        calc
          (⨅ x : H, compositePrimalObjective f g L x) ≤
              ⨅ x : {x // L x = y}, (f x.1 : EReal) + (g y : EReal) :=
            hcomposite_le_fiber
          _ = (⨅ x : {x // L x = y}, (f x.1 : EReal)) + (g y : EReal) := by
            rw [← hgy_coe, iInf_add_real_const_local]
          _ = (L ▷ f) y + (g y : EReal) := by
            simpa using
              congrArg (fun t : EReal ↦ t + (g y : EReal))
                (infimal_postcomposition_apply_eq_iInf_fiber (L := L) (f := f) (y := y)).symm
          _ = primalObjective (properIoi (L ▷ f) hproper) g y := by
            simpa [properIoi_apply] using (primalObjective_apply (properIoi (L ▷ f) hproper) g y).symm
      · -- Outside `effectiveDomain g`, the same-space primal objective is `⊤`.
        have hgy_top : (g y : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hyg))
        rw [primalObjective_apply, properIoi_apply, hgy_top,
          EReal.add_top_of_ne_bot (hproper.1 y)]
        exact le_top
    · -- Outside `dom (L ▷ f)`, the packaged first summand is `⊤`.
      have hLy_top : (L ▷ f) y = ⊤ := le_antisymm le_top (not_lt.mp hyDom)
      rw [primalObjective_apply, properIoi_apply, hLy_top,
        EReal.top_add_of_ne_bot (ne_of_gt (g y).2)]
      exact le_top
  · refine le_iInf fun x ↦ ?_
    by_cases hxDom : x ∈ effectiveDomain f
    · have hLDom : L x ∈ dom (L ▷ f) := by
        rw [dom_infimalPostcomposition]
        exact ⟨x, hxDom, rfl⟩
      -- Evaluate the same-space infimum at `L x` and compare the first summand fiberwise.
      calc
        (⨅ y : K, primalObjective (properIoi (L ▷ f) hproper) g y) ≤
            primalObjective (properIoi (L ▷ f) hproper) g (L x) :=
          iInf_le _ (L x)
        _ = (L ▷ f) (L x) + (g (L x) : EReal) := by
          simpa [properIoi_apply] using
            (primalObjective_apply (properIoi (L ▷ f) hproper) g (L x)).symm
        _ ≤ (f x : EReal) + (g (L x) : EReal) := by
          exact add_le_add
            (infimalPostcomposition_le_apply_of_map_eq_local (f := f) (L := L) x)
            le_rfl
        _ = compositePrimalObjective f g L x := by
          rw [compositePrimalObjective_apply]
    · -- If `x ∉ effectiveDomain f`, then the composite primal value at `x` is `⊤`.
      have hfx_top : (f x : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hxDom))
      calc
        (⨅ y : K, primalObjective (properIoi (L ▷ f) hproper) g y) ≤ ⊤ := le_top
        _ = compositePrimalObjective f g L x := by
          rw [compositePrimalObjective_apply, hfx_top,
            EReal.top_add_of_ne_bot (ne_of_gt (g (L x)).2)]

/-- Helper for Fact 15 25: the composite dual objective is the same-space Fenchel dual objective
for the pair `(L ▷ f, g)` on `K`. -/
private theorem compositeDualObjective_eq_fenchelDualObjective_infimalPostcomposition
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hproper : IsProper (L ▷ f)) :
    compositeDualObjective f g L = fenchelDualObjective (properIoi (L ▷ f) hproper) g := by
  -- Evaluate both objectives and rewrite the conjugate of `L ▷ f` through Proposition 13.24.
  funext v
  rw [compositeDualObjective_apply, fenchelDualObjective_apply,
    conjugate_infimalPostcomposition_eq_comp_adjoint]
  simp

/-- Helper for Fact 15 25: the raw same-space dual objective on `K` attached to `L ▷ f` is
definitionally the composite dual objective after rewriting the conjugate by
`conjugate_infimalPostcomposition_eq_comp_adjoint`. -/
private theorem rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    (fun v : K ↦ ((L ▷ f)∗ (-v)) + g.asEReal∗ v) =
      compositeDualObjective f g L := by
  -- Normalize the raw same-space dual integrand to the owner dual objective pointwise.
  funext v
  have hconj :
      ((L ▷ f)∗ (-v)) = f.asEReal∗ (L.adjoint (-v)) :=
    congrFun (conjugate_infimalPostcomposition_eq_comp_adjoint (f := f) (L := L)) (-v)
  calc
    ((L ▷ f)∗ (-v)) + g.asEReal∗ v = f.asEReal∗ (L.adjoint (-v)) + g.asEReal∗ v := by
      rw [hconj]
    _ = compositeDualObjective f g L v := by
      simp [compositeDualObjective_apply]

/-- Helper for Fact 15 25: a minimizing witness for the raw same-space dual objective on `K`
immediately transports to a minimizing witness for the owner composite dual objective. -/
private theorem mem_argmin_rawDualObjective_to_composite_local
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) {v : K}
    (hv :
      v ∈ Argmin (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w)) :
    v ∈ Argmin (compositeDualObjective f g L) := by
  -- The two minimization problems have the same pointwise objective after the raw dual rewrite.
  have hrange :
      Set.range (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w) =
        Set.range (compositeDualObjective f g L) := by
    ext a
    constructor
    · rintro ⟨w, rfl⟩
      exact
        ⟨w,
          (congrFun
            (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
              (f := f) (g := g) (L := L))
            w).symm⟩
    · rintro ⟨w, rfl⟩
      exact
        ⟨w,
          congrFun
            (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
              (f := f) (g := g) (L := L))
            w⟩
  rw [mem_argmin_iff_eq_sInf] at hv ⊢
  calc
    compositeDualObjective f g L v = ((L ▷ f)∗ (-v)) + g.asEReal∗ v := by
      symm
      exact
        congrFun
          (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
            (f := f) (g := g) (L := L))
          v
    _ = sInf (Set.range (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w)) := hv
    _ = sInf (Set.range (compositeDualObjective f g L)) := by
      exact congrArg sInf hrange

/-- Helper for Fact 15 25: the same pointwise identification also transports a minimizing witness
for the owner composite dual objective back to the raw same-space dual objective on `K`. -/
private theorem mem_argmin_compositeDualObjective_to_rawDualObjective_local
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) {v : K}
    (hv : v ∈ Argmin (compositeDualObjective f g L)) :
    v ∈ Argmin (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w) := by
  -- The raw same-space dual objective has exactly the same range as the owner composite dual
  -- objective, so `Argmin` membership rewrites back along the pointwise equality.
  have hrange :
      Set.range (compositeDualObjective f g L) =
        Set.range (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w) := by
    ext a
    constructor
    · rintro ⟨w, rfl⟩
      exact
        ⟨w,
          congrFun
            (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
              (f := f) (g := g) (L := L))
            w⟩
    · rintro ⟨w, rfl⟩
      exact
        ⟨w,
          (congrFun
            (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
              (f := f) (g := g) (L := L))
            w).symm⟩
  rw [mem_argmin_iff_eq_sInf] at hv ⊢
  calc
    ((L ▷ f)∗ (-v)) + g.asEReal∗ v = compositeDualObjective f g L v := by
      exact
        congrFun
          (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
            (f := f) (g := g) (L := L))
          v
    _ = sInf (Set.range (compositeDualObjective f g L)) := hv
    _ = sInf (Set.range (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w)) := by
      exact congrArg sInf hrange

/-- Helper for Fact 15 25: if the raw same-space dual objective on `K` is everywhere `⊤`, then
the origin is already an `Argmin` witness for the owner composite dual objective. -/
private theorem zero_mem_argmin_of_rawDualObjective_eq_top_local
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hall : ∀ v : K, ((L ▷ f)∗ (-v)) + g.asEReal∗ v = ⊤) :
    (0 : K) ∈ Argmin (compositeDualObjective f g L) := by
  -- Transport the all-`⊤` branch through the raw-dual/composite-dual identification.
  have hallComposite : ∀ v : K, compositeDualObjective f g L v = ⊤ := by
    intro v
    calc
      compositeDualObjective f g L v = ((L ▷ f)∗ (-v)) + g.asEReal∗ v := by
        symm
        exact
          congrFun
            (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
              (f := f) (g := g) (L := L))
            v
      _ = ⊤ := hall v
  exact zero_mem_argmin_of_compositeDualObjective_eq_top f g L hallComposite

/-- Helper for Fact 15 25: the source regularity split transports directly to the same-space pair
`(L ▷ f, g)` after rewriting `effectiveDomain (L ▷ f)` as `L '' effectiveDomain f`. -/
private theorem rawInfimalPostcomposition_regular_split_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (effectiveDomain g ∩ ri (dom (L ▷ f))).Nonempty ∨
      (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
        (effectiveDomain g ∩ dom (L ▷ f)).Nonempty) := by
  -- Rewrite the source regularity split through `dom_infimalPostcomposition` before trying to
  -- package `L ▷ f` as a proper `Γ₀` object.
  rcases hregular with hri | hpoly
  · -- Branch `(i)` is exactly the raw same-space `ri` condition on `dom (L ▷ f)`.
    left
    simpa [dom_infimalPostcomposition] using hri
  · -- Branch `(ii)` keeps the same polyhedral witness after the raw domain rewrite.
    rcases hpoly with ⟨hfdH, hf_polyhedral, hdom⟩
    right
    exact ⟨hfdH, hf_polyhedral, by simpa [dom_infimalPostcomposition] using hdom⟩

/-- Helper for Fact 15 25: the source regularity split transports directly to the same-space pair
`(L ▷ f, g)` after rewriting `effectiveDomain (L ▷ f)` as `L '' effectiveDomain f`. -/
private theorem infimalPostcomposition_regular_split_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hproper : IsProper (L ▷ f))
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (effectiveDomain g ∩ ri (effectiveDomain (properIoi (L ▷ f) hproper))).Nonempty ∨
      (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
        (effectiveDomain g ∩ effectiveDomain (properIoi (L ▷ f) hproper)).Nonempty) := by
  -- First stay at the raw `EReal`-valued infimal postcomposition, then transport the domain to
  -- the packaged `properIoi` spelling only at the last step.
  rcases rawInfimalPostcomposition_regular_split_of_polyhedral_regularity
      (f := f) (g := g) (L := L) hregular with hri | hpoly
  · -- Branch `(i)` is now just the `properIoi` domain rewrite.
    left
    simpa [effectiveDomain_properIoi_eq_dom hproper] using hri
  · -- Branch `(ii)` keeps the same finite-dimensional/polyhedral witness after packaging.
    rcases hpoly with ⟨hfdH, hf_polyhedral, hdom⟩
    right
    exact ⟨hfdH, hf_polyhedral, by
      simpa [effectiveDomain_properIoi_eq_dom hproper] using hdom⟩

/-- Helper for Fact 15 25: the identity-map case of Theorem 15.23 is exactly the same-space
Fenchel dual-attainment statement. -/
private theorem
    exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain_local
    (p g : K → Set.Ioi (⊥ : EReal)) (hp : p ∈ Γ₀(K)) (hg : g ∈ Γ₀(K))
    (hsri : (0 : K) ∈ sri (effectiveDomain g - effectiveDomain p)) :
    ∃ v ∈ Argmin (fenchelDualObjective p g),
      primalOptimalValue p g = -(fenchelDualObjective p g v) := by
  have hsri_id :
      (0 : K) ∈ sri (effectiveDomain g - (ContinuousLinearMap.id ℝ K) '' effectiveDomain p) := by
    simpa using hsri
  obtain ⟨v, hvArg, hvEq⟩ :=
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      p hp g hg (ContinuousLinearMap.id ℝ K) hsri_id
  refine ⟨v, ?_, ?_⟩
  · -- Under `L = id`, the composite dual owner is definitionally the same-space Fenchel dual
    -- objective.
    rw [mem_argmin_iff_eq_sInf] at hvArg ⊢
    simpa [compositeDualObjective_apply, fenchelDualObjective_apply] using hvArg
  · -- The primal owner similarly collapses to the ordinary same-space primal optimal value.
    simpa [compositePrimalOptimalValue, primalOptimalValue_eq_iInf_primalObjective,
      compositePrimalObjective_apply, primalObjective_apply, compositeDualObjective_apply,
      fenchelDualObjective_apply] using hvEq

/-- Helper for Fact 15 25: once the same-space polyhedral owner on `K` is available for the pair
`(L ▷ f, g)`, the public composite statement follows by the two owner rewrites above. -/
private theorem
    exists_mem_argmin_rawDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regular_split_local
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    [FiniteDimensional ℝ K] (hg_polyhedral : Polyhedral g.asEReal)
    (hrawRegularity :
      (effectiveDomain g ∩ ri (dom (L ▷ f))).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ dom (L ▷ f)).Nonempty)) :
    ∃ v ∈ Argmin (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w),
      compositePrimalOptimalValue f g L =
        -((((L ▷ f)∗ (-v)) + g.asEReal∗ v)) := by
  -- Route correction: reuse the existing polyhedral composite owner and only transport its
  -- certificate back to the raw same-space dual objective on `K`.
  have hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) := by
    simpa [dom_infimalPostcomposition] using hrawRegularity
  have hpolyRegularity :
      (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
        (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
      (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
        FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
        (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) := by
    rcases hregular with hri | hpoly
    · left
      exact ⟨inferInstance, hg_polyhedral, hri⟩
    · rcases hpoly with ⟨hfinH, hf_polyhedral, hdom⟩
      right
      exact ⟨inferInstance, hg_polyhedral, hfinH, hf_polyhedral, hdom⟩
  obtain ⟨v, hvComposite, hvStrong⟩ :=
    exists_mem_argmin_compositeDualObjective_and_strongDuality_of_polyhedralRegularity
      (hf := hf) (hg := hg) (L := L) (hregular := hpolyRegularity)
  have hvRaw :
      v ∈ Argmin (fun w : K ↦ ((L ▷ f)∗ (-w)) + g.asEReal∗ w) :=
    mem_argmin_compositeDualObjective_to_rawDualObjective_local
      (f := f) (g := g) (L := L) hvComposite
  have hvDualValue :
      compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
    simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf).mp hvComposite
  refine ⟨v, hvRaw, ?_⟩
  calc
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := hvStrong
    _ = -(compositeDualObjective f g L v) := by rw [← hvDualValue]
    _ = -((((L ▷ f)∗ (-v)) + g.asEReal∗ v)) := by
      congr 1
      symm
      exact
        congrFun
          (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
            (f := f) (g := g) (L := L))
          v

/-- Helper for Fact 15 25: once the raw same-space owner on `K` is available for the pair
`(L ▷ f, g)`, the public composite statement follows by transporting its minimizer through the raw
dual/composite-dual identification. -/
private theorem exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_secondSummand_local
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    [FiniteDimensional ℝ K] (hg_polyhedral : Polyhedral g.asEReal)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
  -- Route correction: keep the blocker in the raw same-space owner, and make this composite
  -- wrapper only transport the minimizer/value through the already-proved raw-dual rewrite.
  have hrawRegularity :
      (effectiveDomain g ∩ ri (dom (L ▷ f))).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ dom (L ▷ f)).Nonempty) :=
    rawInfimalPostcomposition_regular_split_of_polyhedral_regularity
      (f := f) (g := g) (L := L) hregular
  -- First obtain the minimizing raw dual vector from the isolated same-space owner.
  obtain ⟨v, hvArg, hvEq⟩ :=
    exists_mem_argmin_rawDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regular_split_local
      (f := f) (hf := hf) (g := g) (hg := hg) (L := L)
      (hg_polyhedral := hg_polyhedral) (hrawRegularity := hrawRegularity)
  refine ⟨v, ?_, ?_⟩
  · -- Transport the raw same-space minimizer to the owner composite dual objective.
    exact mem_argmin_rawDualObjective_to_composite_local
      (f := f) (g := g) (L := L) hvArg
  · -- The same pointwise raw/composite dual rewrite gives the displayed value identity.
    calc
      compositePrimalOptimalValue f g L =
          -((((L ▷ f)∗ (-v)) + g.asEReal∗ v)) := hvEq
      _ = -(compositeDualObjective f g L v) := by
        congr 1
        exact
          congrFun
            (rawDualObjective_infimalPostcomposition_eq_compositeDualObjective_local
              (f := f) (g := g) (L := L))
            v

/-- Helper for Fact 15 25: once `L ▷ f` is packaged as a proper `]-∞,+∞]`-valued function, the
same-space regularity split on `K` is exactly the source regularity split rewritten through
`dom_infimalPostcomposition`. -/
private theorem infimalPostcomposition_sameSpaceRegularity_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hproper : IsProper (L ▷ f))
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    (effectiveDomain g ∩ ri (effectiveDomain (properIoi (L ▷ f) hproper))).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ effectiveDomain (properIoi (L ▷ f) hproper)).Nonempty) := by
  -- This is just the domain transport needed by the packaged same-space owner.
  exact
    infimalPostcomposition_regular_split_of_polyhedral_regularity
      (f := f) (g := g) (L := L) (hproper := hproper) hregular

-- Proof sketch: rewrite the composite problem to the same-space pair `(L ▷ f, g)` on `K`, apply
-- the finite-dimensional/polyhedral same-space attainment owner there, and transport the result
-- back through the primal/dual owner equalities above.
set_option linter.style.longLine false in
/-- Fact 15.25: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, `K` is finite-dimensional, `g` is polyhedral, and
either (i) `effectiveDomain g` meets `ri (L '' effectiveDomain f)` or (ii) `H` is
finite-dimensional, `f` is polyhedral, and `effectiveDomain g` meets `L '' effectiveDomain f`,
then the composite primal optimal value is the negative of the minimum of the dual objective
`v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) [FiniteDimensional ℝ K] (hg_polyhedral : Polyhedral g.asEReal)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
  -- Route correction: work directly with the same-space pair `(L ▷ f, g)` on `K`, then transport
  -- the attained dual vector back through the canonical owner rewrites.
  exact
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_secondSummand_local
      (f := f) (hf := hf) (g := g) (hg := hg) (L := L)
      (hg_polyhedral := hg_polyhedral) (hregular := hregular)

-- Proof sketch: apply the source-facing attainment theorem above and rewrite the attained minimum
-- as `compositeDualOptimalValue f g L`.
/-- Companion reformulation of Fact 15.25: the attained dual minimum rewrites to the canonical
dual optimal value `compositeDualOptimalValue f g L`. -/
theorem compositePrimalOptimalValue_eq_neg_compositeDualOptimalValue_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) [FiniteDimensional ℝ K] (hg_polyhedral : Polyhedral g.asEReal)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  -- Reuse the attainment statement and then rewrite the minimizing value as the owner optimum.
  obtain ⟨v, hvArg, hvEq⟩ :=
    (
      exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regularity
        (f := f) (hf := hf) (g := g) (hg := hg) (L := L)
        (hg_polyhedral := hg_polyhedral) (hregular := hregular)
    )
  -- Membership in `Argmin` identifies the attained dual value with the dual optimal value.
  have hvValue : compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
    rw [compositeDualOptimalValue_def]
    exact (mem_argmin_iff_eq_sInf).1 hvArg
  rw [hvValue] at hvEq
  exact hvEq

end FenchelRockafellarDuality

end ERealFunction
