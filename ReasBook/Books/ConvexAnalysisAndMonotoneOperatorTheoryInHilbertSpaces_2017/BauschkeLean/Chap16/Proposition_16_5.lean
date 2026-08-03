import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section BiconjugationAndSubdifferentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (x : H)

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: a nonempty effective domain makes the canonical Fenchel conjugate
proper above `⊥`. -/
private theorem conjugate_ne_bot_of_effectiveDomain_nonempty
    (hdom : (effectiveDomain f).Nonempty) (u : H) :
    f.asEReal∗ u ≠ ⊥ := by
  have hproper : IsProper f.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (f y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  exact conjugate_ne_bot_of_isProper hproper u

end

/-- Helper for Proposition 16 5: the conjugate can be repackaged as an `]-∞,+∞]`-valued
function once the effective domain is nonempty. -/
private noncomputable abbrev properConjugateIoi (hdom : (effectiveDomain f).Nonempty) :
    H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨f.asEReal∗ u,
      bot_lt_iff_ne_bot.mpr (conjugate_ne_bot_of_effectiveDomain_nonempty (f := f) hdom u)⟩

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: coercing the packaged conjugate back to `EReal` recovers the raw
Fenchel conjugate. -/
@[simp] private theorem properConjugateIoi_apply
    (hdom : (effectiveDomain f).Nonempty) (u : H) :
    (properConjugateIoi (f := f) hdom u : EReal) = f.asEReal∗ u :=
  rfl

end

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: for a function with nonempty effective domain, subgradient
membership is equivalent to Fenchel--Young equality. -/
private theorem mem_subdifferential_iff_fenchel_young_eq
    (hdom : (effectiveDomain f).Nonempty) (u : H) :
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
    -- Proposition 16.4 upgrades subgradient membership to finiteness at the base point.
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
    -- Proposition 16.4 reduces the converse to the affine half-space description.
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

end

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: an active subgradient of `f` becomes a subgradient of the
packaged Fenchel conjugate with the arguments reversed. -/
private theorem mem_subdifferential_properConjugateIoi_of_mem_subdifferential
    (hdom : (effectiveDomain f).Nonempty) {u : H} (hu : u ∈ (∂ f) x) :
    x ∈ (∂ (properConjugateIoi (f := f) hdom)) u := by
  let g : H → Set.Ioi (⊥ : EReal) := properConjugateIoi (f := f) hdom
  have hproper : IsProper f.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (f y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  have hx : x ∈ effectiveDomain f :=
    SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hu⟩
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hgu_top : (g u : EReal) ≠ ⊤ := by
    have hfy_source :
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq (f := f) (x := x) hdom u).1 hu
    intro hu_top
    have hu_top' : f.asEReal∗ u = ⊤ := by
      simpa [g, properConjugateIoi_apply] using hu_top
    have hpair_top : (((⟪x, u⟫_ℝ : ℝ) : EReal)) = ⊤ := by
      calc
        (((⟪x, u⟫_ℝ : ℝ) : EReal)) = (f x : EReal) + f.asEReal∗ u := hfy_source.symm
        _ = ⊤ := by
          rw [hu_top']
          exact EReal.add_top_of_ne_bot hfx_bot
    exact EReal.coe_ne_top _ hpair_top
  have hgu_bot : (g u : EReal) ≠ ⊥ := ne_of_gt (g u).2
  have hfy :
      (f x : EReal) + (g u : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    simpa [g, properConjugateIoi_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f := f) (x := x) hdom u).1 hu
  have hfy_real : (f x : EReal).toReal + (g u : EReal).toReal = ⟪x, u⟫_ℝ := by
    have hfy' := hfy
    rw [← EReal.coe_toReal hfx_top hfx_bot,
      ← EReal.coe_toReal hgu_top hgu_bot, ← EReal.coe_add] at hfy'
    exact EReal.coe_eq_coe_iff.mp hfy'
  rw [mem_subdifferential_iff]
  intro v
  by_cases hv : v ∈ effectiveDomain g
  · have hgv_top : (g v : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hv)
    have hgv_bot : (g v : EReal) ≠ ⊥ := ne_of_gt (g v).2
    have hfy_v :
        ((⟪x, v⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + (g v : EReal) := by
      simpa [g, properConjugateIoi_apply, real_inner_comm] using
        fenchel_young_inequality hproper x v
    have hfy_v_real : ⟪x, v⟫_ℝ ≤ (f x : EReal).toReal + (g v : EReal).toReal := by
      have hfy_v' := hfy_v
      rw [← EReal.coe_toReal hfx_top hfx_bot,
        ← EReal.coe_toReal hgv_top hgv_bot, ← EReal.coe_add] at hfy_v'
      exact EReal.coe_le_coe_iff.mp hfy_v'
    have hinner_sub :
        ⟪v - u, x⟫_ℝ = ⟪x, v⟫_ℝ - ⟪x, u⟫_ℝ := by
      calc
        ⟪v - u, x⟫_ℝ = ⟪v, x⟫_ℝ - ⟪u, x⟫_ℝ := by
          simp [sub_eq_add_neg, inner_add_left]
        _ = ⟪x, v⟫_ℝ - ⟪x, u⟫_ℝ := by
          rw [real_inner_comm v x, real_inner_comm u x]
    have hineq_real :
        ⟪v - u, x⟫_ℝ ≤ (g v : EReal).toReal - (g u : EReal).toReal := by
      have hinner_add : ⟪v - u, x⟫_ℝ + ⟪x, u⟫_ℝ = ⟪x, v⟫_ℝ := by
        linarith [hinner_sub]
      linarith [hfy_v_real, hfy_real, hinner_add]
    have hsub :
        ((((g v : EReal).toReal - (g u : EReal).toReal : ℝ) : EReal)) =
          (g v : EReal) - (g u : EReal) := by
      calc
        ((((g v : EReal).toReal - (g u : EReal).toReal : ℝ) : EReal)) =
            ((((g v : EReal).toReal : ℝ) : EReal)) -
              ((((g u : EReal).toReal : ℝ) : EReal)) := by
                rw [EReal.coe_sub]
        _ = (g v : EReal) - (g u : EReal) := by
              rw [EReal.coe_toReal hgv_top hgv_bot, EReal.coe_toReal hgu_top hgu_bot]
    have hineq :
        ((⟪v - u, x⟫_ℝ : ℝ) : EReal) ≤ (g v : EReal) - (g u : EReal) := by
      rw [← hsub]
      exact EReal.coe_le_coe_iff.mpr hineq_real
    exact (EReal.le_sub_iff_add_le (Or.inl hgu_bot) (Or.inl hgu_top)).1 hineq
  · have hgv_top : (g v : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hv))
    have hineq : (((⟪v - u, x⟫_ℝ : ℝ) : EReal) + (g u : EReal)) ≤ (g v : EReal) := by
      rw [hgv_top]
      exact le_top
    simpa [g] using hineq

end

section

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 5: if the effective domain is empty, then the canonical
`EReal`-valued coercion of `f` is identically `+∞`. -/
private theorem asEReal_eq_top_of_effectiveDomain_eq_empty
    (hempty : effectiveDomain f = ∅) :
    f.asEReal = (fun _ : H ↦ (⊤ : EReal)) := by
  funext y
  -- Empty effective domain means every point value fails to be finite above, hence equals `⊤`.
  have hy_not_mem : y ∉ effectiveDomain f := by
    simp [hempty]
  have hy_not_lt : ¬ (f y : EReal) < ⊤ := by
    simpa [mem_effectiveDomain_iff] using hy_not_mem
  exact le_antisymm le_top (not_lt.mp hy_not_lt)

end

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: the Fenchel conjugate of the constant `+∞` function is the
constant `-∞` function. -/
private theorem conjugate_top_eq_bot :
    ((fun _ : H ↦ (⊤ : EReal))∗) = (fun _ : H ↦ (⊥ : EReal)) := by
  funext u
  rw [conjugate_apply]
  apply le_antisymm
  · -- Every affine defect against `⊤` is `⊥`, so the supremum is bounded above by `⊥`.
    refine iSup_le fun y ↦ ?_
    simp
  · exact bot_le

end

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: the Fenchel biconjugate of the constant `+∞` function is again
the constant `+∞` function. -/
private theorem biconjugate_top_eq_top :
    ((fun _ : H ↦ (⊤ : EReal))∗∗) = (fun _ : H ↦ (⊤ : EReal)) := by
  rw [conjugate_top_eq_bot]
  funext x
  rw [conjugate_apply]
  apply le_antisymm
  · exact le_top
  · -- Evaluating the defining supremum at `0` already yields the value `⊤`.
    have htop_le :
        (⊤ : EReal) ≤
          ⨆ u : H, ((⟪u, x⟫_ℝ : ℝ) : EReal) - (⊥ : EReal) := by
      refine le_iSup (fun u : H ↦ ((⟪u, x⟫_ℝ : ℝ) : EReal) - (⊥ : EReal)) 0
    exact htop_le

end

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: at a genuine subdifferentiability point, the active conjugate
value is finite above. -/
private theorem conjugate_value_ne_top_of_mem_subdifferential
    (hdom : (effectiveDomain f).Nonempty) {u : H} (hu : u ∈ (∂ f) x) :
    f.asEReal∗ u ≠ ⊤ := by
  have hx : x ∈ effectiveDomain f :=
    SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hu⟩
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hfy :
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f) (x := x) hdom u).1 hu
  intro hu_top
  -- If the conjugate value were `⊤`, Fenchel--Young equality would force a finite real to equal
  -- `⊤`.
  have hpair_top : (((⟪x, u⟫_ℝ : ℝ) : EReal)) = ⊤ := by
    calc
      (((⟪x, u⟫_ℝ : ℝ) : EReal)) = (f x : EReal) + f.asEReal∗ u := hfy.symm
      _ = ⊤ := by
        rw [hu_top]
        exact EReal.add_top_of_ne_bot hx_bot
  exact EReal.coe_ne_top _ hpair_top

end

section

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: a finite conjugate value gives an effective-domain point of the
packaged Fenchel conjugate. -/
private theorem mem_effectiveDomain_properConjugateIoi_of_ne_top
    (hdom : (effectiveDomain f).Nonempty) {u : H} (hu_top : f.asEReal∗ u ≠ ⊤) :
    u ∈ effectiveDomain (properConjugateIoi f hdom) := by
  -- The packaged conjugate has the same pointwise values as the raw conjugate on its owner
  -- surface, so finiteness above is exactly the effective-domain condition.
  rw [mem_effectiveDomain_iff, properConjugateIoi_apply]
  exact lt_top_iff_ne_top.mpr hu_top

end

-- Proof sketch: choose a subgradient `u ∈ (∂ f) x`. Apply Proposition 16.10 to `f` to obtain
-- Fenchel--Young equality for `(x,u)`, then use Proposition 16.10 again on the packaged Fenchel
-- conjugate `properConjugateIoi f hdom` to obtain the corresponding equality for `(u,x)`. After
-- rewriting the middle conjugate value by `toReal`, both identities solve for the same quantity,
-- so `f** x = f x`.
/-- Proposition 16 5 (1): if an `]-∞,+∞]`-valued function is subdifferentiable at `x`, then its
Fenchel biconjugate agrees with `f` at `x`. -/
theorem biconjugate_eq_self_at_of_subdifferentiableAt
    (hxsub : SubdifferentiableAt f x) :
    f.asEReal∗∗ x = f.asEReal x := by
  let _ : CompleteSpace H := inferInstance
  by_cases hdom : (effectiveDomain f).Nonempty
  · rcases hxsub with ⟨u, hu⟩
    have hconj_top : f.asEReal∗ u ≠ ⊤ :=
      conjugate_value_ne_top_of_mem_subdifferential (f := f) (x := x) hdom hu
    have hconj_bot : f.asEReal∗ u ≠ ⊥ :=
      conjugate_ne_bot_of_effectiveDomain_nonempty (f := f) hdom u
    have hfy_f :
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq (f := f) (x := x) hdom u).1 hu
    let g : H → Set.Ioi (⊥ : EReal) := properConjugateIoi f hdom
    have hxu : x ∈ (∂ g) u := by
      -- Active subgradients transfer directly to the packaged conjugate.
      simpa [g] using
        mem_subdifferential_properConjugateIoi_of_mem_subdifferential
          (f := f) (x := x) hdom hu
    have hgdom : (effectiveDomain g).Nonempty := by
      refine ⟨u, ?_⟩
      -- The active slope remains a finite point after packaging the conjugate.
      simpa [g] using
        mem_effectiveDomain_properConjugateIoi_of_ne_top (f := f) hdom hconj_top
    have hfy_g :
        (g u : EReal) + g.asEReal∗ x = ((⟪u, x⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq (f := g) (x := u) hgdom x).1 hxu
    have hgu_eq : (g u : EReal) = f.asEReal∗ u := by
      simp [g]
    have hgstar_apply : g.asEReal∗ x = f.asEReal∗∗ x := by
      simp [g]
    let a : ℝ := (f.asEReal∗ u).toReal
    have ha : ((a : ℝ) : EReal) = f.asEReal∗ u := by
      exact EReal.coe_toReal hconj_top hconj_bot
    have hf_eq :
        f.asEReal x = ((⟪x, u⟫_ℝ : ℝ) : EReal) - (a : EReal) := by
      -- The first Fenchel--Young identity solves for `f x`.
      have hfy_f' : f.asEReal x + (a : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        rw [ha]
        simpa using hfy_f
      have hfy_f'' := congrArg (fun t : EReal ↦ t - a) hfy_f'
      simpa [EReal.add_sub_cancel_right] using hfy_f''
    have hbiconj_eq :
        f.asEReal∗∗ x = ((⟪x, u⟫_ℝ : ℝ) : EReal) - (a : EReal) := by
      have hfy_g' :
          f.asEReal∗∗ x + (a : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        -- The packaged-conjugate Fenchel--Young identity solves for `f** x`.
        rw [ha, ← hgu_eq, ← hgstar_apply]
        simpa [real_inner_comm, add_comm] using hfy_g
      have hfy_g'' := congrArg (fun t : EReal ↦ t - a) hfy_g'
      simpa [EReal.add_sub_cancel_right] using hfy_g''
    exact hbiconj_eq.trans hf_eq.symm
  · have hempty : effectiveDomain f = ∅ := Set.not_nonempty_iff_eq_empty.mp hdom
    have htop : f.asEReal = (fun _ : H ↦ (⊤ : EReal)) :=
      asEReal_eq_top_of_effectiveDomain_eq_empty (f := f) hempty
    have hbtop : f.asEReal∗∗ = (fun _ : H ↦ (⊤ : EReal)) := by
      rw [htop]
      exact biconjugate_top_eq_top (H := H)
    have hfx_top : f.asEReal x = ⊤ := by
      simpa [htop] using congrFun htop x
    -- If the effective domain is empty, both `f` and its biconjugate are the constant `⊤`
    -- function.
    simpa [hfx_top] using congrFun hbtop x

-- Proof sketch: choose `u₀ ∈ ∂ f x` from `hxsub` and package the conjugate as
-- `g := properConjugateIoi f hdom`. The one-way transfer from active subgradients sends
-- `u ∈ ∂ f x` to `x ∈ ∂ g u`, and applying the same transfer to `g` yields
-- `u ∈ ∂ f** x`. For the converse inclusion, rewrite `u ∈ ∂ f** x` as Fenchel--Young equality for
-- the packaged biconjugate `p := properConjugateIoi g hgdom`, then use clause (1) to replace
-- `p x = f x` and Proposition 13.16 to identify `p* = g = f*`.
/-- Clause (2) of Proposition 16 5: if an `]-∞,+∞]`-valued function is subdifferentiable at `x`,
then the
subdifferential of the Fenchel biconjugate `f^{**}` at `x` coincides with the subdifferential of
`f` at `x`. -/
theorem biconjugate_subdifferential_eq_subdifferential_at_of_subdifferentiableAt
    (hxsub : SubdifferentiableAt f x) :
    (∂ (f.asEReal∗∗)) x = (∂ f) x := by
  by_cases hdom : (effectiveDomain f).Nonempty
  · have hxsub' := hxsub
    rcases hxsub with ⟨u0, hu0⟩
    have hxeff : x ∈ effectiveDomain f :=
      SubdifferentiableAt.mem_effectiveDomain hdom hxsub'
    have hconj_top : f.asEReal∗ u0 ≠ ⊤ :=
      conjugate_value_ne_top_of_mem_subdifferential (f := f) (x := x) hdom hu0
    let g : H → Set.Ioi (⊥ : EReal) := properConjugateIoi f hdom
    have hgdom : (effectiveDomain g).Nonempty := by
      refine ⟨u0, ?_⟩
      -- The chosen slope `u₀` lies in the effective domain of the packaged conjugate.
      simpa [g] using
        mem_effectiveDomain_properConjugateIoi_of_ne_top (f := f) hdom hconj_top
    let p : H → Set.Ioi (⊥ : EReal) := properConjugateIoi g hgdom
    have hbiconj_eq :
        f.asEReal∗∗ x = f.asEReal x :=
      biconjugate_eq_self_at_of_subdifferentiableAt (f := f) (x := x) hxsub'
    have hpx : (p x : EReal) = f.asEReal x := by
      simpa [p, g, properConjugateIoi_apply] using hbiconj_eq
    have hpdom : (effectiveDomain p).Nonempty := by
      refine ⟨x, ?_⟩
      rw [mem_effectiveDomain_iff]
      simpa [hpx] using
        (mem_effectiveDomain_iff.mp hxeff)
    have htriple_apply (u : H) : p.asEReal∗ u = (g u : EReal) := by
      simpa [p, g, properConjugateIoi_apply] using
        congrFun (triple_conjugate_eq_conjugate (f := f.asEReal)) u
    ext u
    constructor
    · intro hu
      have hEq_p :
          (p x : EReal) + p.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        have hu_p : u ∈ (∂ p) x := by
          -- Rewrite the biconjugate fiber on the packaged surface.
          simpa [p, g, properConjugateIoi_apply] using hu
        exact (mem_subdifferential_iff_fenchel_young_eq (f := p) (x := x) hpdom u).1 hu_p
      have hEq_f :
          (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        have hpx' : (p x : EReal) = (f x : EReal) := by
          simpa using hpx
        have hpstar : p.asEReal∗ u = f.asEReal∗ u := by
          simpa [p, g, properConjugateIoi_apply] using htriple_apply u
        calc
          (f x : EReal) + f.asEReal∗ u = (p x : EReal) + p.asEReal∗ u := by
            rw [← hpx', ← hpstar]
          _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hEq_p
      exact (mem_subdifferential_iff_fenchel_young_eq (f := f) (x := x) hdom u).2 hEq_f
    · intro hu
      have hxu : x ∈ (∂ g) u := by
        -- First transfer `u ∈ ∂ f x` to the packaged conjugate `g`.
        simpa [g] using
          mem_subdifferential_properConjugateIoi_of_mem_subdifferential
            (f := f) (x := x) hdom hu
      have hu_p : u ∈ (∂ p) x := by
        -- Apply the same transfer once more to package the biconjugate.
        simpa [p] using
          mem_subdifferential_properConjugateIoi_of_mem_subdifferential
            (f := g) (x := u) hgdom hxu
      -- The second packaged conjugate is exactly the Fenchel biconjugate of `f`.
      simpa [p, g, properConjugateIoi_apply] using hu_p
  · have hempty : effectiveDomain f = ∅ := Set.not_nonempty_iff_eq_empty.mp hdom
    have htop : f.asEReal = (fun _ : H ↦ (⊤ : EReal)) :=
      asEReal_eq_top_of_effectiveDomain_eq_empty (f := f) hempty
    have hbtop : f.asEReal∗∗ = (fun _ : H ↦ (⊤ : EReal)) := by
      rw [htop]
      exact biconjugate_top_eq_top (H := H)
    -- In the empty-domain branch, both operators are the subdifferential of the constant `⊤`
    -- function, hence both fibers are all of `H`.
    ext u
    rw [mem_subdifferential_iff, mem_subdifferential_iff]
    have htop_apply (z : H) : (f z : EReal) = ⊤ := by
      simpa using congrFun htop z
    have hbtop_apply (z : H) : f.asEReal∗∗ z = ⊤ := by
      simpa using congrFun hbtop z
    constructor
    · intro _hu y
      calc
        (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + (f x : EReal)) =
            (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + (⊤ : EReal)) := by
              rw [htop_apply x]
        _ ≤ (f y : EReal) := by
              rw [htop_apply y]
              exact le_top
    · intro _hu y
      calc
        (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + f.asEReal∗∗ x) =
            (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + (⊤ : EReal)) := by
              rw [hbtop_apply x]
        _ ≤ f.asEReal∗∗ y := by
              rw [hbtop_apply y]
              exact le_top

end BiconjugationAndSubdifferentials

end ERealFunction
