import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal))

/-- Helper for Proposition 16.10: finiteness of the raw conjugate value gives an effective-domain
point for the packaged conjugate. -/
theorem mem_effectiveDomain_properConjugateIoi_of_ne_top
    (hdom : (effectiveDomain f).Nonempty) {u : H} (hu_top : f.asEReal∗ u ≠ ⊤) :
    u ∈ effectiveDomain (properConjugateIoi f hdom) := by
  -- The packaged conjugate has the same `EReal` value, so `≠ ⊤` is exactly effective-domain
  -- membership.
  rw [mem_effectiveDomain_iff]
  have hgu_top : (properConjugateIoi f hdom u : EReal) ≠ ⊤ := by
    simpa [properConjugateIoi_apply] using hu_top
  exact lt_of_le_of_ne le_top hgu_top

/-- Helper for Proposition 16.10: conjugating the packaged conjugate recovers the Fenchel
biconjugate of the original function. -/
theorem properConjugateIoi_conjugate_eq_biconjugate
    (hdom : (effectiveDomain f).Nonempty) (x : H) :
    (properConjugateIoi f hdom).asEReal∗ x = f.asEReal∗∗ x := by
  -- Coercing `properConjugateIoi f hdom` back to `EReal` is definitionally the raw conjugate.
  simp [Function.asEReal]

/-- Proposition 16.10 (1): `u` is a
subgradient of `f` at `x` exactly when equality holds in the Fenchel--Young inequality
`f(x) + f^*(u) = ⟪x, u⟫`. -/
theorem mem_subdifferential_iff_fenchel_young_eq
    (hdom : (effectiveDomain f).Nonempty) (x u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  -- Upgrade the `]-∞,+∞]`-valued function to a proper `EReal`-valued function so that
  -- Proposition 13.15 applies.
  have hproper : IsProper f.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (f y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  constructor
  · intro hu
    have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    -- Proposition 16.4 puts the base point inside the effective domain.
    have hx : x ∈ effectiveDomain f :=
      subdifferential_domain_subset_effectiveDomain f hdom hx_dom
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hu_halfspace :
        ∀ y ∈ effectiveDomain f,
          ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hu
      exact hu
    -- Every affine defect is bounded by the defect at `x`.
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
    -- Proposition 13.15 supplies the reverse Fenchel--Young inequality.
    have hfy_le :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + f.asEReal∗ u := by
      simpa using fenchel_young_inequality hproper x u
    exact le_antisymm hsum_le hfy_le
  · intro hEq
    have hconj_bot : f.asEReal∗ u ≠ ⊥ :=
      conjugate_ne_bot_of_effectiveDomain_nonempty hdom u
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
    -- Proposition 16.4 turns the contact equality back into the affine half-space inequalities.
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

/-- Helper for Proposition 16.10: Fenchel--Young equality at an active subgradient forces the
conjugate value to stay finite above. -/
theorem conjugate_value_ne_top_of_mem_subdifferential
    (hdom : (effectiveDomain f).Nonempty) {x u : H} (hu : u ∈ (∂ f) x) :
    f.asEReal∗ u ≠ ⊤ := by
  -- First place `x` in the effective domain so the primal value is finite above.
  have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  have hx : x ∈ effectiveDomain f :=
    subdifferential_domain_subset_effectiveDomain f hdom hx_dom
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  -- Then the contact equality from Proposition 16.10(1) rules out `f*(u) = +∞`.
  have hEq :
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u).1 hu
  intro hu_top
  have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
    rw [hu_top]
    exact EReal.add_top_of_ne_bot hfx_bot
  exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)

-- Semantic recall: `lean_leansearch` was uninformative for this project-local API; local Chapter
-- 16 uses confirm that clause (2) at the properness level is the one-way transfer to the packaged
-- conjugate, while the inverse-operator identity is deferred to the later `Γ₀(H)` specialization.
/-- Proposition 16.10 (2): if `u ∈ (∂ f) x`, then `x` is a subgradient of the packaged Fenchel
conjugate `properConjugateIoi f hdom` at `u`. -/
theorem mem_subdifferential_properConjugateIoi_of_mem_subdifferential
    (hdom : (effectiveDomain f).Nonempty) (x u : H) :
    u ∈ (∂ f) x → x ∈ (∂ (properConjugateIoi f hdom)) u := by
  intro hu
  let g : H → Set.Ioi (⊥ : EReal) := properConjugateIoi f hdom
  -- First extract the contact equality for `(f, x, u)`.
  have hcontact_f :
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u).1 hu
  have hconj_top : f.asEReal∗ u ≠ ⊤ :=
    conjugate_value_ne_top_of_mem_subdifferential (f := f) hdom hu
  have hu_dom_g : u ∈ effectiveDomain g :=
    mem_effectiveDomain_properConjugateIoi_of_ne_top (f := f) hdom hconj_top
  have hdom_g : (effectiveDomain g).Nonempty := ⟨u, hu_dom_g⟩
  have hproper_g : IsProper g.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (g y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom_g
  -- The biconjugate minorizes `f`, so the contact equality for `f` bounds the packaged
  -- conjugate pair from above.
  have hcontact_g_le :
      (g u : EReal) + g.asEReal∗ x ≤ ((⟪u, x⟫_ℝ : ℝ) : EReal) := by
    calc
      (g u : EReal) + g.asEReal∗ x
          = f.asEReal∗ u + f.asEReal∗∗ x := by
              simp [g, Function.asEReal]
      _ ≤ f.asEReal∗ u + (f x : EReal) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (biconjugate_le (f := f.asEReal) x) (f.asEReal∗ u)
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
            simpa [add_comm] using hcontact_f
      _ = ((⟪u, x⟫_ℝ : ℝ) : EReal) := by
            rw [real_inner_comm]
  -- Proposition 13.15 gives the reverse inequality for the packaged conjugate.
  have hcontact_g_ge :
      ((⟪u, x⟫_ℝ : ℝ) : EReal) ≤ (g u : EReal) + g.asEReal∗ x := by
    simpa [g] using fenchel_young_inequality hproper_g u x
  have hcontact_g :
      (g u : EReal) + g.asEReal∗ x = ((⟪u, x⟫_ℝ : ℝ) : EReal) :=
    le_antisymm hcontact_g_le hcontact_g_ge
  -- Apply Proposition 16.10(1) to the packaged conjugate at `(u, x)`.
  exact
    (mem_subdifferential_iff_fenchel_young_eq (f := g) hdom_g u x).2 hcontact_g

end SubdifferentialConjugation

end

end ERealFunction
