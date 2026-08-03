import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap15.Definition_15_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 15 9: outside the effective domain, an `]-∞,+∞]`-valued function takes
the value `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {X : Type*} (φ : X → Set.Ioi (⊥ : EReal)) {x : X}
    (hx : x ∉ effectiveDomain φ) :
    (φ x : EReal) = ⊤ := by
  -- Convert failure of effective-domain membership into failure of finiteness.
  have hnot_lt : ¬ ((φ x : EReal) < ⊤) := by
    simpa [mem_effectiveDomain_iff] using hx
  -- In `EReal`, the only nonfinite-above value allowed by the codomain is `⊤`.
  exact le_antisymm le_top (not_lt.mp hnot_lt)

/-- Helper for Proposition 15 9: an `]-∞,+∞]`-valued function is proper once its effective domain
is nonempty. -/
private theorem isProper_asEReal_of_effectiveDomain_nonempty
    {X : Type*} (φ : X → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain φ).Nonempty) :
    IsProper φ.asEReal := by
  refine ⟨fun x ↦ ne_of_gt (φ x).2, ?_⟩
  simpa [effectiveDomain, dom] using hdom

/-- Helper for Proposition 15 9: the pairings from the two Fenchel--Young inequalities cancel
exactly. -/
private theorem fenchel_pairings_cancel
    (x u : H) :
    (((⟪x, -u⟫_ℝ : ℝ) : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal)) = 0 := by
  -- Cancel the two pairings in the real scalar field before coercing to `EReal`.
  have hreal : (-⟪x, u⟫_ℝ : ℝ) + ⟪x, u⟫_ℝ = 0 := by
    simp
  have hcancel :
      (((-⟪x, u⟫_ℝ : ℝ) : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal)) = 0 := by
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  simpa [inner_neg_right] using hcancel

/-- Helper for Proposition 15 9: a nonnegative sum yields the corresponding weak-duality
inequality. -/
private theorem neg_right_le_of_add_nonneg
    {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (h : 0 ≤ a + b) :
    -b ≤ a := by
  have hneg_b_top : -b ≠ ⊤ := by
    simpa using hb
  have hsub_nonneg : 0 ≤ a - -b := by
    simpa [sub_eq_add_neg, neg_neg] using h
  exact (EReal.sub_nonneg (Or.inr hneg_b_top) (Or.inl ha)).1 hsub_nonneg

-- Proof sketch: if either effective domain is empty, then the corresponding function is
-- identically `+∞`, so the inequality is immediate. Otherwise apply the Fenchel--Young inequality
-- to `f` at `(x, -u)` and to `g` at `(x, u)`, then add the resulting inequalities and simplify the
-- pairing terms, which cancel.
/-- Proposition 15 9 (1): every primal value dominates the negative dual value, i.e.
`-fenchelDualObjective f g u ≤ primalObjective f g x`. -/
theorem primalObjective_ge_neg_dualObjective
    (f g : H → Set.Ioi (⊥ : EReal))
    (x u : H) :
    -fenchelDualObjective f g u ≤ primalObjective f g x := by
  by_cases hf_dom : (effectiveDomain f).Nonempty
  · by_cases hg_dom : (effectiveDomain g).Nonempty
    · -- In the proper branch, add the two Fenchel--Young inequalities and cancel the pairings.
      have hf_proper : IsProper f.asEReal :=
        isProper_asEReal_of_effectiveDomain_nonempty f hf_dom
      have hg_proper : IsProper g.asEReal :=
        isProper_asEReal_of_effectiveDomain_nonempty g hg_dom
      have hsum :
          (((⟪x, -u⟫_ℝ : ℝ) : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal)) ≤
            (((f x : EReal) + f.asEReal∗ (-u)) + ((g x : EReal) + g.asEReal∗ u)) := by
        exact add_le_add
          (fenchel_young_inequality hf_proper x (-u))
          (fenchel_young_inequality hg_proper x u)
      have hnonneg :
          (0 : EReal) ≤ primalObjective f g x + fenchelDualObjective f g u := by
        -- Normalize the two Fenchel--Young bounds to the owner primal and dual objectives.
        calc
          (0 : EReal)
              = (((⟪x, -u⟫_ℝ : ℝ) : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal)) := by
                symm
                exact fenchel_pairings_cancel x u
          _ ≤ (((f x : EReal) + f.asEReal∗ (-u)) + ((g x : EReal) + g.asEReal∗ u)) := hsum
          _ = primalObjective f g x + fenchelDualObjective f g u := by
                simp [primalObjective_apply, fenchelDualObjective_apply,
                  add_assoc, add_left_comm]
      have hf_conj_ne_bot : f.asEReal∗ (-u) ≠ ⊥ :=
        conjugate_ne_bot_of_isProper hf_proper (-u)
      have hg_conj_ne_bot : g.asEReal∗ u ≠ ⊥ :=
        conjugate_ne_bot_of_isProper hg_proper u
      have hdual_ne_bot : fenchelDualObjective f g u ≠ ⊥ := by
        rw [fenchelDualObjective_apply, EReal.add_ne_bot_iff]
        exact ⟨hf_conj_ne_bot, hg_conj_ne_bot⟩
      have hprimal_ne_bot : primalObjective f g x ≠ ⊥ := by
        rw [primalObjective_apply, EReal.add_ne_bot_iff]
        exact ⟨ne_of_gt (f x).2, ne_of_gt (g x).2⟩
      exact neg_right_le_of_add_nonneg hprimal_ne_bot hdual_ne_bot hnonneg
    · -- If `g` has empty effective domain, then `g x = ⊤`, so the primal value is `⊤`.
      have hxg : x ∉ effectiveDomain g := by
        intro hxg
        exact hg_dom ⟨x, hxg⟩
      have hg_top : (g x : EReal) = ⊤ :=
        value_eq_top_of_not_mem_effectiveDomain g hxg
      have hsum_top : (f x : EReal) + (g x : EReal) = ⊤ := by
        rw [hg_top]
        exact EReal.add_top_of_ne_bot (ne_of_gt (f x).2)
      rw [primalObjective_apply, hsum_top]
      exact le_top
  · -- If `f` has empty effective domain, then `f x = ⊤`, so the primal value is `⊤`.
    have hxf : x ∉ effectiveDomain f := by
      intro hxf
      exact hf_dom ⟨x, hxf⟩
    have hf_top : (f x : EReal) = ⊤ :=
      value_eq_top_of_not_mem_effectiveDomain f hxf
    have hsum_top : (f x : EReal) + (g x : EReal) = ⊤ := by
      rw [hf_top]
      exact EReal.top_add_of_ne_bot (ne_of_gt (g x).2)
    rw [primalObjective_apply, hsum_top]
    exact le_top

/-- Helper for Proposition 15 9: each fixed primal value bounds the infimum dual value from below
after negation. -/
private lemma neg_primalObjective_le_iInf_fenchelDualObjective
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    -primalObjective f g x ≤ ⨅ u : H, fenchelDualObjective f g u := by
  -- Infimize the pointwise weak-duality inequality over the dual variable.
  refine le_iInf ?_
  intro u
  have hpoint := primalObjective_ge_neg_dualObjective f g x u
  exact EReal.neg_le_of_neg_le hpoint

-- Proof sketch: combine the improper-case triviality with the pointwise estimate from part (1),
-- then pass to the infimum over `x` on the left and over `u` on the right.
/-- Proposition 15 9 (2): the infimum of the primal objective is bounded below by the negative of
the infimum of the dual objective. -/
theorem iInf_primalObjective_ge_neg_iInf_dualObjective
    (f g : H → Set.Ioi (⊥ : EReal)) :
    -(⨅ u : H, fenchelDualObjective f g u) ≤ ⨅ x : H, primalObjective f g x := by
  -- Infimize the fixed-`x` lower bound over the primal variable.
  refine le_iInf ?_
  intro x
  have hdual := neg_primalObjective_le_iInf_fenchelDualObjective f g x
  exact EReal.neg_le_of_neg_le hdual

end FenchelDuality

end ERealFunction
