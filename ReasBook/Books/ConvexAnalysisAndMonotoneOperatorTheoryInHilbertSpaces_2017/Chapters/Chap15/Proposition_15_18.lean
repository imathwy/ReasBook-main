import Mathlib
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap15.Definition_15_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Proposition 15 18: outside the effective domain, an `]-∞,+∞]`-valued function
takes the value `⊤`. -/
lemma coe_eq_top_of_not_mem_effectiveDomain
    {X : Type*} (φ : X → Set.Ioi (⊥ : EReal)) {x : X}
    (hx : x ∉ effectiveDomain φ) :
    (φ x : EReal) = ⊤ := by
  -- Convert failure of effective-domain membership into failure of finiteness.
  have hnot_lt : ¬ ((φ x : EReal) < ⊤) := by
    simpa [mem_effectiveDomain_iff] using hx
  -- In `EReal`, the only non-`< ⊤` value above `⊥` is `⊤` itself.
  exact le_antisymm le_top (not_lt.mp hnot_lt)

/-- Helper for Proposition 15 18: the adjoint pairings from the two Fenchel--Young inequalities
cancel exactly. -/
lemma adjoint_pairings_cancel
    (L : H →L[ℝ] K) (x : H) (v : K) :
    (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) + ((⟪L x, v⟫_ℝ : ℝ) : EReal)) = 0 := by
  -- Rewrite the first pairing through the adjoint and cancel in the real scalar field first.
  have hreal : (-⟪L x, v⟫_ℝ : ℝ) + ⟪L x, v⟫_ℝ = 0 := by
    simp
  have hcancel :
      ((-⟪L x, v⟫_ℝ : ℝ) : EReal) + ((⟪L x, v⟫_ℝ : ℝ) : EReal) = 0 := by
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  simpa [ContinuousLinearMap.adjoint_inner_right] using hcancel

-- Proof sketch: apply the Fenchel--Young inequality to `f` at `(x, -L.adjoint v)` and to `g` at
-- `(L x, v)`, then rewrite the first pairing with `ContinuousLinearMap.adjoint_inner_right` so the
-- two pairings cancel. This is the composite-objective analogue of Proposition 15.9 in the
-- source-facing adjoint form from Definition 15.19.
/-- Proposition 15 18 (1): every primal value `f(x) + g(Lx)` dominates the negative of the
corresponding adjoint-based composite dual objective. -/
theorem compositePrimalObjective_ge_neg_compositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (x : H) (v : K) :
    compositePrimalObjective f g L x ≥ -(compositeDualObjective f g L v) := by
  by_cases hf_dom : (effectiveDomain f).Nonempty
  · by_cases hg_dom : (effectiveDomain g).Nonempty
    · -- In the proper case, add the two Fenchel--Young inequalities and cancel the pairings.
      have hf_proper : IsProper f.asEReal := by
        refine ⟨?_, ?_⟩
        · intro z
          exact ne_of_gt (f z).2
        · simpa [effectiveDomain, dom] using hf_dom
      have hg_proper : IsProper g.asEReal := by
        refine ⟨?_, ?_⟩
        · intro z
          exact ne_of_gt (g z).2
        · simpa [effectiveDomain, dom] using hg_dom
      have hsum :
          (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) + ((⟪L x, v⟫_ℝ : ℝ) : EReal)) ≤
            (((f x : EReal) + f.asEReal∗ (-(L.adjoint v))) +
              ((g (L x) : EReal) + g.asEReal∗ v)) := by
        exact add_le_add
          (fenchel_young_inequality hf_proper x (-(L.adjoint v)))
          (fenchel_young_inequality hg_proper (L x) v)
      have hnonneg :
          (0 : EReal) ≤ compositePrimalObjective f g L x + compositeDualObjective f g L v := by
        -- Normalize the right-hand side to the owner primal and dual objectives.
        calc
          (0 : EReal)
              = (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) + ((⟪L x, v⟫_ℝ : ℝ) : EReal)) := by
                symm
                exact adjoint_pairings_cancel L x v
          _ ≤ (((f x : EReal) + f.asEReal∗ (-(L.adjoint v))) +
                ((g (L x) : EReal) + g.asEReal∗ v)) := hsum
          _ = compositePrimalObjective f g L x + compositeDualObjective f g L v := by
                simp [compositePrimalObjective_apply, compositeDualObjective_apply,
                  add_assoc, add_left_comm, add_comm]
      have hdual_conj_ne_bot : f.asEReal∗ (-(L.adjoint v)) ≠ ⊥ :=
        conjugate_ne_bot_of_isProper hf_proper (-(L.adjoint v))
      have hg_conj_ne_bot : g.asEReal∗ v ≠ ⊥ :=
        conjugate_ne_bot_of_isProper hg_proper v
      have hdual_ne_bot : compositeDualObjective f g L v ≠ ⊥ := by
        rw [compositeDualObjective_apply, EReal.add_ne_bot_iff]
        exact ⟨hdual_conj_ne_bot, hg_conj_ne_bot⟩
      have hprimal_ne_bot : compositePrimalObjective f g L x ≠ ⊥ := by
        rw [compositePrimalObjective_apply, EReal.add_ne_bot_iff]
        exact ⟨ne_of_gt (f x).2, ne_of_gt (g (L x)).2⟩
      have hneg_dual_ne_top : -compositeDualObjective f g L v ≠ ⊤ := by
        simpa using hdual_ne_bot
      have hsub_nonneg :
          0 ≤ compositePrimalObjective f g L x - -compositeDualObjective f g L v := by
        -- Rewrite the normalized nonnegativity statement as a subtraction inequality.
        simpa [sub_eq_add_neg, neg_neg] using hnonneg
      exact (EReal.sub_nonneg (Or.inr hneg_dual_ne_top) (Or.inl hprimal_ne_bot)).1 hsub_nonneg
    · -- If `g` has empty effective domain, then `g (L x) = ⊤`, so the primal value is `⊤`.
      have hxg : L x ∉ effectiveDomain g := by
        intro hxg
        exact hg_dom ⟨L x, hxg⟩
      have hg_top : (g (L x) : EReal) = ⊤ :=
        coe_eq_top_of_not_mem_effectiveDomain g hxg
      have hsum_top : (f x : EReal) + (g (L x) : EReal) = ⊤ := by
        rw [hg_top]
        exact EReal.add_top_of_ne_bot (ne_of_gt (f x).2)
      rw [compositePrimalObjective_apply, hsum_top]
      exact le_top
  · -- If `f` has empty effective domain, then `f x = ⊤`, so the primal value is `⊤`.
    have hxf : x ∉ effectiveDomain f := by
      intro hxf
      exact hf_dom ⟨x, hxf⟩
    have hf_top : (f x : EReal) = ⊤ :=
      coe_eq_top_of_not_mem_effectiveDomain f hxf
    have hsum_top : (f x : EReal) + (g (L x) : EReal) = ⊤ := by
      rw [hf_top]
      exact EReal.top_add_of_ne_bot (ne_of_gt (g (L x)).2)
    rw [compositePrimalObjective_apply, hsum_top]
    exact le_top

/-- Helper for Proposition 15 18: each fixed composite primal value bounds the composite dual
optimal value from below after negation. -/
lemma neg_composite_primal_objective_le_compositeDualOptimalValue
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (x : H) :
    -compositePrimalObjective f g L x ≤ compositeDualOptimalValue f g L := by
  rw [compositeDualOptimalValue_def]
  -- Infimize the pointwise weak-duality inequality over the dual variable.
  refine le_sInf ?_
  rintro y ⟨v, rfl⟩
  have hpoint := compositePrimalObjective_ge_neg_compositeDualObjective f g L x v
  exact EReal.neg_le_of_neg_le hpoint

-- Proof sketch: apply the pointwise inequality from clause (1) for each `x` and fixed `v`, take
-- the infimum over `x`, and then take the infimum over `v` on the dual side.
/-- Clause (2) of Proposition 15 18: the primal optimal value of `x ↦ f(x) + g(Lx)` is bounded
below by the
negative of the corresponding adjoint-based composite dual optimal value. -/
theorem compositePrimalOptimalValue_ge_neg_compositeDualOptimalValue
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    compositePrimalOptimalValue f g L ≥ -(compositeDualOptimalValue f g L) := by
  rw [compositePrimalOptimalValue_def]
  -- Infimize the fixed-`x` lower bound over the primal variable.
  refine le_sInf ?_
  rintro y ⟨x, rfl⟩
  have hdual :=
    neg_composite_primal_objective_le_compositeDualOptimalValue f g L x
  exact EReal.neg_le_of_neg_le hdual

end FenchelRockafellarDuality

end ERealFunction
