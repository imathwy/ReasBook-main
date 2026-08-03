import Mathlib
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap15.Corollary_15_15

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 15.16 is the explicit two-sided affine bound
  `f(x) + g(x) ≥ g(x) + ⟪x, v⟫ + g(v) ≥ 0`.
- `core/canonical`: the owner declarations are `primalObjective`,
  `exists_dual_vector_le_zero_of_pointwiseAdd_nonneg_and_conjugate_eq_comp`,
  and `fenchel_young_inequality`.
- `bridge/view`: the reflected-conjugate hypothesis `g.asEReal∗ = g.asERealᵛ`
  identifies Corollary 15.15 with the source-facing dual inequality
  `f.asEReal∗ v + (g v : EReal) ≤ 0`.
-/

section ExplicitInequalities

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Corollary 15 16: any point where an `]-∞,+∞]`-valued function is not `⊤` lies in
its effective domain, so the effective domain is nonempty. -/
private theorem effectiveDomain_nonempty_of_ne_top
    (h : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : (h x : EReal) ≠ ⊤) :
    (effectiveDomain h).Nonempty := by
  -- A finite value at `x` is exactly the domain-membership certificate needed for nonemptiness.
  refine ⟨x, ?_⟩
  simpa [mem_effectiveDomain_iff] using (lt_of_le_of_ne le_top hx)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Corollary 15 16: nonempty effective domain upgrades the canonical `EReal`
coercion of an `]-∞,+∞]`-valued function to a proper function. -/
private theorem isProper_asEReal_of_effectiveDomain_nonempty
    (h : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain h).Nonempty) :
    IsProper h.asEReal := by
  -- `]-∞,+∞]`-valued functions are never `⊥`, and nonempty effective domain supplies a finite
  -- point, so the `IsProper` owner conditions hold.
  refine ⟨fun y ↦ ne_of_gt (h y).2, ?_⟩
  simpa [effectiveDomain, dom] using hdom

-- Proof sketch: if `f x = +∞`, then the inequality is immediate. Otherwise `x` lies in the
-- effective domain of `f`, so `f.asEReal` is proper and Fenchel--Young applies at `(x, v)`.
-- Combining `⟪x, v⟫ ≤ f(x) + f^*(v)` with `f^*(v) + g(v) ≤ 0` gives the desired affine upper
-- bound.
/-- A dual vector with `f^*(v) + g(v) ≤ 0` gives the first inequality in the explicit form of
Corollary 15.16. -/
theorem affine_shift_le_primalObjective_of_conjugate_add_value_le_zero
    (f g : H → Set.Ioi (⊥ : EReal)) (v : H)
    (hv : f.asEReal∗ v + (g v : EReal) ≤ 0)
    (x : H) :
    (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) ≤
      primalObjective f g x := by
  by_cases hfx_top : (f x : EReal) = ⊤
  · -- Outside the effective domain, the primal objective is `⊤`, so the estimate is trivial.
    have hprimal_top : primalObjective f g x = ⊤ := by
      rw [primalObjective_apply, hfx_top]
      exact EReal.top_add_of_ne_bot (ne_of_gt (g x).2)
    rw [hprimal_top]
    exact le_top
  · have hf_dom : (effectiveDomain f).Nonempty :=
      effectiveDomain_nonempty_of_ne_top f hfx_top
    have hf_proper : IsProper f.asEReal :=
      isProper_asEReal_of_effectiveDomain_nonempty f hf_dom
    have hconj_ne_bot : f.asEReal∗ v ≠ ⊥ :=
      conjugate_ne_bot_of_isProper hf_proper v
    have hconj_ne_top : f.asEReal∗ v ≠ ⊤ := by
      intro htop
      have hsum_top : f.asEReal∗ v + (g v : EReal) = ⊤ := by
        rw [htop]
        exact EReal.top_add_of_ne_bot (ne_of_gt (g v).2)
      rw [hsum_top] at hv
      simp at hv
    have hinner_sub :
        (((⟪x, v⟫_ℝ : ℝ) : EReal) - f.asEReal∗ v) ≤ (f x : EReal) := by
      exact (EReal.sub_le_iff_le_add (.inl hconj_ne_bot) (.inl hconj_ne_top)).2
        (fenchel_young_inequality hf_proper x v)
    have hgv_le_neg_conj : (g v : EReal) ≤ -f.asEReal∗ v := by
      rw [← EReal.sub_nonpos, sub_eq_add_neg, neg_neg, add_comm]
      exact hv
    have hshift_le_fx :
        (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) ≤ (f x : EReal) := by
      calc
        (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal))
            ≤ (((⟪x, v⟫_ℝ : ℝ) : EReal) + (-f.asEReal∗ v)) := by
              simpa [add_comm] using
                add_le_add_right hgv_le_neg_conj (((⟪x, v⟫_ℝ : ℝ) : EReal))
        _ = (((⟪x, v⟫_ℝ : ℝ) : EReal) - f.asEReal∗ v) := by
              simp [sub_eq_add_neg]
        _ ≤ (f x : EReal) := hinner_sub
    -- Add the common `g x` term to recover the primal objective.
    calc
      (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal))
          ≤ (g x : EReal) + (f x : EReal) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right hshift_le_fx (g x : EReal)
      _ = primalObjective f g x := by
            rw [primalObjective_apply, add_comm]

-- Proof sketch: if `g x = +∞`, the inequality is immediate. Otherwise `x` lies in the effective
-- domain of `g`, so Fenchel--Young applies to `g` at `(x, -v)`. The reflection identity rewrites
-- `g^*(-v)` as `g(v)`, and rearranging yields the lower affine bound.
/-- The reflected-conjugate identity `g^* = gᵛ` gives the second inequality in the explicit form of
Corollary 15.16. -/
theorem zero_le_affine_shift_of_conjugate_eq_reflection
    (g : H → Set.Ioi (⊥ : EReal)) (hg_reflected : g.asEReal∗ = g.asERealᵛ)
    (x v : H) :
    (0 : EReal) ≤ (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) := by
  by_cases hgx_top : (g x : EReal) = ⊤
  · -- Outside the effective domain, the affine shift is already `⊤`.
    have hshift_top :
        (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) = ⊤ := by
      rw [hgx_top]
      exact EReal.top_add_of_ne_bot <|
        (EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, ne_of_gt (g v).2⟩)
    rw [hshift_top]
    exact le_top
  · have hg_dom : (effectiveDomain g).Nonempty :=
      effectiveDomain_nonempty_of_ne_top g hgx_top
    have hg_proper : IsProper g.asEReal :=
      isProper_asEReal_of_effectiveDomain_nonempty g hg_dom
    have hfy :
        (((⟪x, -v⟫_ℝ : ℝ) : EReal)) ≤ (g x : EReal) + g.asEReal∗ (-v) :=
      fenchel_young_inequality hg_proper x (-v)
    have hconj_eval : g.asEReal∗ (-v) = (g v : EReal) := by
      calc
        g.asEReal∗ (-v) = g.asERealᵛ (-v) := by rw [hg_reflected]
        _ = (g v : EReal) := by simp
    have hneg_pair_le_aux :
        (-(((⟪x, v⟫_ℝ : ℝ) : EReal))) ≤ (g x : EReal) + g.asEReal∗ (-v) := by
      simpa [inner_neg_right] using hfy
    have hneg_pair_le :
        (-(((⟪x, v⟫_ℝ : ℝ) : EReal))) ≤ (g x : EReal) + (g v : EReal) := by
      calc
        (-(((⟪x, v⟫_ℝ : ℝ) : EReal))) ≤ (g x : EReal) + g.asEReal∗ (-v) := hneg_pair_le_aux
        _ = (g x : EReal) + (g v : EReal) := by rw [hconj_eval]
    have hleft_zero :
        (((⟪x, v⟫_ℝ : ℝ) : EReal) + (-(((⟪x, v⟫_ℝ : ℝ) : EReal)))) = 0 := by
      simpa [sub_eq_add_neg] using
        (EReal.sub_self (x := (((⟪x, v⟫_ℝ : ℝ) : EReal))) (EReal.coe_ne_top _)
          (EReal.coe_ne_bot _))
    -- Add back the pairing term so the left-hand side collapses to `0`.
    calc
      (0 : EReal) = (((⟪x, v⟫_ℝ : ℝ) : EReal) + (-(((⟪x, v⟫_ℝ : ℝ) : EReal)))) := by
        symm
        exact hleft_zero
      _ ≤ (((⟪x, v⟫_ℝ : ℝ) : EReal) + ((g x : EReal) + (g v : EReal))) := by
        exact add_le_add_right hneg_pair_le (((⟪x, v⟫_ℝ : ℝ) : EReal))
      _ = (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) := by
        simp [add_assoc, add_comm]

end ExplicitInequalities

section ExplicitCorollary

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Corollary 15 16: the reflected-conjugate identity is exactly composition with the
negative identity map. -/
private theorem conjugate_eq_comp_negative_id_of_reflection
    (g : H → Set.Ioi (⊥ : EReal)) (hg_reflected : g.asEReal∗ = g.asERealᵛ) :
    g.asEReal∗ = g.asEReal ∘ (-ContinuousLinearMap.id ℝ H) := by
  -- Evaluate the reflection identity pointwise and unfold both sides at the negative identity.
  funext u
  calc
    g.asEReal∗ u = g.asERealᵛ u := by rw [hg_reflected]
    _ = (g.asEReal ∘ (-ContinuousLinearMap.id ℝ H)) u := by
      simp [Function.comp]

/-- Helper for Corollary 15 16: Corollary 15.15 specialized to the negative identity produces a
dual vector satisfying the source-facing inequality `f^*(v) + g(v) ≤ 0`. -/
private theorem exists_dual_vector_with_conjugate_add_value_le_zero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g))
    (hg_reflected : g.asEReal∗ = g.asERealᵛ)
    (hfg_nonneg : ∀ x : H, (0 : EReal) ≤ primalObjective f g x) :
    ∃ v : H, f.asEReal∗ v + (g v : EReal) ≤ 0 := by
  -- Route correction: use the earlier Corollary 15.15 with `L = -id` instead of the later
  -- composite-attainment theorem, so the proof stays inside the dependency-closed prefix.
  have hg_comp : g.asEReal∗ = g.asEReal ∘ (-ContinuousLinearMap.id ℝ H) :=
    conjugate_eq_comp_negative_id_of_reflection g hg_reflected
  obtain ⟨u, hu⟩ :=
    exists_dual_vector_le_zero_of_pointwiseAdd_nonneg_and_conjugate_eq_comp
      f g hf hg hsri (-ContinuousLinearMap.id ℝ H) hfg_nonneg hg_comp
  -- Negating the Corollary 15.15 witness removes the reflected argument.
  refine ⟨-u, ?_⟩
  simpa using hu

-- Proof sketch: Corollary 15.15 specialized to `L = -id` supplies the dual witness. The
-- reflected-conjugate hypothesis identifies its conclusion with `f.asEReal∗ v + g(v) ≤ 0`, and
-- the two explicit inequality lemmas finish.
/-- Corollary 15 16: if `f, g ∈ Γ₀(H)`, if `0 ∈ sri (dom f - dom g)`, if `g^* = gᵛ`, and if
`f + g ≥ 0`, then there exists `v ∈ H` such that for every `x ∈ H`,
`f(x) + g(x) ≥ g(x) + ⟪x, v⟫ + g(v) ≥ 0`. -/
lemma exists_dual_vector_with_explicit_bounds_of_primalObjective_nonneg_and_conjugate_eq_reflection
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g))
    (hg_reflected : g.asEReal∗ = g.asERealᵛ)
    (hfg_nonneg : ∀ x : H, (0 : EReal) ≤ primalObjective f g x) :
    ∃ v : H, ∀ x : H,
      (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) ≤
        (f x : EReal) + (g x : EReal) ∧
      (0 : EReal) ≤ (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) := by
  obtain ⟨v, hv⟩ :=
    exists_dual_vector_with_conjugate_add_value_le_zero
      f g hf hg hsri hg_reflected hfg_nonneg
  refine ⟨v, ?_⟩
  intro x
  have hupper :
      (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) ≤
        primalObjective f g x :=
    affine_shift_le_primalObjective_of_conjugate_add_value_le_zero f g v hv x
  have hlower :
      (0 : EReal) ≤
        (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) :=
    zero_le_affine_shift_of_conjugate_eq_reflection g hg_reflected x v
  constructor
  · -- The dual inequality supplies the upper affine bound.
    simpa [primalObjective_apply, add_assoc, add_left_comm, add_comm] using hupper
  · -- The reflection identity supplies the lower affine bound.
    simpa using hlower

end ExplicitCorollary

end FenchelDuality

end ERealFunction
