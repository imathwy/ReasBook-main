import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Example_9_2_2_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Pointwise Rockafellar
open Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.1.3 studies the function
  `x ↦ inf {f y | y ∈ C + {x}}` attached to a convex function `f` and a convex set `C`.
- `core/canonical`: the owner abstractions are `indicatorFunction`, `infimal_convolution` / `□`,
  `Function.IsConvex`, the source formula `x ↦ sInf (f '' (C + {x}))` at
  `f : E → WithBotTop 𝕜`, and the continuity owner theorem from `Theorem_10_1`.
- `bridge/view`: the source formula is the indicator-specialized infimal convolution
  `((δ[𝕜](· | -C)) □ f) x`, identified with the translate infimum `sInf (f '' (C + {x}))`; the
  finite-valued textbook surface is recovered by specializing `f` to `f.toWithTopBot`.

Domain-style sampling used here:
- `infimal_convolution_indicator_neg_eq_sInf_image_translate`;
- `Function.IsConvex.indicator_neg_infimal_convolution`;
- the chapter bridge `Function.isConvex_coe_of_convexOn_univ`;
- the continuity owner theorem
  `Function.IsConvex.continuousOn`
  from Theorem 10.1.

Primitive data vs derived API:
- primitive inputs for convexity: the set `C`, the scalar `𝕜`, and an owner-level function
  `f : E → WithBotTop 𝕜` with the no-`⊥` guard `∀ y, ⊥ < f y` needed by the indicator-translate
  identity;
- primitive inputs for continuity: the same owner-level function in the real topological layer of
  Theorem 10.1, with the pointwise finite-above guard `∀ y, f y < ⊤`;
- derived API: the finite-valued source-facing corollaries obtained by specializing to
  `f.toWithTopBot` and `ConvexOn 𝕜 univ f`.
-/

section Pointwise

variable {E : Type*} [AddGroup E]
variable {α : Type*} [ConditionallyCompleteLattice α] [Add α] [Zero α]

private theorem indicator_neg_infimal_convolution_eq_sInf_image_translate
    (C : Set E) (f : E → WithBotTop α) (hf_bot : ∀ y : E, ⊥ < f y) :
    ((δ[α](· | -C)) □ f) =
      fun x ↦ sInf (f '' (C + {x})) := by
  funext x
  simpa using infimal_convolution_indicator_neg_eq_sInf_image_translate C f hf_bot x

end Pointwise

section Convex

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: rewrite the translate-infimum surface by the canonical identity from
-- Example 9.2.2.2, then apply convexity of the indicator-specialized infimal convolution.
/-- Canonical owner form of Theorem 10.1.3 (1): for `f : E → WithBotTop 𝕜`, if `C` is convex,
`f` is convex, and `f` avoids `⊥`, then `x ↦ sInf (f '' (C + {x}))` is convex. -/
theorem Function.IsConvex.sInf_image_translate_of_bot_lt
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜)
    (C : Set E) (hC_convex : Convex 𝕜 C) (hf_bot : ∀ y : E, ⊥ < f y) :
    (fun x ↦ sInf (f '' (C + {x}))).IsConvex 𝕜 := by
  rw [← indicator_neg_infimal_convolution_eq_sInf_image_translate C f hf_bot]
  exact hf_convex.indicator_neg_infimal_convolution C hC_convex

-- Proof sketch: this is the finite-valued specialization of
-- `Function.IsConvex.sInf_image_translate_of_bot_lt`; the no-`⊥` guard is automatic for
-- `f.toWithTopBot`.
/-- Canonical finite-valued owner form of Theorem 10.1.3 (1): if `f.toWithTopBot` is convex and
`C` is convex, then `x ↦ sInf (f.toWithTopBot '' (C + {x}))` is convex. -/
theorem Function.IsConvex.sInf_image_translate_toWithTopBot
    {f : E → 𝕜} (hf_convex : f.toWithTopBot.IsConvex 𝕜)
    (C : Set E) (hC_convex : Convex 𝕜 C) :
    (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))).IsConvex 𝕜 := by
  exact
    hf_convex.sInf_image_translate_of_bot_lt
      C hC_convex (fun y ↦ WithBotTop.bot_lt_coe (f y))

-- Proof sketch: specialize the canonical owner theorem above to `f.toWithTopBot` and discharge
-- the no-`⊥` guard by `WithBotTop.bot_lt_coe`; convert the convexity assumption with
-- `Function.isConvex_coe_of_convexOn_univ`.
/-- Source-facing form of Theorem 10.1.3 (1): if `f : E → 𝕜` is convex and `C ⊆ E` is convex,
then the translate-infimum function
`x ↦ inf {f y | y ∈ C + {x}}`, rendered as
`x ↦ sInf (f.toWithTopBot '' (C + {x}))`, is convex. -/
theorem Function.isConvex_sInf_image_translate_toWithTopBot_of_convexOn_univ
    (C : Set E) (hC_convex : Convex 𝕜 C) (f : E → 𝕜)
    (hf_convex : ConvexOn 𝕜 univ f) :
    (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))).IsConvex 𝕜 := by
  exact
    (Function.isConvex_coe_of_convexOn_univ hf_convex).sInf_image_translate_toWithTopBot
      C hC_convex

end Convex

section ContinuityAux

variable {E : Type*} [AddCommGroup E]
variable {α : Type*} [ConditionallyCompleteLattice α] [AddMonoid α]

private theorem indicator_neg_infimal_convolution_lt_top_of_nonempty
    (C : Set E) (hC_nonempty : C.Nonempty) (f : E → WithBotTop α)
    (hf_top : ∀ y : E, f y < ⊤) (x : E) :
    (((δ[α](· | -C)) □ f) x) < (⊤ : WithBotTop α) := by
  rcases hC_nonempty with ⟨c, hc⟩
  have hnegc : -c ∈ -C := by
    rwa [Set.mem_neg, neg_neg]
  have hle :
      (((δ[α](· | -C)) □ f) x) ≤
        f (x + c) := by
    rw [infimal_convolution_apply]
    refine iInf_le_of_le (-c) ?_
    simp [hnegc]
  exact lt_of_le_of_lt hle (hf_top (x + c))

end ContinuityAux

section Continuity

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply Theorem 10.1 on `univ` to
-- `g := ((δ[ℝ](· | -C)) □ f)`, using convexity from Example 9.2.2.2 and pointwise finiteness from
-- the nonempty-translate estimate.
/-- Nonempty-set owner form for Theorem 10.1.3 (2): if `C` is convex and nonempty, `f` is convex,
and `f` is finite from above, then `((δ[ℝ](· | -C)) □ f)` is continuous. -/
theorem Function.IsConvex.continuous_indicator_neg_infimal_convolution_of_nonempty_of_lt_top
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty)
    (hf_top : ∀ x : E, f x < ⊤) :
    Continuous (((δ[ℝ](· | -C)) □ f)) := by
  let g : E → WithBotTop ℝ := ((δ[ℝ](· | -C)) □ f)
  have hconv : g.IsConvex ℝ := by
    simpa [g] using hf_convex.indicator_neg_infimal_convolution C hC_convex
  have hdom : (univ : Set E) ⊆ dom(g) := by
    intro x _
    exact
      indicator_neg_infimal_convolution_lt_top_of_nonempty
        C hC_nonempty f hf_top x
  simpa [g, continuousOn_univ] using
    Function.IsConvex.continuousOn
      hconv isOpen_univ.isRelativelyOpen convex_univ hdom

-- Proof sketch: Example 9.2.2.2 gives convexity of `((δ[ℝ](· | -C)) □ f)`. If `C = ∅`, then
-- `δ[ℝ](· | -C)` is constantly `⊤`; the no-`⊥` guard on `f` makes the infimal convolution
-- constantly `⊤`. If `C` is nonempty, the private lemma above gives `((δ[ℝ](· | -C)) □ f) x < ⊤`
-- everywhere, so Theorem 10.1 applies on `univ`.
/-- Canonical owner form of Theorem 10.1.3 (2): for `f : E → WithBotTop ℝ`, if `C` is convex, `f`
is convex, `f` avoids `⊥`, and `f` is finite from above, then
`((δ[ℝ](· | -C)) □ f)` is continuous. -/
theorem Function.IsConvex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C)
    (hf_bot : ∀ x : E, ⊥ < f x) (hf_top : ∀ x : E, f x < ⊤) :
    Continuous (((δ[ℝ](· | -C)) □ f)) := by
  let g : E → WithBotTop ℝ := ((δ[ℝ](· | -C)) □ f)
  have hcont : Continuous g := by
    have hconv : g.IsConvex ℝ := by
      simpa [g] using
        hf_convex.indicator_neg_infimal_convolution C hC_convex
    by_cases hC_empty : C = ∅
    · have htop :
        g =
          fun _ : E ↦ (⊤ : WithBotTop ℝ) := by
          subst hC_empty
          have hdelta :
              (δ[ℝ](· | -∅)) = fun _ : E ↦ (⊤ : WithBotTop ℝ) := by
            funext y
            simp
          ext x
          change (((δ[ℝ](· | -∅)) □ f) x) = ⊤
          rw [hdelta, infimal_convolution_apply]
          have hconst : ∀ i : E, (⊤ : WithBotTop ℝ) + f (x - i) = ⊤ := by
            intro i
            exact WithBotTop.top_add_of_ne_bot (ne_of_gt (hf_bot (x - i)))
          simp [hconst]
      rw [htop]
      exact continuous_const
    · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
      simpa [g] using
        hf_convex.continuous_indicator_neg_infimal_convolution_of_nonempty_of_lt_top
          C hC_convex hC_nonempty hf_top
  simpa [g] using hcont

-- Proof sketch: rewrite by the indicator-translate identity from Example 9.2.2.2 and apply the
-- owner theorem above.
/-- Canonical source-form owner of Theorem 10.1.3 (2): under the same assumptions as
`Function.IsConvex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top`, the translate
infimum function `x ↦ sInf (f '' (C + {x}))` is continuous. -/
theorem Function.IsConvex.continuous_sInf_image_translate_of_bot_lt_of_lt_top
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C)
    (hf_bot : ∀ x : E, ⊥ < f x) (hf_top : ∀ x : E, f x < ⊤) :
    Continuous (fun x ↦ sInf (f '' (C + {x}))) := by
  rw [← indicator_neg_infimal_convolution_eq_sInf_image_translate C f hf_bot]
  exact
    hf_convex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top
      C hC_convex hf_bot hf_top

-- Proof sketch: specialize the owner theorem above to `f.toWithTopBot`, where both
-- `⊥ < f.toWithTopBot x` and `f.toWithTopBot x < ⊤` are immediate.
/-- Canonical finite-valued owner form of Theorem 10.1.3 (2): if `f.toWithTopBot` is convex and
`C` is convex, then `((δ[ℝ](· | -C)) □ f.toWithTopBot)` is continuous. -/
theorem Function.IsConvex.continuous_indicator_neg_infimal_convolution_toWithTopBot
    {f : E → ℝ} (hf_convex : f.toWithTopBot.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C) :
    Continuous (((δ[ℝ](· | -C)) □ f.toWithTopBot)) := by
  exact
    hf_convex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top
      C hC_convex
      (fun y ↦ WithBotTop.bot_lt_coe (f y))
      (fun y ↦ WithBotTop.coe_lt_top (f y))

-- Proof sketch: specialize the owner theorem to `f.toWithTopBot`, where both
-- `⊥ < f.toWithTopBot x` and `f.toWithTopBot x < ⊤` are immediate.
/-- Source-facing owner form of Theorem 10.1.3 (2): if `f : E → ℝ` is convex on `univ` and `C` is
convex, then `((δ[ℝ](· | -C)) □ f.toWithTopBot)` is continuous. -/
theorem continuous_indicator_neg_infimal_convolution_toWithTopBot_of_convexOn_univ
    (C : Set E) (hC_convex : Convex ℝ C) (f : E → ℝ)
    (hf_convex : ConvexOn ℝ univ f) :
    Continuous (((δ[ℝ](· | -C)) □ f.toWithTopBot)) := by
  exact
    Function.IsConvex.continuous_indicator_neg_infimal_convolution_toWithTopBot
      (hf_convex := Function.isConvex_coe_of_convexOn_univ hf_convex)
      C hC_convex

-- Proof sketch: specialize the canonical source-form owner theorem above to `f.toWithTopBot`.
/-- Canonical finite-valued source-form owner of Theorem 10.1.3 (2): if `f.toWithTopBot` is convex
and `C` is convex, then `x ↦ sInf (f.toWithTopBot '' (C + {x}))` is continuous. -/
theorem Function.IsConvex.continuous_sInf_image_translate_toWithTopBot
    {f : E → ℝ} (hf_convex : f.toWithTopBot.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C) :
    Continuous (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))) := by
  exact
    hf_convex.continuous_sInf_image_translate_of_bot_lt_of_lt_top
      C hC_convex
      (fun y ↦ WithBotTop.bot_lt_coe (f y))
      (fun y ↦ WithBotTop.coe_lt_top (f y))

-- Proof sketch: specialize the canonical source-form owner theorem above to `f.toWithTopBot`.
/-- Source-facing form of Theorem 10.1.3 (2): if `f : E → ℝ` is convex and `C ⊆ E` is convex,
then the translate-infimum function
`x ↦ inf {f y | y ∈ C + {x}}`, rendered as
`x ↦ sInf (f.toWithTopBot '' (C + {x}))`, depends continuously on `x`. -/
theorem continuous_sInf_image_translate_toWithTopBot_of_convexOn_univ
    (C : Set E) (hC_convex : Convex ℝ C) (f : E → ℝ)
    (hf_convex : ConvexOn ℝ univ f) :
    Continuous (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))) := by
  exact
    Function.IsConvex.continuous_sInf_image_translate_toWithTopBot
      (hf_convex := Function.isConvex_coe_of_convexOn_univ hf_convex)
      C hC_convex

end Continuity
