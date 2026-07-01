import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap05.Example_23_0_7
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_8

-- Declarations for this item were appended by the statement pipeline.

noncomputable section

open scoped BigOperators Pointwise Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {m : ℕ}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem indicator_isProper_of_nonempty
    (C : Set E) (hC : C.Nonempty) :
    (indicator ℝ C : E → EReal).IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨?_, ?_⟩
  · rcases hC with ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩
  · intro x
    by_cases hx : x ∈ C <;> simp [indicator_def, hx]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem sum_indicator_eq_indicator_iInter
    (C : Fin m → Set E) :
    (∑ i, indicator ℝ (C i)) = indicator ℝ (⋂ i, C i) := by
  funext x
  by_cases hx : ∀ i : Fin m, x ∈ C i
  · have hmem : x ∈ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have hzero : ∀ i : Fin m, indicator ℝ (C i) x = 0 := by
      intro i
      simp [indicator_def, hx i]
    have hsum_zero : (∑ i, indicator ℝ (C i) x) = 0 := by
      calc
        (∑ i, indicator ℝ (C i) x) = ∑ i, (0 : EReal) := by
          congr with i
          exact hzero i
        _ = 0 := by simp
    simpa [indicator_def, hmem] using hsum_zero
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hnotmem : x ∉ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have hsum_ne_bot :
        Finset.sum (Finset.univ.erase i) (fun j ↦ indicator ℝ (C j) x) ≠ (⊥ : EReal) := by
      refine WithBotTop.sum_ne_bot_of_forall_ne_bot ?_
      intro j hj
      by_cases hjx : x ∈ C j
      · rw [indicator_def, if_pos hjx]
        exact WithBotTop.zero_ne_bot
      · rw [indicator_def, if_neg hjx]
        exact WithBotTop.top_ne_bot
    have htail_bot :
        ⊥ < Finset.sum (Finset.univ.erase i) (fun j ↦ indicator ℝ (C j) x) := by
      simpa using (WithBot.bot_lt_iff_ne_bot.mpr hsum_ne_bot)
    have hsum_top : (∑ j, indicator ℝ (C j) x) = ⊤ := by
      rw [← Finset.add_sum_erase Finset.univ (fun j ↦ indicator ℝ (C j) x) (Finset.mem_univ i)]
      have hi_top : indicator ℝ (C i) x = ⊤ := by
        simp [indicator_def, hi]
      rw [hi_top]
      simpa using WithBotTop.top_add_of_ne_bot (bot_lt_iff_ne_bot.mp htail_bot)
    simpa [indicator_def, hnotmem] using hsum_top

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.8.1 is the normal-cone formula for a finite intersection of convex
  sets, together with the mixed polyhedral-prefix qualification.
- `core/canonical`: the relevant owner surfaces already present in the project are
  `N[ℝ](x | C)`, the relative-interior notation `ri[ℝ](C)`, the pointwise indicator
  `δ[ℝ](· | C)`, `s.IsPolyhedral ℝ`, and the Chapter 23 finite-sum subdifferential equalities.
- `bridge/view`: the corollary is obtained by applying Theorem 23.8 to indicator functions and
  then transporting the result back to sets via the indicator-function normal-cone bridge; no new
  wrapper around subdifferentials or intersections is introduced.
-/

-- Proof sketch: apply
-- `Function.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom`
-- to the indicator family `i ↦ δ[ℝ](· | C i)`. Convexity of each summand is
-- `indicator_isConvex_iff`, its relative domain is `ri[ℝ](C i)`, the pointwise sum is
-- the indicator of `⋂ i, C i`, and `Function.subdifferentialAt_indicatorFunction_eq_normalCone`
-- identifies the resulting subdifferentials with the corresponding normal cones.
/-- Corollary 23.8.1 (1): if convex sets `C 0, …, C (m - 1)` in a finite-dimensional real inner
product space have relative interiors with a common point, then the normal cone of their
intersection at `x` is the finite Minkowski sum of the individual normal cones at `x`. -/
theorem normalCone_iInter_eq_sum_normalCone_of_common_ri
    (C : Fin m → Set E)
    (hC_convex : ∀ i : Fin m, Convex ℝ (C i))
    (hri : (⋂ i, ri[ℝ](C i)).Nonempty)
    (x : E) :
    (N[ℝ](x | ⋂ i, C i) : Set E) = ∑ i, (N[ℝ](x | C i) : Set E) := by
  let f : Fin m → E → EReal := fun i ↦ indicator ℝ (C i)
  have hC_nonempty : ∀ i : Fin m, (C i).Nonempty := by
    rcases hri with ⟨y, hy⟩
    have hy : ∀ i : Fin m, y ∈ ri[ℝ](C i) := by
      simpa [Set.mem_iInter] using hy
    intro i
    exact ⟨y, intrinsicInterior_subset (hy i)⟩
  have hf_convex : ∀ i : Fin m, (f i).IsConvex ℝ := by
    intro i
    simpa [f] using ((indicator_isConvex_iff (C i)).2 (hC_convex i) :
      (indicator ℝ (C i) : E → EReal).IsConvex ℝ)
  have hf_proper : ∀ i : Fin m, (f i).IsProper := by
    intro i
    simpa [f] using (indicator_isProper_of_nonempty (C i) (hC_nonempty i) :
      (indicator ℝ (C i) : E → EReal).IsProper)
  have hri_f : (⋂ i, riDom[ℝ](f i)).Nonempty := by
    rcases hri with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro i
    have hyi : y ∈ ri[ℝ](C i) := (Set.mem_iInter.mp hy) i
    change y ∈ ri[ℝ](effectiveDomain (f i))
    change y ∈ ri[ℝ](effectiveDomain ((indicator ℝ (C i) : E → EReal)))
    simpa [effectiveDomain_indicator] using hyi
  simpa [f, sum_indicator_eq_indicator_iInter,
    Function.subdifferentialAt_indicatorFunction_eq_normalCone] using
    Function.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom
      f hf_convex hf_proper hri_f x

-- Proof sketch: again apply Theorem 23.8, now in its mixed-domain polyhedral-prefix form, to the
-- indicator family `i ↦ δ[ℝ](· | C i)`. The prefix polyhedral hypotheses transfer through
-- `Function.HasPolyhedralEpigraph.indicator_iff_isPolyhedral`, the suffix convexity through
-- `indicator_isConvex_iff`, the mixed common-point hypothesis becomes the theorem's
-- domain/relative-domain condition, and the indicator-function subdifferentials are the normal
-- cones by `Function.subdifferentialAt_indicatorFunction_eq_normalCone`.
/-- Corollary 23.8.1 (2): if `C 0, …, C (k - 1)` are polyhedral and the family
`C 0, …, C (k - 1), ri[ℝ](C k), …, ri[ℝ](C (m - 1))` has a common point, then the same normal-cone
sum formula holds for the intersection `⋂ i, C i`. -/
theorem normalCone_iInter_eq_sum_normalCone_of_polyhedralPrefix_mixedCommonPoint
    (C : Fin m → Set E) (k : ℕ)
    (hC_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → Convex ℝ (C i))
    (hC_poly : ∀ i : Fin m, (i : ℕ) < k → (C i).IsPolyhedral ℝ)
    (hcommon :
      ∃ y : E,
        (∀ i : Fin m, (i : ℕ) < k → y ∈ C i) ∧
          ∀ i : Fin m, k ≤ (i : ℕ) → y ∈ ri[ℝ](C i))
    (x : E) :
    (N[ℝ](x | ⋂ i, C i) : Set E) = ∑ i, (N[ℝ](x | C i) : Set E) := by
  let f : Fin m → E → EReal := fun i ↦ indicator ℝ (C i)
  have hC_nonempty : ∀ i : Fin m, (C i).Nonempty := by
    rcases hcommon with ⟨y, hy_prefix, hy_suffix⟩
    intro i
    by_cases hik : (i : ℕ) < k
    · exact ⟨y, hy_prefix i hik⟩
    · exact ⟨y, intrinsicInterior_subset (hy_suffix i (Nat.le_of_not_gt hik))⟩
  have hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex ℝ := by
    intro i hik
    simpa [f] using ((indicator_isConvex_iff (C i)).2 (hC_suffixConvex i hik) :
      (indicator ℝ (C i) : E → EReal).IsConvex ℝ)
  have hf_proper : ∀ i : Fin m, (f i).IsProper := by
    intro i
    simpa [f] using (indicator_isProper_of_nonempty (C i) (hC_nonempty i) :
      (indicator ℝ (C i) : E → EReal).IsProper)
  have hpoly : f.HasPolyhedralPrefix k := by
    intro i hik
    simpa [f] using
      ((Function.HasPolyhedralEpigraph.indicator_iff_isPolyhedral (𝕜 := ℝ) (E := E) (C i)).2
        (hC_poly i hik) :
      (indicator ℝ (C i)).HasPolyhedralEpigraph)
  have hdom : f.HasMixedPrefixDomainPoint k := by
    rcases hcommon with ⟨y, hy_prefix, hy_suffix⟩
    refine ⟨y, ?_, ?_⟩
    · intro i hik
      simpa [f] using hy_prefix i hik
    · intro i hik
      simpa [f, riDom_eq_intrinsicInterior_dom, effectiveDomain_indicator] using hy_suffix i hik
  simpa [f, sum_indicator_eq_indicator_iInter,
    Function.subdifferentialAt_indicatorFunction_eq_normalCone] using
    Function.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralPrefix_mixedDomain
      f k hf_suffixConvex hf_proper hpoly hdom x

end
