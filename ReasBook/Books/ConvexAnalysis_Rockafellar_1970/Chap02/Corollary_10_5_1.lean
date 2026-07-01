import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_10_1_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_5

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set
open Filter
open scoped Rockafellar

variable {𝕜 : Type*} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 10.5.1 assumes finiteness of the ray-quotient liminf
  `liminf_{λ → +∞} f (λ y) / λ` for every direction `y` and concludes that the finite convex
  function `f` is globally Lipschitz on a finite-dimensional normed space over an ordered normed
  field. The textbook `R^n` statement is the specialization `𝕜 = ℝ` and
  `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: the owner abstractions already present in the project are
  `ConvexOn 𝕜 univ f` for the finite-valued convexity surface,
  `LowerSemicontinuous (f.toWithBotTop)` as the primitive closedness input to the Chapter 8
  difference-quotient bridge,
  `exists_lipschitzWith_of_recessionFunction_finite_everywhere`, and the global Lipschitz
  predicate `LipschitzWith`.
- `bridge/view`: the source ray quotient is a source-facing presentation of finiteness of the
  recession function of the canonical `WithBotTop 𝕜` lift. The bridge remains proof-level here,
  without introducing a separate public declaration, and the owner-level Lipschitz conclusion is
  exposed directly.

Domain-style sampling used here:
- `ConvexOn 𝕜 univ f`;
- `LowerSemicontinuous`;
- `Function.tendsto_differenceQuotient_atTop_recessionFunction`;
- `Function.recessionFunction`;
- `exists_lipschitzWith_of_recessionFunction_finite_everywhere`.

Primitive data vs derived API:
- primitive inputs for the core owner theorem below: a globally convex function `f : E → 𝕜`,
  lower semicontinuity of `f.toWithBotTop`, and the source-visible ray-quotient
  liminf hypothesis in every direction;
- source-facing bridge: lower semicontinuity is recovered from finite-valued convexity of the
  canonical lift;
- derived output: existence of a global Lipschitz constant for `f`.
-/

private theorem recessionFunction_lt_top_of_liminf_ray_quotient_lt_top
    [FiniteDimensional 𝕜 E]
    (f : E → 𝕜) (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hf_closed : LowerSemicontinuous (f.toWithBotTop))
    (y : E)
    (hliminf :
      liminf (fun t : 𝕜 ↦ (f (t • y) : WithBotTop 𝕜) / (t : WithBotTop 𝕜)) atTop < ⊤) :
    ((f.toWithBotTop)₀⁺) y < ⊤ := by
  let g : E → WithBotTop 𝕜 := f.toWithBotTop
  have hg_convex : g.IsConvex 𝕜 := by
    simpa [g, Function.IsConvex] using
      (Function.isConvex_coe_of_convexOn_univ (f := f) hf_convex)
  have hg_proper : g.IsProper := by
    refine ⟨⟨0, ?_⟩, ?_⟩
    · change g 0 < ⊤
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
    · intro x
      simp [g, Function.toWithBotTop]
  have hg_closed : LowerSemicontinuous g := by
    simpa [g] using hf_closed
  let q : 𝕜 → WithBotTop 𝕜 := fun t ↦ (f (t • y) : WithBotTop 𝕜) / (t : WithBotTop 𝕜)
  obtain ⟨d, hd_left, hd_right⟩ := exists_between hliminf
  have hd_ne_bot : d ≠ (⊥ : WithBotTop 𝕜) := by
    intro hd
    exact (WithBot.not_lt_bot (liminf q atTop)) (hd ▸ hd_left)
  obtain ⟨d, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd_ne_bot
  have hd_lt_top : d < (⊤ : WithTop 𝕜) := by
    exact WithBot.coe_lt_coe.mp (by simpa using hd_right)
  have hd_ne_top : d ≠ (⊤ : WithTop 𝕜) := ne_of_lt hd_lt_top
  obtain ⟨c, rfl⟩ := WithTop.ne_top_iff_exists.mp hd_ne_top
  have hq_lt : liminf q atTop < (c : WithBotTop 𝕜) := by
    simpa using hd_left
  have hq_cobounded : atTop.IsCoboundedUnder (· ≥ ·) q := by
    isBoundedDefault
  have hfreq_q : ∃ᶠ t : 𝕜 in atTop, q t < (c : WithBotTop 𝕜) :=
    frequently_lt_of_liminf_lt hq_cobounded hq_lt
  have hfreq_dq :
      ∃ᶠ t : 𝕜 in atTop,
        (((f (t • y) - f 0) / t : 𝕜) : WithBotTop 𝕜) < (c + |f 0| : WithBotTop 𝕜) := by
    refine (hfreq_q.and_eventually <| eventually_ge_atTop (1 : 𝕜)).mono ?_
    intro t ht
    rcases ht with ⟨hq, ht⟩
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    have hq' : f (t • y) / t < c := by
      have hqE : (((f (t • y) / t : 𝕜) : WithBotTop 𝕜) < (c : WithBotTop 𝕜)) := by
        simpa [q] using hq
      exact WithBotTop.coe_lt_coe.mp hqE
    have hdiv : -(f 0 / t) ≤ |f 0| := by
      have habs_div : |f 0 / t| ≤ |f 0| := by
        calc
          |f 0 / t| = |f 0| / |t| := by rw [abs_div]
          _ ≤ |f 0| / 1 := by
            gcongr
            simpa [abs_of_nonneg ht0.le] using ht
          _ = |f 0| := by ring
      exact (neg_le_abs _).trans habs_div
    have hdq' : (f (t • y) - f 0) / t < c + |f 0| := by
      calc
        (f (t • y) - f 0) / t = f (t • y) / t + -(f 0 / t) := by
          field_simp [ht_ne]
          ring
        _ < c + |f 0| := add_lt_add_of_lt_of_le hq' hdiv
    exact WithBotTop.coe_lt_coe.mpr hdq'
  have h_tendsto :
      Tendsto (fun t : 𝕜 ↦ (((f (t • y) - f 0) / t : 𝕜) : WithBotTop 𝕜)) atTop
        (nhds (((f.toWithBotTop)₀⁺) y)) := by
    have hg0 : (0 : E) ∈ dom(g) := by
      rw [mem_effectiveDomain]
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
    have h_tendsto_g :
        Tendsto (fun t : 𝕜 ↦ (g (0 + t • y) - g 0) / (t : WithBotTop 𝕜)) atTop
          (nhds (((g)₀⁺) y)) :=
      Function.tendsto_differenceQuotient_atTop_recessionFunction
        g hg_convex (fun z => hg_proper.ne_bot z) hg_closed hg0 y
    convert h_tendsto_g using 1
    · funext t
      simp only [WithBotTop.coe_div, WithBotTop.div_eq_mul_inv, zero_add, WithBotTop.sub_eq_add_neg]
      conv_lhs =>
        congr
        rw [sub_eq_add_neg, WithBotTop.coe_add, WithBotTop.coe_neg]
  have h_liminf : ((f.toWithBotTop)₀⁺) y ≤ (c + |f 0| : WithBotTop 𝕜) := by
    rw [← h_tendsto.liminf_eq]
    exact liminf_le_of_frequently_le' <| hfreq_dq.mono fun _ ht ↦ ht.le
  have h_recession_lt_top : ((f.toWithBotTop)₀⁺) y < ⊤ := by
    exact lt_of_le_of_lt h_liminf <| WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  exact h_recession_lt_top

-- Proof sketch: translate the source ray-quotient hypothesis into the owner finiteness condition
-- `dom((f.toWithBotTop)₀⁺) = univ` for the recession function of the canonical
-- `WithBotTop 𝕜` lift using the Chapter 8
-- difference-quotient limit theorem at the base point `0`. Then apply
-- Theorem 10.5's owner-level Lipschitz criterion
-- `exists_lipschitzWith_of_recessionFunction_finite_everywhere`.
/-- Core owner form of Corollary 10.5.1: if a finite convex function `f : E → 𝕜`
has lower-semicontinuous canonical lift `f.toWithBotTop`, and every ray-quotient
liminf is finite, then `f` is globally Lipschitz. -/
theorem exists_lipschitzWith_of_forall_liminf_ray_quotient_lt_top_of_lowerSemicontinuous
    [FiniteDimensional 𝕜 E]
    (f : E → 𝕜) (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hf_closed : LowerSemicontinuous (f.toWithBotTop))
    (hliminf : ∀ y : E,
      liminf (fun t : 𝕜 ↦ (f (t • y) : WithBotTop 𝕜) / (t : WithBotTop 𝕜)) atTop < ⊤) :
    ∃ α : NNReal, LipschitzWith α f := by
  refine exists_lipschitzWith_of_recessionFunction_finite_everywhere f hf_convex ?_
  ext y
  constructor
  · intro _
    simp
  · intro _
    simpa [mem_effectiveDomain] using
      recessionFunction_lt_top_of_liminf_ray_quotient_lt_top f hf_convex hf_closed y (hliminf y)

end

section

open Set
open Filter
open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Corollary 10.5.1, source-facing real specialization: a finite globally convex
real-valued function is globally Lipschitz whenever
`liminf_{λ → +∞} f (λ y) / λ` is finite in every direction `y`.

The canonical abstraction layer is exposed by
`exists_lipschitzWith_of_forall_liminf_ray_quotient_lt_top_of_lowerSemicontinuous`; this theorem
is the textbook `R^n` surface specialization `E = EuclideanSpace ℝ (Fin n)`. -/
theorem exists_lipschitzWith_of_forall_liminf_ray_quotient_lt_top
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f)
    (hliminf : ∀ y : E,
      liminf (fun t : ℝ ↦ (f (t • y) : WithBotTop ℝ) / (t : WithBotTop ℝ)) atTop < ⊤) :
    ∃ α : NNReal, LipschitzWith α f := by
  letI : TopologicalSpace (WithBotTop ℝ) := by
    change TopologicalSpace EReal
    infer_instance
  letI : OrderTopology (WithBotTop ℝ) := by
    change OrderTopology EReal
    infer_instance
  have hf_finite : ∀ x : E, (f.toWithBotTop x) < ⊤ := by
    intro x
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  have hf_convex' : ConvexOn ℝ (Set.univ : Set E) (f.toWithBotTop) := by
    exact convexOn_of_convex_finiteHeight_epigraph
      (s := (Set.univ : Set E)) (f := f.toWithBotTop)
      (by simpa [Function.IsConvex] using Function.isConvex_coe_of_convexOn_univ hf_convex)
      convex_univ
  have hf_closed : LowerSemicontinuous (f.toWithBotTop) :=
    (hf_convex'.continuous_of_finite hf_finite).lowerSemicontinuous
  exact exists_lipschitzWith_of_forall_liminf_ray_quotient_lt_top_of_lowerSemicontinuous
    f hf_convex hf_closed hliminf

end
