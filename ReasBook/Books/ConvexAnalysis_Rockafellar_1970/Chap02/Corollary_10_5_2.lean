import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_10_5_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open Filter Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance : TopologicalSpace (WithBotTop ℝ) := by
  change TopologicalSpace EReal
  infer_instance

noncomputable local instance : OrderTopology (WithBotTop ℝ) := by
  change OrderTopology EReal
  infer_instance

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 10.5.2 says that if a finite convex function is majorized by a
  globally Lipschitz function, then it is globally Lipschitz.
- `core/canonical`: the owners used here are `ConvexOn ℝ univ f`,
  `LowerSemicontinuous (f.toWithBotTop)`, `LipschitzWith α g`, and the Chapter 10 core theorem
  `exists_lipschitzWith_of_forall_liminf_ray_quotient_lt_top_of_lowerSemicontinuous`.
- `bridge/view`: once `LipschitzWith α g` is fixed, convexity of `g` is not needed. The majorant
  hypothesis `f ≤ g` plus this Lipschitz witness gives finite ray-quotient liminf bounds for `f`.

Primitive data vs derived API:
- primitive inputs for the core theorem below: global convexity of `f`, lower semicontinuity of
  `f.toWithBotTop`, majorization `f ≤ g`, and one explicit witness `LipschitzWith α g`;
- derived source wrapper: dropping explicit lower semicontinuity by deriving it from finite-valued
  convexity of `f.toWithBotTop`;
- derived existential wrapper: replacing a fixed witness by `∃ α, LipschitzWith α g`.

Layer target: keep the item on the primitive closedness core owner layer first, then provide
source-facing wrappers.
-/

private theorem liminf_ray_quotient_lt_top_of_le_lipschitzWith_majorant
    {f g : E → ℝ} {α : NNReal} (hfg : f ≤ g) (hg : LipschitzWith α g) (y : E) :
    liminf (fun t : ℝ ↦ (f (t • y) : WithBotTop ℝ) / (t : WithBotTop ℝ)) atTop < ⊤ := by
  let c : ℝ := |g 0| + α * ‖y‖
  have h_eventually :
      ∀ᶠ t : ℝ in atTop,
        (f (t • y) : WithBotTop ℝ) / (t : WithBotTop ℝ) ≤ (c : WithBotTop ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hf_div : f (t • y) / t ≤ g (t • y) / t :=
      div_le_div_of_nonneg_right (hfg (t • y)) ht0.le
    have h_norm : ‖t • y‖ ≤ t * ‖y‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
    have h_abs : |g 0| ≤ |g 0| * t := by
      simpa [mul_comm] using le_mul_of_one_le_left (abs_nonneg (g 0)) ht
    have hg_div : g (t • y) / t ≤ c := by
      have hg_bound : g (t • y) ≤ c * t := by
        calc
          g (t • y) ≤ g 0 + α * dist (t • y) 0 := hg.le_add_mul _ _
          _ = g 0 + α * ‖t • y‖ := by simp [dist_eq_norm]
          _ ≤ |g 0| + α * ‖t • y‖ := by gcongr; exact le_abs_self (g 0)
          _ ≤ |g 0| + α * (t * ‖y‖) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h_norm α.coe_nonneg)
          _ ≤ |g 0| * t + α * (t * ‖y‖) := add_le_add h_abs le_rfl
          _ = c * t := by
            simp [c]
            ring
      exact (div_le_iff₀ ht0).2 hg_bound
    change (((f (t • y) / t : ℝ) : WithBotTop ℝ) ≤ (c : WithBotTop ℝ))
    exact WithBotTop.coe_le_coe.mpr (hf_div.trans hg_div)
  exact lt_of_le_of_lt (liminf_le_of_frequently_le' h_eventually.frequently)
    (WithBotTop.coe_lt_top c)

/-- Core owner form for Corollary 10.5.2 at the primitive closedness layer: if `f : E → ℝ` is
convex on `univ`, lower-semicontinuous after canonical lift, and majorized by a function `g` with
an explicit global Lipschitz witness, then `f` is globally Lipschitz. -/
theorem exists_lipschitzWith_of_convexOn_univ_of_lowerSemicontinuous_of_le_lipschitzWith_majorant
    [FiniteDimensional ℝ E]
    {f g : E → ℝ} (hf_convex : ConvexOn ℝ univ f)
    (hf_closed : LowerSemicontinuous (f.toWithBotTop))
    (hfg : f ≤ g)
    {α : NNReal} (hg_lipschitzWith : LipschitzWith α g) :
    ∃ β : NNReal, LipschitzWith β f := by
  refine exists_lipschitzWith_of_forall_liminf_ray_quotient_lt_top_of_lowerSemicontinuous
    f hf_convex hf_closed ?_
  intro y
  exact liminf_ray_quotient_lt_top_of_le_lipschitzWith_majorant hfg hg_lipschitzWith y

/-- Source-facing witness form of Corollary 10.5.2: if a globally convex finite-valued function
`f : E → ℝ` is majorized by a function `g : E → ℝ` with one explicit global Lipschitz witness,
then `f` is globally Lipschitz. -/
theorem exists_lipschitzWith_of_convexOn_univ_of_le_lipschitzWith_majorant
    [FiniteDimensional ℝ E]
    {f g : E → ℝ} (hf_convex : ConvexOn ℝ univ f)
    (hfg : f ≤ g)
    {α : NNReal} (hg_lipschitzWith : LipschitzWith α g) :
    ∃ β : NNReal, LipschitzWith β f := by
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
  exact exists_lipschitzWith_of_convexOn_univ_of_lowerSemicontinuous_of_le_lipschitzWith_majorant
    hf_convex hf_closed hfg hg_lipschitzWith

/-- Corollary 10.5.2: if a globally convex real-valued function `f : E → ℝ` is majorized by a
 globally Lipschitz function `g : E → ℝ`, then `f` is globally Lipschitz. -/
-- Proof sketch: for each direction `y`, the Lipschitz bound on `g` at the base point `0` yields
-- an eventual upper bound for the ray quotients `g (t • y) / t`, hence also for the ray quotients
-- of `f` because `f ≤ g`. Corollary 10.5.1 then upgrades these source-facing liminf bounds to a
-- global Lipschitz bound for `f`.
theorem exists_lipschitzWith_of_convexOn_univ_of_le_lipschitz_majorant
    [FiniteDimensional ℝ E]
    {f g : E → ℝ} (hf_convex : ConvexOn ℝ univ f) (hfg : f ≤ g)
    (hg_lipschitz : ∃ α : NNReal, LipschitzWith α g) :
    ∃ β : NNReal, LipschitzWith β f := by
  rcases hg_lipschitz with ⟨α, hα⟩
  exact exists_lipschitzWith_of_convexOn_univ_of_le_lipschitzWith_majorant
    hf_convex hfg hα

end
