import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_10_5_1 (from Chap02) -/
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

/-! ### Corollary_10_5_2 (from Chap02) -/
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

/-! ### Definition_10_5_3 (from Chap02) -/
section

universe u v w

variable {ι : Sort u} {X : Type v} {Y : Type w}
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 10.5.3 names the family-level condition that one nonnegative
  Lipschitz constant works uniformly for every member of a family on a subset `S`.
- `core/canonical`: the intrinsic owner abstraction is the set-level predicate
  `Set.EquiLipschitzOn F S := ∃ α : NNReal, ∀ g ∈ F, LipschitzOnWith α g S`, independent of any
  indexing model.
- `bridge/view`: the chapter indexed owner is the thin bridge
  `EquiLipschitzOn f S := Set.EquiLipschitzOn (Set.range f) S`; the bundled `UniformFun` view is
  a derived bridge via `UniformFun.lipschitzOnWith_ofFun_iff`; then `LipschitzOnWith` gives the
  canonical emetric inequality bridge,
  `lipschitzOnWith_iff_dist_le_mul` gives the metric inequality bridge, and
  `dist_eq_norm` gives the norm specialization.

Domain-style sampling used here:
- `LipschitzOnWith`;
- `lipschitzOnWith_iff_dist_le_mul`;
- `UniformFun.lipschitzOnWith_ofFun_iff`;
- `dist_eq_norm`;

Primitive data vs derived API:
- primitive data: a single `α : NNReal` and one family-set owner
  `∀ g ∈ F, LipschitzOnWith α g S`;
- derived API: the indexed-family bridge through `Set.range`, the bundled `UniformFun` bridge,
  and the emetric/metric/norm inequality reformulations, plus uniform-equicontinuity
  consequences.

Layer target: `source-facing`, with `EquiLipschitzOn` as the chapter vocabulary for the family
notion built on the intrinsic set owner, with indexed and bundled formulations provided as thin
bridges.
-/

/-- Intrinsic owner for equi-Lipschitz families on `S`: one nonnegative constant works for every
member of a function family set `F`. -/
def Set.EquiLipschitzOn (F : Set (X → Y)) (S : Set X) : Prop :=
  ∃ α : NNReal, ∀ g ∈ F, LipschitzOnWith α g S

/-- Primitive-owner unfolding of `Set.EquiLipschitzOn`. -/
theorem Set.equiLipschitzOn_iff_exists_forall_lipschitzOnWith
    {F : Set (X → Y)} {S : Set X} :
    F.EquiLipschitzOn S ↔ ∃ α : NNReal, ∀ g ∈ F, LipschitzOnWith α g S :=
  Iff.rfl

/-- Intrinsic bundled bridge: the set-owner `F.EquiLipschitzOn S` is equivalent to one
`LipschitzOnWith` witness for the canonical subtype-indexed bundled family. -/
theorem Set.equiLipschitzOn_iff_exists_lipschitzOnWith_uniformFun
    {F : Set (X → Y)} {S : Set X} :
    F.EquiLipschitzOn S ↔
      ∃ α : NNReal,
        LipschitzOnWith α (fun x ↦ UniformFun.ofFun (fun g : F ↦ (g : X → Y) x)) S := by
  rw [Set.equiLipschitzOn_iff_exists_forall_lipschitzOnWith]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, (UniformFun.lipschitzOnWith_ofFun_iff).2 ?_⟩
    intro g
    exact hα g g.2
  · rintro ⟨α, hα⟩
    have hα' :
        ∀ g : F, LipschitzOnWith α (fun x ↦ (g : X → Y) x) S :=
      (UniformFun.lipschitzOnWith_ofFun_iff).1 hα
    refine ⟨α, ?_⟩
    intro g hg
    exact hα' ⟨g, hg⟩

/-- Definition 10.5.3: a family of functions on a subset `S` is equi-Lipschitzian relative to `S`
if one nonnegative Lipschitz constant works uniformly for every member of the family on `S`. -/
def EquiLipschitzOn (f : ι → X → Y) (S : Set X) : Prop :=
  (Set.range f).EquiLipschitzOn S

/-- The source-facing family predicate `EquiLipschitzOn f S` is exactly the existence of one
common nonnegative Lipschitz constant for all coordinate functions `f i` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_lipschitzOnWith
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, LipschitzOnWith α (f i) S := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, fun i ↦ hα (f i) ⟨i, rfl⟩⟩
  · rintro ⟨α, hα⟩
    exact ⟨α, fun g hg ↦ by
      rcases hg with ⟨i, rfl⟩
      exact hα i⟩

/-- The source-facing owner `EquiLipschitzOn f S` is equivalent to the bundled `UniformFun`
Lipschitz owner for a `Type`-indexed family. -/
theorem equiLipschitzOn_iff_exists_lipschitzOnWith_uniformFun
    {ι' : Type u} (f : ι' → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal,
        LipschitzOnWith α (fun x ↦ UniformFun.ofFun (fun i : ι' ↦ f i x)) S := by
  rw [equiLipschitzOn_iff_exists_forall_lipschitzOnWith]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, (UniformFun.lipschitzOnWith_ofFun_iff).2 ?_⟩
    intro i
    simpa using hα i
  · rintro ⟨α, hα⟩
    have hα' : ∀ i : ι', LipschitzOnWith α (fun x ↦ f i x) S :=
      (UniformFun.lipschitzOnWith_ofFun_iff).1 hα
    refine ⟨α, ?_⟩
    intro i
    simpa using hα' i

/-- Owner-style bridge: from `hf : EquiLipschitzOn f S`, extract one common coordinatewise
Lipschitz witness for all members of the family on `S`. -/
theorem EquiLipschitzOn.exists_forall_lipschitzOnWith
    {f : ι → X → Y} {S : Set X} (hf : EquiLipschitzOn f S) :
    ∃ α : NNReal, ∀ i, LipschitzOnWith α (f i) S :=
  (equiLipschitzOn_iff_exists_forall_lipschitzOnWith f S).1 hf

section Core

-- Proof sketch: unfold `EquiLipschitzOn` and each coordinate `LipschitzOnWith` owner.
/-- Canonical emetric bridge for Definition 10.5.3: a family is equi-Lipschitz on `S` iff one
nonnegative constant controls all coordinatewise extended metric differences
`edist (f i x) (f i y) ≤ α * edist x y` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_edist_le_mul
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, ∀ x ∈ S, ∀ y ∈ S, edist (f i x) (f i y) ≤ α * edist x y := by
  simp [equiLipschitzOn_iff_exists_forall_lipschitzOnWith, LipschitzOnWith]

end Core

section Metric

variable {ι : Sort u} {X : Type v} {Y : Type w}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

-- Proof sketch: unfold `EquiLipschitzOn` and rewrite each coordinate owner with
-- `lipschitzOnWith_iff_dist_le_mul`.
/-- Canonical metric bridge for Definition 10.5.3: a family is equi-Lipschitz on `S` iff one
nonnegative constant controls all coordinatewise metric differences
`dist (f i x) (f i y) ≤ α * dist x y` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_dist_le_mul
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, ∀ x ∈ S, ∀ y ∈ S, dist (f i x) (f i y) ≤ α * dist x y := by
  simp [equiLipschitzOn_iff_exists_forall_lipschitzOnWith, lipschitzOnWith_iff_dist_le_mul]

end Metric

section Normed

variable {ι : Sort u} {X : Type v} {Y : Type w}
variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

-- Proof sketch: specialize the metric bridge and rewrite distances by norms.
/-- Normed-group specialization of the canonical metric bridge: a family is equi-Lipschitz on `S`
iff one nonnegative constant bounds every coordinatewise norm difference
`‖f_i x - f_i y‖` by `α ‖x - y‖` on `S`. -/
theorem equiLipschitzOn_iff_exists_forall_norm_sub_le
    (f : ι → X → Y) (S : Set X) :
    EquiLipschitzOn f S ↔
      ∃ α : NNReal, ∀ i, ∀ x ∈ S, ∀ y ∈ S, ‖f i x - f i y‖ ≤ α * ‖x - y‖ := by
  simpa [dist_eq_norm] using
    (equiLipschitzOn_iff_exists_forall_dist_le_mul (f := f) (S := S))

end Normed

end

/-! ### Definition_10_5_4 (from Chap02) -/
universe u v w

section

variable {ι : Type u} {X : Type v} {Y : Type w}

section EMetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-
Source/core/bridge triage:
- `source-facing`: Definition 10.5.4 introduces the notion that a family of functions on a subset
  `S` shares one common `ε`-`δ` modulus on `S`.
- `core/canonical`: mathlib's owner notion for this is `UniformEquicontinuousOn`.
- `bridge/view`: the canonical pseudoemetric `edist` formulation is the primary specialization of
  `UniformEquicontinuousOn`; metric and norm formulations are thin downstream specializations.
- Primitive data vs derived API: the item adds no new owner object beyond the canonical
  uniform-space notion; the displayed `ε`-`δ` condition is a thin source-facing specification view.

Domain-style sampling used here:
- `UniformEquicontinuousOn`;
- `uniformity_basis_edist_le`;
- `Filter.HasBasis.uniformEquicontinuousOn_iff`.

Layer target: `bridge/view`, with `UniformEquicontinuousOn` kept as the main owner-facing recall
and the pseudoemetric `edist` criterion used as the primary bridge surface; metric and norm
formulas are retained as thin downstream specialization companions. In particular, norm-output
specializations are kept first at the primitive mixed layer (domain metric, codomain norm), with
domain norm-difference formulas as downstream companions.
-/

/- Definition 10.5.4: the canonical mathlib notion of a family of functions on `S` being uniformly
equicontinuous relative to `S` is `UniformEquicontinuousOn`. -/
recall UniformEquicontinuousOn

-- Proof sketch: specialize `Filter.HasBasis.uniformEquicontinuousOn_iff` to the closed-ball
-- pseudoemetric bases on the canonical subtype-indexed family `((↑) : F → X → Y)`.
/-- Intrinsic owner bridge (set-family layer): `F.UniformEquicontinuousOn S` is equivalent to one
common `ε`-`δ` modulus on subtype points `x y : S`, uniformly for all `g ∈ F`. -/
theorem Set.uniformEquicontinuousOn_iff_forall_edist_le_subtype
    {F : Set (X → Y)} {S : Set X} :
    F.UniformEquicontinuousOn S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, edist x y ≤ δ → ∀ g ∈ F, edist (g x) (g y) ≤ ε := by
  have hX := uniformity_basis_edist_le.inf_principal (S ×ˢ S)
  rw [Set.UniformEquicontinuousOn]
  rw [Filter.HasBasis.uniformEquicontinuousOn_iff hX uniformity_basis_edist_le]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g hg
    exact hF x y ⟨hxy, x.2, y.2⟩ ⟨g, hg⟩
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g
    rcases g with ⟨g, hg⟩
    rcases hxy with ⟨hxy, hx, hy⟩
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy g hg

/-- Textbook ambient owner bridge (set-family layer): `F.UniformEquicontinuousOn S` is equivalent
to one common `ε`-`δ` modulus with ambient hypotheses `x ∈ S`, `y ∈ S`, uniformly for all
`g ∈ F`. -/
theorem Set.uniformEquicontinuousOn_iff_forall_edist_le
    {F : Set (X → Y)} {S : Set X} :
    F.UniformEquicontinuousOn S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, edist x y ≤ δ → ∀ g ∈ F, edist (g x) (g y) ≤ ε := by
  rw [Set.uniformEquicontinuousOn_iff_forall_edist_le_subtype (F := F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy g hg
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy g hg
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g hg
    exact hF x x.2 y y.2 hxy g hg

-- Proof sketch: pass through the intrinsic set-owner theorem on `Set.range F` and reindex via
-- `uniformEquicontinuousOn_iff_range`.
/-- Intrinsic pseudoemetric bridge: uniform equicontinuity on `S` is equivalent to one common
`ε`-`δ` modulus on subtype points `x y : S`. -/
theorem UniformEquicontinuousOn.iff_forall_edist_le_subtype
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, edist x y ≤ δ → ∀ i, edist (F i x) (F i y) ≤ ε := by
  rw [uniformEquicontinuousOn_iff_range]
  change (Set.range F).UniformEquicontinuousOn S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, edist x y ≤ δ → ∀ i, edist (F i x) (F i y) ≤ ε
  rw [Set.uniformEquicontinuousOn_iff_forall_edist_le_subtype (F := Set.range F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x y hxy (F i) ⟨i, rfl⟩
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy g hg
    rcases hg with ⟨i, rfl⟩
    exact hF x y hxy i

/-- Textbook ambient pseudoemetric bridge: uniform equicontinuity on `S` is equivalent to one
common `ε`-`δ` modulus written with hypotheses `x ∈ S` and `y ∈ S`. -/
theorem UniformEquicontinuousOn.iff_forall_edist_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, edist x y ≤ δ → ∀ i, edist (F i x) (F i y) ≤ ε := by
  rw [UniformEquicontinuousOn.iff_forall_edist_le_subtype (F := F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy i
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy i
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x x.2 y y.2 hxy i

end EMetric

section Metric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

-- Proof sketch: specialize the owner theorem
-- `Filter.HasBasis.uniformEquicontinuousOn_iff` to the closed-ball metric bases
-- `Metric.uniformity_basis_dist_le` on both the domain and codomain. This yields the relative
-- metric `ε`-`δ` criterion directly.
/-- Intrinsic metric bridge: uniform equicontinuity on `S` is equivalent to one common
`ε`-`δ` modulus on subtype points `x y : S`. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le_subtype
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, dist x y ≤ δ → ∀ i, dist (F i x) (F i y) ≤ ε := by
  have hX := Metric.uniformity_basis_dist_le.inf_principal (S ×ˢ S)
  rw [Filter.HasBasis.uniformEquicontinuousOn_iff hX Metric.uniformity_basis_dist_le]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x y ⟨hxy, x.2, y.2⟩ i
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    rcases hxy with ⟨hxy, hx, hy⟩
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy i

/-- Textbook ambient metric bridge: uniform equicontinuity on `S` is equivalent to one common
`ε`-`δ` modulus written with hypotheses `x ∈ S` and `y ∈ S`. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ → ∀ i, dist (F i x) (F i y) ≤ ε := by
  rw [UniformEquicontinuousOn.iff_forall_dist_le_subtype (F := F) (S := S)]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy i
    exact hF ⟨x, hx⟩ ⟨y, hy⟩ hxy i
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ, hF⟩
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy i
    exact hF x x.2 y y.2 hxy i

end Metric

section NormCodomain

variable [PseudoMetricSpace X] [SeminormedAddCommGroup Y]

-- Proof sketch: specialize the metric bridge and rewrite codomain distances as norm
-- differences in the additive codomain.
/-- Intrinsic mixed bridge: with a metric domain and seminormed additive codomain, uniform
equicontinuity on `S` is equivalent to one common `ε`-`δ` modulus on subtype points `x y : S`,
measured by `dist` in the domain and `‖· - ·‖` in the codomain. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le_subtype
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x y : S, dist x y ≤ δ → ∀ i, ‖F i x - F i y‖ ≤ ε := by
  simpa [dist_eq_norm] using
    (UniformEquicontinuousOn.iff_forall_dist_le_subtype (F := F) (S := S))

/-- Ambient mixed bridge companion: with a metric domain and seminormed additive codomain, uniform
equicontinuity on `S` is equivalent to one common `ε`-`δ` modulus written with hypotheses
`x ∈ S` and `y ∈ S`, measured by `dist` in the domain and `‖· - ·‖` in the codomain. -/
theorem UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ → ∀ i, ‖F i x - F i y‖ ≤ ε := by
  simpa [dist_eq_norm] using
    (UniformEquicontinuousOn.iff_forall_dist_le (F := F) (S := S))

end NormCodomain

section NormValued

variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

-- Proof sketch: specialize the mixed metric/norm bridge
-- `UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le` by rewriting domain distances as
-- norm differences.
/-- For families between seminormed additive commutative groups, the metric
criterion with codomain norm differences specializes to the full norm-difference `ε`-`δ`
criterion on both domain and codomain. -/
theorem UniformEquicontinuousOn.iff_forall_norm_sub_le
    {F : ι → X → Y} {S : Set X} :
    UniformEquicontinuousOn F S ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ δ → ∀ i, ‖F i x - F i y‖ ≤ ε := by
  simpa [dist_eq_norm] using
    (UniformEquicontinuousOn.iff_forall_dist_le_norm_sub_le (F := F) (S := S))

end NormValued

end

/-! ### Theorem_10_5 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.5 characterizes global uniform continuity of a finite convex
  function on a finite-dimensional normed space over an ordered normed field, by global finiteness
  of its recession function, and then records the stronger global Lipschitz conclusion.
- `core/canonical`: the convexity owner on theorem surfaces is `ConvexOn 𝕜 Set.univ f`; the
  recession object is computed on the canonical codomain lift `f.toWithBotTop`. The other owners
  are mathlib's global continuity/Lipschitz predicates
  `UniformContinuous f` and `LipschitzWith α f`, together with the chapter effective-domain owner
  `dom(·)` applied to the recession function.
- `bridge/view`: the source's finite-valued convex function is viewed through the canonical
  codomain lift `Function.toWithBotTop`.

Domain-style sampling used here:
- `ConvexOn 𝕜 Set.univ f`;
- the project bridge `Function.toWithBotTop`;
- `Function.recessionFunction`;
- `Function.IsConvex.continuous_of_finite`;
- `LipschitzWith.uniformContinuous`.

Primitive data vs derived API:
- primitive input: global convexity `ConvexOn 𝕜 Set.univ f` of the finite-valued map;
- source-facing comparison object: the recession function of the canonical `WithBotTop` lift
  `f.toWithBotTop`;
- derived API: the global uniform continuity criterion, whose finite-value side is expressed by the
  intrinsic effective-domain owner condition `dom((f.toWithBotTop)₀⁺) = univ`; for a proper
  recession function, the alternative value `⊥` is already excluded. The stronger Lipschitz
  consequence uses the same owner-level finiteness hypothesis.

Layer target: `source-facing`, expressed with the canonical global continuity/Lipschitz owners and
the existing chapter recession-function owner, without introducing a parallel wrapper for finite
convex functions.

Scalar/ambient minimality note:
- this owner is kept at the finite-dimensional ordered normed-field layer needed by the
  convex-order and recession-function owners; no real-specific specialization is exposed on the
  theorem surfaces below.
-/

/- The canonical owner theorem used to pass from the Lipschitz conclusion in Theorem 10.5 to
uniform continuity. -/
recall LipschitzWith.uniformContinuous

variable (f : E → 𝕜)

-- Proof sketch: for the forward implication, use uniform continuity to bound each increment
-- `f (x + z) - f x` uniformly for small `z`, then apply the recession-function supremum formula to
-- deduce that `(f.toWithBotTop)₀⁺` takes finite scalar values on a neighborhood of `0`, hence
-- everywhere by positive homogeneity and properness of the recession function.
-- For the reverse implication, the owner bridge
-- `Function.IsConvex.continuous_of_finite` gives continuity of the recession function of the
-- `WithBotTop` lift `f.toWithBotTop`, so its restriction to the unit sphere has finite supremum
-- `α`.
-- Corollary 8.5.1
-- then yields `f y - f x ≤ f0⁺ (y - x) ≤ α ‖y - x‖`, and the same bound with `x` and `y`
-- exchanged gives a global Lipschitz estimate, hence uniform continuity.
/-- Theorem 10.5: for a finite-valued map `f : E → 𝕜` with intrinsically convex canonical lift
`ConvexOn 𝕜 Set.univ f`, global uniform continuity is equivalent to finiteness everywhere of
the recession function of that lift, rendered by `dom((f.toWithBotTop)₀⁺) = univ`. -/
theorem uniformContinuous_iff_recessionFunction_finite_everywhere
    [FiniteDimensional 𝕜 E]
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f) :
    UniformContinuous f ↔
      dom((f.toWithBotTop)₀⁺) = (Set.univ : Set E) := sorry

-- Proof sketch: by Theorem 10.5, finiteness of the recession function is equivalent to uniform
-- continuity. The second half of the same argument bounds the recession function on the unit
-- sphere by some `α`, and Corollary 8.5.1 converts that bound into the global estimate
-- `|f y - f x| ≤ α ‖y - x‖`, which is exactly `LipschitzWith α f`.
/-- If the recession function of the canonical `WithBotTop` lift of a globally convex finite-valued
function is finite everywhere, then the function is globally Lipschitz. -/
theorem exists_lipschitzWith_of_recessionFunction_finite_everywhere
    [FiniteDimensional 𝕜 E]
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hf_recession_finite : dom((f.toWithBotTop)₀⁺) = (Set.univ : Set E)) :
    ∃ α : NNReal, LipschitzWith α f := sorry

end

/-! ### Theorem_10_5_5 (from Chap02) -/
section

universe u v w

variable {X : Type v} {Y : Type w}
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.5.5 says that an equi-Lipschitz family on a subset `S` is uniformly
  equicontinuous on `S`.
- `core/canonical`: the intrinsic owner is `Set.EquiLipschitzOn F S`, independent of any indexing
  model; the corresponding canonical uniformly equicontinuous family is the subtype-indexed family
  `fun g : F ↦ (g : X → Y)`.
- `bridge/view`: the chapter owner `EquiLipschitzOn f S` is exactly
  `(Set.range f).EquiLipschitzOn S`, and `UniformEquicontinuousOn.comp` transports the intrinsic
  subtype-indexed conclusion back to the original indexed family along `Set.rangeFactorization f`.

Domain-style sampling used here:
- `Set.EquiLipschitzOn`;
- `EquiLipschitzOn`;
- `UniformEquicontinuousOn`;
- `LipschitzOnWith.uniformEquicontinuousOn`;
- `UniformEquicontinuousOn.comp`.

Primitive data vs derived API:
- primitive data: one common nonnegative Lipschitz constant for all members of a function-family
  set, i.e. `hF : F.EquiLipschitzOn S`;
- derived API: uniform equicontinuity for subtype-indexed families and then for range-indexed
  source families.

Layer target: `core/canonical` first (intrinsic theorem on `Set.EquiLipschitzOn`), then the
`source-facing` theorem `EquiLipschitzOn.uniformEquicontinuousOn` as a thin range/reindex bridge.
-/

/-- Intrinsic owner theorem: an equi-Lipschitz family set on `S` is uniformly equicontinuous on
`S`, stated on the canonical set-owner surface `F.UniformEquicontinuousOn S`. -/
theorem Set.EquiLipschitzOn.uniformEquicontinuousOn
    {F : Set (X → Y)} {S : Set X} (hF : F.EquiLipschitzOn S) :
    F.UniformEquicontinuousOn S := by
  rcases hF with ⟨α, hα⟩
  exact LipschitzOnWith.uniformEquicontinuousOn (fun g : F ↦ (g : X → Y)) α
    (fun g ↦ hα g g.2)

-- Proof sketch: pass through the intrinsic `Set.EquiLipschitzOn` theorem on `Set.range f`,
-- then reindex the resulting uniformly equicontinuous family along `Set.rangeFactorization f`.
/-- Theorem 10.5.5: if a family of functions on `S` is equi-Lipschitzian relative to `S`, then it
is uniformly equicontinuous relative to `S`. -/
theorem EquiLipschitzOn.uniformEquicontinuousOn
    {ι : Type u} {f : ι → X → Y} {S : Set X} (hf : EquiLipschitzOn f S) :
    UniformEquicontinuousOn f S := by
  have hsub : (Set.range f).UniformEquicontinuousOn S :=
    Set.EquiLipschitzOn.uniformEquicontinuousOn (S := S) hf
  simpa [Function.comp] using
    UniformEquicontinuousOn.comp hsub (Set.rangeFactorization f)

end

/-! ### Definition_10_5_6 (from Chap02) -/
section

universe u v

variable {X : Type u} {ι : Sort v} {Y : Type*}
variable [Bornology Y]

open Bornology

/-!
Source/core/bridge triage:
- `source-facing`: Definition 10.5.6 names the condition that a family of `Y`-valued functions is
  bounded at each point of a subset `S`.
- `core/canonical`: the intrinsic owner abstraction is the set-family predicate
  `Set.PointwiseBoundedOn F S`, defined by applying the canonical bornology owner
  `Bornology.IsBounded` to the restricted family in `S → Y`, so pointwise boundedness is expressed
  in the Pi-space bornology independently of any indexing model.
- `bridge/view`: the intrinsic subtype-indexed fiberwise and order-bounded reformulations
  `Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype` and
  `Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval_subtype`; the chapter indexed owner
  `PointwiseBoundedOn f S` is a thin bridge through `Set.range`.

Domain-style sampling used here:
- `Bornology.IsBounded`;
- `Bornology.forall_isBounded_image_eval_iff`;
- `Function.eval`;
- `isBounded_iff_bddBelow_bddAbove`;
- `Bornology.IsBounded.bddBelow`;
- `Bornology.IsBounded.bddAbove`.

Primitive data vs derived API:
- primitive data: a subset `S` and a family set `F : Set (X → Y)`;
- derived API: the chapter predicate `PointwiseBoundedOn f S`, obtained canonically as
  `(Set.range f).PointwiseBoundedOn S`, with subtype-indexed and ambient companion reformulations.

Layer target: `source-facing`; the textbook indexed-family predicate is kept as chapter
vocabulary, now stated directly on the canonical bornology owner on the restricted function space
`S → Y`, with fiberwise and order-theoretic reformulations kept as thin bridges.
-/

/-- Intrinsic owner for pointwise boundedness on `S`: a family set `F` is pointwise bounded on `S`
when the restricted family in `S → Y` is bounded in the canonical function-space bornology. -/
def Set.PointwiseBoundedOn (F : Set (X → Y)) (S : Set X) : Prop :=
  IsBounded ((fun g : X → Y ↦ fun x : S ↦ g x) '' F)

/-- Intrinsic fiberwise bridge for family sets: pointwise boundedness on `S` is equivalent to
boundedness of each evaluation image over subtype points `x : S`. -/
theorem Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype
    {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x : S, IsBounded ((fun g : X → Y ↦ g x) '' F) := by
  have hEval (x : S) :
      Function.eval x '' ((fun g : X → Y ↦ fun y : S ↦ g y) '' F) =
        (fun g : X → Y ↦ g x) '' F := by
    ext y
    constructor
    · rintro ⟨h, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(fun y : S ↦ g y), ⟨g, hg, rfl⟩, rfl⟩
  rw [Set.PointwiseBoundedOn, ← forall_isBounded_image_eval_iff]
  constructor
  · intro h x
    simpa [hEval x] using h x
  · intro h x
    simpa [hEval x] using h x

/-- Owner-elimination lemma on subtype points: from `F.PointwiseBoundedOn S`, each subtype
evaluation image `((fun g ↦ g x) '' F)` is bounded. -/
theorem Set.PointwiseBoundedOn.isBounded_image_eval_subtype
    {S : Set X} {F : Set (X → Y)} (h : F.PointwiseBoundedOn S) (x : S) :
    IsBounded ((fun g : X → Y ↦ g x) '' F) :=
  (Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype.mp h) x

/-- Textbook ambient bridge for family sets: pointwise boundedness on `S` is equivalent to
boundedness of each evaluation image at points `x ∈ S`. -/
theorem Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x ∈ S, IsBounded ((fun g : X → Y ↦ g x) '' F) := by
  rw [Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

/-- Owner-elimination lemma on ambient points: from `F.PointwiseBoundedOn S`, each evaluation
image at `x ∈ S` is bounded. -/
theorem Set.PointwiseBoundedOn.isBounded_image_eval
    {S : Set X} {F : Set (X → Y)} (h : F.PointwiseBoundedOn S) {x : X} (hx : x ∈ S) :
    IsBounded ((fun g : X → Y ↦ g x) '' F) :=
  (Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval.mp h) x hx

/-- Intrinsic order bridge for family sets: for an order-bornology codomain, pointwise
boundedness on `S` is equivalent to two-sided order bounds on each subtype-indexed evaluation
image. -/
theorem Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval_subtype
    [Preorder Y] [IsOrderBornology Y] {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x : S, BddBelow ((fun g : X → Y ↦ g x) '' F) ∧
        BddAbove ((fun g : X → Y ↦ g x) '' F) := by
  rw [Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype]
  simp [isBounded_iff_bddBelow_bddAbove]

/-- Textbook ambient order bridge for family sets: for an order-bornology codomain, pointwise
boundedness on `S` is equivalent to two-sided order bounds on each evaluation image at points
`x ∈ S`. -/
theorem Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval
    [Preorder Y] [IsOrderBornology Y] {S : Set X} {F : Set (X → Y)} :
    F.PointwiseBoundedOn S ↔
      ∀ x ∈ S,
        BddBelow ((fun g : X → Y ↦ g x) '' F) ∧
          BddAbove ((fun g : X → Y ↦ g x) '' F) := by
  rw [Set.pointwiseBoundedOn_iff_bddBelow_bddAbove_image_eval_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

/-- Definition 10.5.6 (source-facing indexed bridge): an indexed family is pointwise bounded on
`S` when its range family set is pointwise bounded on `S` in the intrinsic owner layer. -/
def PointwiseBoundedOn (f : ι → X → Y) (S : Set X) : Prop :=
  (Set.range f).PointwiseBoundedOn S

/-- Intrinsic fiberwise bridge for indexed families: pointwise boundedness on `S` is equivalent to
boundedness of each fiber over subtype points `x : S`. -/
theorem pointwiseBoundedOn_iff_forall_isBounded_range_subtype {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x : S, IsBounded (Set.range fun i ↦ f i x) := by
  rw [PointwiseBoundedOn, Set.pointwiseBoundedOn_iff_forall_isBounded_image_eval_subtype]
  have hRange (x : S) :
      (fun g : X → Y ↦ g x) '' Set.range f = Set.range (fun i ↦ f i x) := by
    ext y
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  constructor
  · intro h x
    simpa [hRange x] using h x
  · intro h x
    simpa [hRange x] using h x

/-- Owner-elimination lemma on subtype points: from `PointwiseBoundedOn f S`, each subtype fiber
`Set.range (fun i ↦ f i x)` is bounded. -/
theorem PointwiseBoundedOn.isBounded_range_subtype {S : Set X} {f : ι → X → Y}
    (h : PointwiseBoundedOn f S) (x : S) :
    IsBounded (Set.range fun i ↦ f i x) :=
  (pointwiseBoundedOn_iff_forall_isBounded_range_subtype.mp h) x

/-- Textbook ambient bridge: pointwise boundedness on `S` is equivalent to boundedness of each
fiber at points `x ∈ S`. -/
theorem pointwiseBoundedOn_iff_forall_isBounded_range {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x ∈ S, IsBounded (Set.range fun i ↦ f i x) := by
  rw [pointwiseBoundedOn_iff_forall_isBounded_range_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

/-- Owner-elimination lemma on ambient points: from `PointwiseBoundedOn f S`, each fiber at
`x ∈ S` is bounded. -/
theorem PointwiseBoundedOn.isBounded_range {S : Set X} {f : ι → X → Y}
    (h : PointwiseBoundedOn f S) {x : X} (hx : x ∈ S) :
    IsBounded (Set.range fun i ↦ f i x) :=
  (pointwiseBoundedOn_iff_forall_isBounded_range.mp h) x hx

/-- Intrinsic order bridge: for an order-bornology codomain, pointwise boundedness on `S` is
equivalent to two-sided order bounds on each subtype-indexed fiber. -/
theorem pointwiseBoundedOn_iff_bddBelow_bddAbove_subtype [Preorder Y] [IsOrderBornology Y]
    {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x : S, BddBelow (Set.range fun i ↦ f i x) ∧ BddAbove (Set.range fun i ↦ f i x) := by
  rw [pointwiseBoundedOn_iff_forall_isBounded_range_subtype]
  simp [isBounded_iff_bddBelow_bddAbove]

/-- Textbook ambient order bridge: for an order-bornology codomain, pointwise boundedness on `S`
is equivalent to two-sided order bounds on each fiber at points `x ∈ S`. -/
theorem pointwiseBoundedOn_iff_bddBelow_bddAbove [Preorder Y] [IsOrderBornology Y]
    {S : Set X} {f : ι → X → Y} :
    PointwiseBoundedOn f S ↔
      ∀ x ∈ S, BddBelow (Set.range fun i ↦ f i x) ∧ BddAbove (Set.range fun i ↦ f i x) := by
  rw [pointwiseBoundedOn_iff_bddBelow_bddAbove_subtype]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x x.2

end

/-! ### Definition_10_5_7 (from Chap02) -/
section

universe u v w

open Bornology

variable {X : Type u} {ι : Sort v} {α : Type w}
variable [Bornology α]

/-
Source/core/bridge triage:
- `source-facing`: the textbook phrase "uniformly bounded on `S`" is one common two-sided
  scalar bound for all values `f i x` with `x ∈ S`.
- `core/canonical`: the owner is the canonical bornology primitive `Bornology.IsBounded` on the
  canonical evaluation image `Set.image2 (fun g x ↦ g x) (Set.range f) S`.
- `bridge/view`: `uniformlyBoundedOn_iff_exists_bounds` and
  `uniformlyBoundedOn_iff_exists_bounds_mapsTo` are textbook quantifier and `MapsTo` bridges from
  that canonical owner surface.
- Domain-style sampling used here:
  `Bornology.IsBounded`, `isBounded_iff_bddBelow_bddAbove`,
  `bddBelow_bddAbove_iff_subset_Icc`.
- Primitive data vs derived API:
  primitive data: the subset `S` and the indexed family `f : ι → X → α`;
  derived API: the chapter owner `UniformlyBoundedOn f S` and its order-bounded reformulations.
- Layer target: `source-facing`; the chapter predicate is retained, but now directly exposes the
  canonical owner primitive rather than introducing an additional set-family owner wrapper.
-/

/-- Definition 10.5.7 (owner layer): a family of `α`-valued functions is uniformly bounded on `S`
when the common value set of all pairs `(i, x)` with `x ∈ S` is bounded in the ambient bornology
on `α`. -/
def UniformlyBoundedOn (f : ι → X → α) (S : Set X) : Prop :=
  IsBounded (Set.image2 (fun g x ↦ g x) (Set.range f) S)

/-- Monotonicity in the subset variable: if `f` is uniformly bounded on `S`, then it is uniformly
bounded on every `T ⊆ S`. -/
theorem UniformlyBoundedOn.mono {f : ι → X → α} {S T : Set X}
    (h : UniformlyBoundedOn f S) (hTS : T ⊆ S) :
    UniformlyBoundedOn f T := by
  refine (show IsBounded (Set.image2 (fun g x ↦ g x) (Set.range f) S) from h).subset ?_
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact Set.mem_image2_of_mem hg (hTS hx)

/-- Owner-elimination lemma on subtype points: from `UniformlyBoundedOn f S`, each subtype fiber
`Set.range (fun i ↦ f i x)` is bounded. -/
theorem UniformlyBoundedOn.isBounded_range_subtype {f : ι → X → α} {S : Set X}
    (h : UniformlyBoundedOn f S) (x : S) :
    IsBounded (Set.range fun i ↦ f i x) := by
  refine (show IsBounded (Set.image2 (fun g x ↦ g x) (Set.range f) S) from h).subset ?_
  rintro y ⟨i, rfl⟩
  exact Set.mem_image2_of_mem ⟨i, rfl⟩ x.2

/-- Owner-elimination lemma on ambient points: from `UniformlyBoundedOn f S`, each fiber
`Set.range (fun i ↦ f i x)` at `x ∈ S` is bounded. -/
theorem UniformlyBoundedOn.isBounded_range {f : ι → X → α} {S : Set X}
    (h : UniformlyBoundedOn f S) {x : X} (hx : x ∈ S) :
    IsBounded (Set.range fun i ↦ f i x) :=
  h.isBounded_range_subtype ⟨x, hx⟩

/-- Intrinsic subtype bridge for families: `f` is uniformly bounded on `S` iff two common bounds
work for every index at every subtype point `x : S`. -/
theorem uniformlyBoundedOn_iff_exists_bounds_subtype [Preorder α] [IsOrderBornology α]
    {f : ι → X → α} {S : Set X} :
    UniformlyBoundedOn f S ↔
      ∃ α₁ α₂ : α, ∀ x : S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂ := by
  let T : Set α := Set.image2 (fun g x ↦ g x) (Set.range f) S
  rw [UniformlyBoundedOn, isBounded_iff_bddBelow_bddAbove, bddBelow_bddAbove_iff_subset_Icc]
  change (∃ α₁ α₂ : α, T ⊆ Set.Icc α₁ α₂) ↔
    ∃ α₁ α₂ : α, ∀ x : S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂
  constructor
  · rintro ⟨α₁, α₂, hT⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x i
    have hmem : f i x ∈ T := Set.mem_image2_of_mem ⟨i, rfl⟩ x.2
    simpa [Set.mem_Icc] using hT hmem
  · rintro ⟨α₁, α₂, hT⟩
    refine ⟨α₁, α₂, ?_⟩
    rintro y ⟨g, hg, x, hx, rfl⟩
    rcases hg with ⟨i, rfl⟩
    simpa [Set.mem_Icc] using hT ⟨x, hx⟩ i

/-- A family of `α`-valued functions is uniformly bounded on `S` exactly when there are two
bounds `α₁` and `α₂` satisfying `α₁ ≤ f i x ≤ α₂` for every `x ∈ S` and every index `i`. -/
theorem uniformlyBoundedOn_iff_exists_bounds [Preorder α] [IsOrderBornology α]
    {f : ι → X → α} {S : Set X} :
    UniformlyBoundedOn f S ↔
      ∃ α₁ α₂ : α, ∀ x ∈ S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂ := by
  rw [uniformlyBoundedOn_iff_exists_bounds_subtype]
  constructor
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x hx i
    exact h ⟨x, hx⟩ i
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x i
    exact h x x.2 i

/-- Intrinsic bridge for indexed families: `f` is uniformly bounded on `S` iff each `f i` maps
`S` into one common interval `Set.Icc α₁ α₂`. -/
theorem uniformlyBoundedOn_iff_exists_bounds_mapsTo [Preorder α] [IsOrderBornology α]
    {f : ι → X → α} {S : Set X} :
    UniformlyBoundedOn f S ↔
      ∃ α₁ α₂ : α, ∀ i, Set.MapsTo (f i) S (Set.Icc α₁ α₂) := by
  rw [uniformlyBoundedOn_iff_exists_bounds]
  constructor
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro i x hx
    exact h x hx i
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨α₁, α₂, ?_⟩
    intro x hx i
    exact h i hx

end
