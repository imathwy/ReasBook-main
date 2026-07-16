import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open Function.RecedesInDirection
open scoped Topology

universe u
section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [ProperSpace E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.27.2 says that if a convex proper lower-semicontinuous function
  has a unique
  minimizer `x`, then every sequence whose function values converge to the infimum actually
  converges to `x`.
- `core/canonical`: the chapter-local owner `minimumSet`, the primitive convex/proper/closed
  owners `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`, and the canonical
  convergence/cluster owners `Tendsto` and `MapClusterPt`.
- `bridge/view`: the uniqueness hypothesis is stated directly as `minimumSet f = {x}` rather than
  via a packaged argmin object or an existential uniqueness wrapper.

Domain-style sampling used here:
- the Chapter 6 minimum-set owner `minimumSet` from `Definition_6_27_3`;
- primitive owners `Function.IsConvex`, `Function.IsProper`, and `LowerSemicontinuous`;
- the source-facing recession-direction owner `Function.RecedesInDirection` from
  `Definition_6_27_4`;
- the no-recession boundedness bridge
  `isBounded_range_of_tendsto_infimum_of_no_recession_direction`;
- the cluster-point minimum-set bridge `mapClusterPt_mem_minimumSet_of_tendsto_infimum`.

Primitive data vs derived API:
- primitive inputs: the function `f`, its unique minimizer `x`, and a sequence `xSeq` along which
  `f (xSeq n)` tends to `⨅ y, f y`;
- derived API: the no-recession consequence of singleton minimality, boundedness of `xSeq`, and
  the cluster-point consequence that every subsequential limit belongs to `minimumSet f`.

Layer target: `source-facing`, stated directly on the canonical minimum-set owner and sequence
convergence owner rather than through a separate asymptotic-minimizer structure.
-/

-- Proof sketch: singleton minimality rules out nonzero recession directions (the ray from a
-- minimizer stays in `minimumSet f`, contradicting `minimumSet f = {x}`). Then Corollary 6.27.1
-- gives boundedness of the sequence. If the sequence did not converge to `x`, one could extract a
-- subsequence staying at distance at least `ε` from `x`; boundedness plus properness gives a
-- convergent sub-subsequence. Its limit is a cluster point of the original
-- sequence, hence belongs to `minimumSet f = {x}`, contradicting the uniform `ε`-separation.
/-- Corollary 6.27.2: if a convex proper lower-semicontinuous function has the singleton
minimum set `{x}`, then
every sequence whose function values converge to the infimum converges to `x`. -/
theorem tendsto_of_tendsto_infimum_of_minimumSet_eq_singleton
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f) {x : E}
    (hminimum : minimumSet f = {x}) {xSeq : ℕ → E}
    (hxSeq : Tendsto (fun n ↦ f (xSeq n)) atTop (𝓝 (⨅ y : E, f y))) :
    Tendsto xSeq atTop (𝓝 x) := by
  have hx_min : x ∈ minimumSet f := by simp [hminimum]
  have hx_le : f x ≤ ⨅ y : E, f y := mem_minimumSet_iff_le_iInf.mp hx_min
  rcases hf_proper.nonempty_dom with ⟨y, hy_dom⟩
  have hx_top : f x < ⊤ := by
    exact lt_of_le_of_lt (le_trans hx_le (iInf_le f y)) (mem_effectiveDomain.mp hy_dom)
  have hx_dom : x ∈ dom(f) := mem_effectiveDomain.mpr hx_top
  have hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y := by
    rintro ⟨y, hy⟩
    have hxy_min : x + y ∈ minimumSet f := by
      rw [mem_minimumSet_iff_le_iInf]
      have h01 : (0 : 𝕜) ≤ 1 := zero_le_one
      simpa [one_smul] using le_trans (ray_le hy hx_dom h01) hx_le
    have hxy : x + y = x := by simpa [hminimum, one_smul] using hxy_min
    have hy_zero : y = 0 := by
      have hsub := congrArg (fun z ↦ z - x) hxy
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
    exact hy.ne_zero hy_zero
  have hbounded : Bornology.IsBounded (Set.range xSeq) :=
    isBounded_range_of_tendsto_infimum_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession hxSeq
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra htail
  push Not at htail
  have hfar : ∃ᶠ n in atTop, ε ≤ dist (xSeq n) x := by
    exact frequently_atTop.2 htail
  rcases extraction_of_frequently_atTop hfar with ⟨φ, hφmono, hφfar⟩
  have hbounded_subseq : Bornology.IsBounded (Set.range (xSeq ∘ φ)) := by
    refine hbounded.subset ?_
    rintro y ⟨n, rfl⟩
    exact ⟨φ n, rfl⟩
  obtain ⟨a, -, ψ, hψmono, hconv⟩ :=
    tendsto_subseq_of_bounded hbounded_subseq (fun n ↦ Set.mem_range_self n)
  have hcluster_subsub : MapClusterPt a atTop (((xSeq ∘ φ) ∘ ψ)) :=
    (Filter.Tendsto.mapClusterPt hconv)
  have hcluster_sub : MapClusterPt a atTop (xSeq ∘ φ) :=
    hcluster_subsub.of_comp hψmono.tendsto_atTop
  have hcluster : MapClusterPt a atTop xSeq :=
    hcluster_sub.of_comp hφmono.tendsto_atTop
  have ha_min : a ∈ minimumSet f :=
    mapClusterPt_mem_minimumSet_of_tendsto_infimum hf_closed hxSeq hcluster
  have ha_eq : a = x := by simpa [hminimum] using ha_min
  have hclosed_far : IsClosed ({y : E | ε ≤ dist y x} : Set E) := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  have ha_far : ε ≤ dist a x := by
    refine hclosed_far.mem_of_tendsto hconv ?_
    exact Filter.Eventually.of_forall fun n ↦ hφfar (ψ n)
  exact (not_le_of_gt hε) (by simpa [ha_eq] using ha_far)

end
