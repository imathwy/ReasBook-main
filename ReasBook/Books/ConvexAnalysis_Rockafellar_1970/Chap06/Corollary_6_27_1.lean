import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open Bornology
open Filter
open scoped Topology Rockafellar

universe u

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.27.1 says that any sequence along which a closed proper convex
  function tends to its infimum is bounded when the function has no recession direction, and that
  every cluster point of such a sequence belongs to the minimum set of the function.
- `core/canonical`: the relevant owner abstractions already present are the primitive convexity,
  properness, and lower-semicontinuity owners (`Function.IsConvex`, `Function.IsProper`,
  `LowerSemicontinuous`) together with `Function.RecedesInDirection` for the boundedness clause,
  the Chapter 6 minimum-set owner `minimumSet`, the bornological boundedness owner `IsBounded`,
  and the sequence-cluster owner `MapClusterPt`.
- `bridge/view`: the textbook sequence statement is split into two atomic declarations, one for
  boundedness of the range and one for membership of cluster points in `minimumSet f`, instead of
  a single conjunction.

Domain-style sampling used here:
- `minimumSet` from `Definition_6_27_3`;
- `Function.RecedesInDirection` from `Definition_6_27_4`;
- primitive owners `Function.IsConvex`, `Function.IsProper`, and `LowerSemicontinuous`;
- `LowerSemicontinuous.isClosed_preimage` from mathlib's semicontinuity API;
- `IsBounded` and `MapClusterPt` from the canonical mathlib topology/bornology API.

Primitive data vs derived API:
- primitive inputs: a sequence `x : ℕ → E`, convergence of the scalar sequence `f ∘ x` to the
  infimum `⨅ y, f y`, and then either convexity/properness/lower-semicontinuity of `f` for the
  boundedness clause or just `LowerSemicontinuous f` for the cluster-point clause;
- extra source-side hypothesis for the boundedness clause: `f` has no recession direction;
- derived outputs: boundedness of `Set.range x` and membership of every cluster point in
  `minimumSet f`.

Layer target: `source-facing`, stated directly on the canonical sequence and minimum-set owners
rather than through a packaged asymptotic-minimization structure.
-/

omit [OrderTopology 𝕜]
  [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)] [FiniteDimensional 𝕜 E] in
private theorem functionRecessionCone_eq_singleton_zero_of_no_recession_direction
    {f : E → WithBotTop 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y) :
    Function.recessionCone ((f)₀⁺) = ({0} : Set E) := by
  ext y
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact False.elim <| hno_recession ⟨y,
        Function.RecedesInDirection.of_mem_recessionCone hf_convex hf_proper hy0 hy⟩
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [Function.mem_recessionCone_iff, Function.recessionFunction_apply]
    refine sSup_le ?_
    rintro r ⟨u, _, rfl⟩
    simpa using (WithBotTop.sub_self_le_zero : f u - f u ≤ (0 : WithBotTop 𝕜))

private theorem isBounded_sublevelSet_of_no_recession_direction
    {f : E → WithBotTop 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    {a : 𝕜} (ha_nonempty : (f ⁻¹' Set.Iic a).Nonempty) :
    IsBounded (f ⁻¹' Set.Iic a) := by
  have hsublevel_recession :
      0⁺[𝕜] (f ⁻¹' Set.Iic a) = ({0} : Set E) := by
    calc
      0⁺[𝕜] (f ⁻¹' Set.Iic a) = Function.recessionCone ((f)₀⁺) := by
        simpa using
          hf_convex.recessionCone_sublevelSet_eq_functionRecessionCone
            hf_proper hf_closed a ha_nonempty
      _ = ({0} : Set E) :=
        functionRecessionCone_eq_singleton_zero_of_no_recession_direction
          hf_convex hf_proper hno_recession
  exact
    ((hf_convex.convex_le (a : WithBotTop 𝕜)).isBounded_iff_recessionCone_eq_singleton_zero
      ((lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf_closed) a)
      ha_nonempty).mpr hsublevel_recession

-- Proof sketch: pick a finite minimizer value `m = ⨅ y, f y` from Theorem 6.27.2 and consider the
-- fixed scalar sublevel set `{u | f u ≤ m + 1}`. Its recession cone agrees with the function
-- recession cone and is therefore `{0}` by the no-recession hypothesis, so Theorem 8.4 gives
-- boundedness of that sublevel set. Convergence of `f (x n)` to `⨅ y, f y` puts the tail of `x`
-- in this bounded set, and adjoining finitely many initial terms preserves boundedness of
-- `Set.range x`.
/-- Corollary 6.27.1 (1): if a closed proper convex function has no recession direction, then any
sequence along which the function values converge to the infimum is bounded. -/
theorem isBounded_range_of_tendsto_infimum_of_no_recession_direction
    {f : E → WithBotTop 𝕜} {x : ℕ → E}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    (hx : Tendsto (fun n ↦ f (x n)) atTop (𝓝 (⨅ y : E, f y))) :
    IsBounded (Set.range x) := by
  obtain ⟨x0, hx0, hx0_dom⟩ :=
    exists_mem_minimumSet_dom_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession
  have hx0_top : f x0 < ⊤ := mem_effectiveDomain.mp hx0_dom
  have hx0_bot : ⊥ < f x0 := hf_proper.bot_lt x0
  lift f x0 to 𝕜 using ⟨ne_of_lt hx0_top, ne_of_gt hx0_bot⟩ with m hm
  have hiInf_eq : (⨅ y : E, f y) = (m : WithBotTop 𝕜) := by
    have hx0_eq_iInf : f x0 = ⨅ y : E, f y :=
      le_antisymm (mem_minimumSet_iff_le_iInf.mp hx0) (iInf_le f x0)
    simpa [hm] using hx0_eq_iInf.symm
  let S : Set E := f ⁻¹' Set.Iic (m + 1)
  have hS_bounded : IsBounded S := by
    refine isBounded_sublevelSet_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession ?_
    refine ⟨x0, ?_⟩
    calc
      f x0 = (m : WithBotTop 𝕜) := hm.symm
      _ ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) :=
        WithBotTop.coe_le_coe.mpr (le_add_of_nonneg_right zero_le_one)
  have htail : ∀ᶠ n in atTop, x n ∈ S := by
    have hlt : (⨅ y : E, f y) < ((m + 1 : 𝕜) : WithBotTop 𝕜) := by
      rw [hiInf_eq]
      exact WithBotTop.coe_lt_coe.mpr (lt_add_of_pos_right m zero_lt_one)
    simpa [S] using hx (Iic_mem_nhds hlt)
  rcases Filter.eventually_atTop.1 htail with ⟨N, hN⟩
  have hinitial : IsBounded (x '' Set.Iic N) :=
    (Set.finite_Iic N).image x |>.isBounded
  refine (hinitial.union hS_bounded).subset ?_
  rintro y ⟨n, rfl⟩
  by_cases hn : n ≤ N
  · exact Or.inl ⟨n, hn, rfl⟩
  · exact Or.inr <| hN n (Nat.le_of_not_ge hn)

end

section

variable {E : Type u} [TopologicalSpace E]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoTopOrder 𝕜] [Nonempty 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

-- Proof sketch: choose a finite threshold `a` strictly between `⨅ y, f y` and `f x₀`. Convergence
-- of `f ∘ x` to the infimum makes the map eventually stay in the closed sublevel set
-- `f ⁻¹' Set.Iic a`, and lower semicontinuity makes that set closed. A cluster point must
-- therefore belong to that sublevel set, contradicting `a < f x₀`.
/-- Corollary 6.27.1 (2): every cluster point (along any filter) of points whose function values
converge to the infimum belongs to the minimum set. For the textbook
closed-proper-convex hypothesis, this clause uses only lower semicontinuity, so it is stated on
that weaker canonical owner. -/
theorem mapClusterPt_mem_minimumSet_of_tendsto_infimum
    {ι : Type*} {l : Filter ι} {f : E → WithBotTop 𝕜} {x : ι → E} {x0 : E}
    (hf : LowerSemicontinuous f)
    (hx : Tendsto (fun i ↦ f (x i)) l (𝓝 (⨅ y : E, f y)))
    (hx0 : MapClusterPt x0 l x) :
    x0 ∈ minimumSet f := by
  rw [mem_minimumSet_iff_le_iInf]
  by_contra hx0_not_mem
  obtain ⟨a, ha_left, ha_right⟩ :=
    WithBotTop.exists_between_coe_of_lt (lt_of_not_ge hx0_not_mem)
  have hmem : ∀ᶠ i in l, x i ∈ f ⁻¹' Set.Iic a := by
    exact hx (Iic_mem_nhds ha_left)
  have hx0_mem : x0 ∈ f ⁻¹' Set.Iic a :=
    (hf.isClosed_preimage a).mem_of_mapClusterPt hx0 hmem
  exact (not_le.mpr ha_right) hx0_mem

end
