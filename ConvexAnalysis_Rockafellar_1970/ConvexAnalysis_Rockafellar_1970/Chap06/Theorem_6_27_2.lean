import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1_WithBotTopBridge
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_7
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_27_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Rockafellar

section Attainment

variable {E : Type u}
variable {𝕜 : Type*}
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable {f : E → WithBotTop 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.27.2 combines an attained finite infimum for a convex proper lower-
  semicontinuous function with no recession direction and a later metric proximity statement for
  sufficiently low sublevel sets. The attainment companion below already lives on the weaker
  finite-dimensional scalar-generic topological vector-space layer reused from Theorem 6.27.3,
  while the boundedness and distance clauses below use normed-space structure.
- `core/canonical`: the owner abstractions are the source-facing Chapter 6 minimum-set owner
  `minimumSet`, the recession-direction predicate `Function.RecedesInDirection`, the primitive
  owners `Function.IsConvex`, `Function.IsProper`, and `LowerSemicontinuous`, the unconstrained
  attainment owner
  `exists_mem_isMinOn_of_no_common_recession_direction`, the common-sublevel recession-cone owner
  `recessionCone_sublevelSet_eq_functionRecessionCone`, and the closed-convex boundedness owner
  `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
- `bridge/view`: the main public theorem is stated directly on the source-facing owner
  `minimumSet f`, while the attained-minimum and minimum-set geometry clauses are kept as separate
  companion theorems instead of being bundled into one long conjunction.

Domain-style sampling used here:
- `minimumSet` from `Definition_6_27_3`;
- `Function.RecedesInDirection` from `Definition_6_27_4`;
- primitive `Function.IsConvex` / `Function.IsProper` assumptions and `LowerSemicontinuous`;
- `exists_mem_isMinOn_of_no_common_recession_direction` from `Theorem_6_27_3`;
- `recessionCone_sublevelSet_eq_functionRecessionCone` from `Chap02/Theorem_8_7`;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero` from `Chap02/Theorem_8_4`.

Primitive data vs derived API:
- primitive inputs: the function `f : E → WithBotTop 𝕜`, convexity/properness/lower-
  semicontinuity assumptions, and the source-facing no-recession hypothesis
  `¬ ∃ y, f.RecedesInDirection 𝕜 y`;
- derived API in this file: the first clause is a source-facing bridge from the canonical owner
  `IsMinOn` to `minimumSet`, and it already lives on the weaker finite-dimensional scalar-generic
  topological vector-space layer of Theorem 6.27.3; the second clause is the corresponding
  boundedness bridge obtained by rewriting `minimumSet f` as the attained real sublevel set and
  applying the Chapter 8 recession owners in the normed finite-dimensional setting; the third
  clause is the genuinely new source-facing quantitative proximity statement.

Layer target: `source-facing`, reusing the existing minimum-set owner rather than replacing the
theorem by a packaged minimization structure or a purely `IsMinOn`-based wrapper.
-/

-- Proof sketch: specialize the canonical unconstrained-attainment theorem
-- `exists_mem_isMinOn_of_no_common_recession_direction` to `Set.univ` and convert the obtained
-- minimizer to the source-facing owner `minimumSet`. Properness supplies a finite point in
-- `dom(f)`, so the minimizer is finite as well in the canonical owner `dom(f)`.
/-- A convex proper lower-semicontinuous function with no recession direction on a finite-
dimensional topological vector space has a minimizer in the canonical finite-value owner
`dom(f)`. This attainment clause already lives on the same scalar-generic owner layer as the
upstream theorem. -/
theorem exists_mem_minimumSet_dom_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    : ∃ x ∈ minimumSet f, x ∈ dom(f) := by
  obtain ⟨x, -, hxmin⟩ :=
    exists_mem_isMinOn_of_no_common_recession_direction
      Set.univ_nonempty isClosed_univ convex_univ hf_convex hf_proper hf_closed
      (by
        rintro ⟨y, -, hy⟩
        exact hno_recession ⟨y, hy⟩)
  refine ⟨x, by simpa [minimumSet] using hxmin, ?_⟩
  exact hxmin.mem_dom_of_nonempty_dom hf_proper.nonempty_dom

end Attainment

section BoundedGeometry

open Bornology
open Filter

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {f : E → WithBotTop 𝕜}

omit [FiniteDimensional 𝕜 E] [OrderTopology 𝕜]
  [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)] in
private theorem functionRecessionCone_eq_singleton_zero_of_no_recession_direction
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
    rintro r ⟨u, hu, rfl⟩
    simpa using (WithBotTop.sub_self_le_zero : f u - f u ≤ (0 : WithBotTop 𝕜))

private theorem isBounded_sublevelSet_of_no_recession_direction
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

-- Proof sketch: first obtain a minimizer `x` in `dom(f)`. Its value is a scalar level `a`, and
-- `minimumSet f` is exactly the sublevel set `{u | f u ≤ a}`. The Chapter 8 theorem
-- `recessionCone_sublevelSet_eq_functionRecessionCone` identifies the recession cone of that
-- nonempty sublevel set with the function recession cone. The no-recession hypothesis forces the
-- latter to be `{0}`, so Theorem 8.4 yields boundedness of `minimumSet f`.
/-- Under the no-recession hypothesis, the minimum set of a convex proper lower-semicontinuous
function is bounded. -/
theorem minimumSet_isBounded_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    : IsBounded (minimumSet f) := by
  obtain ⟨x, hx, hx_dom⟩ :=
    exists_mem_minimumSet_dom_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession
  have hx_top : f x < ⊤ := mem_effectiveDomain.mp hx_dom
  have hx_bot : ⊥ < f x := hf_proper.bot_lt x
  lift f x to 𝕜 using ⟨ne_of_lt hx_top, ne_of_gt hx_bot⟩ with a ha
  have hx_eq_iInf : f x = ⨅ y : E, f y := by
    exact le_antisymm (mem_minimumSet_iff_le_iInf.mp hx) (iInf_le f x)
  have hminimumSet : minimumSet f = f ⁻¹' Set.Iic a := by
    ext u
    rw [Set.mem_preimage, Set.mem_Iic, mem_minimumSet_iff_le_iInf, ← hx_eq_iInf]
    simp [ha]
  have hsublevel_nonempty : (f ⁻¹' Set.Iic a).Nonempty := by
    refine ⟨x, ?_⟩
    rw [Set.mem_preimage, Set.mem_Iic]
    simp [ha]
  rw [hminimumSet]
  exact isBounded_sublevelSet_of_no_recession_direction
    hf_convex hf_proper hf_closed hno_recession hsublevel_nonempty

end BoundedGeometry

section MetricGeometry

open Bornology
open Filter

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [Archimedean 𝕜] [LocallyCompactSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {f : E → WithBotTop 𝕜}

-- Proof sketch: argue by contradiction with the closed bounded sets obtained by removing the
-- `ε`-neighborhood of `minimumSet f` from successively lower sublevel sets
-- `{x | f x ≤ inf f + δ}`. If every such truncated set were nonempty, compactness in finite
-- dimension would produce a point outside the `ε`-neighborhood but still in `minimumSet f`, a
-- contradiction.
/-- Theorem 6.27.2: for a convex proper lower-semicontinuous function with no recession direction,
every
sufficiently low sublevel point lies within any prescribed distance of the minimum set. -/
theorem sublevel_exists_mem_minimumSet_dist_lt_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : 𝕜, 0 < δ ∧
      ∀ x : E, f x ≤ (⨅ y : E, f y) + δ → ∃ z ∈ minimumSet f, dist x z < ε := by
  by_contra h
  push Not at h
  let δ : ℕ → 𝕜 := fun n ↦ ((n : 𝕜) + 1)⁻¹
  let x : ℕ → E := fun n ↦
    Classical.choose (h (δ n) (by
      dsimp [δ]
      positivity))
  have hx_sub : ∀ n, f (x n) ≤ (⨅ y : E, f y) + δ n := by
    intro n
    exact (Classical.choose_spec (h (δ n) (by
      dsimp [δ]
      positivity))).1
  have hx_far : ∀ n z, z ∈ minimumSet f → ε ≤ dist (x n) z := by
    intro n z hz
    exact (Classical.choose_spec (h (δ n) (by
      dsimp [δ]
      positivity))).2 z hz
  obtain ⟨x0, hx0, hx0_dom⟩ :=
    exists_mem_minimumSet_dom_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession
  have hx0_top : f x0 < ⊤ := mem_effectiveDomain.mp hx0_dom
  have hx0_bot : ⊥ < f x0 := hf_proper.bot_lt x0
  lift f x0 to 𝕜 using ⟨ne_of_lt hx0_top, ne_of_gt hx0_bot⟩ with m hm
  have hx0_eq_iInf : f x0 = ⨅ y : E, f y := by
    exact le_antisymm (mem_minimumSet_iff_le_iInf.mp hx0) (iInf_le f x0)
  have hiInf_eq : (⨅ y : E, f y) = (m : WithBotTop 𝕜) := by
    simpa [hm] using hx0_eq_iInf.symm
  let S : Set E := {u : E | f u ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜)}
  have hS_bdd : IsBounded S := by
    refine isBounded_sublevelSet_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession ?_
    refine ⟨x0, ?_⟩
    calc
      f x0 = (m : WithBotTop 𝕜) := hm.symm
      _ ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) :=
        WithBotTop.coe_le_coe.mpr (le_add_of_nonneg_right zero_le_one)
  have hx_memS : ∀ n, x n ∈ S := by
    intro n
    change f (x n) ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜)
    have hx' :
        f (x n) ≤ ((m + δ n : 𝕜) : WithBotTop 𝕜) := by
      simpa [hiInf_eq] using hx_sub n
    refine le_trans hx' ?_
    have hdiv_le : δ n ≤ 1 := by
      have hle : (1 : 𝕜) ≤ (n : 𝕜) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa [δ, one_div] using
        (one_div_le_one_div_of_le (show (0 : 𝕜) < 1 by positivity) hle)
    simpa [add_comm, add_left_comm, add_assoc] using
      (WithBotTop.coe_le_coe.mpr (add_le_add_right hdiv_le m))
  letI : ProperSpace E := FiniteDimensional.proper 𝕜 E
  obtain ⟨a, haS_closure, φ, hφ, hconv⟩ := tendsto_subseq_of_bounded hS_bdd hx_memS
  have hS_closed : IsClosed S := by
    simpa [S] using (lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf_closed) (m + 1)
  have haS : a ∈ S := by
    rwa [hS_closed.closure_eq] at haS_closure
  let T : Set E := (Metric.thickening ε (minimumSet f))ᶜ
  have hT_closed : IsClosed T := Metric.isOpen_thickening.isClosed_compl
  have hxφ_memT : ∀ n, x (φ n) ∈ T := by
    intro n
    have hx_not_thick : x (φ n) ∉ Metric.thickening ε (minimumSet f) := by
      rw [Metric.mem_thickening_iff]
      rintro ⟨z, hz, hzdist⟩
      exact (not_lt_of_ge (hx_far (φ n) z hz)) hzdist
    simpa [T] using hx_not_thick
  have haT : a ∈ T :=
    hT_closed.mem_of_tendsto hconv (Filter.Eventually.of_forall hxφ_memT)
  have haS' : f a ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) := by
    simpa [S] using haS
  have ha_top_f : f a < ⊤ :=
    lt_of_le_of_lt haS' (WithBotTop.coe_lt_top (m + 1))
  have ha_bot_f : ⊥ < f a := hf_proper.bot_lt a
  lift f a to 𝕜 using ⟨ne_of_lt ha_top_f, ne_of_gt ha_bot_f⟩ with r hr
  have ha_sublevel (k : ℕ) :
      ((r : 𝕜) : WithBotTop 𝕜) ≤ ((m + δ k : 𝕜) : WithBotTop 𝕜) := by
    let Sk : Set E := {u : E | f u ≤ ((m + δ k : 𝕜) : WithBotTop 𝕜)}
    have hSk_closed : IsClosed Sk := by
      simpa [Sk] using
        (lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf_closed) (m + δ k)
    have hSk_eventually : ∀ᶠ n in atTop, x (φ n) ∈ Sk := by
      refine Filter.eventually_atTop.2 ⟨k, ?_⟩
      intro n hn
      change f (x (φ n)) ≤
        ((m + δ k : 𝕜) : WithBotTop 𝕜)
      have hx' :
          f (x (φ n)) ≤
            ((m + δ (φ n) : 𝕜) : WithBotTop 𝕜) := by
        simpa [hiInf_eq] using hx_sub (φ n)
      refine le_trans hx' ?_
      have hdiv_le : δ (φ n) ≤ δ k := by
        have hle : (k : 𝕜) + 1 ≤ (φ n : 𝕜) + 1 := by
          exact_mod_cast Nat.succ_le_succ (le_trans hn (hφ.id_le n))
        simpa [δ, one_div] using
          (one_div_le_one_div_of_le (show (0 : 𝕜) < (k : 𝕜) + 1 by positivity) hle)
      simpa [add_comm, add_left_comm, add_assoc] using
        (WithBotTop.coe_le_coe.mpr (add_le_add_right hdiv_le m))
    have : a ∈ Sk := hSk_closed.mem_of_tendsto hconv hSk_eventually
    simpa [Sk, hr] using this
  have haS' : ((r : 𝕜) : WithBotTop 𝕜) ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) := by
    simpa [S, hr] using haS
  have ha_top : ((r : 𝕜) : WithBotTop 𝕜) < ⊤ :=
    lt_of_le_of_lt haS' (WithBotTop.coe_lt_top (m + 1))
  have hr_le : r ≤ m := by
    rw [le_iff_forall_pos_lt_add]
    intro η hη
    rcases exists_nat_one_div_lt hη with ⟨k, hk⟩
    have hak : ((r : 𝕜) : WithBotTop 𝕜) ≤
        ((m + δ k : 𝕜) : WithBotTop 𝕜) := ha_sublevel k
    have hr_le' : r ≤ m + (1 : 𝕜) / ((k : 𝕜) + 1) := by
      simpa [δ] using WithBotTop.coe_le_coe.mp hak
    nlinarith
  have ha_minimum : a ∈ minimumSet f := by
    rw [mem_minimumSet_iff_le_iInf]
    simpa [hiInf_eq, hr] using (WithBotTop.coe_le_coe.mpr hr_le :
      ((r : 𝕜) : WithBotTop 𝕜) ≤ (m : WithBotTop 𝕜))
  have ha_thick : a ∈ Metric.thickening ε (minimumSet f) := by
    rw [Metric.mem_thickening_iff]
    exact ⟨a, ha_minimum, by simpa using hε⟩
  have ha_not_thick : a ∉ Metric.thickening ε (minimumSet f) := by
    simpa [T] using haT
  exact ha_not_thick ha_thick

end MetricGeometry
