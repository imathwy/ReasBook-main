import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_7_0_14 (from Chap02) -/
noncomputable section

attribute [local instance] Classical.propDecidable

section

open scoped Rockafellar
open Function (verticalInfimum verticalInfimum_eq_sInf verticalInfimum_le_of_mem)

universe u

variable {X : Type u} [TopologicalSpace X]
variable {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIciTopology 𝕜] [Zero 𝕜]

/-- Canonical owner form behind Text 7.0.14: for any set in any topological space, the closure of
its indicator is the indicator of the set closure. -/
theorem lowerSemicontinuousHull_indicator_eq_indicator_closure (C : Set X) :
    cl((δ[𝕜](· | C))) = (δ[𝕜](· | closure C)) := by
  have hepi :
      closure (epi (δ[𝕜](· | C))) = epi (δ[𝕜](· | closure C)) := by
    calc
      closure (epi (δ[𝕜](· | C)))
          = closure (C ×ˢ Set.Ici (0 : 𝕜)) := by rw [epi_indicator_eq_prod]
      _ = closure C ×ˢ Set.Ici (0 : 𝕜) := by simp [closure_prod_eq]
      _ = epi (δ[𝕜](· | closure C)) := by rw [epi_indicator_eq_prod]
  ext x
  rw [lowerSemicontinuousHull, hepi]
  by_cases hx : x ∈ closure C
  · have hle :
        verticalInfimum (epi (δ[𝕜](· | closure C))) x ≤ (0 : WithBotTop 𝕜) :=
      verticalInfimum_le_of_mem <| by simp [indicator_def, hx]
    have hge :
        (0 : WithBotTop 𝕜) ≤
          verticalInfimum (epi (δ[𝕜](· | closure C))) x := by
      rw [verticalInfimum_eq_sInf]
      refine le_sInf ?_
      rintro _ ⟨μ, hμ, rfl⟩
      simpa [indicator_def, hx] using hμ
    have hvi :
        verticalInfimum (epi (δ[𝕜](· | closure C))) x = (0 : WithBotTop 𝕜) := by
      exact le_antisymm hle hge
    rw [hvi]
    simp [hx]
  · rw [Function.verticalInfimum_eq_sInf]
    simp [indicator_def, hx]

-- Proof sketch: specialize the canonical indicator-closure theorem to the set `Metric.ball x r`.
/-- Metric-ball specialization of the indicator-closure owner theorem. -/
theorem lowerSemicontinuousHull_indicator_ball_eq_indicator_closure_ball
    {E : Type*} [PseudoMetricSpace E] (x : E) (r : ℝ) :
    cl((δ[𝕜](· | Metric.ball x r))) =
      (δ[𝕜](· | closure (Metric.ball x r))) := by
  simpa using
    (lowerSemicontinuousHull_indicator_eq_indicator_closure
      (X := E) (C := Metric.ball x r))

-- Proof sketch: this is the `x = 0`, `r = 1` specialization of the ball-level bridge.
/-- Text 7.0.14 at intrinsic metric ambient level: for the open unit ball around `0`, the closure
of its indicator is the indicator of its closure. The source's `R²` open-unit-disk statement is
the Euclidean two-dimensional specialization of this theorem. -/
theorem lowerSemicontinuousHull_indicatorFunction_unitDisk_eq_indicatorFunction_closure_unitDisk
    {E : Type*} [PseudoMetricSpace E] [Zero E] :
    cl((δ[𝕜](· | Metric.ball (0 : E) (1 : ℝ)))) =
      (δ[𝕜](· | closure (Metric.ball (0 : E) (1 : ℝ)))) := by
  simpa using
    (lowerSemicontinuousHull_indicator_ball_eq_indicator_closure_ball
      (𝕜 := 𝕜) (x := (0 : E)) (r := (1 : ℝ)))

end

/-! ### Text_7_0_15 (from Chap02) -/
section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.15 says that for an improper convex function, the Chapter 2 closure
  `cl(f)` agrees with `f` on the relative interior of the effective domain.
- `core/canonical`: the owner abstractions already fixed earlier in the chapter are
  `Function.IsConvex 𝕜`, `Function.IsProper`, the closure owner `cl(·)`, and the scalar-indexed
  relative-interior notation `riDom[𝕜](·)`.
- `bridge/view`: the source-facing improperness assumption `¬ f.IsProper` is a wrapper over the
  primitive bottom-attainment datum `∃ x, f x = ⊥` once one has a domain point.

Domain-style sampling used here:
- `Function.IsConvex.eq_bot_of_mem_riDom_of_exists_eq_bot` from `Theorem_7_2`;
- `Function.not_isProper_iff_exists_eq_bot_of_nonempty_dom` from `Definition_4_6`;
- `lowerSemicontinuousHull_le` from `Text_7_0_4`;
- `Set.EqOn` as the canonical owner for agreement on `riDom[𝕜](f)`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop 𝕜`, the convexity owner
  `Function.IsConvex 𝕜 f`, and bottom-attainment data `∃ x, f x = ⊥`;
- derived output: agreement of `cl(f)` with `f` on `riDom[𝕜](f)`;
- source-facing wrapper: the same agreement theorem under `¬ f.IsProper`, discharged through the
  canonical improperness bridge once a domain point is provided by `riDom`.

Layer target: primitive owner theorem first, with a thin source-facing improperness wrapper.
-/

namespace Function.IsConvex

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithBotTop 𝕜}

/-- Primitive-data form of Text 7.0.15: if a convex function attains `⊥`, then `cl(f)` agrees
with `f` on `ri (dom f)`, represented here by `riDom[𝕜](f)`. -/
-- Proof sketch: Theorem 7.2 gives `f x = ⊥` on `riDom[𝕜](f)`. Also `cl(f) ≤ f` pointwise, so on
-- `riDom[𝕜](f)` one gets `cl(f) x ≤ ⊥`, hence `cl(f) x = ⊥` as well.
theorem cl_eqOn_riDom_of_exists_eq_bot
    (hf : f.IsConvex 𝕜) (hbot : ∃ x, f x = ⊥) :
    Set.EqOn (cl(f)) f riDom[𝕜](f) := by
  intro x hx
  have hfx_bot : f x = ⊥ := hf.eq_bot_of_mem_riDom_of_exists_eq_bot hbot hx
  have hcl_le : cl(f) x ≤ f x := lowerSemicontinuousHull_le f x
  have hcl_bot : cl(f) x = ⊥ := le_bot_iff.mp (by simpa [hfx_bot] using hcl_le)
  simp [hcl_bot, hfx_bot]

/-- Source-facing improperness form of Text 7.0.15. -/
theorem cl_eqOn_riDom_of_not_isProper
    (hf : f.IsConvex 𝕜) (hf_not_proper : ¬ f.IsProper) :
    Set.EqOn (cl(f)) f riDom[𝕜](f) := by
  intro x hx
  have hdom_nonempty : dom(f).Nonempty := ⟨x, intrinsicInterior_subset hx⟩
  rcases (Function.not_isProper_iff_exists_eq_bot_of_nonempty_dom (f := f) hdom_nonempty).1
      hf_not_proper with ⟨u, hu_eq_bot⟩
  exact cl_eqOn_riDom_of_exists_eq_bot hf ⟨u, hu_eq_bot⟩ hx

end Function.IsConvex

end

/-! ### Text_7_0_17 (from Chap02) -/
noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: the remark records that the strict inequality hypothesis
  `(⨅ x, f x) < α` in Theorem 7.6 is essential: when `α = inf f`, the closure and relative-interior
  formulas can fail.
- `core/canonical`: the counterexample function itself is the existing chapter indicator owner
  `δ[𝕜](· | Set.Ioi (0 : 𝕜))`, while the failure statements live on the Theorem 7.6 owner surface
  around `Function.IsConvex`, `Function.IsProper`, the Chapter 7 closure owner `cl(·)`, and the
  scalar-indexed relative-interior owners `ri[𝕜](·)` and `riDom[𝕜](·)`.
- `bridge/view`: this file keeps the explicit half-line indicator as the source-facing object,
  but the public owner layer is generalized from the concrete real model to a scalar-generic
  ordered/topological setting, with ring assumptions retained only on the `ri`/`riDom` clause.

Domain-style sampling used here:
- `indicator` / `δ[𝕜](· | C)`;
- `indicator_isConvex_iff`;
- `effectiveDomain_indicator`;
- `lowerSemicontinuousHull_indicator_eq_indicator_closure`;
- `Function.IsConvex.closure_openSublevel_eq_closedSublevel_lowerSemicontinuousHull`;
- `Function.IsConvex.intrinsicInterior_closedSublevel_eq_riDom_inter_openSublevel`;
- `closure`, `ri[𝕜](·)`, and `riDom[𝕜](·)`.

Primitive data vs derived API:
- primitive data: the canonical indicator owner `δ[𝕜](· | Set.Ioi (0 : 𝕜))`;
- derived API: convexity, properness, the boundary value `(⨅ x, f x) = 0`, and the two failure
  statements showing that the Theorem 7.6 formulas do not extend to `α = inf f`.

Layer target: `source-facing`, via the explicit half-line counterexample at the scalar-generic
canonical owner layer.
-/

section IndicatorOwners

variable {𝕜 : Type*} [Semiring 𝕜] [LinearOrder 𝕜]

/-- The indicator of the open positive half-line is convex in Rockafellar's global epigraph
sense. -/
-- Proof sketch: this is the `C = Set.Ioi (0 : 𝕜)` instance of the owner theorem
-- `indicator_isConvex_iff`.
theorem indicator_Ioi_isConvex :
    (δ[𝕜](· | Set.Ioi (0 : 𝕜))).IsConvex 𝕜 := sorry

/-- Assuming `∃ x, 0 < x`, the indicator of the open positive half-line is proper. -/
-- Proof sketch: every `x > 0` lies in the effective domain because the function value there is
-- `0`, while the definition gives no point where the function takes the value `-∞`.
theorem indicator_Ioi_isProper (hpos : ∃ x : 𝕜, 0 < x) :
    (δ[𝕜](· | Set.Ioi (0 : 𝕜))).IsProper := sorry

end IndicatorOwners

section ConditionallyComplete

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜]

/-- Assuming `∃ x, 0 < x`, the infimum of the indicator of the open positive half-line is `0`. -/
-- Proof sketch: the function never drops below `0`, since its only finite value is `0` and the
-- remaining values are `+∞`; conversely every `x > 0` realizes the value `0`, so `0` is the
-- indexed infimum.
theorem iInf_indicator_Ioi_eq_zero (hpos : ∃ x : 𝕜, 0 < x) :
    (⨅ x : 𝕜, δ[𝕜](x | Set.Ioi (0 : 𝕜))) = 0 := sorry

end ConditionallyComplete

section BoundaryClosureFailure

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ClosedIciTopology 𝕜]

/-- Text 7.0.17 (closure clause): at the boundary level
`α = inf f` for `f = δ[𝕜](· | Set.Ioi (0 : 𝕜))`, the closure formula from
Theorem 7.6 (3) fails when `∃ x, 0 < x`. -/
-- Proof sketch: `{x | f x < inf f} = ∅`, while `{x | cl(f) x ≤ inf f}` still contains the
-- boundary point `0`.
theorem closure_formula_fails_at_iInf_indicator_Ioi (hpos : ∃ x : 𝕜, 0 < x) :
    closure {x : 𝕜 | δ[𝕜](x | Set.Ioi (0 : 𝕜)) < (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))} ≠
      {x | cl((δ[𝕜](· | Set.Ioi (0 : 𝕜)))) x ≤ (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))} := sorry

end BoundaryClosureFailure

section BoundaryRelativeInteriorFailure

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ClosedIciTopology 𝕜]

/-- Text 7.0.17 (relative-interior clause): at the same boundary level `α = inf f`, the
relative-interior formula from Theorem 7.6 (2) fails for
`f = δ[𝕜](· | Set.Ioi (0 : 𝕜))` when `∃ x, 0 < x`. -/
-- Proof sketch: `{x | f x ≤ inf f}` is the positive half-line and has nonempty intrinsic
-- interior, while `riDom[𝕜](f) ∩ {x | f x < inf f} = ∅`.
theorem intrinsicInterior_formula_fails_at_iInf_indicator_Ioi (hpos : ∃ x : 𝕜, 0 < x) :
    ri[𝕜]({x : 𝕜 | δ[𝕜](x | Set.Ioi (0 : 𝕜)) ≤ (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))}) ≠
      riDom[𝕜]((δ[𝕜](· | Set.Ioi (0 : 𝕜)))) ∩
        {x : 𝕜 | δ[𝕜](x | Set.Ioi (0 : 𝕜)) < (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))} := sorry

/-- Text 7.0.17: for the proper convex counterexample `δ[𝕜](· | Set.Ioi (0 : 𝕜))`, the closure
formula from Theorem 7.6 (3) and the relative-interior formula from Theorem 7.6 (2) both fail at
the boundary level `α = inf f`, assuming `∃ x, 0 < x`. -/
theorem closure_and_intrinsicInterior_formulas_fail_at_iInf_indicator_Ioi
    (hpos : ∃ x : 𝕜, 0 < x) :
    (closure {x : 𝕜 | δ[𝕜](x | Set.Ioi (0 : 𝕜)) < (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))} ≠
      {x | cl((δ[𝕜](· | Set.Ioi (0 : 𝕜)))) x ≤ (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))}) ∧
    (ri[𝕜]({x : 𝕜 | δ[𝕜](x | Set.Ioi (0 : 𝕜)) ≤ (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))}) ≠
      riDom[𝕜]((δ[𝕜](· | Set.Ioi (0 : 𝕜)))) ∩
        {x : 𝕜 | δ[𝕜](x | Set.Ioi (0 : 𝕜)) < (⨅ y : 𝕜, δ[𝕜](y | Set.Ioi (0 : 𝕜)))}) := by
  exact ⟨closure_formula_fails_at_iInf_indicator_Ioi hpos,
    intrinsicInterior_formula_fails_at_iInf_indicator_Ioi hpos⟩

end BoundaryRelativeInteriorFailure

end

/-! ### Text_7_0_18 (from Chap02) -/
universe u

section

/-- Text 7.0.18: if `α` lies strictly below `inf f`, then the canonical closed `α`-sublevel set
`{x | f x ≤ α}` is empty, so the sublevel-set formulas from Theorem 7.6 are vacuous. -/
-- Proof sketch: if `x` belonged to the closed `α`-sublevel set, then
-- `⨅ y, f y ≤ f x ≤ α`, contradicting the strict inequality `α < ⨅ y, f y`.
theorem closedSublevel_eq_empty_of_lt_iInf
    {E : Type u} {β : Type*} [CompleteSemilatticeInf β] (f : E → β) (α : β)
    (hα : α < ⨅ x : E, f x) :
    {x | f x ≤ α} = (∅ : Set E) := by
  ext x
  constructor
  · intro hx
    have hInf_le : (⨅ y : E, f y) ≤ f x := by
      change sInf (Set.range f) ≤ f x
      exact sInf_le (s := Set.range f) (Set.mem_range.mpr ⟨x, rfl⟩)
    exact (not_le_of_gt hα) (hInf_le.trans hx)
  · intro hx
    exact False.elim hx

/- The boundary case `α = inf f` is genuinely different: Text 7.0.17 gives a concrete
counterexample showing that, at this boundary level, the closure and relative-interior formulas
from Theorem 7.6 can fail. -/

end

/-! ### Remark_7_0_21 (from Chap02) -/
section

/-!
Source/core/bridge triage:

- `source-facing`: Remark 7.0.21 observes that the chapter closure operator `cl(·)` acts as a
  normalization in convex analysis: it produces the lower-semicontinuous representative, and
  closed-epigraph functions are precisely fixed points of that normalization.
- `core/canonical`: the owner abstraction is the Chapter 2 closure operator
  `lowerSemicontinuousHull`, written `cl(·)`.
- `bridge/view`: the fixed-point sentence of the remark is already the upstream theorem
  `cl_eq_self_of_isClosed_epi`, derived from the epigraph-closure owner API.

Domain-style sampling used here:
- `lowerSemicontinuousHull` from `Text_7_0_4`;
- `closure_epi_eq_epi_lowerSemicontinuousHull` from `Text_7_0_4`;
- `cl_eq_self_of_isClosed_epi` from `Text_7_0_4`.

Primitive data vs derived API:
- primitive datum: a function `f`;
- owner abstraction: the closure operator `cl(f) = lowerSemicontinuousHull f`;
- derived API: the closed-epigraph fixed-point statement, which should be recalled directly rather
  than restated through a parallel local wrapper.

Layer target: `bridge/view`. This remark does not define new mathematical data, so the canonical
form is a direct recall of the existing owner theorem instead of a local alias or `_iff`
reformulation.
-/

/- Remark 7.0.21: the fixed-point clause for the chapter closure operator is the canonical theorem
`cl_eq_self_of_isClosed_epi`. -/
recall cl_eq_self_of_isClosed_epi

end

/-! ### Example_7_0_22 (from Chap02) -/
noncomputable section

section

open scoped Rockafellar
open Function

variable {𝕜 : Type*} {Y Z : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 7.0.22 fixes a finite convex function `f` on a product space
  `Y × Z`, defines the first-coordinate infimum
  `g(y) = inf_{z ∈ Z} f(y, z)`, and records the convexity and
  finiteness properties of `g` together with the consequence for lower bounds on first-coordinate
  fibers.
- `core/canonical`: the owner abstraction for taking infima along fibers is the intrinsic
  `Function.partialInfimum` from Text 5.7.2, together with the owner convexity predicate
  `Function.IsConvex` on `WithBotTop 𝕜`-valued functions.
- `bridge/view`: the textbook coordinate formula
  `g(ξ₁) = inf_{ξ₂} f(ξ₁, ξ₂)` is exactly `partialInfimum`.
  The equivalent linear-image view is given by specialization at the intrinsic product projection
  `LinearMap.fst 𝕜 Y Z : Y × Z →ₗ[𝕜] Y`.
  Rockafellar's statement that `g` is finite everywhere is rendered by the owner equality
  `dom(partialInfimum f.toWithBotTop) = Set.univ`, and "bounded below on a line
  parallel to the `ξ₂`-axis" is rendered by `BddBelow` of the corresponding fiber value set.
- Primitive data vs derived API: the primitive input is the finite-valued function `f`; the
  first-coordinate infimum is expressed directly by the intrinsic owner
  `Function.partialInfimum`, and the convexity/finiteness statements are companion API.
- Layer target: `source-facing` for the textbook consequences below, implemented directly through
  the intrinsic owner surface rather than through a duplicate local alias.

Domain-style sampling used here:
- `Function.partialInfimum_apply` from Text 5.7.2 as the
  intrinsic first-coordinate infimum owner formula;
- `Function.IsConvex.partialInfimum` from Text 5.7.2 as the owner convexity theorem;
- `Function.IsConvex.all_gt_bot_or_all_infinite` from
  Corollary 7.2.3
  as the owner dichotomy used in part (3).
-/

-- Proof sketch: apply Text 5.7.2 owner theorem `Function.IsConvex.partialInfimum`
-- to the canonical codomain lift `toWithBotTop f`.
/-- Example 7.0.22 (1): for a finite convex function `f` on `Y × Z`, the first-coordinate
infimum `g(y) = inf_{z ∈ Z} f(y, z)` is convex, in the canonical owner form
`(partialInfimum f.toWithBotTop).IsConvex 𝕜`. -/
theorem verticalLineInfimum_isConvex
    [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid Y] [Module 𝕜 Y] [AddCommMonoid Z] [Module 𝕜 Z]
    (f : Y × Z → 𝕜) (hf : ConvexOn 𝕜 (Set.univ : Set (Y × Z)) f) :
    (partialInfimum f.toWithBotTop).IsConvex 𝕜 := by
  simpa using
    Function.IsConvex.partialInfimum (h := f.toWithBotTop)
      (Function.isConvex_coe_of_convexOn_univ hf)

-- Proof sketch: choose a witness `z₀ : Z` and evaluate the defining infimum at `z₀`. This gives
-- `partialInfimum f.toWithBotTop y ≤ f (y, z₀) < ⊤`, hence every `y` lies in
-- `dom(partialInfimum f.toWithBotTop)`.
/-- Example 7.0.22 (2): the first-coordinate infimum has effective domain all of `Y`, in canonical
owner form `dom(g) = Set.univ`. -/
theorem dom_verticalLineInfimum_eq_univ
    {α : Type*} [ConditionallyCompleteLattice α] [Nonempty Z]
    (f : Y × Z → α) :
    dom(partialInfimum f.toWithBotTop) = Set.univ := by
  rcases ‹Nonempty Z› with ⟨z₀⟩
  ext y
  simp only [mem_effectiveDomain, Set.mem_univ, iff_true]
  have hsInf_le : partialInfimum f.toWithBotTop y ≤ f (y, z₀) := by
    rw [partialInfimum_apply]
    exact sInf_le ⟨z₀, rfl⟩
  exact lt_of_le_of_lt hsInf_le (WithBotTop.coe_lt_top (f (y, z₀)))

-- Proof sketch: apply Corollary 7.2.3 to the convex `WithBotTop 𝕜`-valued function
-- `partialInfimum f.toWithBotTop`. Part (2) identifies its effective domain with all of
-- `Y`, so the alternative "all values are infinite" reduces to `g y = -∞` for every `y`.
/-- Example 7.0.22 (3): the first-coordinate infimum of a finite convex function on `Y × Z` is
either finite everywhere in owner form `⊥ < g(y) < ⊤`, or equal to `-∞` everywhere on `Y`. -/
theorem verticalLineInfimum_all_finite_or_all_eq_bot
    [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (f : Y × Z → 𝕜) (hf : ConvexOn 𝕜 (Set.univ : Set (Y × Z)) f) :
    (∀ y : Y, ⊥ < partialInfimum f.toWithBotTop y ∧ partialInfimum f.toWithBotTop y < ⊤) ∨
      (∀ y : Y, partialInfimum f.toWithBotTop y = ⊥) := by
  have hlt_top (y : Y) : partialInfimum f.toWithBotTop y < ⊤ := by
    have hy : y ∈ dom(partialInfimum f.toWithBotTop) := by
      simp [dom_verticalLineInfimum_eq_univ f]
    simpa [mem_effectiveDomain] using hy
  have hdom_open : IsRelativelyOpen 𝕜 dom(partialInfimum f.toWithBotTop) := by
    simpa [dom_verticalLineInfimum_eq_univ f] using
      (IsOpen.isRelativelyOpen isOpen_univ : IsRelativelyOpen 𝕜 (Set.univ : Set Y))
  rcases
      Function.IsConvex.all_gt_bot_or_all_infinite
        (verticalLineInfimum_isConvex f hf)
        hdom_open with
    hfinite | hinf
  · left
    intro y
    exact ⟨hfinite y, hlt_top y⟩
  · right
    intro y
    rcases hinf y with hbot | htop
    · exact hbot
    · exfalso
      have hlt : (⊤ : WithBotTop 𝕜) < ⊤ := by
        have hlt' := hlt_top y
        rwa [htop] at hlt'
      exact (lt_irrefl (⊤ : WithBotTop 𝕜)) hlt

-- Proof sketch: if one first-coordinate fiber value set is `BddBelow`, then the infimum on that
-- fiber is not `-∞`. By part (3), the first-coordinate infimum therefore cannot be identically
-- `-∞`, so it is
-- finite everywhere. Translating finiteness of the infimum back to the fibers yields `BddBelow`
-- for every first-coordinate fiber value set.
/-- Example 7.0.22 (4): if a finite convex function on `Y × Z` is bounded below on one
first-coordinate fiber, then the value set on every such fiber is `BddBelow`. -/
theorem bddBelow_range_verticalLine_of_bddBelow_range_one_verticalLine
    [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (f : Y × Z → 𝕜) (hf : ConvexOn 𝕜 (Set.univ : Set (Y × Z)) f) {y₀ : Y}
    (hline : BddBelow (Set.range fun z : Z ↦ f (y₀, z))) (y : Y) :
    BddBelow (Set.range fun z : Z ↦ f (y, z)) := by
  rcases verticalLineInfimum_all_finite_or_all_eq_bot f hf with hfinite | hall_bot
  · rcases hfinite y with ⟨hgt, hlt⟩
    have hne_top : partialInfimum f.toWithBotTop y ≠ ⊤ := hlt.ne
    have hne_bot : partialInfimum f.toWithBotTop y ≠ ⊥ := ne_of_gt hgt
    lift (partialInfimum f.toWithBotTop y) to 𝕜 using ⟨hne_top, hne_bot⟩ with r hr'
    refine ⟨r, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hsInf_le : partialInfimum f.toWithBotTop y ≤ (f (y, z) : WithBotTop 𝕜) := by
      calc
        partialInfimum f.toWithBotTop y
            = sInf (Set.range fun z : Z ↦ (f (y, z) : WithBotTop 𝕜)) := by
              rw [partialInfimum_apply]
        _ ≤ (f (y, z) : WithBotTop 𝕜) := sInf_le ⟨z, rfl⟩
    exact (WithBotTop.coe_le_coe).1 <| by
      calc
        (r : WithBotTop 𝕜) = partialInfimum f.toWithBotTop y := by simpa using hr'
        _ ≤ (f (y, z) : WithBotTop 𝕜) := hsInf_le
  · rcases hline with ⟨a, ha⟩
    have hsInf_ge : (a : WithBotTop 𝕜) ≤ partialInfimum f.toWithBotTop y₀ := by
      rw [partialInfimum_apply]
      refine le_sInf ?_
      rintro _ ⟨z, rfl⟩
      exact show (a : WithBotTop 𝕜) ≤ (f (y₀, z) : WithBotTop 𝕜) by
        exact WithBotTop.coe_le_coe.2 (ha ⟨z, rfl⟩)
    exfalso
    have hge : (a : WithBotTop 𝕜) ≤ ⊥ := by
      rw [hall_bot y₀] at hsInf_ge
      exact hsInf_ge
    have hbot_lt : (⊥ : WithBotTop 𝕜) < a := WithBotTop.bot_lt_coe a
    exact (not_le_of_gt hbot_lt) hge

end

/-! ### Remark_7_0_23 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 E : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: the remark isolates the geometric locus governing the comparison between a
  convex function `f` and its closure `cl(f)`, namely the relative interior `ri[𝕜](epi f)` of the
  epigraph.
- `core/canonical`: the owner notions already present in the chapter are the convexity predicate
  `Function.IsConvex 𝕜`, the epigraph owner `epi`, Rockafellar's closure owner `cl(·)`, and the
  scalar-parameterized relative-interior notation `ri[𝕜](·)`.
- `bridge/view`: the prose claim that the comparison between `f` and `cl(f)` hinges on relative
  interiors is rendered as equality of the two epigraph relative interiors.

Domain-style sampling used here:
- `Function.IsConvex` from Theorem 4.2;
- `epi` from Definition 4.1;
- `ri[𝕜](·)` from Text 6.8;
- `cl(·)` and `closure_epi_eq_epi_lowerSemicontinuousHull` from Text 7.0.4.

Primitive data vs derived API:
- primitive input: a convex `WithBotTop 𝕜`-valued function `f`;
- primitive geometric output: closure-invariance of the epigraph relative interior
  `ri[𝕜](closure (epi f)) = ri[𝕜](epi f)`;
- derived closure-operator output: the common relative interior of `epi f` and `epi (cl(f))`.

Layer target: `source-facing`, stated directly in the chapter's epigraph and relative-interior
language rather than through a separate wrapper around the later comparison theorems.
-/

namespace Function.IsConvex

section Geometry

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable {f : E → WithBotTop 𝕜}

/-- Primitive geometric owner form behind Remark 7.0.23: for a convex function, the relative
interior of the epigraph is invariant under ambient closure. -/
theorem ri_closure_epi_eq (hf : f.IsConvex 𝕜) :
    ri[𝕜](closure (epi f)) = ri[𝕜](epi f) := by
  simpa using hf.convex_epi.intrinsicInterior_closure_eq_intrinsicInterior

end Geometry

section LowerSemicontinuousHull

variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: Text 7.0.4 identifies `epi (cl(f))` with `closure (epi f)`. Since `epi f` is
-- convex by `hf`, Theorem 6.3 gives invariance of relative interior under closure for that set,
-- yielding the claimed identity.
/-- Remark 7.0.23: for a convex function, the comparison between `f` and its closure `cl(f)` is
governed by the common relative interior of their epigraphs; equivalently,
`ri[𝕜](epi (cl(f))) = ri[𝕜](epi f)`. -/
theorem ri_epi_lowerSemicontinuousHull_eq
    (hf : f.IsConvex 𝕜) :
    ri[𝕜](epi (cl(f))) = ri[𝕜](epi f) := by
  calc
    ri[𝕜](epi (cl(f))) = ri[𝕜](closure (epi f)) := by
      simp [closure_epi_eq_epi_lowerSemicontinuousHull]
    _ = ri[𝕜](epi f) := hf.ri_closure_epi_eq

end LowerSemicontinuousHull

end Function.IsConvex

end

/-! ### Remark_7_0_24 (from Chap02) -/
section

open scoped Rockafellar

universe u

variable {𝕜 E : Type u}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: in the improper case, Text 7.0.15 identifies `f` with its lower-semicontinuous
-- hull `cl(f)` on `riDom[𝕜](f)`. In the proper case, Theorem 7.4 gives the same identification
-- away from the relative frontier `rb[𝕜](dom(f))`. If `x ∉ closure (dom(f))`, then a neighborhood
-- of
-- `x` is disjoint from `dom(f)`, so `f = ⊤` near `x` and lower semicontinuity is immediate.
/-- Remark 7.0.24: a convex extended-real-valued function is lower semicontinuous at every point
outside the relative boundary `rb[𝕜](dom(f))` of its effective domain. Equivalently, any failure
of lower semicontinuity can occur only at relative-boundary points of `dom(f)`. -/
theorem lowerSemicontinuousAt_of_not_mem_intrinsicFrontier_dom
    (hf : f.IsConvex 𝕜) {x : E} (hx : x ∉ rb[𝕜](dom(f))) :
    LowerSemicontinuousAt f x := by
  by_cases hx_closure : x ∈ closure (dom(f))
  · have hx_ri : x ∈ riDom[𝕜](f) := by
      rw [← closure_diff_intrinsicFrontier (dom(f))]
      exact ⟨hx_closure, hx⟩
    have hcl_eq_fx : cl(f) x = f x := by
      by_cases hf_proper : f.IsProper
      · have hEqOn : Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ := by
          simpa using
            hf.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper hf_proper
        exact hEqOn (by simpa using hx)
      · exact hf.cl_eqOn_riDom_of_not_isProper hf_proper hx_ri
    have hcl_lsc_at : LowerSemicontinuousAt (cl(f)) x :=
      (lowerSemicontinuous_lowerSemicontinuousHull f).lowerSemicontinuousAt x
    have hcl_liminf : cl(f) x ≤ Filter.liminf (cl(f)) (nhds x) :=
      (lowerSemicontinuousAt_iff_le_liminf).1 hcl_lsc_at
    have hliminf_mono :
        Filter.liminf (cl(f)) (nhds x) ≤ Filter.liminf f (nhds x) :=
      Filter.liminf_le_liminf <| Filter.Eventually.of_forall (lowerSemicontinuousHull_le f)
    exact (lowerSemicontinuousAt_iff_le_liminf).2 <|
      by simpa [hcl_eq_fx] using hcl_liminf.trans hliminf_mono
  · have hx_not_dom : x ∉ dom(f) := fun hx_dom ↦ hx_closure (subset_closure hx_dom)
    have hfx_top : f x = ⊤ := by
      by_contra hfx_ne_top
      exact hx_not_dom <| mem_effectiveDomain.2 <| lt_of_le_of_ne le_top hfx_ne_top
    change SemicontinuousAt (fun x' y ↦ y < f x') x
    intro y hy
    have hy_top : y < (⊤ : WithBotTop 𝕜) := by
      simpa [hfx_top] using hy
    have hnhds :
        (closure (dom(f)))ᶜ ∈ nhds x :=
      (isOpen_compl_iff.mpr isClosed_closure).mem_nhds hx_closure
    filter_upwards [hnhds] with x' hx'
    have hx'_not_dom : x' ∉ dom(f) := fun hx'_dom ↦ hx' (subset_closure hx'_dom)
    have hfx'_top : f x' = ⊤ := by
      by_contra hfx'_ne_top
      exact hx'_not_dom <| mem_effectiveDomain.2 <| lt_of_le_of_ne le_top hfx'_ne_top
    simpa [hfx'_top] using hy_top

/-- The `ri(dom f)` formulation in Remark 7.0.24 is the relative-interior specialization of the
full off-boundary theorem. -/
theorem lowerSemicontinuousAt_of_mem_riDom
    (hf : f.IsConvex 𝕜) {x : E} (hx : x ∈ riDom[𝕜](f)) :
    LowerSemicontinuousAt f x := by
  apply hf.lowerSemicontinuousAt_of_not_mem_intrinsicFrontier_dom
  intro hx_frontier
  have hpair : x ∈ closure (dom(f)) \ rb[𝕜](dom(f)) := by
    rw [closure_diff_intrinsicFrontier (dom(f))]
    simpa using hx
  exact hpair.2 hx_frontier

end Function.IsConvex

/- The relative continuity assertion mentioned in this remark is exactly the Chapter 10 owner
theorem `Function.IsConvex.continuousOn_riDom`. -/
recall Function.IsConvex.continuousOn_riDom

end

/-! ### Remark_7_0_25 (from Chap02) -/
noncomputable section

universe u

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: the remark records a concrete `WithBotTop ℝ`-valued example on the unit ball,
  with value `-√(1 - ‖x‖²)` on the open unit ball and `+∞` on its boundary and exterior.
- `core/canonical`: the chapter owner abstractions are `Function.IsConvex ℝ`,
  `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull`, and the affine-combination owner
  `lineMap`.
- `bridge/view`: the textbook formula `(1 - λ) x + λ y` is rendered by `lineMap x y λ`, and the
  source-facing boundary value `0` is the specialization of the closure value `cl(f) y` at points
  with `‖y‖ = 1`.

Domain-style sampling used here:
- `Function.IsConvex` on `WithBotTop ℝ`-valued functions, available from Mathlib/project owners;
- `Function.toWithBotTopOn` for extension by `+∞` outside the open unit ball;
- `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull` from Theorem 7.5;
- `AffineMap.lineMap` for the segment parameterization.

Primitive data vs derived API:
- primitive data: the explicit formula `x ↦ -√(1 - ‖x‖²)` on the open unit ball, extended by `⊤`
  outside;
- derived API: the convexity theorem for that function and the boundary-limit specialization of the
  Chapter 7 owner theorem.

Layer target: the function definition is `source-facing`; the limit theorem is `bridge/view`,
stated as the concrete boundary-value specialization of the canonical owner theorem from
Theorem 7.5 rather than as a second boundary-limit owner.
-/

variable {E : Type u} [Norm E]

/-- The `WithBotTop ℝ`-valued function equal to `-√(1 - ‖x‖²)` on the open unit ball and `+∞`
outside it. -/
def openUnitBallNegativeSqrtExtension : E → WithBotTop ℝ :=
  Function.toWithBotTopOn
    (fun x : E ↦ -Real.sqrt (1 - ‖x‖ ^ 2))
    {x : E | ‖x‖ < 1}

@[simp] theorem openUnitBallNegativeSqrtExtension_of_norm_lt_one {x : E} (hx : ‖x‖ < 1) :
    openUnitBallNegativeSqrtExtension x =
      ((-(Real.sqrt (1 - ‖x‖ ^ 2)) : ℝ) : WithBotTop ℝ) := by
  simpa [openUnitBallNegativeSqrtExtension] using
    (Function.toWithBotTopOn_of_mem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      {y : E | ‖y‖ < 1} hx)

@[simp] theorem openUnitBallNegativeSqrtExtension_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) :
    openUnitBallNegativeSqrtExtension x = (⊤ : WithBotTop ℝ) := by
  exact
    Function.toWithBotTopOn_of_notMem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      {y : E | ‖y‖ < 1}
      (by simpa using (not_lt_of_ge hx))

end

section

open AffineMap Filter
open scoped Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "fUnit" => (openUnitBallNegativeSqrtExtension (E := E))

-- Proof sketch: this is the canonical Chapter-7 owner theorem specialized to the present
-- source-facing function, with endpoint hypothesis on the intrinsic closure of the effective
-- domain.
/-- Canonical owner-level segment-limit statement for `openUnitBallNegativeSqrtExtension`: from
`x ∈ riDom[ℝ](f)` toward any endpoint `y ∈ intrinsicClosure ℝ dom(f)`, the profile along
`lineMap x y` converges to `cl(f) y` as `t → 1⁻`. -/
theorem tendsto_openUnitBallNegativeSqrtExtension_lineMap_left_to_cl_of_mem_intrinsicClosure_dom
    {x y : E} (hconv : Function.IsConvex ℝ fUnit) (hx : x ∈ riDom[ℝ](fUnit))
    (hy : y ∈ intrinsicClosure ℝ dom(fUnit)) :
    Tendsto (fun t : ℝ ↦ fUnit (lineMap x y t))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (cl(fUnit) y)) := by
  simpa using
    (Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull_of_mem_intrinsicClosure_dom
      (f := fUnit) hconv (x := x) (y := y) hx hy)

-- Proof sketch: as `t → 1⁻`, the points `AffineMap.lineMap x y t` approach the boundary point
-- `y`. The quantity `1 - ‖AffineMap.lineMap x y t‖²` tends to `0` through nonnegative values, so
-- the interior branch `-√(1 - ‖·‖²)` tends to `0`, which is the boundary value of the
-- lower-semicontinuous hull predicted by Theorem 7.5.
/-- At a boundary point `y` with `‖y‖ = 1`, the segment profile of
`openUnitBallNegativeSqrtExtension` from any `x ∈ riDom[ℝ](fUnit)` tends to `0` as the parameter
approaches `1` from the left. -/
theorem tendsto_openUnitBallNegativeSqrtExtension_lineMap_left_to_zero_of_norm_eq_one
    {x y : E} (hx : x ∈ riDom[ℝ](fUnit)) (hy : ‖y‖ = 1) :
    Tendsto (fun t : ℝ ↦ fUnit (lineMap x y t))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (0 : WithBotTop ℝ)) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "fUnit" => (openUnitBallNegativeSqrtExtension (E := E))

-- Proof sketch: the function is smooth on the open unit ball, hence convex on the interior of its
-- effective domain. The companion boundary-limit theorem supplies the Theorem-7.5 style limit
-- relation at points with `‖y‖ = 1`, which is the use of Theorem 7.5 highlighted by the remark
-- for this explicit example.
/-- Remark 7.0.25: the `WithBotTop ℝ`-valued function that equals `-√(1 - ‖x‖²)` on the open unit
ball and `+∞` for `‖x‖ ≥ 1` is convex. -/
theorem openUnitBallNegativeSqrtExtension_isConvex :
    Function.IsConvex ℝ fUnit := sorry

end
