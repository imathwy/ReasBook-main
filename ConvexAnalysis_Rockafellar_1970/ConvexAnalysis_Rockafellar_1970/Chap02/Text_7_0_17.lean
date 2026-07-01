import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

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
