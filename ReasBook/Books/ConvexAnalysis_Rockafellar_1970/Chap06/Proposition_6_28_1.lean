import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_8
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Rockafellar

universe u v

namespace Function

section

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {ι : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 6.28.1 is the Slater-qualified subdifferential formula for the
  constrained objective from Definition 6.28.8.
- `core/canonical`: the owner abstractions already upstream are
  `Function.toWithTopBotOn` on the finite feasible-set owner for the constrained objective,
  `strictConvexInequalitySolutionSetOn` for the strict feasible region on the same finite
  subsystem, and
  `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom` for the
  intrinsic finite-sum subdifferential equality on the dual owner.
- `bridge/view`: the proposition rewrites the single constrained-objective owner into the sum of
  the lifted objective subdifferential and the individual indicator-sublevel subdifferentials, all
  on the intrinsic dual owner.

Domain-style sampling used here:
- the Definition 6.28.8 owner surface
  `Function.toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)`;
- `strictConvexInequalitySolutionSetOn` from `Chap04.Text_21_0_1`;
- `weakConvexInequalitySolutionSetOn` from `Chap04.Text_21_0_1`, the canonical Chapter 21 owner
  reused by Definition 6.28.8;
- `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom` from
  `Chap05.Theorem_23_8`.

Primitive data vs derived API:
- primitive source data: a `𝕜`-valued objective `f₀`, a finite subsystem `s`, a family of
  `𝕜`-valued constraints `f i`, their convexity on `s`, and the Chapter 21 strict feasible region
  for those inequalities;
- derived API: the intrinsic dual-owner subdifferential decomposition of the constrained
  objective.

Abstraction audit:
- codomain/scalar layer: this proposition lives on the ordered-field scalar layer `𝕜` and
  `WithTopBot 𝕜`, not on a concrete `ℝ` specialization.

Layer target: `source-facing`, but on the intrinsic dual-owner subdifferential layer and with the
feasible-set surface routed through the existing Chapter 21 weak/strict finite-subsystem owners
instead of the fully expanded mixed-relation feasible-set expression.
-/

-- Proof sketch: rewrite the constrained objective from Definition 6.28.8 as the finite sum of
-- `f₀.toWithTopBot` and the indicator functions of the individual sublevel sets
-- `{y | f i y ≤ 0}`. Use the finite-sum formula
-- `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom` from
-- Theorem 23.8.
-- A point of the Chapter 21 strict feasible set lies in the relative interior of every sublevel
-- set because each `f i` is finite and convex on `Set.univ`, hence continuous, so the common
-- relative-interior qualification holds.
/-- Proposition 6.28.1: if the finite-valued objective `f₀` and the constraint functions `f i`
indexed by the finite subsystem `s` are convex on all of `E`, and the Chapter 21 strict feasible
set of those inequalities is nonempty, then the subdifferential of the Definition 6.28.8
`toWithTopBotOn` owner on `weakConvexInequalitySolutionSetOn s f` equals the Minkowski sum of the
intrinsic dual-owner subdifferential of the objective lift and the intrinsic dual-owner
subdifferentials of the individual constraint indicators. -/
theorem
    subdifferentialAt_toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq
    (f₀ : E → 𝕜) (s : Finset ι) (f : ι → E → 𝕜)
    (hf₀_convex : ConvexOn 𝕜 Set.univ f₀)
    (hf_convex : ∀ i ∈ s, ConvexOn 𝕜 Set.univ (f i))
    (hstrict : (strictConvexInequalitySolutionSetOn s f).Nonempty)
    (x : E) :
    (∂ (toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)) at x) =
      (∂ f₀.toWithTopBot at x) +
        s.sum (fun i ↦ (∂ (δ[𝕜](· | {y : E | f i y ≤ 0})) at x)) := sorry

end

end Function
