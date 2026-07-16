import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_2_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_24

noncomputable section

open scoped Rockafellar
open Function

universe u v

namespace Bifunction

section Convexity

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (U × X)]
variable [AddCommGroup (U × X)] [Module 𝕜 (U × X)]
variable [IsTopologicalAddGroup (U × X)] [ContinuousConstSMul 𝕜 (U × X)]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.29.4 says that for a convex bifunction `F`, the bifunction
  closure `cl F` is closed and convex, and is proper exactly when `F` is proper.
- `core/canonical`: the existing owner for bifunction closure is `Bifunction.closure`, while the
  mathematical properties are already organized on the graph-function side through
  `Function.uncurry`, `Function.IsConvex`, `LowerSemicontinuous`, and `Function.IsProper`.
- `bridge/view`: the item is therefore best stated as the direct bifunction specialization of the
  Chapter 2 function-side closure theorems for `cl(·)`, using `uncurry_closure` from
  Definition 6.29.24 to identify the graph function of `cl F`.

Primary mathematical domain:
- convex extended-codomain bifunctions and the lower-semicontinuous hull of their graph
  functions.

Domain-style sampling used here:
- source-facing bifunction owner notation `convᵇ[𝕜](·)`, `closedᵇ(·)`, and `properᵇ(·)`;
- `Bifunction.closure` and `Bifunction.uncurry_closure` from `Definition_6_29_24`;
- `Function.IsConvex.lowerSemicontinuousHull_isConvex` from `Chap02.Corollary_7_2_2`;
- `lowerSemicontinuous_lowerSemicontinuousHull` from `Chap02.Text_7_0_4` through
  `Chap02.Corollary_7_2_2`;
- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper` from
  `Chap02.Theorem_7_4`;
- `Function.lowerSemicontinuousHull_not_isProper_of_not_isProper` from
  `Chap02.Corollary_7_2_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive source-facing owners: `convᵇ[𝕜](F)`, `closedᵇ(F)`, and `properᵇ(F)`;
- primitive source-facing closure owner: `cl F`;
- derived bridge API: uncurried graph-function forms used only as proof bridges.

Layer target: `source-facing` owner surfaces, with uncurried graph-function expressions retained
only as bridge statements when needed.
-/

-- Proof sketch: rewrite `Function.uncurry (cl F)` using `uncurry_closure`, then specialize
-- the Chapter 2 theorem `Function.IsConvex.lowerSemicontinuousHull_isConvex` to the graph
-- function `Function.uncurry F`.
/-- Proposition 6.29.4 (1): if a bifunction `F` is convex, then its closure `cl F` is convex. -/
theorem closure_isConvex
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F)) :
    convᵇ[𝕜](cl F) := by
  simpa [uncurry_closure] using hF_convex.lowerSemicontinuousHull_isConvex

end Convexity

section LowerSemicontinuity

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜] [NoMinOrder 𝕜]
variable [AddCommGroup 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜]
variable [Nonempty 𝕜]
variable [TopologicalSpace (U × X)]

-- Proof sketch: rewrite `Function.uncurry (cl F)` as `cl(Function.uncurry F)` by
-- `uncurry_closure`, then apply the Chapter 2 owner theorem
-- `lowerSemicontinuous_lowerSemicontinuousHull`.
/-- Proposition 6.29.4 (2), source owner notation form: the closure bifunction `cl F` is
graph-closed. -/
theorem closure_isGraphClosed
    {F : U → X → WithBotTop 𝕜} :
    closedᵇ(cl F) := by
  simpa [uncurry_closure] using
    (lowerSemicontinuous_lowerSemicontinuousHull (uncurry F))

/-- Bridge form of Proposition 6.29.4 (2): the graph function of `cl F` is lower
semicontinuous. -/
theorem lowerSemicontinuous_uncurry_closure
    {F : U → X → WithBotTop 𝕜} :
    LowerSemicontinuous (uncurry (cl F)) := by
  simpa using (closure_isGraphClosed (F := F))

end LowerSemicontinuity

section PropernessCore

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [NoBotOrder 𝕜]
variable [TopologicalSpace (U × X)]

-- Proof sketch: this is the contrapositive of the Chapter 2 persistence theorem
-- `Function.lowerSemicontinuousHull_not_isProper_of_not_isProper` after rewriting
-- `uncurry (cl F)` as `cl(uncurry F)`.
/-- Primitive properness direction: if the closure of a bifunction is proper, then the
bifunction is proper. -/
theorem proper_of_closure_proper
    {F : U → X → WithBotTop 𝕜}
    (hcl_proper : properᵇ(cl F)) :
    properᵇ(F) := by
  by_contra hF_not_proper
  exact
    (Function.lowerSemicontinuousHull_not_isProper_of_not_isProper hF_not_proper) <|
      by simpa [uncurry_closure] using hcl_proper

end PropernessCore

section Properness

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup (U × X)] [NormedSpace 𝕜 (U × X)]
variable [FiniteDimensional 𝕜 (U × X)]

-- Proof sketch: rewrite `uncurry (cl F)` as `cl(uncurry F)` and apply
-- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper`,
-- extracting the properness field.
/-- Primitive properness direction under the finite-dimensional convex hypotheses used in
Theorem 7.4: properness of `F` implies properness of `cl F`. -/
theorem closure_proper_of_proper
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F))
    (hF_proper : properᵇ(F)) :
    properᵇ(cl F) := by
  simpa [uncurry_closure] using
    (hF_convex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper hF_proper).proper

-- Proof sketch: combine the generic primitive direction
-- `proper_of_closure_proper` with the finite-dimensional convex direction
-- `closure_proper_of_proper`.
/-- Proposition 6.29.4 (3): for a convex bifunction `F`, `cl F` is proper
if and only if `F` is proper. -/
theorem closure_proper_iff
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F)) :
    properᵇ(cl F) ↔ properᵇ(F) := by
  constructor
  · exact proper_of_closure_proper
  · exact closure_proper_of_proper hF_convex

end Properness

end Bifunction
