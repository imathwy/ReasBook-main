import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 26.2.1 introduces strict convexity on a convex set and the Chapter
  26 notion of essential strict convexity for a proper convex function, phrased through convex
  subsets of the subdifferential domain.
- `core/canonical`: the owner abstractions are mathlib's
  `StrictConvexOn 𝕜 C g`, `Function.IsConvex`, `Function.IsProper`, and the canonical
  relation-domain owner `dom∂[Y](f)` at explicit pairing codomain `Y`.
- `bridge/view`: the textbook set `{x | ∂f(x) ≠ ∅}` is the companion reformulation of the
  canonical owner domain `dom∂[Y](f)` via
  `mem_subdifferentialGraph_dom`.

Domain-style sampling used here:
- `StrictConvexOn` from mathlib's convex-function owner layer;
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `SetRel.dom` specialized to the subdifferential graph in `Chap05.Definition_5_24_1`.

Primitive data vs derived API:
- primitive source data: a proper convex function `f : E → WithTopBot 𝕜` and pairing codomain `Y`;
- primitive owner: `Function.IsEssentiallyStrictlyConvex f Y`, storing convexity, properness,
  and strict convexity of `f` on each convex subset of `dom∂[Y](f)`;
- derived API: the textbook reformulation using pointwise nonemptiness `∂[Y]f(x) ≠ ∅`.

Layer target:
- `StrictConvexOn`: `core/canonical` recall, since the source strict-convexity clause already has
  the canonical mathlib owner;
- `Function.IsEssentiallyStrictlyConvex`: `source-facing`, because this numbered item is the
  source definition site of the Chapter 26 notion;
- `strictConvexOn_of_forall_subdifferentialAt_nonempty`: `bridge/view` at the canonical
  nonemptiness layer;
- `strictConvexOn_of_forall_subdifferentialAt_ne_empty`: `bridge/view` in textbook `≠ ∅` form.
-/

/- Definition 26.2.1 (strict-convexity clause): the source notion of a function being strictly
convex on a convex set is the canonical mathlib owner `StrictConvexOn`. -/
recall StrictConvexOn

namespace Function

section

variable {𝕜 : Type _} [Semiring 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-- Definition 26.2.1: a proper `WithTopBot 𝕜`-valued function is essentially strictly convex
when it is strictly convex on every convex subset of the canonical subgradient-domain owner
`dom∂[Y](f)`. -/
@[mk_iff]
class IsEssentiallyStrictlyConvex (f : E → WithTopBot 𝕜)
    (Y : Type _ := StrongDual 𝕜 E) [HasPairing E Y 𝕜] : Prop where
  convex : f.IsConvex 𝕜
  proper : f.IsProper
  strictConvexOn {C : Set E} (hC_convex : Convex 𝕜 C) (hC_dom : C ⊆ dom∂[Y](f)) :
      StrictConvexOn 𝕜 C f

namespace IsEssentiallyStrictlyConvex

/-- Canonical nonemptiness bridge for Definition 26.2.1: on any convex set contained in the points
where `∂[Y]f(x)` is nonempty, `f` is strictly convex. -/
theorem strictConvexOn_of_forall_subdifferentialAt_nonempty
    {f : E → WithTopBot 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : IsEssentiallyStrictlyConvex (Y := Y) f)
    {C : Set E} (hC_convex : Convex 𝕜 C)
    (hC_subdiff_nonempty : ∀ ⦃x : E⦄, x ∈ C → (∂[Y]f(x)).Nonempty) :
    StrictConvexOn 𝕜 C f := by
  have hC_dom : C ⊆ dom∂[Y](f) := by
    intro x hx
    exact (_root_.mem_domSubdifferential_iff_nonempty (f := f) (Y := Y)).2
      (hC_subdiff_nonempty hx)
  exact hf.strictConvexOn hC_convex hC_dom

/-- Textbook reformulation of Definition 26.2.1 in `≠ ∅` form. -/
theorem strictConvexOn_of_forall_subdifferentialAt_ne_empty
    {f : E → WithTopBot 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : IsEssentiallyStrictlyConvex (Y := Y) f)
    {C : Set E} (hC_convex : Convex 𝕜 C)
    (hC_subdiff_nonempty : ∀ ⦃x : E⦄, x ∈ C → ∂[Y]f(x) ≠ ∅) :
    StrictConvexOn 𝕜 C f := by
  refine strictConvexOn_of_forall_subdifferentialAt_nonempty (Y := Y) hf hC_convex ?_
  intro x hx
  exact Set.nonempty_iff_ne_empty.2 (hC_subdiff_nonempty hx)

end IsEssentiallyStrictlyConvex

end

end Function
