import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.4 states that the minimum set `M` of a convex function is a
  convex subset.
- `core/canonical`: the source-facing set owner is `minimumSet`, and the primitive convexity owner
  for this item is `QuasiconvexOn 𝕜 Set.univ f`; convexity of a minimum set only needs convexity
  of all closed sublevel sets.
- `bridge/view`: intrinsically, `minimumSet f` is the intersection of the sublevel sets
  `{x | f x ≤ f y}` over all `y`, so the canonical theorem applies `QuasiconvexOn` pointwise and
  intersects the resulting convex sets; Proposition 6.27.4 is then the specialization
  `Function.IsConvex → QuasiconvexOn`.

Domain-style sampling used here:
- the Chapter 6 minimum-set owner `minimumSet` from Definition 6.27.3;
- the extrema owner theorem `isMinOn_univ_iff` from mathlib;
- `QuasiconvexOn 𝕜 (Set.univ : Set E)` from mathlib's ordered convex-analysis owner layer;
- `Function.IsConvex 𝕜` from the chapter convex-function owner layer;
- `ConvexOn.convex_le` from mathlib for convex closed-sublevel sets.

Primitive data vs derived API:
- primitive input: a function `f` and a quasiconvexity owner on `Set.univ`;
- derived API: convexity of the canonical minimum set `minimumSet f`;
- source-facing specialization: the convex-function owner `f.IsConvex 𝕜`.

Layer target: `source-facing`, stated directly on the canonical owner `minimumSet f` rather than
on the equivalent raw sublevel-set expression.
-/

universe u v w

open scoped Rockafellar

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [Preorder β]

namespace QuasiconvexOn

-- Proof sketch: `minimumSet f` is exactly the intersection of the sublevel sets
-- `{x | f x ≤ f y}` as `y` varies. Quasiconvexity on `Set.univ` says each of these sublevel
-- sets is convex, and arbitrary intersections of convex sets are convex.
/-- A quasiconvex function on the whole ambient space has a convex minimum set. -/
theorem convex_minimumSet {f : E → β} (hf : QuasiconvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 (argmin(f)) := by
  have hminimumSet :
      argmin(f) = ⋂ y : E, {x : E | f x ≤ f y} := by
    ext x
    simp [mem_minimumSet_iff]
  rw [hminimumSet]
  refine convex_iInter ?_
  intro y
  simpa [Set.sep_univ] using hf (f y)

end QuasiconvexOn

/-- The minimum set of a quasiconvex function on the ambient space is convex. -/
theorem minimumSet_isConvex_of_quasiconvexOn {f : E → β}
    (hf_quasiconvex : QuasiconvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 (argmin(f)) :=
  hf_quasiconvex.convex_minimumSet

end

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

namespace ConvexOn

-- Proof sketch: rewrite `minimumSet f` as an intersection of closed sublevel sets
-- `{x | f x ≤ f y}` and apply the intrinsic owner theorem `ConvexOn.convex_le` to each
-- level `f y`.
/-- A convex function on the whole ambient space has a convex minimum set. -/
theorem convex_minimumSet {f : E → β} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 (argmin(f)) := by
  have hminimumSet :
      argmin(f) = ⋂ y : E, {x : E | f x ≤ f y} := by
    ext x
    simp [mem_minimumSet_iff]
  rw [hminimumSet]
  refine convex_iInter ?_
  intro y
  simpa [Set.sep_univ] using hf.convex_le (r := f y)

end ConvexOn

end

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

namespace Function.IsConvex

-- Proof sketch: pass from the chapter owner `Function.IsConvex` to whole-space quasiconvexity
-- via `Function.IsConvex.quasiconvexOn`, then apply `QuasiconvexOn.convex_minimumSet`.
/-- A convex function has a convex minimum set. -/
theorem convex_minimumSet {f : E → WithTopBot α} (hf : f.IsConvex 𝕜) :
    Convex 𝕜 (argmin(f)) := by
  exact (hf.quasiconvexOn).convex_minimumSet

end Function.IsConvex

/-- Proposition 6.27.4: the minimum set of a convex function is a convex subset of the ambient
module. -/
theorem minimumSet_isConvex {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) :
    Convex 𝕜 (argmin(f)) :=
  hf_convex.convex_minimumSet

end
