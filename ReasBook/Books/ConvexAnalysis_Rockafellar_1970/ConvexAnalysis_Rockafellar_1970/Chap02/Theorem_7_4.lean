import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_10
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 E α : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable [TopologicalSpace (WithBotTop α)] [AddCommMonoid α] [SMul 𝕜 α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 7.4 says that for a proper convex function, the Chapter 7 closure
  `cl(f)` is a closed proper convex function and agrees with `f` away from the relative boundary
  of `dom(f)`.
- `core/canonical`: the owner abstractions already fixed in the project are
  `Function.IsConvex 𝕜`, `Function.IsProper`, Rockafellar's closure owner `cl(·)`, the effective
  domain owner `dom(·)`, mathlib's `intrinsicFrontier 𝕜` with chapter notation `rb[𝕜](·)`, and the
  chapter core predicate `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook phrase "except perhaps at relative boundary points of `dom f`" is
  rendered by a `Set.EqOn` statement on the complement of `rb[𝕜](dom(f))`.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsProper` and `dom(·)` from `Chap01.Definition_4_6` and `Chap01.Definition_4_4`;
- the relative-boundary notation `rb[𝕜](·)` from `Chap02.Text_6_10`;
- Rockafellar's closure owner `cl(·)` from `Chap02.Text_7_0_4`;
- the bundled closed/proper/convex predicate `Function.IsClosedProperConvex` from
  `Chap03.Text_12_3_6`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop α` on the chapter scalar/ambient layer,
  together with convexity and properness;
- derived outputs: the bundled closed/proper/convex status of `cl(f)` and the pointwise agreement
  of `cl(f)` with `f` off the relative boundary `rb[𝕜](dom(f))` of the effective domain.

Layer target: `source-facing`, stated directly on the canonical owners `cl(·)`,
`Function.IsClosedProperConvex`, and `intrinsicFrontier 𝕜`, with the chapter theorem surface
written using `rb[𝕜](·)`.

Remaining scalar/ambient strength rationale:
- the codomain layer is decoupled from the scalar: `f` is `WithBotTop α`-valued, with `α` carrying
  only the order/topology/module data needed by the imported owner APIs;
- the scalar layer is generalized from `ℝ` to `𝕜`, following the upstream owner surfaces used by
  `Function.IsConvex`, `cl(·)`, `rb[𝕜](·)`, and `Function.IsClosedProperConvex`;
- finite-dimensional normed ambient hypotheses are retained because this theorem is the
  finite-dimensional closure theorem in the chapter's current upstream dependency chain.
-/

namespace Function.IsConvex

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

variable {f : E → WithBotTop α}

-- Proof sketch: `hf_proper` rules out the `-∞` branch, so the closure operator stays the
-- lower-semicontinuous hull `cl(f)`. Convexity of `cl(f)` comes from closure of the convex
-- epigraph, lower semicontinuity is built into `cl(·)`, and the second clause of the theorem
-- shows that `cl(f)` is finite on `dom(f)`, which yields properness.
/-- Theorem 7.4: if `f` is a proper convex function on a finite-dimensional normed space,
then its Chapter 7 closure `cl(f)` is a closed proper convex function. -/
theorem lowerSemicontinuousHull_isClosedProperConvex_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    IsClosedProperConvex[𝕜] (cl(f)) := sorry

-- Proof sketch: on `ri(dom f)`, the epigraph argument from Lemma 7.3 and the line-intersection
-- closure theorem identify `cl(f)` with `f`. If `x ∉ closure dom(f)`, then both functions take
-- the value `⊤`. The only points not covered by these two cases are the relative-boundary points
-- of `dom(f)`.
/-- For a proper convex function, `cl(f)` agrees with `f` away from the relative boundary of its
effective domain. -/
theorem lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ := sorry

end Function.IsConvex

end
