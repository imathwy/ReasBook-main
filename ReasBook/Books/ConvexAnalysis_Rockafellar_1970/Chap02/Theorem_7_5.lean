import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open AffineMap Filter
open scoped Rockafellar

variable {𝕜 E α : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [Preorder α] [ConditionallyCompleteLattice α] [TopologicalSpace α]
  [TopologicalSpace (WithTopBot α)]
  [AddCommMonoid α] [SMul 𝕜 α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 7.5 gives the boundary-limit formula for a convex function along the
  segment from a point `x ∈ ri (dom f)` to an arbitrary point `y`, with value at the boundary
  represented by the closure `cl(f) y`.
- `core/canonical`: the owner abstractions already present in the project are `Function.IsConvex`,
  `Function.IsProper`, the effective-domain owners `dom(·)` and `riDom[𝕜](·)`, Rockafellar's closure
  owner `cl(·)`, the affine-combination owner `lineMap`, and the filter owner
  `Tendsto ... (nhdsWithin 1 (Set.Iio 1))`, with codomain neighborhoods taken in the
  ambient topological structure on `WithTopBot α`.
- `bridge/view`: the textbook formula
  `(1 - λ) x + λ y` is rendered canonically by `lineMap x y λ`, and the one-sided limit
  `λ ↑ 1` is rendered by `nhdsWithin (1 : 𝕜) (Set.Iio 1)`.

Domain-style sampling used here:
- `riDom[𝕜](·)` and `dom(·)` from Definition 4.4;
- `Function.IsProper` from Definition 4.6;
- `Function.IsConvex` from Theorem 4.2;
- Rockafellar's closure owner `cl(·)` from Text 7.0.4.

Primitive data vs derived API:
- primitive inputs for the numbered theorem: the convex function `f`, the properness hypothesis,
  the base point `x ∈ riDom[𝕜](f)`, and an arbitrary endpoint `y`;
- derived companion API: the intrinsic-closure specialization/extension where the endpoint
  hypothesis is stated explicitly as `y ∈ intrinsicClosure 𝕜 dom(f)`.

Layer target: the main theorem stays `source-facing`, but it is stated directly on the canonical
owner layer of `Tendsto`, `lineMap`, and `cl(·)` rather than as a bespoke "limit exists"
wrapper.

Ambient-space refinement: this chapter-level boundary theorem is kept on the established
finite-dimensional normed-space scalar layer over an ordered/topological scalar `𝕜`, with
intrinsic/relative-domain operators `riDom[𝕜](·)` and `intrinsicClosure 𝕜`; only the codomain is
generalized to the ordered extended layer `WithTopBot α` used by the chapter closure owner `cl(·)`.
-/

namespace Function.IsConvex

variable {f : E → WithTopBot α}

/-- Theorem 7.5: if `f` is a proper convex function and `x ∈ riDom[𝕜](f)`, then for every `y`
the values of `f` along the segment `λ ↦ lineMap x y λ` converge to `cl(f) y` as
`λ → 1` from the left. -/
-- Proof sketch: if `y ∈ intrinsicClosure 𝕜 dom(f)`, use the companion intrinsic-closure theorem
-- below. If `y ∉ intrinsicClosure 𝕜 dom(f)`, the Chapter 7 closure/domain theorems identify the
-- boundary value as `cl(f) y = ⊤`, and properness forces the segment profile to tend to `⊤` as
-- the endpoint leaves the closure of the effective domain.
theorem tendsto_lineMap_to_lowerSemicontinuousHull
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) {x y : E} (hx : x ∈ riDom[𝕜](f)) :
    Tendsto (fun t : 𝕜 ↦ f (lineMap x y t))
      (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
      (nhds (cl(f) y)) := sorry

/-- Boundary-value extension of the segment-limit formula: if
`y ∈ intrinsicClosure 𝕜 dom(f)`, then the same convergence to `cl(f) y` holds without assuming
properness of `f`. -/
-- Proof sketch: use Lemma 7.3 to place `(x, α)` in `ri(epi f)` for every scalar `α > f x`, then
-- apply Theorem 6.1 to the segment joining `(x, α)` to a point of `closure (epi f)` over `y`.
-- This gives the upper bound on the limsup. The lower bound comes from lower semicontinuity of
-- `cl(f)` and the pointwise inequality `cl(f) ≤ f`. When `f` is improper, Corollary 7.2.1
-- identifies the whole segment profile with `⊥` on the intrinsic closure of the effective domain.
theorem tendsto_lineMap_to_lowerSemicontinuousHull_of_mem_intrinsicClosure_dom
    (hf : f.IsConvex 𝕜) {x y : E} (hx : x ∈ riDom[𝕜](f))
    (hy : y ∈ intrinsicClosure 𝕜 dom(f)) :
    Tendsto (fun t : 𝕜 ↦ f (lineMap x y t))
      (nhdsWithin (1 : 𝕜) (Set.Iio (1 : 𝕜)))
      (nhds (cl(f) y)) := sorry

end Function.IsConvex

end
