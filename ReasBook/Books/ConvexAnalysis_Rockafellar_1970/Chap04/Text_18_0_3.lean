import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-!
Source/core/bridge triage:
- `source-facing`: a zero-dimensional face of `C` is a singleton face `{x}` of `C`; this is most
  naturally written on the chapter face-family notation `𝓕[R](C)`.
- `core/canonical`: owner-level content is still `Set.IsFace` together with `C.extremePoints R`.
- `bridge/view`: the primitive bridge is
  `Set.IsFace.singleton_iff_mem_extremePoints_of_convex`, and the no-noise module wrapper is
  `Set.IsFace.singleton_iff_mem_extremePoints`.
- Primitive data vs derived API: this item introduces no new data; it records the singleton-face /
  extreme-point identification both at the primitive layer and at the ordinary module wrapper
  layer.
- Domain-style sampling used here: `Set.IsFace`, `Set.IsFace.faces`, `𝓕[R](C)`,
  `Set.IsFace.mem_faces_iff`, `Set.IsFace.singleton_iff_mem_extremePoints_of_convex`,
  `Set.IsFace.singleton_iff_mem_extremePoints`, and `Set.extremePoints`.
- Layer target: `source-facing`, with theorem surfaces on chapter notation.

Abstraction checks:
- codomain/ambient layer: no ordered-extended codomain is involved.
- scalar/ambient minimization: we keep the primitive `[SMul R E]` bridge when singleton convexity
  is provided as data, and separately expose the no-noise `[Module R E]` wrapper theorem.
- owner correctness: `Set.IsFace` and `Set.extremePoints` are the intrinsic owners.
- topology phrasing: this item has no ambient-vs-relative topological content.
- notation surface: theorem surfaces are stated using `𝓕[R](C)`.
-/

namespace Set.IsFace

section

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [SMul R E]
variable {C : Set E} {x : E}

/-- Text 18.0.3, notation form at the primitive scalar-action layer: a singleton belongs to the
face family iff its point is extreme, once singleton convexity is given. -/
theorem singleton_mem_faces_iff_mem_extremePoints_of_convex
    (hxs : Convex R ({x} : Set E)) :
    ({x} : Set E) ∈ 𝓕[R](C) ↔ x ∈ C.extremePoints R := by
  simpa [Set.IsFace.mem_faces_iff] using
    (Set.IsFace.singleton_iff_mem_extremePoints_of_convex hxs)

end

section

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [Module R E]
variable {C : Set E} {x : E}

/-- Text 18.0.3, notation form at the ordinary module layer: singleton faces correspond exactly to
extreme points. -/
theorem singleton_mem_faces_iff_mem_extremePoints :
    ({x} : Set E) ∈ 𝓕[R](C) ↔ x ∈ C.extremePoints R :=
  singleton_mem_faces_iff_mem_extremePoints_of_convex (convex_singleton x)

end

end Set.IsFace

/- Text 18.0.3 (owner form, no-noise module wrapper): a singleton face `{x}` is equivalent to `x`
being an extreme point of `C`. -/
recall Set.IsFace.singleton_iff_mem_extremePoints

/- Text 18.0.3 (notation bridge, primitive layer): singleton-face membership in `𝓕[R](C)` is
equivalent to extreme-point membership once singleton convexity is provided. -/
recall Set.IsFace.singleton_mem_faces_iff_mem_extremePoints_of_convex

/- Text 18.0.3 (notation bridge, module layer): singleton-face membership in `𝓕[R](C)` is
equivalent to extreme-point membership. -/
recall Set.IsFace.singleton_mem_faces_iff_mem_extremePoints
