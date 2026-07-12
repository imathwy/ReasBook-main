import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_18_0_5

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Text 32.0.4 is a prose bridge from maximizing linear functionals on a convex
  set to the extreme-point geometry used later in Section 32.
- `core/canonical`: the owner abstractions already exist upstream as
  `Set.maximizers`, `LinearMap.isFace_maximizers`, `Set.IsFace`, `𝓕[𝕜](C)`, `IsMaxOn`, and
  `Set.IsFace.extremePoints_subset_of_mem_faces`.
- `bridge/view`: this file should not introduce a second "maximizer face" or "extreme maximizer"
  wrapper. The source-facing content is exactly the earlier face owner theorem, together with the
  standard face-to-extreme-point bridge.

Domain-style sampling used here:
- `Set.maximizers` and `Set.mem_maximizers_iff` from `Chap04/Text_18_0_5`;
- `LinearMap.isFace_maximizers` from `Chap04/Text_18_0_5`;
- `Set.IsFace.mem_faces_iff` and `Set.IsFace.extremePoints_subset_of_mem_faces` from
  `Chap04/Defn_18_1`;
- `Set.extremePoints` as the canonical owner for extreme points;
- `IsMaxOn` as the canonical maximizer predicate.

Primitive data vs derived API:
- primitive owner data: face-family membership `C.maximizers f ∈ 𝓕[𝕜](C)` for the maximizer owner;
- pointwise bridge data: membership in the owner is
  `x ∈ C.maximizers f ↔ x ∈ C ∧ IsMaxOn f C x`;
- derived source-facing API: for linear `h` on convex `C`, the previous chapter theorem
  `LinearMap.isFace_maximizers` supplies this face-family membership automatically.

Abstraction checks:
- codomain/ambient layer: the surface stays at an ordered-module codomain `β`, not `ℝ`/`EReal`;
- scalar minimization: the core theorem now uses only the primitive face owner data, and the
  linear-map/convex-set assumptions appear only in the derived source-facing corollary;
- owner correctness: the bridge uses canonical owners only (`Set.maximizers`, `Set.IsFace`,
  `𝓕[𝕜](C)`, `Set.extremePoints`);
- topology phrasing: this bridge is geometric/order-theoretic and introduces no ambient topology;
- notation surface: existing owner notation already expresses the source sentence directly.

Layer target: `bridge/view`.
-/

/- Text 32.0.4 uses the canonical owner for the maximizer slice of a map on `C`. -/
recall Set.maximizers

/- Membership in the maximizer owner is feasibility plus maximality on `C`. -/
recall Set.mem_maximizers_iff

/- Text 32.0.4: for a convex set `C`, the linear-map maximizer owner `C.maximizers h` is a face.
This is exactly the earlier owner theorem `LinearMap.isFace_maximizers`. -/
recall LinearMap.isFace_maximizers

/- Extreme points are owned canonically by `Set.extremePoints`. -/
recall Set.extremePoints

/- Extreme points of that maximizer face are therefore extreme points of the ambient convex set by
the standard face bridge `Set.IsFace.extremePoints_subset`. -/
recall Set.IsFace.extremePoints_subset

/- Face-family notation bridge used in this file: `F ∈ 𝓕[𝕜](C)` is equivalent to
`F.IsFace 𝕜 C`. -/
recall Set.IsFace.mem_faces_iff

/- Extreme points are monotone along membership in the face family `𝓕[𝕜](·)`. -/
recall Set.IsFace.extremePoints_subset_of_mem_faces

universe u v w

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]

section LinearMapBridge

variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {β : Type w} [AddCommMonoid β] [Module 𝕜 β]
variable [LinearOrder β] [IsOrderedCancelAddMonoid β] [PosSMulStrictMono 𝕜 β]

namespace LinearMap

/-- Text 32.0.4 owner bridge: on a convex set `C`, the linear-map maximizer owner belongs to the
face family `𝓕[𝕜](C)`. -/
theorem maximizers_mem_faces (h : E →ₗ[𝕜] β) {C : Set E} (hC : Convex 𝕜 C) :
    C.maximizers h ∈ 𝓕[𝕜](C) := by
  exact Set.IsFace.mem_faces_iff.2 (isFace_maximizers h hC)

/-- Text 32.0.4 bridge theorem: on a convex set `C`, extreme points of the maximizer face of a
linear map are extreme points of `C`. -/
theorem extremePoints_maximizers_subset (h : E →ₗ[𝕜] β) {C : Set E}
    (hC : Convex 𝕜 C) :
    (C.maximizers h).extremePoints 𝕜 ⊆ C.extremePoints 𝕜 := by
  exact Set.IsFace.extremePoints_subset_of_mem_faces (maximizers_mem_faces h hC)

end LinearMap
end LinearMapBridge

end
