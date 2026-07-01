import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_32_2

open scoped Convex Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: this file records the Section 32 transfer from `C` to `rb[𝕜](C)` in the form
  actually consumed by the convex-hull maximization API.
- `core/canonical`: the primitive owner abstractions are set-local quasiconvexity
  `QuasiconvexOn 𝕜 C f`,
  `intrinsicFrontier 𝕜 C`, `convexHull 𝕜`, and the Section 32 owners
  `QuasiconvexOn.sSup_image_convexHull_eq` and
  `QuasiconvexOn.exists_isMaxOn_of_isMaxOn_convexHull`;
  source-facing `ConvexOn` statements are thin wrappers through
  `ConvexOn.quasiconvexOn`.
- `bridge/view`: the only geometric input needed here is the primitive hull identity
  `C = convexHull 𝕜 (rb[𝕜](C))`; stronger Chapter 18 recognition hypotheses belong in separate
  bridge files.

Domain-style sampling used here:
- `rb[𝕜](C)` notation for `intrinsicFrontier 𝕜 C`;
- `QuasiconvexOn.sSup_image_convexHull_eq`;
- `QuasiconvexOn.exists_isMaxOn_of_isMaxOn_convexHull`;
- `ConvexOn.quasiconvexOn`.

Primitive data vs derived API:
- primitive owner input: `hf : QuasiconvexOn 𝕜 C f` and
  `hC_hull : C = convexHull 𝕜 (rb[𝕜](C))`;
- derived source-facing API: convex-on wrappers from `ConvexOn` to the same
  transfer statements from `C` to `rb[𝕜](C)`.

Layer target: `bridge/view` at the primitive canonical layer, avoiding stronger recognition
assumptions in the public theorem surface.
-/

section

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

section SupremumClause

section CoreOwner

variable {β : Type*} [CompleteLattice β]
variable {f : E → β}

namespace QuasiconvexOn

/-- Corollary 32.2.1 at the primitive owner layer (supremum clause): if
`C = convexHull 𝕜 (rb[𝕜](C))`, then a quasiconvex function has the same supremum on `C` as on
`rb[𝕜](C)`. -/
theorem sSup_image_eq_sSup_image_rb_of_eq_convexHull
    {C : Set E} (hf : QuasiconvexOn 𝕜 C f)
    (hC_hull : C = convexHull 𝕜 (rb[𝕜](C))) :
    sSup (f '' C) = sSup (f '' rb[𝕜](C)) := by
  have hf_hull : QuasiconvexOn 𝕜 (convexHull 𝕜 (rb[𝕜](C))) f := by
    simpa [hC_hull] using hf
  have hSupHull : sSup (f '' convexHull 𝕜 (rb[𝕜](C))) = sSup (f '' rb[𝕜](C)) :=
    hf_hull.sSup_image_convexHull_eq
  simpa [hC_hull] using hSupHull

end QuasiconvexOn

end CoreOwner

section SourceFacing

variable {α : Type*} [AddCommMonoid α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
  [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable {f : E → WithTopBot α}

namespace ConvexOn

/-- Corollary 32.2.1, canonical bridge form (supremum clause): if
`C = convexHull 𝕜 (rb[𝕜](C))`, then a convex function on `C` has the same supremum on `C`
as on `rb[𝕜](C)`. -/
theorem sSup_image_eq_sSup_image_rb_of_eq_convexHull
    {C : Set E} (hf : ConvexOn 𝕜 C f)
    (hC_hull : C = convexHull 𝕜 (rb[𝕜](C))) :
    sSup (f '' C) = sSup (f '' rb[𝕜](C)) := by
  have hC_convex : Convex 𝕜 C := by
    simpa [hC_hull] using (convexHull_convex 𝕜 (rb[𝕜](C)))
  exact (hf.quasiconvexOn hC_convex).sSup_image_eq_sSup_image_rb_of_eq_convexHull hC_hull

end ConvexOn

end SourceFacing

end SupremumClause

section AttainmentClause

section CoreOwner

variable {β : Type*} [LinearOrder β]
variable {f : E → β}

namespace QuasiconvexOn

/-- Corollary 32.2.1 at the primitive owner layer (attainment clause): if
`C = convexHull 𝕜 (rb[𝕜](C))` and a quasiconvex function attains a maximum on `C`,
then it also attains a maximum on `rb[𝕜](C)`. -/
theorem exists_isMaxOn_rb_of_eq_convexHull_of_mem_of_isMaxOn
    {C : Set E} (hf : QuasiconvexOn 𝕜 C f)
    (hC_hull : C = convexHull 𝕜 (rb[𝕜](C)))
    {x : E} (hxC : x ∈ C) (hxmax : IsMaxOn f C x) :
    ∃ y ∈ rb[𝕜](C), IsMaxOn f (rb[𝕜](C)) y := by
  have hf_hull : QuasiconvexOn 𝕜 (convexHull 𝕜 (rb[𝕜](C))) f := by
    simpa [hC_hull] using hf
  have hxHull : x ∈ convexHull 𝕜 (rb[𝕜](C)) := by
    simpa [hC_hull] using hxC
  have hxmaxHull : IsMaxOn f (convexHull 𝕜 (rb[𝕜](C))) x := by
    simpa [hC_hull] using hxmax
  exact hf_hull.exists_isMaxOn_of_isMaxOn_convexHull hxHull hxmaxHull

/-- Corollary 32.2.1 at the primitive owner layer: existential packaging of
`exists_isMaxOn_rb_of_eq_convexHull_of_mem_of_isMaxOn`. -/
theorem exists_isMaxOn_rb_of_eq_convexHull_of_exists_isMaxOn
    {C : Set E} (hf : QuasiconvexOn 𝕜 C f)
    (hC_hull : C = convexHull 𝕜 (rb[𝕜](C)))
    (hmaxC : ∃ x ∈ C, IsMaxOn f C x) :
    ∃ y ∈ rb[𝕜](C), IsMaxOn f (rb[𝕜](C)) y := by
  rcases hmaxC with ⟨x, hxC, hxmax⟩
  exact hf.exists_isMaxOn_rb_of_eq_convexHull_of_mem_of_isMaxOn hC_hull hxC hxmax

end QuasiconvexOn

end CoreOwner

section SourceFacing

variable {α : Type*} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
  [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable {f : E → WithTopBot α}

namespace ConvexOn

/-- Corollary 32.2.1, canonical bridge form (attainment clause): if
`C = convexHull 𝕜 (rb[𝕜](C))` and a convex function on `C` attains a maximum on `C`, then it
also attains a maximum on `rb[𝕜](C)`. -/
theorem exists_isMaxOn_rb_of_eq_convexHull_of_mem_of_isMaxOn
    {C : Set E} (hf : ConvexOn 𝕜 C f)
    (hC_hull : C = convexHull 𝕜 (rb[𝕜](C)))
    {x : E} (hxC : x ∈ C) (hxmax : IsMaxOn f C x) :
    ∃ y ∈ rb[𝕜](C), IsMaxOn f (rb[𝕜](C)) y := by
  have hC_convex : Convex 𝕜 C := by
    simpa [hC_hull] using (convexHull_convex 𝕜 (rb[𝕜](C)))
  exact (hf.quasiconvexOn hC_convex).exists_isMaxOn_rb_of_eq_convexHull_of_mem_of_isMaxOn
    hC_hull hxC hxmax

/-- Corollary 32.2.1, derived existential packaging of
`exists_isMaxOn_rb_of_eq_convexHull_of_mem_of_isMaxOn`. -/
theorem exists_isMaxOn_rb_of_eq_convexHull_of_exists_isMaxOn
    {C : Set E} (hf : ConvexOn 𝕜 C f)
    (hC_hull : C = convexHull 𝕜 (rb[𝕜](C)))
    (hmaxC : ∃ x ∈ C, IsMaxOn f C x) :
    ∃ y ∈ rb[𝕜](C), IsMaxOn f (rb[𝕜](C)) y := by
  rcases hmaxC with ⟨x, hxC, hxmax⟩
  exact hf.exists_isMaxOn_rb_of_eq_convexHull_of_mem_of_isMaxOn hC_hull hxC hxmax

end ConvexOn

end SourceFacing

end AttainmentClause

end
