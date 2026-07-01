import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set
open scoped Convex

section

namespace Set

section MaximizersOwner

variable {α : Type u} {β : Type v} [Preorder β]

/-- The maximizer slice of a function `f` on a set `C`. -/
def maximizers (C : Set α) (f : α → β) : Set α :=
  {x ∈ C | IsMaxOn f C x}

/-- Membership in `C.maximizers f` is feasibility in `C` plus maximality on `C`. -/
@[simp] theorem mem_maximizers_iff {f : α → β} {C : Set α} {x : α} :
    x ∈ C.maximizers f ↔ x ∈ C ∧ IsMaxOn f C x :=
  Iff.rfl

end MaximizersOwner

end Set

variable {𝕜 : Type v} [Semiring 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {β : Type w} [AddCommMonoid β] [Module 𝕜 β]

/-!
Source/core/bridge triage:
- `source-facing`: this item studies the subset of a convex set `C` where a linear
  map `h` attains its largest value.
- `core/canonical`: the chapter owner for the source statement is `Set.IsFace`; its primitive
  fields are `Convex` and `IsExtreme`.
- `bridge/view`: the maximizer slice `{x ∈ C | IsMaxOn h C x}` is shown to be an extreme subset
  first, then a face under the extra convexity hypothesis on `C`.

Domain-style sampling used here:
- `Set.maximizers`;
- `Set.IsFace`;
- `Set.IsFace.isExtreme`;
- `IsExtreme.right_mem_of_mem_openSegment`;
- `IsMaxOn`;
- `LinearMap.concaveOn`.

Primitive data vs derived API:
- primitive owner data: convexity of the maximizer slice and extremeness of that slice in `C`;
- pointwise source data: membership in the maximizer slice is `x ∈ C` together with `IsMaxOn h C x`;
- derived API: the face theorem itself and the segment-propagation consequence.
- ambient minimization: the reused owner lemmas `Set.IsFace`, `LinearMap.concaveOn`, and the
  segment concavity bounds all already live over the semiring and ordered-codomain layer, so no
  ring subtraction data belongs in the public statements here.

Layer target: `source-facing`, centered on the face owner `Set.IsFace`.
-/

section OrderedCodomain

variable [PartialOrder 𝕜]
variable [LinearOrder β] [PosSMulStrictMono 𝕜 β]

namespace Set

section SmulAmbient

variable {X : Type u} [AddCommMonoid X] [SMul 𝕜 X]

/-- A convex objective on `C` has an extreme maximizer slice in `C`. -/
theorem isExtreme_maximizers_of_convexOn {f : X → β} {C : Set X}
    [IsOrderedCancelAddMonoid β]
    (hf : ConvexOn 𝕜 C f) :
    IsExtreme 𝕜 C (C.maximizers f) := by
  refine ⟨fun _ hx ↦ hx.1, ?_⟩
  intro x hxC y hyC z hzMax hzSeg
  rcases hzMax with ⟨_, hzMax⟩
  refine ⟨hxC, ?_⟩
  intro w hwC
  have hy_le_z : f y ≤ f z := hzMax hyC
  have hz_le_x : f z ≤ f x := hf.le_left_of_right_le hxC hyC hzSeg hy_le_z
  exact (hzMax hwC).trans hz_le_x

/-- Primitive face constructor for maximizer slices: convexity of values along segments together
with extremeness of the slice yields facehood. -/
theorem isFace_maximizers_of_isExtreme_of_concaveOn {f : X → β} {C : Set X}
    [IsOrderedAddMonoid β]
    (hMax : IsExtreme 𝕜 C (C.maximizers f)) (hfConc : ConcaveOn 𝕜 C f) :
    (C.maximizers f).IsFace 𝕜 C := by
  refine ⟨?_, hMax⟩
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rcases hx with ⟨hxC, hxMax⟩
  rcases hy with ⟨hyC, hyMax⟩
  have hzC : z ∈ C := hfConc.1.segment_subset hxC hyC hz
  refine ⟨hzC, ?_⟩
  intro w hwC
  have hx_le_y : f x ≤ f y := hyMax hxC
  have hxz : f x ≤ f z := by
    simpa [min_eq_left hx_le_y] using hfConc.ge_on_segment hxC hyC hz
  exact (hxMax hwC).trans hxz

/-- A convex/concave objective on `C` has a maximizer slice that is a face of `C`. -/
theorem isFace_maximizers_of_convexOn_concaveOn {f : X → β} {C : Set X}
    [IsOrderedCancelAddMonoid β]
    (hfConv : ConvexOn 𝕜 C f) (hfConc : ConcaveOn 𝕜 C f) :
    (C.maximizers f).IsFace 𝕜 C := by
  exact isFace_maximizers_of_isExtreme_of_concaveOn
    (isExtreme_maximizers_of_convexOn (f := f) hfConv) hfConc

end SmulAmbient

section MulActionWithZeroAmbient

variable {X : Type u} [AddCommMonoid X] [MulActionWithZero 𝕜 X]

/-- If a maximizer lies in an open segment inside `C`, local convexity/concavity on `C`
force the whole segment to consist of maximizers. -/
theorem segment_subset_maximizers_of_mem_openSegment_of_isExtreme
    {f : X → β} {C : Set X} (hMax : IsExtreme 𝕜 C (C.maximizers f))
    [IsOrderedAddMonoid β]
    (hfConc : ConcaveOn 𝕜 C f)
    [ZeroLEOneClass 𝕜] {x y z : X}
    (hxyC : [x -[𝕜] y] ⊆ C) (hzSeg : z ∈ openSegment 𝕜 x y)
    (hzMax : z ∈ C.maximizers f) :
    [x -[𝕜] y] ⊆ C.maximizers f := by
  have hxC : x ∈ C := hxyC (left_mem_segment 𝕜 x y)
  have hyC : y ∈ C := hxyC (right_mem_segment 𝕜 x y)
  have hxMax : x ∈ C.maximizers f :=
    hMax.left_mem_of_mem_openSegment hxC hyC hzMax hzSeg
  have hyMax : y ∈ C.maximizers f :=
    hMax.right_mem_of_mem_openSegment hxC hyC hzMax hzSeg
  rcases hxMax with ⟨_, hxMax⟩
  rcases hyMax with ⟨_, hyMax⟩
  intro w hwSeg
  have hwC : w ∈ C := hxyC hwSeg
  refine ⟨hwC, ?_⟩
  intro u huC
  have hx_le_y : f x ≤ f y := hyMax hxC
  have hxw : f x ≤ f w := by
    simpa [min_eq_left hx_le_y] using hfConc.ge_on_segment hxC hyC hwSeg
  exact (hxMax huC).trans hxw

/-- If a maximizer lies in an open segment inside `C`, local convexity/concavity on `C`
force the whole segment to consist of maximizers. -/
theorem segment_subset_maximizers_of_mem_openSegment
    {f : X → β} {C : Set X}
    [IsOrderedCancelAddMonoid β]
    (hfConv : ConvexOn 𝕜 C f) (hfConc : ConcaveOn 𝕜 C f)
    [ZeroLEOneClass 𝕜] {x y z : X}
    (hxyC : [x -[𝕜] y] ⊆ C) (hzSeg : z ∈ openSegment 𝕜 x y)
    (hzMax : z ∈ C.maximizers f) :
    [x -[𝕜] y] ⊆ C.maximizers f := by
  exact segment_subset_maximizers_of_mem_openSegment_of_isExtreme
    (isExtreme_maximizers_of_convexOn (f := f) hfConv) hfConc hxyC hzSeg hzMax

end MulActionWithZeroAmbient

end Set

namespace LinearMap

/-- On a convex ambient set, the maximizer slice of a linear map is extreme. -/
theorem isExtreme_maximizers (h : E →ₗ[𝕜] β) [IsOrderedCancelAddMonoid β]
    {C : Set E} (hC : Convex 𝕜 C) :
    IsExtreme 𝕜 C (C.maximizers h) := by
  simpa using
    (Set.isExtreme_maximizers_of_convexOn (f := h) (h.convexOn hC))

/-- Text 18.0.5: for a convex set `C`, the set of points where the linear map `h`
attains its largest value on `C` is a face of `C`. -/
theorem isFace_maximizers (h : E →ₗ[𝕜] β) [IsOrderedCancelAddMonoid β]
    {C : Set E} (hC : Convex 𝕜 C) :
    (C.maximizers h).IsFace 𝕜 C := by
  simpa using
    (Set.isFace_maximizers_of_convexOn_concaveOn (f := h)
      (h.convexOn hC) (h.concaveOn hC))

/-- Text 18.0.5 (2): if a maximizer lies in the relative interior of a segment contained in `C`,
then the whole segment consists of maximizers. -/
theorem segment_subset_maximizers_of_mem_openSegment (h : E →ₗ[𝕜] β)
    [IsOrderedCancelAddMonoid β]
    [ZeroLEOneClass 𝕜]
    {C : Set E} (hC : Convex 𝕜 C) {x y z : E}
    (hxyC : [x -[𝕜] y] ⊆ C) (hzSeg : z ∈ openSegment 𝕜 x y)
    (hzMax : z ∈ C.maximizers h) :
    [x -[𝕜] y] ⊆ C.maximizers h := by
  simpa using
    (Set.segment_subset_maximizers_of_mem_openSegment
      (f := h) (h.convexOn hC) (h.concaveOn hC) hxyC hzSeg hzMax)

end LinearMap

end OrderedCodomain

end
