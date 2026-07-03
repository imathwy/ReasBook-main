import Mathlib
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_18_0_1 (from Chap04) -/
open scoped Rockafellar

/-!
Source/core/bridge triage:
- `source-facing`: Text 18.0.1 says the empty set is a face of any set.
- `core/canonical`: the chapter owner is `Set.IsFace`; the source sentence is exactly
  `Set.IsFace.empty`.
- `bridge/view`: no extra bridge theorem is needed, since this is already an owner theorem.

Abstraction checks:
- codomain/ambient layer: no ordered-extended codomain is involved.
- scalar/ambient minimization: the reused owner theorem is already at the weak primitive layer
  `[Semiring R] [PartialOrder R] [SMul R E]`, not a concrete `ℝ`/module specialization.
- owner correctness: `Set.IsFace` is the intrinsic chapter owner; no concrete-model wrapper appears.
- topology phrasing: this item has no ambient-vs-relative topological content.
- notation surface: expose both the owner-facing statement and the textbook face-family surface
  `(∅ : Set E) ∈ 𝓕[R](C)` through owner theorem `Set.IsFace.empty_mem_faces`.
-/

/-- Text 18.0.1 (notation form): the empty set belongs to every face family. -/
recall Set.IsFace.empty_mem_faces

/-- Text 18.0.1: the empty set is a face of any set.

This source statement is exposed at the intrinsic set-theoretic surface `∅`. -/
recall Set.IsFace.empty

/-! ### Text_18_0_2 (from Chap04) -/
open scoped Rockafellar

/-!
Source/core/bridge triage:
- `source-facing`: the item states that a convex set is a face of itself.
- `core/canonical`: the source-facing owner is `Set.IsFace`, with reflexivity theorem
  `Set.IsFace.refl`.
- `bridge/view`: for textbook face-family notation, use the canonical bridge theorem
  `Set.IsFace.mem_faces_self` from `Defn_18_1`.

Abstraction checks:
- codomain/ambient layer: no ordered extended codomain is involved in this item;
  the statement only concerns face ownership on sets.
- scalar/ambient minimization: the reused owner theorem already lives over the weak
  `[Semiring R] [PartialOrder R] [SMul R E]` layer from `Defn_18_1`, not a concrete
  real-scalar/module specialization.
- owner correctness: `Set.IsFace` is the intrinsic chapter owner for faces; no concrete-model
  wrapper is present.
- topology phrasing: this item has no topological content, so there is no ambient-vs-relative
  topology choice to normalize.
- notation surface: the source-facing API is exposed both in owner form (`C.IsFace R C`) and
  in textbook face-family notation form `C ∈ 𝓕[R](C)` through the canonical bridge theorem
  `Set.IsFace.mem_faces_self`.

Domain-style sampling used here:
- `Set.IsFace`;
- `𝓕[R](C) = Set.IsFace.faces R C`;
- `Set.IsFace.mem_faces_iff`;
- `Set.IsFace.mem_faces_self`;
- `Set.IsFace.refl`;
- `Convex`.
-/

/- Text 18.0.2 (notation form): every convex set belongs to its own face family. -/
recall Set.IsFace.mem_faces_self

/- Text 18.0.2: every convex set is a face of itself. This is exactly the owner theorem
`Set.IsFace.refl`. -/
recall Set.IsFace.refl

/-! ### Text_18_0_3 (from Chap04) -/
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

/-! ### Text_18_0_5 (from Chap04) -/
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

/-! ### Text_18_0_6 (from Chap04) -/
universe u v

section

open Set

/-!
Source/core/bridge triage:
- `source-facing`: Text 18.0.6 says that an exposed subset of a convex set is a face of that set.
- `core/canonical`: the owner abstractions are mathlib's `IsExposed 𝕜 A B` together with the
  chapter face owner `B.IsFace 𝕜 A`.
- `bridge/view`: this item keeps the exposed-set bridge on the canonical `IsExposed` owner and
  builds facehood directly from primitive owner data (`Convex 𝕜 B` and `IsExtreme 𝕜 A B`).

Domain-style sampling used here:
- `Set.IsFace.of_convex_isExtreme`;
- `IsExposed.convex_semiring`;
- `IsExposed.isExtreme_semiring`;
- `IsExposed.isFace_of_convex`;
- `IsExposed`;
- `ContinuousLinearMap.toExposed`;
- `ContinuousLinearMap.toLinearMap.convexOn`;
- `ContinuousLinearMap.toLinearMap.concaveOn`;
- `Set.IsFace`, used in its canonical postfix surface form `B.IsFace 𝕜 A`.

Primitive data vs derived API:
- primitive owner data for facehood: convexity of `B` plus extremality of `B` in `A`;
- source-facing derived input: the exposed-set hypothesis `hAB : IsExposed 𝕜 A B`, where
  the primitive exposing-functional witness is used directly to recover extremality and
  convexity, avoiding stronger ring-only bridge lemmas.

Layer target: `bridge/view`.
-/

section Exposed

namespace IsExposed

section ConvexProjection

variable {𝕜 : Type v} [TopologicalSpace 𝕜] [Semiring 𝕜] [PartialOrder 𝕜]
  [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable {E : Type u} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]

/-- Primitive owner bridge at the partially ordered semiring layer: exposed subsets of convex sets
are convex. This matches `IsExposed.convex` but avoids upgrading to ring assumptions. -/
theorem convex_semiring {A B : Set E} (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) :
    Convex 𝕜 B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
  · obtain ⟨l, rfl⟩ := hAB hB
    intro x₁ hx₁ x₂ hx₂ a b ha hb hab
    refine ⟨hA hx₁.1 hx₂.1 ha hb hab, ?_⟩
    intro y hyA
    exact
      ((l.toLinearMap.concaveOn convex_univ).convex_ge _
        ⟨mem_univ _, hx₁.2 y hyA⟩ ⟨mem_univ _, hx₂.2 y hyA⟩ ha hb hab).2

end ConvexProjection

section ExtremeProjection

variable {𝕜 : Type v} [TopologicalSpace 𝕜] [Semiring 𝕜] [LinearOrder 𝕜]
  [IsOrderedCancelAddMonoid 𝕜] [PosSMulStrictMono 𝕜 𝕜]
variable {E : Type u} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]

/-- Primitive owner bridge at the ordered-semiring layer: exposed subsets are extreme. This
matches `IsExposed.isExtreme` but avoids upgrading to ring assumptions. -/
theorem isExtreme_semiring {A B : Set E} (hAB : IsExposed 𝕜 A B) :
    IsExtreme 𝕜 A B := by
  refine ⟨?_, ?_⟩
  · intro x hxB
    rcases hAB ⟨x, hxB⟩ with ⟨l, rfl⟩
    exact hxB.1
  · intro x₁ hx₁A x₂ hx₂A x hxB hxSeg
    rcases hAB ⟨x, hxB⟩ with ⟨l, rfl⟩
    have hl : ConvexOn 𝕜 (Set.univ : Set E) l := l.toLinearMap.convexOn convex_univ
    have hlx₁ : l x₁ ≤ l x := hxB.2 x₁ hx₁A
    have hlx₂ : l x₂ ≤ l x := hxB.2 x₂ hx₂A
    have hlxx₁ : l x ≤ l x₁ :=
      hl.le_left_of_right_le (mem_univ _) (mem_univ _) hxSeg hlx₂
    refine ⟨hx₁A, ?_⟩
    intro y hyA
    exact (hxB.2 y hyA).trans hlxx₁

/-- Derived bridge: exposed subsets are faces once convexity of that subset is available. -/
theorem isFace_of_convex {A B : Set E} (hAB : IsExposed 𝕜 A B) (hB : Convex 𝕜 B) :
    B.IsFace 𝕜 A :=
by
  exact Set.IsFace.of_convex_isExtreme hB hAB.isExtreme_semiring

/-- Text 18.0.6: every exposed subset of a convex set is a face of that set. -/
theorem isFace {A B : Set E} (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) :
    B.IsFace 𝕜 A :=
by
  exact hAB.isFace_of_convex (hAB.convex_semiring hA)

end ExtremeProjection

end IsExposed

end Exposed

end

/-! ### Text_18_0_7 (from Chap04) -/
universe u v

section

open Set

variable {𝕜 : Type v} [TopologicalSpace 𝕜] [Semiring 𝕜] [Preorder 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
variable {C F : Set E}
local notation "E⋆" => StrongDual 𝕜 E

/-!
Source/core/bridge triage:
- `source-facing`: the item identifies nonempty exposed faces of a convex set with supporting
  level-set slices, and then records the proper-face refinement by nontrivial supporting
  hyperplanes.
- `core/canonical`: the owner abstraction for exposed faces is `IsExposed 𝕜 C F`, and the
  supporting slice is most economically represented by a continuous linear functional together with
  one of its supporting level sets; properness is what upgrades this to a nonzero hyperplane
  description.
- `bridge/view`: this item is a bridge theorem relating the canonical exposed-face predicate to the
  supporting-functional description of the same hyperplane cut.

Domain-style sampling used here:
- `IsExposed 𝕜 C F`;
- `E⋆`;
- canonical maximizer owner surfaces `C.maximizers l`;
- preorder-level supporting slices `{x ∈ C | a ≤ l x}` and supporting half-spaces
  `{x | l x ≤ a}`.

Primitive data vs derived API:
- the primitive mathematical inputs are the ambient set `C`, the candidate subset `F`, and
  nonemptiness of `F`;
- properness of `F` is only needed for the nontrivial-hyperplane refinement, not for the core
  supporting-level-set characterization;
- the containment `F ⊆ C` is derived on both sides of the bridge statement, so it should not
  remain a primitive binder;
- the supporting-hyperplane description is theorem-level bridge API from `IsExposed`, written
  directly as existence data rather than stored in a second wrapper predicate;
- ambient minimization: the statement can stay on the ordered-semiring preorder layer by avoiding
  order antisymmetry (`l x = a`) on theorem surfaces and keeping only the primitive half-space/slice
  inequalities, so it should not be specialized to `ℝ`.

Layer target: `bridge/view`.
-/

namespace IsExposed

/-- Primitive constructor bridge on the canonical owner surface. -/
theorem of_eq_maximizers
    (l : E⋆) (hF_eq : F = C.maximizers l) :
    IsExposed 𝕜 C F := by
  intro _
  refine ⟨l, ?_⟩
  simpa [Set.maximizers, IsMaxOn] using hF_eq

/-- Primitive elimination bridge on the canonical owner surface. -/
theorem exists_eq_maximizers
    (hF : IsExposed 𝕜 C F) (hF_ne : F.Nonempty) :
    ∃ l : E⋆, F = C.maximizers l := by
  rcases hF hF_ne with ⟨l, hF_eq⟩
  refine ⟨l, ?_⟩
  simpa [Set.maximizers, IsMaxOn] using hF_eq

/-- Core bridge: for nonempty `F`, exposedness is equivalent to one maximizer-set equation. -/
theorem iff_exists_eq_maximizers (hF_ne : F.Nonempty) :
    IsExposed 𝕜 C F ↔ ∃ l : E⋆, F = C.maximizers l := by
  constructor
  · intro hF
    exact hF.exists_eq_maximizers hF_ne
  · rintro ⟨l, hF_eq⟩
    exact of_eq_maximizers l hF_eq

/-- Proper-face refinement on the canonical owner surface: for nonempty proper `F`, the exposing
functional can be chosen nonzero. -/
theorem iff_exists_nonzero_eq_maximizers (hF_ne : F.Nonempty) (hproper : F ≠ C) :
    IsExposed 𝕜 C F ↔
      ∃ l : E⋆, l ≠ 0 ∧ F = C.maximizers l := by
  rw [iff_exists_eq_maximizers hF_ne]
  constructor
  · rintro ⟨l, hF_eq⟩
    refine ⟨l, ?_, hF_eq⟩
    intro hl
    apply hproper
    calc
      F = C.maximizers l := hF_eq
      _ = C := by
        ext x
        simp [Set.maximizers, isMaxOn_iff, hl]
  · rintro ⟨l, _, hF_eq⟩
    exact ⟨l, hF_eq⟩

/-- Derived constructor bridge: a supporting threshold-slice description yields exposedness. -/
theorem of_supporting_levelSet
    (l : E⋆) (a : 𝕜) (hC : C ⊆ {x : E | l x ≤ a})
    (hF_eq : F = {x ∈ C | a ≤ l x}) :
    IsExposed 𝕜 C F := by
  intro hF_ne
  refine ⟨l, ?_⟩
  ext x
  constructor
  · intro hxF
    rw [hF_eq] at hxF
    refine ⟨hxF.1, ?_⟩
    intro y hyC
    exact (hC hyC).trans hxF.2
  · intro hx
    rcases hF_ne with ⟨x₀, hx₀F⟩
    have hx₀ : x₀ ∈ {x ∈ C | a ≤ l x} := by
      simpa [hF_eq] using hx₀F
    have ha_le : a ≤ l x := (hx₀.2).trans (hx.2 x₀ hx₀.1)
    rw [hF_eq]
    exact ⟨hx.1, ha_le⟩

/-- Derived constructor bridge: existentially packaged supporting threshold-slice data yields
exposedness. -/
theorem of_exists_supporting_levelSet :
    (∃ l : E⋆, ∃ a : 𝕜,
      C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x}) →
      IsExposed 𝕜 C F := by
  rintro ⟨l, a, hC, hF_eq⟩
  exact of_supporting_levelSet l a hC hF_eq

/-- Forward bridge: a nonempty exposed subset admits one supporting threshold-slice
representation. -/
theorem exists_supporting_levelSet
    (hF : IsExposed 𝕜 C F) (hF_ne : F.Nonempty) :
    ∃ l : E⋆, ∃ a : 𝕜,
      C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x} := by
  rcases hF_ne with ⟨x₀, hx₀F⟩
  rcases hF.exists_eq_maximizers ⟨x₀, hx₀F⟩ with ⟨l, hF_eq_max⟩
  refine ⟨l, l x₀, ?_, ?_⟩
  · intro x hxC
    have hx₀Max : x₀ ∈ C ∧ ∀ y ∈ C, l y ≤ l x₀ := by
      simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hx₀F
    exact hx₀Max.2 x hxC
  · ext x
    constructor
    · intro hxF
      have hxMax : x ∈ C ∧ ∀ y ∈ C, l y ≤ l x := by
        simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hxF
      have hx₀Max : x₀ ∈ C ∧ ∀ y ∈ C, l y ≤ l x₀ := by
        simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hx₀F
      refine ⟨hxMax.1, ?_⟩
      exact hxMax.2 x₀ hx₀Max.1
    · intro hx
      have hx₀Max : x₀ ∈ C ∧ ∀ y ∈ C, l y ≤ l x₀ := by
        simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hx₀F
      have hxMax : x ∈ C ∧ ∀ y ∈ C, l y ≤ l x := by
        refine ⟨hx.1, ?_⟩
        intro y hyC
        exact (hx₀Max.2 y hyC).trans hx.2
      have hxMax' : x ∈ C.maximizers l := by
        simpa [Set.maximizers, isMaxOn_iff] using hxMax
      simpa [hF_eq_max] using hxMax'

/-- Text 18.0.7, core bridge: for a nonempty subset `F` of `C`, being exposed is equivalent to
having one supporting threshold-slice description. -/
theorem iff_exists_supporting_levelSet (hF_ne : F.Nonempty) :
    IsExposed 𝕜 C F ↔
      ∃ l : E⋆, ∃ a : 𝕜,
        C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x} := by
  constructor
  · intro hF
    exact hF.exists_supporting_levelSet hF_ne
  · rintro ⟨l, a, hC, hF_eq⟩
    exact of_supporting_levelSet l a hC hF_eq

/-- Text 18.0.7, proper-face refinement: for a nonempty proper subset `F` of `C`, the supporting
functional in the level-set characterization can be chosen nonzero, so the supporting hyperplane is
nontrivial. -/
theorem iff_exists_nonzero_supporting_levelSet (hF_ne : F.Nonempty) (hproper : F ≠ C) :
    IsExposed 𝕜 C F ↔
      ∃ l : E⋆, ∃ a : 𝕜,
        l ≠ 0 ∧ C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x} := by
  rw [iff_exists_supporting_levelSet hF_ne]
  constructor
  · rintro ⟨l, a, hC, hF_eq⟩
    refine ⟨l, a, ?_, hC, hF_eq⟩
    intro hl
    apply hproper
    ext x
    constructor
    · intro hxF
      rw [hF_eq] at hxF
      exact hxF.1
    · intro hxC
      rw [hF_eq]
      rcases hF_ne with ⟨x₀, hx₀F⟩
      have hx₀ : x₀ ∈ {x ∈ C | a ≤ l x} := by
        simpa [hF_eq] using hx₀F
      have ha_le_zero : a ≤ (0 : 𝕜) := by
        simpa [hl] using hx₀.2
      exact ⟨hxC, by simpa [hl] using ha_le_zero⟩
  · rintro ⟨l, a, _, hC, hF_eq⟩
    exact ⟨l, a, hC, hF_eq⟩

end IsExposed

end

/-! ### Text_18_0_8 (from Chap04) -/
/-!
Source/core/bridge triage:
- `source-facing`: the text says that every exposed point of a convex set is an extreme point.
- `core/canonical`: mathlib's owner abstractions are `Set.exposedPoints` and
  `Set.extremePoints`.
- `bridge/view`: the source sentence is exactly the canonical subset theorem
  `exposedPoints_subset_extremePoints`.
- Primitive data vs derived API: this item introduces no new data; it records a direct consequence
  between two existing canonical point sets.
- Domain-style sampling used here: `Set.exposedPoints`,
  `mem_exposedPoints_iff_exposed_singleton`, `IsExposed.isExtreme`, and
  `exposedPoints_subset_extremePoints`.
- Layer target: `core/canonical`, by direct recall of the existing owner theorem.

Abstraction checks:
- codomain/ambient layer: this item has no ordered-extended function codomain surface.
- scalar/ambient minimization: the canonical theorem already carries the needed scalar/topological
  layer and is not a concrete model specialization.
- owner correctness: `Set.exposedPoints` and `Set.extremePoints` are the intrinsic owners.
- topology phrasing: this item is not an ambient-vs-relative topology statement.
- notation surface: the owner-level set inclusion is already the canonical theorem surface.
-/

/- Text 18.0.8: every exposed point of a convex set is an extreme point. The canonical theorem
`exposedPoints_subset_extremePoints` is strictly stronger, since it is stated for an arbitrary set
(with no convexity hypothesis). -/
recall exposedPoints_subset_extremePoints

/-! ### Text_18_0_9 (from Chap04) -/
/-!
Source/core/bridge triage:
- `source-facing`: Text 18.0.9 characterizes exposed directions of `C` as rays `r` for which some
  affine half-line `affineHalfLine x r` is exposed in `C`.
- `core/canonical`: the owner is `Set.exposedDirections`, built from `IsExposed` on
  `affineHalfLine`.
- `bridge/view`: `Defn_18_5` already packages the source phrasing by quantifying over exposed
  affine half-lines, via `Set.mem_exposedDirections_iff`.

Domain-style sampling used here:
- `IsExposed`;
- `affineHalfLine`;
- `Set.exposedDirections`;
- `Set.mem_exposedDirections_iff`.

Primitive data vs derived API:
- primitive owner data (`Set.exposedDirections`) is defined upstream in `Defn_18_5`;
- this item records the source-facing membership characterization bridge
  `Set.mem_exposedDirections_iff`.

Abstraction checks:
- codomain/ambient layer: no ordered-extended codomain appears in this item;
- scalar/ambient minimization: the bridge theorem already lives over the weakest owner layer used
  by `Set.exposedDirections`, with no `ℝ` specialization;
- owner correctness: `Set.exposedDirections` is the intrinsic direction owner for exposed
  half-line faces;
- topology phrasing: this item is not an ambient-vs-relative topology theorem;
- notation surface: owner-level theorem surface is primary; no extra notation owner is needed.
-/

/- Text 18.0.9: exposed directions are exactly rays carried by exposed affine half-line faces.
This is the canonical bridge theorem `Set.mem_exposedDirections_iff` on the owner
`Set.exposedDirections`. -/
recall Set.mem_exposedDirections_iff

/-! ### Text_18_0_10 (from Chap04) -/
/-!
Source/core/bridge triage:
- `source-facing`: Text 18.0.10 says that every exposed ray of a convex cone is an extreme ray.
- `core/canonical`: the primitive direction-owner theorem is
  `ConvexCone.IsExposedRay.isExtremeRay`.
- `bridge/view`: the source-facing subset theorem `IsExposedRay.isExtremeRay` is kept upstream as a
  bridge through `originRay`; this text item recalls the primitive owner surface directly.

Abstraction checks:
- codomain/ambient layer: no ordered-extended codomain appears in this item.
- scalar/ambient minimization: the primitive theorem already lives on the chapter's cone/ray owner
  layer, with no `ℝ`-specialized binder surface.
- owner correctness: `ConvexCone.IsExposedRay` and `ConvexCone.IsExtremeRay` are the intrinsic
  direction owners; the subset surface remains a bridge.
- topology phrasing: this item is not an ambient-vs-relative topology theorem.
- notation surface: the canonical owner theorem surface is already primary;
  no additional notation is required.
-/

/- Text 18.0.10: every exposed direction ray of a convex cone is an extreme direction ray. This is
the canonical primitive-owner theorem `ConvexCone.IsExposedRay.isExtremeRay`. -/
recall ConvexCone.IsExposedRay.isExtremeRay

/-! ### Text_18_0_11 (from Chap04) -/
open Set
open scoped Rockafellar

section

local notation "R3" => ℝ × ℝ × ℝ

/-!
Source/core/bridge triage:
- `source-facing`: the item gives a concrete counterexample, namely the convex hull of a torus in
  `ℝ³` together with the flat top disk whose rim consists of extreme but non-exposed points.
- `core/canonical`: mathlib's owner abstractions for pointwise extremality and exposedness are
  `Set.extremePoints` and `Set.exposedPoints`, while the relative boundary of the disk is written
  on the chapter surface as `rb(standardTorusTopDisk)`.
- `bridge/view`: the torus and its top disk are given as explicit sets in `R3 = ℝ × ℝ × ℝ`, and
  the source sentence is stated directly as a membership theorem for the canonical owner sets.

Domain-style sampling used here:
- `Set.extremePoints`;
- `mem_extremePoints`;
- `mem_exposedPoints_iff_exposed_singleton`;
- `rb`.

Primitive data vs derived API:
- primitive data: the concrete torus surface and the concrete top disk;
- derived API: the ambient convex body is the canonical owner
  `standardTorusHull = conv[ℝ] standardTorusSurface`, while extremality and exposedness of rim
  points are theorem-level properties expressed through `Set.extremePoints` and
  `Set.exposedPoints`.
-/

/-- The standard torus of major radius `2` and minor radius `1` in `ℝ³`, written in implicit
coordinates. -/
def standardTorusSurface : Set R3 :=
  {x | (Real.sqrt (x.1 ^ 2 + x.2.1 ^ 2) - 2) ^ 2 + x.2.2 ^ 2 = 1}

/-- Membership in `standardTorusSurface` is exactly the usual implicit torus equation. -/
@[simp] theorem mem_standardTorusSurface_iff {x : R3} :
    x ∈ standardTorusSurface ↔ (Real.sqrt (x.1 ^ 2 + x.2.1 ^ 2) - 2) ^ 2 + x.2.2 ^ 2 = 1 :=
  Iff.rfl

/-- The flat top disk of the convex hull of the standard torus, lying in the plane `z = 1`. -/
def standardTorusTopDisk : Set R3 :=
  {x | x.2.2 = 1 ∧ x.1 ^ 2 + x.2.1 ^ 2 ≤ 4}

/-- Membership in `standardTorusTopDisk` means lying in the horizontal disk of radius `2` at
height `1`. -/
@[simp] theorem mem_standardTorusTopDisk_iff {x : R3} :
    x ∈ standardTorusTopDisk ↔ x.2.2 = 1 ∧ x.1 ^ 2 + x.2.1 ^ 2 ≤ 4 :=
  Iff.rfl

/-- The convex hull of the standard torus surface. This is the ambient convex body in
Text 18.0.11. -/
def standardTorusHull : Set R3 :=
  conv[ℝ] standardTorusSurface

/-- Text 18.0.11 in primitive owner form: every point on the top rim of the torus cap is extreme
and not exposed in the torus hull. -/
theorem standardTorusTopRim_subset_extremePoints_and_not_exposedPoints :
    rb(standardTorusTopDisk) ⊆
      {x : R3 | x ∈ standardTorusHull.extremePoints ℝ ∧
        x ∉ standardTorusHull.exposedPoints ℝ} := by
  sorry

/-- Text 18.0.11 in set-difference bridge form. -/
theorem standardTorusTopRim_subset_extremePoints_diff_exposedPoints :
    rb(standardTorusTopDisk) ⊆
      standardTorusHull.extremePoints ℝ \ standardTorusHull.exposedPoints ℝ := by
  intro x hx
  simpa [Set.mem_diff] using
    (standardTorusTopRim_subset_extremePoints_and_not_exposedPoints hx)

/-- Pointwise primitive-owner form of Text 18.0.11. -/
theorem mem_extremePoints_and_not_mem_exposedPoints_of_mem_standardTorusTopRim
    {x : R3}
    (hx : x ∈ rb(standardTorusTopDisk)) :
    x ∈ standardTorusHull.extremePoints ℝ ∧
      x ∉ standardTorusHull.exposedPoints ℝ := by
  exact standardTorusTopRim_subset_extremePoints_and_not_exposedPoints hx

/-- Pointwise set-difference bridge form of Text 18.0.11. -/
theorem mem_extremePoints_diff_exposedPoints_of_mem_standardTorusTopRim
    {x : R3}
    (hx : x ∈ rb(standardTorusTopDisk)) :
    x ∈ standardTorusHull.extremePoints ℝ \ standardTorusHull.exposedPoints ℝ := by
  simpa [Set.mem_diff] using
    (mem_extremePoints_and_not_mem_exposedPoints_of_mem_standardTorusTopRim hx)

end

/-! ### Text_18_0_12 (from Chap04) -/
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 18.0.12 records the transitivity of faces of a convex set and its
  singleton specialization to extreme points.
- `core/canonical`: the chapter owner abstraction is `Set.IsFace`, with `Set.extremePoints` as the
  canonical owner for extreme points.
- `bridge/view`: clause (1) is the owner theorem `Set.IsFace.trans`; clause (2) is
  `Set.IsFace.extremePoints_subset`. On this file surface we expose the same content through the
  chapter notation `𝓕[R](C)` for the family of faces.
- Primitive data vs derived API: the item introduces no new data; it only records derived
  transitivity consequences of the existing owner declarations.
- Domain-style sampling used here: `Set.IsFace`, `Set.IsFace.trans`, `Set.faces`,
  `𝓕[R](C)`, `Set.extremePoints`, and `Set.IsFace.extremePoints_subset`.
- Layer target: `source-facing`, with theorem surfaces stated on the chapter face-family notation.
-/

/- Text 18.0.12 (1): faces are transitive; if `C''` is a face of `C'` and `C'` is a face of `C`,
then `C''` is a face of `C`. This is exactly the owner theorem `Set.IsFace.trans`. -/
recall Set.IsFace.trans

/- Text 18.0.12 (2): the extreme points of a face `C'` of `C` are extreme points of `C`.
This is exactly the owner theorem `Set.IsFace.extremePoints_subset`. -/
recall Set.IsFace.extremePoints_subset

/- Text 18.0.12 (notation bridge): transitivity directly on the chapter face-family notation
`𝓕[R](·)`. -/
recall Set.IsFace.mem_faces_trans

/- Text 18.0.12 (notation bridge): extreme points are monotone along face-family membership in
`𝓕[R](·)`. -/
recall Set.IsFace.extremePoints_subset_of_mem_faces

/-! ### Text_18_0_13 (from Chap04) -/
/-!
Source/core/bridge triage:
- `source-facing`: the item says that a face of `C` remains a face in any intermediate set `D`,
  and that an exposed face of `C` remains exposed in such a `D`.
- `core/canonical`: the source-facing owner for faces is `Set.IsFace`, and exposed faces are owned
  by `IsExposed`.
- `bridge/view`: clause (1) is exactly `Set.IsFace.mono`, surfaced here both in owner form and in
  the chapter face-family notation `𝓕[R](C)`. Clause (2) is the canonical owner monotonicity of
  `IsExposed`, namely `IsExposed.mono`.

Domain-style sampling used here:
- `Set.IsFace.mono`;
- `Set.IsFace.mem_faces_mono`;
- `IsExposed.mono`;
- `IsExtreme.subset`;
- `IsExposed.subset`.

Primitive data vs derived API:
- primitive inputs: the ambient set `C`, the intermediate set `D`, and the face `C'`;
- derived outputs: the face or exposed-face status of `C'` inside `D`.

The source assumes `D` is convex because it is phrased with the textbook face definition. For
clause (1), the source-facing owner `Set.IsFace` only needs `C' ⊆ D ⊆ C`, so that convexity
hypothesis is redundant. Clause (2) is monotonicity of `IsExposed` under intermediate ambient
sets and likewise does not need convexity of `D`.
-/

open scoped Rockafellar

/- Text 18.0.13 (1): if `C'` is a face of `C` and `C' ⊆ D ⊆ C`, then `C'` is also a face of `D`.
This is exactly the owner theorem `Set.IsFace.mono`; the source convexity hypothesis on `D` is
redundant here. -/
recall Set.IsFace.mono

/- Text 18.0.13 (1), notation form: the same monotonicity at the chapter face-family surface
`𝓕[R](·)`, on the canonical owner-namespace bridge theorem. -/
recall Set.IsFace.mem_faces_mono

/- Text 18.0.13 (2): if `C'` is exposed in `C` and `C' ⊆ D ⊆ C`, then `C'` is also exposed in
`D`. This is exactly the canonical owner theorem `IsExposed.mono`; the source
convexity assumption on `D` is redundant in this owner formulation. -/
recall IsExposed.mono

/-! ### Text_18_0_14 (from Chap04) -/
open Set
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Convex

/-!
Source/core/bridge triage:

- `source-facing`: this item says that every extreme direction and every exposed direction of a
  closed convex set in an ordered topological vector space over `𝕜` yields an extreme,
  respectively exposed, ray of its recession cone.
- `core/canonical`: the chapter owners for this geometry are `Set.extremeDirections`,
  `Set.exposedDirections`, `affineHalfLine`, `originRay`, the recession-cone owner
  `recessionCone`, and the canonical exposed/extreme-face owners `IsExposed` / `IsExtreme` on
  `0⁺[𝕜] C`.
- `bridge/view`: `ConvexCone.IsExtremeRay` and `ConvexCone.IsExposedRay` on the bundled view
  `Set.recessionConeCone C 𝕜` are retained as downstream interoperability bridges.
- `bridge/view`: a source half-line face of `C` is rendered canonically as `affineHalfLine x r`;
  the Chapter 8 recession owner is compared to mathlib's `asymptoticCone 𝕜 C` by
  `Convex.recessionCone_eq_asymptoticCone`, and the textbook nonnegative scalar ray is only the
  view `originRay_eq_nonnegative_smul_singleton r.someVector_ne_zero`.

Domain-style sampling used here:
- `Set.extremeDirections`;
- `Set.exposedDirections`;
- `Convex.mem_recessionCone_of_nonneg_ray`;
- `Convex.recessionCone_eq_asymptoticCone`.

Primitive data vs derived API:
- primitive data: a direction ray `r : Module.Ray 𝕜 E` and, for the source-facing half-line, a
  base point `x`;
- derived API: extremality and exposedness stay theorem-level properties of the canonical owner
  directions as `IsExtreme` / `IsExposed` on `0⁺[𝕜] C`; the bundled ray owners
  `ConvexCone.IsExtremeRay` / `ConvexCone.IsExposedRay` are exposed only as bridge lemmas through
  `Set.recessionConeCone`. The step from a
  half-line contained in `C` to a recession direction uses the owner-side
  theorem `Convex.mem_recessionCone_of_nonneg_ray`, and closedness of `0⁺[𝕜] C` is controlled by
  the Chapter 8 asymptotic-cone bridge `Convex.recessionCone_eq_asymptoticCone`, so the ambient
  space must already be an ordered topological vector space over `𝕜` with compatible addition and
  scalar multiplication.
- Layer target: `source-facing`, with the recession-cone step routed through the existing Chapter 8
  owner API rather than a parallel local cone wrapper.
-/

/-- Text 18.0.14: in an ordered topological vector space over `𝕜`, every extreme direction of a
closed convex set `C` determines an extreme origin half-line of its recession cone `0⁺[𝕜] C`.
Specializing `𝕜 = ℝ` recovers the textbook statement. -/
-- Proof sketch: if `r ∈ C.extremeDirections`, choose `x` with `affineHalfLine x r` an
-- extreme face of `C`. The whole forward half-line from `x` in direction `r` lies in `C`, so
-- Theorem 8.3 puts the direction into `0⁺[𝕜] C`. To prove extremality of the origin ray,
-- translate a segment in `0⁺[𝕜] C` whose interior point lies on that ray back to a
-- segment in `C`; extremality of `affineHalfLine x r` forces both endpoints onto the same
-- half-line, hence onto the same origin ray.
theorem isExtreme_originRay_recessionCone_of_mem_extremeDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.extremeDirections 𝕜) :
    IsExtreme 𝕜 (0⁺[𝕜] C) (originRay r) := sorry

/-- Bridge to the direction-owner surface: every extreme direction of a closed convex set induces
an extreme ray direction of the bundled recession cone view. -/
theorem isExtremeRay_recessionCone_of_mem_extremeDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.extremeDirections 𝕜) :
    (Set.recessionConeCone C 𝕜).IsExtremeRay r := by
  simpa [ConvexCone.IsExtremeRay, Set.coe_recessionConeCone] using
    (hC_convex.isExtreme_originRay_recessionCone_of_mem_extremeDirections
      (hC_closed := hC_closed) (hr := hr))

/-- Text 18.0.14: in an ordered topological vector space over `𝕜`, every exposed direction of a
closed convex set `C` determines an exposed origin half-line of its recession cone `0⁺[𝕜] C`.
Specializing `𝕜 = ℝ` recovers the textbook statement. -/
-- Proof sketch: if `r ∈ C.exposedDirections 𝕜`, choose `x` with `affineHalfLine x r` exposed
-- in `C`. As above, the supporting half-line gives a recession direction. Translate the exposing
-- functional so that the base point becomes the origin; the same functional then cuts out
-- `originRay r` inside `0⁺[𝕜] C`.
theorem isExposed_originRay_recessionCone_of_mem_exposedDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.exposedDirections 𝕜) :
    IsExposed 𝕜 (0⁺[𝕜] C) (originRay r) := sorry

/-- Bridge to the direction-owner surface: every exposed direction of a closed convex set induces
an exposed ray direction of the bundled recession cone view. -/
theorem isExposedRay_recessionCone_of_mem_exposedDirections
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    {r : Module.Ray 𝕜 E} (hr : r ∈ C.exposedDirections 𝕜) :
    (Set.recessionConeCone C 𝕜).IsExposedRay r := by
  simpa [ConvexCone.IsExposedRay, Set.coe_recessionConeCone] using
    (hC_convex.isExposed_originRay_recessionCone_of_mem_exposedDirections
      (hC_closed := hC_closed) (hr := hr))

end Convex

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The upward vertical direction ray in `𝕜²`, used in the paraboloid counterexample. -/
noncomputable def paraboloidVerticalRay : Module.Ray 𝕜 (𝕜 × 𝕜) :=
  rayOfNeZero 𝕜 ((0 : 𝕜), (1 : 𝕜)) (by simp)

end

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsTopologicalRing 𝕜]

/-!
The following declarations formalize the standard paraboloid epigraph counterexample witnessing
that the converse in Text 18.0.14 fails.
-/

/-- The vertical origin half-line is an extreme ray of the recession cone of the paraboloid
epigraph. -/
-- Proof sketch: the recession cone of `paraboloidEpigraph` is the nonnegative vertical axis, so
-- its only nontrivial direction ray is extreme.
theorem paraboloidVerticalRay_isExtreme_recessionCone :
    IsExtreme 𝕜 (0⁺[𝕜] (paraboloidEpigraph : Set (𝕜 × 𝕜)))
      (originRay paraboloidVerticalRay) := sorry

/-- The vertical origin half-line is an extreme ray direction of the bundled recession-cone view
of the paraboloid epigraph. -/
theorem paraboloidVerticalRay_isExtremeRay_recessionCone :
    (Set.recessionConeCone (paraboloidEpigraph : Set (𝕜 × 𝕜)) 𝕜).IsExtremeRay
      paraboloidVerticalRay := by
  simpa [ConvexCone.IsExtremeRay, Set.coe_recessionConeCone] using
    (paraboloidVerticalRay_isExtreme_recessionCone (𝕜 := 𝕜))

/-- The vertical origin half-line is an exposed ray of the recession cone of the paraboloid
epigraph. -/
-- Proof sketch: once the recession cone is identified with the nonnegative vertical axis, the
-- functional projecting to the second coordinate exposes `originRay paraboloidVerticalRay`.
theorem paraboloidVerticalRay_isExposed_recessionCone :
    IsExposed 𝕜 (0⁺[𝕜] (paraboloidEpigraph : Set (𝕜 × 𝕜)))
      (originRay paraboloidVerticalRay) := sorry

/-- The vertical origin half-line is an exposed ray direction of the bundled recession-cone view
of the paraboloid epigraph. -/
theorem paraboloidVerticalRay_isExposedRay_recessionCone :
    (Set.recessionConeCone (paraboloidEpigraph : Set (𝕜 × 𝕜)) 𝕜).IsExposedRay
      paraboloidVerticalRay := by
  simpa [ConvexCone.IsExposedRay, Set.coe_recessionConeCone] using
    (paraboloidVerticalRay_isExposed_recessionCone (𝕜 := 𝕜))

/-- The vertical direction is not an extreme direction of the paraboloid epigraph. -/
-- Proof sketch: every supporting line to the parabola meets it in at most one boundary point, so
-- no affine half-line of vertical direction can be an extreme face of `paraboloidEpigraph`.
theorem paraboloidVerticalRay_notMem_extremeDirections :
    paraboloidVerticalRay ∉
      paraboloidEpigraph.extremeDirections 𝕜 := sorry

/-- The vertical direction is not an exposed direction of the paraboloid epigraph. -/
-- Proof sketch: an exposed affine half-line would be cut out by a supporting functional, but the
-- paraboloid epigraph has only point contacts with its supporting lines, never a vertical
-- half-line.
theorem paraboloidVerticalRay_notMem_exposedDirections :
    paraboloidVerticalRay ∉
      paraboloidEpigraph.exposedDirections 𝕜 := sorry

end
