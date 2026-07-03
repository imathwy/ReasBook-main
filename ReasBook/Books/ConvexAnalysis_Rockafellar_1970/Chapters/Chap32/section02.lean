

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_32_2_1 (from Chap06) -/
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

/-! ### Theorem_32_2 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Theorem 32.2 says that maximizing a convex function over a convex hull does not
  change the supremum, and that attainment on the hull forces attainment on the generating set.
- `core/canonical`: the primitive owner for both clauses is quasiconvexity on the working hull
  `convexHull 𝕜 S`, since only convexity of sublevel/strict-sublevel sets on that hull is used.
  The source-facing convex owner is set-local `ConvexOn 𝕜 (convexHull 𝕜 S) f`, with a whole-space
  `ConvexOn 𝕜 Set.univ f` specialization as a derived wrapper.
- `bridge/view`: no extra source-defined structure is introduced; the bridge remains on the same
  `convexHull` and `IsMaxOn` owners. Legacy chapter epigraph aliases
  `Function.IsConvexOn`/`Function.IsConvex` are kept only as compatibility bridges.

Domain-style sampling used here:
- `QuasiconvexOn` and `QuasiconvexOn.convex_lt`;
- `ConvexOn.quasiconvexOn`;
- `convexHull_min` and `subset_convexHull`;
- `sSup`;
- `IsMaxOn`.

Primitive data vs derived API:
- primitive owner data: quasiconvexity of `f` on `convexHull 𝕜 S`;
- derived source-facing API: `ConvexOn` wrappers recovering Theorem 32.2 on
  `convexHull 𝕜 S` and `Set.univ`;
- compatibility bridge API: chapter epigraph aliases `Function.IsConvexOn` / `Function.IsConvex`.

Layer target: `source-facing` `ConvexOn` wrappers over a `core/canonical` quasiconvex owner,
centered on the canonical `convexHull` interface.
-/

section SupremumClause

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {β : Type*} [CompleteLattice β]
variable {f : E → β}

namespace QuasiconvexOn

/-- Core Theorem 32.2 supremum clause at the quasiconvex owner layer. -/
theorem sSup_image_convexHull_eq {S : Set E}
    (hf : QuasiconvexOn 𝕜 (convexHull 𝕜 S) f) :
    sSup (f '' convexHull 𝕜 S) = sSup (f '' S) := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    have hsubset :
        convexHull 𝕜 S ⊆ {y : E | y ∈ convexHull 𝕜 S ∧ f y ≤ sSup (f '' S)} := by
      exact convexHull_min
        (fun y hy ↦ ⟨subset_convexHull 𝕜 S hy, le_sSup (Set.mem_image_of_mem f hy)⟩)
        (by simpa using hf (sSup (f '' S)))
    exact (hsubset hx).2
  · apply sSup_le_sSup
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, subset_convexHull 𝕜 S hx, rfl⟩

end QuasiconvexOn

variable {α : Type*}
variable [AddCommMonoid α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable {f : E → WithTopBot α}

section ConvexOnOwner

variable [Module 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]
namespace ConvexOn

/-- Theorem 32.2 at the canonical convex owner layer (supremum clause): if `f` is convex on
`convexHull 𝕜 S`, then the supremum over `convexHull 𝕜 S` agrees with the supremum over `S`. -/
theorem sSup_image_convexHull_eq {S : Set E}
    (hf : ConvexOn 𝕜 (convexHull 𝕜 S) f) :
    sSup (f '' convexHull 𝕜 S) = sSup (f '' S) := by
  exact hf.quasiconvexOn.sSup_image_convexHull_eq

/-- Whole-space specialization of Theorem 32.2 (supremum clause): if `f` is convex on `Set.univ`,
then the supremum over `convexHull 𝕜 S` agrees with the supremum over `S`. -/
theorem sSup_image_convexHull_eq_univ
    (hf : ConvexOn 𝕜 (Set.univ : Set E) f) (S : Set E) :
    sSup (f '' convexHull 𝕜 S) = sSup (f '' S) := by
  exact (hf.subset (by intro x hx; simp) (convex_convexHull 𝕜 S)).sSup_image_convexHull_eq

end ConvexOn

end ConvexOnOwner

namespace Function.IsConvexOn

/-- Compatibility bridge (supremum clause) from the chapter epigraph owner
`Function.IsConvexOn` to the canonical hull theorem. -/
theorem sSup_image_convexHull_eq {S : Set E}
    (hf : f.IsConvexOn 𝕜 (convexHull 𝕜 S)) :
    sSup (f '' convexHull 𝕜 S) = sSup (f '' S) := by
  exact (hf.quasiconvexOn (convex_convexHull 𝕜 S)).sSup_image_convexHull_eq

end Function.IsConvexOn

namespace Function.IsConvex

/-- Compatibility bridge (supremum clause) from the chapter whole-space epigraph owner
`Function.IsConvex` to the canonical hull theorem. -/
theorem sSup_image_convexHull_eq (hf : f.IsConvex 𝕜) (S : Set E) :
    sSup (f '' convexHull 𝕜 S) = sSup (f '' S) := by
  have hqUniv : QuasiconvexOn 𝕜 (Set.univ : Set E) f := hf.quasiconvexOn
  have hqHull : QuasiconvexOn 𝕜 (convexHull 𝕜 S) f :=
    (convex_convexHull 𝕜 S).quasiconvexOn_restrict hqUniv (by intro x hx; simp)
  exact hqHull.sSup_image_convexHull_eq

end Function.IsConvex

end SupremumClause

section AttainmentClause

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {β : Type*} [LinearOrder β]
variable {f : E → β}

namespace QuasiconvexOn

/-- Core Theorem 32.2 attainment clause at the quasiconvex owner layer. -/
theorem exists_isMaxOn_of_isMaxOn_convexHull
    {S : Set E} (hf : QuasiconvexOn 𝕜 (convexHull 𝕜 S) f) {x : E}
    (hx : x ∈ convexHull 𝕜 S) (hmax : IsMaxOn f (convexHull 𝕜 S) x) :
    ∃ y ∈ S, IsMaxOn f S y := by
  have hmax' : ∀ z ∈ convexHull 𝕜 S, f z ≤ f x := isMaxOn_iff.mp hmax
  have hnot : ¬ S ⊆ {y : E | f y < f x} := by
    intro hS
    have hHull :
        convexHull 𝕜 S ⊆ {y : E | y ∈ convexHull 𝕜 S ∧ f y < f x} := by
      exact convexHull_min
        (fun y hy ↦ ⟨subset_convexHull 𝕜 S hy, hS hy⟩)
        (by simpa using hf.convex_lt (f x))
    exact (lt_irrefl (f x)) (hHull hx).2
  rcases Set.not_subset.mp hnot with ⟨y, hyS, hyNot⟩
  refine ⟨y, hyS, ?_⟩
  rw [isMaxOn_iff]
  intro z hz
  have hzHull : z ∈ convexHull 𝕜 S := subset_convexHull 𝕜 S hz
  have hzle : f z ≤ f x := hmax' z hzHull
  exact hzle.trans (le_of_not_gt hyNot)

end QuasiconvexOn

variable {α : Type*}
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable {f : E → WithTopBot α}

section ConvexOnOwner

variable [Module 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]
namespace ConvexOn

/-- Theorem 32.2 at the canonical convex owner layer (attainment clause): if `f` is convex on
`convexHull 𝕜 S` and attains its maximum there, then it already attains its maximum on `S`. -/
theorem exists_isMaxOn_of_isMaxOn_convexHull
    {S : Set E} (hf : ConvexOn 𝕜 (convexHull 𝕜 S) f) {x : E}
    (hx : x ∈ convexHull 𝕜 S) (hmax : IsMaxOn f (convexHull 𝕜 S) x) :
    ∃ y ∈ S, IsMaxOn f S y := by
  exact hf.quasiconvexOn.exists_isMaxOn_of_isMaxOn_convexHull hx hmax

/-- Whole-space specialization of Theorem 32.2 (attainment clause): if `f` is convex on
`Set.univ` and attains a maximum on `convexHull 𝕜 S`, then it already attains a maximum on `S`. -/
theorem exists_isMaxOn_of_isMaxOn_convexHull_univ
    (hf : ConvexOn 𝕜 (Set.univ : Set E) f) {S : Set E} {x : E}
    (hx : x ∈ convexHull 𝕜 S) (hmax : IsMaxOn f (convexHull 𝕜 S) x) :
    ∃ y ∈ S, IsMaxOn f S y := by
  have hfHull : ConvexOn 𝕜 (convexHull 𝕜 S) f :=
    hf.subset (by intro y hy; simp) (convex_convexHull 𝕜 S)
  exact hfHull.exists_isMaxOn_of_isMaxOn_convexHull hx hmax

end ConvexOn

end ConvexOnOwner

namespace Function.IsConvexOn

/-- Compatibility bridge (attainment clause) from the chapter epigraph owner
`Function.IsConvexOn` to the canonical hull theorem. -/
theorem exists_isMaxOn_of_isMaxOn_convexHull
    {S : Set E} (hf : f.IsConvexOn 𝕜 (convexHull 𝕜 S)) {x : E}
    (hx : x ∈ convexHull 𝕜 S) (hmax : IsMaxOn f (convexHull 𝕜 S) x) :
    ∃ y ∈ S, IsMaxOn f S y := by
  exact (hf.quasiconvexOn (convex_convexHull 𝕜 S)).exists_isMaxOn_of_isMaxOn_convexHull hx hmax

end Function.IsConvexOn

namespace Function.IsConvex

/-- Compatibility bridge (attainment clause) from the chapter whole-space epigraph owner
`Function.IsConvex` to the canonical hull theorem. -/
theorem exists_isMaxOn_of_isMaxOn_convexHull
    (hf : f.IsConvex 𝕜) {S : Set E} {x : E}
    (hx : x ∈ convexHull 𝕜 S) (hmax : IsMaxOn f (convexHull 𝕜 S) x) :
    ∃ y ∈ S, IsMaxOn f S y := by
  have hqUniv : QuasiconvexOn 𝕜 (Set.univ : Set E) f := hf.quasiconvexOn
  have hqHull : QuasiconvexOn 𝕜 (convexHull 𝕜 S) f :=
    (convex_convexHull 𝕜 S).quasiconvexOn_restrict hqUniv (by intro x hx; simp)
  exact hqHull.exists_isMaxOn_of_isMaxOn_convexHull hx hmax

end Function.IsConvex

end AttainmentClause
