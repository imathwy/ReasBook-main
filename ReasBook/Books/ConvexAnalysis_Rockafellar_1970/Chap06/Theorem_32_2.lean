import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6

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
