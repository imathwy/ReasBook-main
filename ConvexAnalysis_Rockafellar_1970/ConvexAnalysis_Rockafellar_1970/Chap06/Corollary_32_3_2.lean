import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_18_5_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_32_2

open scoped Rockafellar

universe u v

section CoreOwner

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.3.2 is usually presented on `ri(dom f)`.
- `core/canonical`: the primitive attainment inputs are compactness, continuity on the working set,
  and the extreme-point hull identity.
- `bridge/view`: relative-interior hypotheses are treated as a thin bridge through an explicit
  continuity-on-`riDom` owner hypothesis.

Primitive data vs derived API:
- primitive core inputs: `C.Nonempty`, `IsCompact C`, `ContinuousOn f C`, and
  `C = convexHull 𝕜 (C.extremePoints 𝕜)`;
- derived core output: existence of an extreme-point maximizer and the value companion
  `∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C)`;
- bridge input/output: `C ⊆ riDom[𝕜](f)` plus `ContinuousOn f (riDom[𝕜](f))`.
-/

section IsMaxOnCore

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Core canonical owner form behind Corollary 32.3.2: on a nonempty compact set whose carrier
equals the convex hull of its extreme points, a convex `WithBotTop α`-valued function that is
continuous on that set attains its supremum at an extreme point. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hC_cont : ContinuousOn f C) (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  obtain ⟨x, hxC, hxmax⟩ := hC_compact.exists_isMaxOn hC_nonempty hC_cont
  have hxHull : x ∈ convexHull 𝕜 (C.extremePoints 𝕜) := by
    rw [← hC_eq]
    exact hxC
  have hxmaxHull : IsMaxOn f (convexHull 𝕜 (C.extremePoints 𝕜)) x := by
    rw [← hC_eq]
    exact hxmax
  obtain ⟨y, hyext, hymaxext⟩ :=
    hf.exists_isMaxOn_of_isMaxOn_convexHull hxHull hxmaxHull
  have hymax : IsMaxOn f C y := by
    rw [hC_eq]
    have hsub : C.extremePoints 𝕜 ⊆ {z : E | f z ≤ f y} := by
      intro z hz
      exact hymaxext hz
    have hsubHull : convexHull 𝕜 (C.extremePoints 𝕜) ⊆ {z : E | f z ≤ f y} :=
      convexHull_min hsub (by simpa using hf.convex_le (f y))
    intro z hz
    exact hsubHull hz
  exact ⟨y, hyext, hymax⟩

end IsMaxOnCore

section IsMaxOnRiDomBridge

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Bridge form of Corollary 32.3.2 using relative-interior domain data:
if `f` is continuous on `riDom[𝕜](f)` and `C ⊆ riDom[𝕜](f)`, then the compact/extreme-hull
conclusion follows. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))
    (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  exact exists_mem_extremePoints_isMaxOn_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hC_cont := hcont_riDom.mono hC_subset) (hC_eq := hC_eq)

end IsMaxOnRiDomBridge

section ValueCore

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Core compact-value companion for Corollary 32.3.2: under the same compact owner hypotheses,
some extreme point realizes `sSup (f '' C)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hC_cont : ContinuousOn f C) (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  obtain ⟨y, hyext, hymax⟩ :=
    exists_mem_extremePoints_isMaxOn_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
      (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
      (hC_cont := hC_cont) (hC_eq := hC_eq)
  have hyC : y ∈ C := (mem_extremePoints.mp hyext).1
  have hRange : Set.range (fun z : C ↦ f z) = f '' C := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hzC, rfl⟩
      exact ⟨⟨z, hzC⟩, rfl⟩
  refine ⟨y, hyext, ?_⟩
  calc
    f y = ⨆ z : C, f z := (hymax.iSup_eq hyC).symm
    _ = sSup (Set.range fun z : C ↦ f z) := by rw [sSup_range]
    _ = sSup (f '' C) := by rw [hRange]

/-- Proper-convex compact companion on the canonical scalar layer: under the same compact owner
hypotheses plus `C ⊆ dom(f)`, the supremum value on `C` is represented by a scalar in `α`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_compact_of_subset_dom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hf_proper : f.IsProper)
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_cont : ContinuousOn f C)
    (hC_dom : C ⊆ dom(f)) (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  obtain ⟨y, hyext, hySup⟩ :=
    exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
      (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
      (hC_cont := hC_cont) (hC_eq := hC_eq)
  have hyC : y ∈ C := (mem_extremePoints.mp hyext).1
  have hy_dom : y ∈ dom(f) := hC_dom hyC
  have hy_top : f y ≠ ⊤ := (mem_effectiveDomain.mp hy_dom).ne
  have hy_bot : f y ≠ ⊥ := hf_proper.ne_bot y
  lift f y to α using ⟨hy_top, hy_bot⟩ with r hr
  refine ⟨r, ?_⟩
  simpa [hr] using hySup.symm

end ValueCore

section ValueRiDomBridge

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Bridge value companion for Corollary 32.3.2 on `riDom[𝕜](f)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))
    (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  exact exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hC_cont := hcont_riDom.mono hC_subset) (hC_eq := hC_eq)

/-- Proper-convex bridge companion on `riDom[𝕜](f)`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hf_proper : f.IsProper)
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))
    (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  refine
    exists_scalar_eq_sSup_image_of_proper_nonempty_compact_of_subset_dom_of_eq_extremeHull
      (hf := hf) (hf_proper := hf_proper) (hC_nonempty := hC_nonempty)
      (hC_compact := hC_compact) (hC_cont := hcont_riDom.mono hC_subset)
      (hC_dom := ?_) (hC_eq := hC_eq)
  intro x hx
  exact intrinsicInterior_subset (hC_subset hx)

end ValueRiDomBridge

end CoreOwner

section CompactConvexBridge

open Bornology

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]

private theorem compact_convex_eq_convexHull_extremePoints
    (hC_compact : IsCompact C) (hC_convex : Convex 𝕜 C) :
    C = convexHull 𝕜 (C.extremePoints 𝕜) :=
  eq_convexHull_extremePoints_of_isClosed_of_isBounded_of_convex
    hC_compact.isClosed hC_compact.isBounded hC_convex

section IsMaxOnLayer

variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
  (hC_convex : Convex 𝕜 C) (hcont_riDom : ContinuousOn f (riDom[𝕜](f)))
  (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_compact hC_convex hcont_riDom hC_subset

/-- Compact-convex bridge form of Corollary 32.3.2. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_compact_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  have hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜) :=
    compact_convex_eq_convexHull_extremePoints (𝕜 := 𝕜) (C := C) hC_compact hC_convex
  exact exists_mem_extremePoints_isMaxOn_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hcont_riDom := hcont_riDom) (hC_subset := hC_subset) (hC_eq := hC_eq)

end IsMaxOnLayer

section ValueLayer

variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
  (hC_convex : Convex 𝕜 C) (hcont_riDom : ContinuousOn f (riDom[𝕜](f)))
  (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_compact hC_convex hcont_riDom hC_subset

/-- Compact-convex value companion: some extreme point of `C` realizes `sSup (f '' C)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  have hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜) :=
    compact_convex_eq_convexHull_extremePoints (𝕜 := 𝕜) (C := C) hC_compact hC_convex
  exact exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hcont_riDom := hcont_riDom) (hC_subset := hC_subset) (hC_eq := hC_eq)

/-- Compact-convex proper companion: the supremum over `C` is represented by a scalar in `α`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_compact_convex_subset_riDom
    (hf_proper : f.IsProper) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  have hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜) :=
    compact_convex_eq_convexHull_extremePoints (𝕜 := 𝕜) (C := C) hC_compact hC_convex
  exact
    exists_scalar_eq_sSup_image_of_proper_nonempty_compact_subset_riDom_of_eq_extremeHull
      (hf := hf) (hf_proper := hf_proper) (hC_nonempty := hC_nonempty)
      (hC_compact := hC_compact) (hcont_riDom := hcont_riDom)
      (hC_subset := hC_subset) (hC_eq := hC_eq)

end ValueLayer

end CompactConvexBridge

section ClosedBoundedBridge

open Bornology

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
variable {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]

private theorem closed_bounded_isCompact (hC_closed : IsClosed C)
    (hC_bounded : IsBounded C) : IsCompact C :=
  Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded

section IsMaxOnLayer

variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
  (hC_bounded : IsBounded C) (hC_convex : Convex 𝕜 C)
  (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_closed hC_bounded hC_convex hcont_riDom hC_subset

/-- Source-facing closed-bounded specialization of Corollary 32.3.2. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_closed_bounded_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  exact exists_mem_extremePoints_isMaxOn_of_nonempty_compact_convex_subset_riDom
    (hf := hf) (hC_nonempty := hC_nonempty)
    (hC_compact := closed_bounded_isCompact hC_closed hC_bounded)
    (hC_convex := hC_convex) (hcont_riDom := hcont_riDom) (hC_subset := hC_subset)

end IsMaxOnLayer

section ValueLayer

variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
  (hC_bounded : IsBounded C) (hC_convex : Convex 𝕜 C)
  (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_closed hC_bounded hC_convex hcont_riDom hC_subset

/-- Source-facing closed-bounded value companion: some extreme point of `C` realizes
`sSup (f '' C)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_closed_bounded_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  exact exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_convex_subset_riDom
    (hf := hf) (hC_nonempty := hC_nonempty)
    (hC_compact := closed_bounded_isCompact hC_closed hC_bounded)
    (hC_convex := hC_convex) (hcont_riDom := hcont_riDom) (hC_subset := hC_subset)

/-- Source-facing closed-bounded proper companion: the supremum over `C` is represented by a
scalar in `α`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_closed_bounded_convex_subset_riDom
    (hf_proper : f.IsProper) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  exact exists_scalar_eq_sSup_image_of_proper_nonempty_compact_convex_subset_riDom
    (hf := hf) (hC_nonempty := hC_nonempty)
    (hC_compact := closed_bounded_isCompact hC_closed hC_bounded)
    (hC_convex := hC_convex) (hcont_riDom := hcont_riDom) (hC_subset := hC_subset)
    hf_proper

end ValueLayer

end ClosedBoundedBridge
