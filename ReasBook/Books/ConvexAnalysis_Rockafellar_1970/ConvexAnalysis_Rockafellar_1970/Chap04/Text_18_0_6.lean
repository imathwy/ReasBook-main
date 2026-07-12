import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

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
