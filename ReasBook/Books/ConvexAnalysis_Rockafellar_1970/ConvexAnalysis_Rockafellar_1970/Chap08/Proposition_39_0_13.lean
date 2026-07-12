import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_5

noncomputable section

open scoped Rockafellar SetRel

universe u v

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.13 attaches to a supremum-oriented convex process `A` the
  canonical slice-indicator owner `indicatorFibers α A` and states its domain,
  graph convexity, properness, and the lower-semicontinuity/graph-closedness equivalence.
- `core/canonical`: the process itself already lives on the relation owner `A : SetRel U X` via
  `A.IsConvexProcess 𝕜`; the bifunction/process owners already present in the chapter are
  `dom F`, `Bifunction.IsProper F`, the graph-owner notations `convᵇ[𝕜](F)` / `closedᵇ(F)`, and
  `A.IsClosed`.
- `bridge/view`: the only extra bridge kept here is the uncurrying identity from the canonical
  slice-indicator owner to the graph indicator of `A`.

Primary mathematical domain:
- convex processes and their indicator bifunctions.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` from `Definition_39_0_1`;
- the Chapter 6 canonical bifunction surface
  `#check (indicatorFibers α A : U → X → WithBotTop α)`;
- `Bifunction.dom` and `Bifunction.IsProper` from `Definition_6_29_8` and `Theorem_38_1`;
- `indicator` notation `δ[α](x | C)` from `Defintion_4_8_1`;
- `indicator_isConvex_iff` from `Remark_4_8_1`;
- `SetRel.IsClosed` from `Definition_39_0_5`.

Primitive data vs derived API:
- primitive source-facing data: the relation `A : SetRel U X`;
- primitive source-facing owner: `indicatorFibers α A`;
- derived API: the uncurrying bridge, the domain identity, the owner-level properness criterion in
  terms of `A.dom`, its convex-process specialization, convexity on the Chapter 6 owner surface
  `convᵇ[𝕜](indicatorFibers α A)`, and the closedness/graph-closedness equivalence on
  `closedᵇ(indicatorFibers α A)`.

Layer target: `source-facing`, stated directly on the canonical `SetRel` and `Bifunction` owners,
with a short owner (`indicatorFibers`) for the recurring slice-indicator surface.
-/

section Indicator

variable {U : Type u} {X : Type v}
variable {α : Type*}
variable [Zero α]

/-- The canonical slice-indicator bifunction of a relation. -/
abbrev indicatorFibers (α : Type*) [Zero α] (A : SetRel U X) : U → X → WithBotTop α :=
  fun u ↦ (δ[α](· | A.image ({u} : Set U)) : X → WithBotTop α)

/-- Uncurrying `indicatorFibers α A` gives the indicator of the graph of `A`. -/
theorem uncurry_indicatorFibers_eq_indicator
    (A : SetRel U X) :
    Function.uncurry (indicatorFibers α A) =
      (δ[α](· | (A : Set (U × X)))) := by
  funext p
  rcases p with ⟨u, x⟩
  simp [indicatorFibers, indicator_def, SetRel.image]

end Indicator

section Domain

variable {U : Type u} {X : Type v}
variable {α : Type*} [Preorder α] [Zero α]

-- Proof sketch: unfold `Bifunction.dom` and `Function.IsProper` for the slice
-- `x ↦ δ[α](x | A.image ({u} : Set U))`. The effective domain of an indicator is exactly the
-- underlying set, and the indicator never takes the value `⊥`, so the slice is proper exactly
-- when the singleton fiber is nonempty, i.e. exactly when `u ∈ A.dom`.
/-- The parameter-domain of the indicator bifunction is exactly the domain of the underlying
process. -/
theorem dom_indicatorFibers_eq_dom (A : SetRel U X) :
    dom (indicatorFibers α A) = A.dom := sorry

end Domain

section Convexity

variable {U : Type u} {X : Type v}
variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable {α : Type*}
variable [Preorder α] [AddCommMonoid α] [IsOrderedAddMonoid α]
variable [SMulZeroClass 𝕜 α] [PosSMulMono 𝕜 α]
variable {A : SetRel U X}

-- Proof sketch: identify the uncurried slice-wise indicator expression with the indicator of the
-- graph `A ⊆ U × X`. Then apply `indicator_isConvex_iff` on the product space. Only graph
-- convexity is used, so the convex-process zero-membership field is not part of this theorem's
-- public input.
/-- The graph function of the fiber-indicator bifunction is convex whenever the graph of the
underlying relation is convex. -/
private theorem indicator_graph_isConvex
    (hA : Convex 𝕜 (A : Set (U × X))) :
    (δ[α](· | (A : Set (U × X)))).IsConvex 𝕜 := by
  exact (indicator_isConvex_iff (𝕜 := 𝕜) (α := α) (C := (A : Set (U × X)))).2 hA

/-- Bridge form of `indicator_graph_isConvex` on the chapter bifunction owner
`indicatorFibers α A`, stated on the canonical Chapter 6 surface `convᵇ[𝕜](·)`. -/
theorem uncurry_indicatorFibers_isConvex
    (hA : Convex 𝕜 (A : Set (U × X))) :
    convᵇ[𝕜](indicatorFibers α A) := by
  simpa [uncurry_indicatorFibers_eq_indicator (α := α) (A := A)] using
    (indicator_graph_isConvex (𝕜 := 𝕜) (α := α) (A := A) hA)

end Convexity

section Proper

variable {U : Type u} {X : Type v}
variable {α : Type*} [Zero α] [Preorder α]
variable {A : SetRel U X}

-- Proof sketch: `Bifunction.IsProper` is definitionally nonemptiness of the slice-domain, and
-- `dom_indicatorFibers_eq_dom` identifies that slice-domain with `A.dom`.
/-- The indicator bifunction is proper exactly when the underlying process has nonempty domain. -/
theorem indicatorFibers_isProper (hA_dom : A.dom.Nonempty) :
    Bifunction.IsProper (indicatorFibers α A) := by
  rw [Bifunction.IsProper, dom_indicatorFibers_eq_dom]
  exact hA_dom

namespace IsConvexProcess

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]

-- Proof sketch: the convex-process owner supplies the primitive domain witness `0 ∈ A.dom`
-- through `hA.zero_mem`, so the owner-level properness criterion applies immediately.
/-- Convex-process specialization of `indicatorFibers_isProper`. -/
theorem indicatorFibers_isProper (hA : A.IsConvexProcess 𝕜) :
    Bifunction.IsProper (indicatorFibers α A) :=
  SetRel.indicatorFibers_isProper ⟨0, ⟨0, hA.zero_mem⟩⟩

end IsConvexProcess

end Proper

section Closed

variable {U : Type u} {X : Type v}
variable {α : Type*}
variable [TopologicalSpace (U × X)]
variable [Zero α] [Preorder α]
variable (A : SetRel U X)

-- Proof sketch: view the uncurried slice-wise indicator expression as the indicator of the graph
-- set `A ⊆ U × X`. For indicator functions, lower semicontinuity is equivalent to closedness of
-- the underlying set, so the closedness of the bifunction is exactly closedness of the graph of
-- `A`.
/-- The indicator bifunction is closed exactly when the graph of the underlying process is
closed. -/
private theorem lowerSemicontinuous_indicator_graph_iff_isClosed :
    LowerSemicontinuous (δ[α](· | (A : Set (U × X)))) ↔
      A.IsClosed := sorry

/-- Bridge form of `lowerSemicontinuous_indicator_graph_iff_isClosed` on
`indicatorFibers α A`, stated on the canonical Chapter 6 surface `closedᵇ(·)`. -/
theorem lowerSemicontinuous_uncurry_indicatorFibers_iff_isClosed :
    closedᵇ(indicatorFibers α A) ↔
      A.IsClosed := by
  simpa [uncurry_indicatorFibers_eq_indicator (α := α) (A := A)] using
    (lowerSemicontinuous_indicator_graph_iff_isClosed (α := α) (A := A))

end Closed

end SetRel
