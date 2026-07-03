import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_34_3 (from Chap07) -/
noncomputable section

universe u v w z

open scoped Rockafellar

namespace SaddleFunction

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace (WithBotTop α)] [SMul 𝕜 α]
variable [AddCommMonoid (WithBotTop α)] [PartialOrder (WithBotTop α)] [SMul 𝕜 (WithBotTop α)]

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 34.3 characterizes closed proper concave-convex saddle-functions by the
  relative-interior closed-slice equalities, the boundary slice-domain closure conditions, and the
  endpoint behavior outside the coordinate domains.
- `core/canonical`: the existing owners already present in the project are
  `SaddleFunction.IsConcaveConvex 𝕜 K`, `SaddleFunction.IsClosed K`,
  `SaddleFunction.IsProper K`, the Chapter 34 domain sets `dom₁ K` and `dom₂ K`, the relative
  interior notation `ri[𝕜](·)`, the ordinary slice effective-domain owner `dom(·)`, and the
  bundled closed/proper/convex owner `Function.IsClosedProperConvex`.

Primary mathematical domain:
- convex analysis of closed concave-convex saddle-functions and their one-variable slices.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `SaddleFunction.IsConcaveConvex` from `Chap07.Definition33_0_1`;
- `SaddleFunction.dom₁`, `SaddleFunction.dom₂`,
  `dom₁_subset_dom_firstSlice`, and `dom₂_subset_dom_secondSlice` from `Chap07.Defn_34_3`;
- the relative-interior notation `ri[𝕜](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive source datum: a saddle bifunction `K : U → X → WithBotTop α`;
- primitive owner hypotheses in the main theorem: `IsConcaveConvex 𝕜 K` and `IsProper K`;
- primitive canonical closedness owner in the conclusion: `IsClosed K`;
- derived API: the theorem-level equivalence between the canonical Chapter 34 closedness owner and
  the reduced source-facing slice conditions that keep only the genuinely new closedness data,
  while slice convexity, slice properness on `dom₁ K`/`dom₂ K`, and the basic inclusions
  `dom₂ K ⊆ dom(K u)` / `dom₁ K ⊆ dom(fun u ↦ -K u v)` stay with the existing chapter owners.

Layer target: `source-facing`.
-/

-- Proof sketch: for the forward implication, use the Chapter 34 closure equations to identify the
-- first- and second-variable slice closures with the original slices on the relative interiors of
-- `dom₁ K` and `dom₂ K`. The remaining closedness-relevant information is exactly the boundary
-- containment of slice domains in the intrinsic closures of the opposite coordinate domains, plus
-- the endpoint behavior outside `dom₁ K` and `dom₂ K`. The omitted convexity/properness and basic
-- domain-inclusion facts are already owned upstream by `IsConcaveConvex 𝕜 K`, `IsProper K`, and
-- the Chapter 34 domain lemmas. For the reverse implication, these reduced clauses recover the
-- same slice closures and endpoint behavior needed by `isClosed_iff`.
/-- Theorem 34.3: for a proper concave-convex saddle-function `K`, the canonical Chapter 34
closedness owner `IsClosed K` is equivalent to the reduced source-facing slicewise closedness
conditions, where `C = dom₁ K` and `D = dom₂ K`. -/
theorem isClosed_iff_closedSliceCharacterization
    (K : U → X → WithBotTop α)
    (hK_shape : IsConcaveConvex 𝕜 K)
    (hK_proper : IsProper K) :
    IsClosed K ↔
      (∀ ⦃u : U⦄, u ∈ ri[𝕜](dom₁ K) →
        IsClosedProperConvex[𝕜] (K u) ∧ dom(K u) = dom₂ K) ∧
      (∀ ⦃u : U⦄, u ∈ dom₁ K \ ri[𝕜](dom₁ K) →
        dom(K u) ⊆ intrinsicClosure 𝕜 (dom₂ K)) ∧
      (∀ ⦃u : U⦄, u ∉ dom₁ K →
        (∀ v ∈ ri[𝕜](dom₂ K), K u v = ⊥) ∧
          (u ∉ intrinsicClosure 𝕜 (dom₁ K) → ∀ v ∈ dom₂ K, K u v = ⊥)) ∧
      (∀ ⦃v : X⦄, v ∈ ri[𝕜](dom₂ K) →
        IsClosedProperConvex[𝕜] (fun u ↦ -K u v) ∧
          dom(fun u ↦ -K u v) = dom₁ K) ∧
      (∀ ⦃v : X⦄, v ∈ dom₂ K \ ri[𝕜](dom₂ K) →
        dom(fun u ↦ -K u v) ⊆ intrinsicClosure 𝕜 (dom₁ K)) ∧
      ∀ ⦃v : X⦄, v ∉ dom₂ K →
        (∀ u ∈ ri[𝕜](dom₁ K), K u v = ⊤) ∧
          (v ∉ intrinsicClosure 𝕜 (dom₂ K) → ∀ u ∈ dom₁ K, K u v = ⊤) := sorry

end

end SaddleFunction
