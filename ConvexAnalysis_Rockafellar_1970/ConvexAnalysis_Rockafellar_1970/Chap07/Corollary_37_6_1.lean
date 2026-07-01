import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_37_6

noncomputable section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section

open Bifunction

variable {R : Type*} {α : Type*}
variable {U : Type u} {X : Type v}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [SMul R (WithBotTop α)]
variable {K : U → X → WithBotTop α}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.6.1 is the immediate existence-level consequence of
  Theorem 37.6 under the same two no-common-recession-direction assumptions.
- `core/canonical`: the owner layer is `SaddleFunction.IsClosed`, `SaddleFunction.IsProper`,
  `SaddleFunction.IsConcaveConvex R`, `SaddleFunction.dom`, and
  `Bifunction.IsSaddlePoint`.
- `bridge/view`: this file keeps only thin corollary surfaces, reusing the theorem-level owner
  abstraction from `Theorem_37_6` directly.

Layer target: `source-facing`.
-/

-- Proof sketch: apply Theorem 37.6 and drop the `dom K` witness while keeping the canonical
-- pair owner.
/-- Corollary 37.6.1, canonical owner form: under the no-common-recession-direction hypotheses,
there exists a saddle-point pair for `K`. -/
theorem exists_pair_saddlePoint_of_no_common_recession_directions
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (h_noCommon : NoCommonRecessionDirections R K) :
    ∃ p : U × X, IsSaddlePoint K p.1 p.2 := by
  rcases exists_pair_saddlePoint_mem_dom_of_no_common_recession_directions
      hK_closed hK_proper hK_concaveConvex h_noCommon with ⟨p, hp_saddle, -⟩
  exact ⟨p, hp_saddle⟩

-- Proof sketch: this is the coordinate-view bridge of Theorem 37.6's pair-domain witness.
/-- Coordinate-view bridge: under the no-common-recession-direction owner, there is a saddle-point
whose pair lies in the Chapter 34 product domain `dom K`. -/
theorem exists_saddlePoint_mem_dom_of_no_common_recession_directions
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (h_noCommon : NoCommonRecessionDirections R K) :
    ∃ u : U, ∃ x : X, IsSaddlePoint K u x ∧ (u, x) ∈ dom K := by
  rcases exists_pair_saddlePoint_mem_dom_of_no_common_recession_directions
      hK_closed hK_proper hK_concaveConvex h_noCommon with ⟨p, hp_saddle, hp_dom⟩
  exact ⟨p.1, p.2, hp_saddle, hp_dom⟩

/-- Corollary 37.6.1: if both no-common-recession-direction hypotheses hold for a closed proper
concave-convex saddle-function, then an ambient saddle-point exists. -/
theorem exists_saddlePoint_of_no_common_recession_directions
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (h_noCommon : NoCommonRecessionDirections R K) :
    ∃ u : U, ∃ x : X, IsSaddlePoint K u x := by
  rcases exists_pair_saddlePoint_of_no_common_recession_directions
      hK_closed hK_proper hK_concaveConvex h_noCommon with ⟨p, hp_saddle⟩
  exact ⟨p.1, p.2, hp_saddle⟩

-- Proof sketch: apply Theorem 37.6 and retain the Chapter 34 product-domain membership witness.
/-- Under the assumptions of Corollary 37.6.1, the Chapter 34 product domain `dom K` is nonempty. -/
theorem dom_nonempty_of_no_common_recession_directions
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (h_noCommon : NoCommonRecessionDirections R K) :
    (dom K).Nonempty := by
  rcases exists_saddlePoint_mem_dom_of_no_common_recession_directions
      hK_closed hK_proper hK_concaveConvex h_noCommon with ⟨u, x, -, hux_dom⟩
  exact ⟨(u, x), hux_dom⟩

end

end SaddleFunction
