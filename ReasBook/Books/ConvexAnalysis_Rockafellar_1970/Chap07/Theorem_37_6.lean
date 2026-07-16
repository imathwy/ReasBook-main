import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_7
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3

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

variable (R) in
/-- Absence of a common recession direction for the second-variable slice family
`u ↦ K(u, ·)` indexed by `u ∈ ri[R](dom₁ K)`. -/
def NoCommonSecondRecessionDirection (K : U → X → WithBotTop α) : Prop :=
  ¬ ∃ y : X,
      ∀ u ∈ ri[R](dom₁ K), (K u).RecedesInDirection R y

variable (R) in
/-- Absence of a common recession direction for the first-variable slice family
`v ↦ -K(·, v)` indexed by `v ∈ ri[R](dom₂ K)`. -/
def NoCommonFirstRecessionDirection (K : U → X → WithBotTop α) : Prop :=
  ¬ ∃ y : U,
      ∀ v ∈ ri[R](dom₂ K), (fun u ↦ -K u v).RecedesInDirection R y

variable (R) in
/-- Joint no-common-recession-direction owner used in Theorem 37.6. -/
def NoCommonRecessionDirections (K : U → X → WithBotTop α) : Prop :=
  NoCommonSecondRecessionDirection R K ∧
    NoCommonFirstRecessionDirection R K

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 37.6 asserts that the two no-common-recession-direction hypotheses from
  Theorem 37.3 force existence of an ambient saddle-point of `K`, and that any such point lies in
  the Chapter 34 product domain `dom K`.
- `core/canonical`: the owner layer is already present in the chapter through
  `SaddleFunction.IsClosed`, `SaddleFunction.IsProper`, `SaddleFunction.IsConcaveConvex R`,
  `SaddleFunction.dom`, `Function.RecedesInDirection`, and mathlib's
  `Bifunction.IsSaddlePoint`.
- `bridge/view`: this item stays source-facing and reuses the existing chapter owners directly,
  rather than reintroducing local copies of the recession-direction or domain API.

Primary mathematical domain:
- minimax theory for closed proper concave-convex saddle-functions via absence of common
  recession directions.

Domain-style sampling used here:
- `Function.RecedesInDirection` from `Chap06.Definition_6_27_4`;
- `SaddleFunction.dom₁`, `SaddleFunction.dom₂`, `SaddleFunction.dom`,
  `SaddleFunction.IsClosed`, and `SaddleFunction.IsConcaveConvex R` from the Chapter 34 owner
  layer;
- `Bifunction.IsSaddlePoint` from `Chap06.Definition_6_28_7`.

Primitive data vs derived API:
- primitive source data: the saddle-function `K`;
- primitive source-facing hypotheses: `IsClosed K`, `IsProper K`, `IsConcaveConvex R K`, and the
  two no-common-recession-direction assumptions on the slice families;
- derived API: existence of a saddle-point together with membership of that point in
  `dom K`.

Layer target: `source-facing`.
-/

-- Proof sketch: first obtain an ambient saddle-point from the Chapter 37 no-common-recession
-- hypotheses using the preceding saddle-point existence criterion in this section. Then apply the
-- Chapter 36 domain lemma saying that any ambient saddle-point of a closed proper concave-convex
-- saddle-function lies in `dom K`.
/-- Theorem 37.6: if both no-common-recession-direction conditions from Theorem 37.3 hold for a
closed proper concave-convex saddle-function `K`, then `K` has an ambient saddle-point; moreover,
the resulting saddle-point lies in the Chapter 34 product domain `dom K`. -/
theorem exists_pair_saddlePoint_mem_dom_of_no_common_recession_directions
    {K : U → X → WithBotTop α}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (h_noCommon : NoCommonRecessionDirections R K) :
    ∃ p : U × X,
      IsSaddlePoint K p.1 p.2 ∧ p ∈ dom K := sorry

end

end SaddleFunction
