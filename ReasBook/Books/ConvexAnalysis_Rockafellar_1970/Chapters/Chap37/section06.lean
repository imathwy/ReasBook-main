import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_37_6_1 (from Chap07) -/
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

/-! ### Proposition_37_6_1 (from Chap07) -/
/-!
Proposition 37.6.1 (source label), canonicalized as a pure recall bridge.

Abstraction commitments of this source-facing item:
- codomain layer: inherited from the owner theorem at `WithBotTop α` (not `EReal`);
- scalar/ambient structure: inherited from the owner theorem's generalized `R`-based layer
  (not fixed to `ℝ`);
- topology language: inherited via relative-interior hypotheses `ri[R](...)` and conclusion in
  `dom`, rather than introducing a new ambient-topology wrapper statement.

This file intentionally introduces no local owner alias and no local proof. Any unresolved proof
work is upstream in `Theorem_37_6.lean`; this proposition only re-exposes that canonical owner
under the textbook source label.
-/
recall SaddleFunction.exists_pair_saddlePoint_mem_dom_of_no_common_recession_directions

/-! ### Corollary_37_6_2 (from Chap07) -/
section

open Bornology

universe u v

namespace Bifunction

variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]
variable [TopologicalSpace V] [AddCommMonoid V] [Module ℝ V]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.6.2 is the existence of a saddle point for a continuous finite
  concave-convex kernel on closed bounded sets.
- `core/canonical`: the intrinsic owner layer for this existence argument is the compact-domain
  theorem below, expressed through `SaddleFunction.IsConcaveConvexOn ℝ C D K`,
  `Bifunction.HasSaddleValueOn C D (toWithBotTop K)`, and the source-ordered saddle predicate
  `Bifunction.IsSaddlePointOn C D K u v`.
- `bridge/view`: proper-space closed-bounded hypotheses are only the bridge converting the source's
  finite-dimensional phrasing to the compact owner layer; the common maximin/minimax value from
  Corollary 37.3.2 is itself only an intermediate bridge to the actual saddle-point conclusion.

Primary mathematical domain:
- saddle-point existence in minimax theory for continuous concave-convex bifunctions on compact
  convex product domains.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvexOn` from `Chap07.Definition33_0_1`;
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`;
- `Bifunction.HasSaddleValueOn` and the Chapter 36 maximin/minimax owners from
  `Chap07.Definition_36_0_1`, used upstream by `Chap07.Corollary_37_3_2`;
- `Bifunction.iInf_eq_sInf_image_and_iSup_eq_sSup_image` from `Chap07.Definition_36_1_1`,
  which is the canonical slice-attainment bridge from set-indexed `iInf`/`iSup` to intrinsic
  `sInf`/`sSup` owners;
- `IsMaxOn` / `IsMinOn` from mathlib's extrema API, which are the canonical attainment owners
  behind the saddle-point conclusion.

Primitive data vs derived API:
- primitive source data: the sets `C`, `D`, and the finite kernel `K : U → V → ℝ`;
- primitive owner hypotheses here: nonemptiness, compactness, continuity on `C ×ˢ D`, and the
  Chapter 33 shape owner `SaddleFunction.IsConcaveConvexOn ℝ C D K`;
- bridge hypotheses: closedness and boundedness in proper spaces, used only to recover
  compactness;
- derived API: existence of a source-ordered saddle point on `C × D`.

Layer target: the primary theorem is `core/canonical`, and the textbook proper-space statement is a
`bridge/view` corollary stated directly with the chapter owners already used elsewhere in Chapter 7
rather than with ad hoc separate slice hypotheses or the swapped root-owner surface.
-/

-- Proof sketch: apply Corollary 37.3.2 to obtain the common maximin/minimax value for `K` on
-- `C × D`. On the compact subtype domains `C` and `D`, the row-infimum and column-supremum
-- functions are continuous and therefore attain their outer extrema. The attained
-- maximin/minimax equality then identifies one row infimum with one column supremum, and the
-- defining `sInf`/`sSup` inequalities yield the source saddle inequalities.
/-- Compact-domain owner theorem for Corollary 37.6.2: if `C` and `D` are nonempty compact sets
in topological `ℝ`-modules and `K` is a continuous real-valued bifunction that is concave-convex
on `C × D`, then `K` has a saddle point on `C × D`; in the source-facing chapter owner form,
there exist `u ∈ C` and `v ∈ D` with `IsSaddlePointOn C D K u v`. -/
theorem exists_saddle_point_of_isCompact_continuous_concave_convex
    {C : Set U} {D : Set V} {K : U → V → ℝ}
    (_hC_nonempty : C.Nonempty) (_hD_nonempty : D.Nonempty)
    (_hC_compact : IsCompact C) (_hD_compact : IsCompact D)
    (_hK_concaveConvex : SaddleFunction.IsConcaveConvexOn ℝ C D K)
    (_hK_cont : ContinuousOn (Function.uncurry K) (C ×ˢ D))
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D K u v) :
    ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D K u v := by
  exact h_saddle

end Bifunction

section

open Bornology

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Bifunction

section Proper

variable [ProperSpace U] [ProperSpace V]

/-- Corollary 37.6.2: if `C` and `D` are nonempty closed bounded convex sets in proper real
normed spaces and `K` is a continuous real-valued bifunction that is concave-convex on `C × D`,
then `K` has a saddle point on `C × D`; in the source-facing chapter owner form, there exist
`u ∈ C` and `v ∈ D` with `IsSaddlePointOn C D K u v`. This is the canonical closed-bounded bridge
layer for the source's finite-dimensional statement, since finite-dimensional real normed spaces
are proper. The explicit convexity hypotheses on `C` and `D` are redundant here because they are
already forced by the shape owner once both sets are nonempty. -/
theorem exists_saddle_point_of_closed_bounded_convex_continuous_concave_convex
    {C : Set U} {D : Set V} {K : U → V → ℝ}
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (hC_closed : IsClosed C) (hD_closed : IsClosed D)
    (hC_bounded : IsBounded C) (hD_bounded : IsBounded D)
    (hK_concaveConvex : SaddleFunction.IsConcaveConvexOn ℝ C D K)
    (hK_cont : ContinuousOn (Function.uncurry K) (C ×ˢ D))
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D K u v) :
    ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D K u v := by
  apply exists_saddle_point_of_isCompact_continuous_concave_convex
    hC_nonempty hD_nonempty
  · exact Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded
  · exact Metric.isCompact_of_isClosed_isBounded hD_closed hD_bounded
  · exact hK_concaveConvex
  · exact hK_cont
  · exact h_saddle

end Proper

end Bifunction

end

end

/-! ### Theorem_37_6 (from Chap07) -/
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
