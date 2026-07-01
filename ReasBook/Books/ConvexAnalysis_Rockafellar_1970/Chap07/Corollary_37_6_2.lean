import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_7
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_1_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary_37_3_2

-- Declarations for this item will be appended below by the statement pipeline.

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
