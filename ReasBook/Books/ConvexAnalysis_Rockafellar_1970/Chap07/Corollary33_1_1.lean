import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_5

noncomputable section

universe u v w

open scoped Rockafellar

namespace SaddleFunction

open Bifunction

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [NoMaxOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]

section FirstVariableClosure

variable [Ring 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜]
variable [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [TopologicalSpace U] [IsOrderedAddMonoid 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary33.1.1 records that the one-variable partial closures of a
  concave-convex saddle bifunction preserve the saddle shape and become closed in the variable in
  which the closure is taken.
- `core/canonical`: the owner surface is already in the chapter API:
  `SaddleFunction.IsConcaveConvex 𝕜`, `Bifunction.closure1`, `Bifunction.closure2`,
  `Bifunction.IsConcaveClosed`, and `Bifunction.IsConvexClosed`.
- `bridge/view`: this file should therefore be a thin theorem-level bridge from the Chapter 33
  shape-preservation lemmas to the fixed-point closedness owners, not a second parallel closure
  API.

Primary mathematical domain:
- saddle bifunctions and their one-variable closure operators.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex 𝕜`;
- `Bifunction.closure1`, `Bifunction.closure2`, written `cl₁`, `cl₂`;
- `SaddleFunction.IsConcaveConvex.closure1`;
- `SaddleFunction.IsConcaveConvex.closure2`;
- `Bifunction.isConcaveClosed_iff_closure1_eq`;
- `Bifunction.isConvexClosed_iff_closure2_eq`.

Primitive data vs derived API:
- primitive input data: a bifunction `K` with the owner hypothesis `IsConcaveConvex 𝕜 K`;
- derived API: the two corollary-level conjunctions below.

Layer target: `source-facing`.
-/

/-- Corollary33.1.1 (1): if `K` is concave-convex, then `cl₁ K` is again concave-convex and is
concave-closed in the first variable. -/
-- Proof sketch: combine the closure-preservation theorem `IsConcaveConvex.closure1` with the
-- fixed-point characterization `isConcaveClosed_iff_closure1_eq`, using idempotence of `cl₁`.
theorem IsConcaveConvex.closure1_closed
    {K : U → X → WithBotTop 𝕜} (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 (cl₁ K) ∧ IsConcaveClosed (cl₁ K) := by
  refine ⟨hK.closure1, ?_⟩
  exact (isConcaveClosed_iff_closure1_eq (cl₁ K)).2 (closure1_idem K)

end FirstVariableClosure

section SecondVariableClosure

variable [Ring 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜]
variable [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [TopologicalSpace X]

/-- Corollary33.1.1 (2): if `K` is concave-convex, then `cl₂ K` is again concave-convex and is
convex-closed in the second variable. -/
-- Proof sketch: combine the closure-preservation theorem `IsConcaveConvex.closure2` with the
-- fixed-point characterization `isConvexClosed_iff_closure2_eq`, using idempotence of `cl₂`.
theorem IsConcaveConvex.closure2_closed
    {K : U → X → WithBotTop 𝕜} (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 (cl₂ K) ∧ IsConvexClosed (cl₂ K) := by
  refine ⟨hK.closure2, ?_⟩
  exact (isConvexClosed_iff_closure2_eq (cl₂ K)).2 (closure2_idem K)

end SecondVariableClosure

end SaddleFunction
