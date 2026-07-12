import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_2_2

noncomputable section

universe u v w

open scoped Rockafellar

namespace SaddleFunction

open Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable {K : U → X → WithBotTop 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.5 says that the one-variable closure operators in the `u` and `v`
  variables preserve the chapter's concave-convex saddle shape.
- `core/canonical`: for `WithBotTop 𝕜`-valued saddle bifunctions, the correct owner surface is
  `SaddleFunction.IsConcaveConvex 𝕜`, while the
  relevant closure operators are the already-owned `Bifunction.closure1` and
  `Bifunction.closure2`, written `cl₁` and `cl₂`.
- `bridge/view`: no new wrapper owner is introduced; the lemma is recorded directly as two
  closure-preservation theorems on the existing owner surface.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex 𝕜`;
- `Bifunction.closure1`, `Bifunction.closure2`;
- slice-wise `ConcaveOn` / `ConvexOn` from the Chapter 33 owner;
- closure-preservation bridges for one-variable closures.

Primitive data vs. derived API:
- primitive input: a saddle bifunction `K`;
- derived API: the two closure-preservation theorems for `cl₁ K` and `cl₂ K`.

Layer target: `source-facing`, stated directly on the canonical Chapter 33 owner surface.
-/

section FirstVariable

variable [Ring 𝕜] [TopologicalSpace U]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]

-- Proof sketch: unpack `hK` into the slice-wise concavity and convexity conditions. For each
-- fixed `x`, `u ↦ cl₁ K u x` is the concave closure of the concave slice `u ↦ K u x`, so it is
-- still concave. For each fixed `u`, the second-variable slice of `cl₁ K` is obtained pointwise
-- from the family of concave majorants defining `concaveClosure`; convexity of `x ↦ K u x`
-- propagates through that closure construction.
/-- Lemma33.0.5 (1): the first-variable partial closure `cl₁ K` of a concave-convex bifunction is
again concave-convex. -/
theorem IsConcaveConvex.closure1 (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 (cl₁ K) := sorry

end FirstVariable

section SecondVariable

variable [Semiring 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [TopologicalSpace X]

-- Proof sketch: unpack `hK` into the slice-wise concavity and convexity conditions. For each
-- fixed `u`, `x ↦ cl₂ K u x` is the lower-semicontinuous hull of the convex slice `x ↦ K u x`,
-- so it remains convex. For each fixed `x`, write `cl₂ K u x` as the monotone limit of the local
-- infimum envelopes of `K`; those envelopes are infima of concave functions in `u`, hence
-- concave, and the decreasing limit preserves concavity.
/-- Lemma33.0.5 (2): the second-variable partial closure `cl₂ K` of a concave-convex bifunction is
again concave-convex. -/
theorem IsConcaveConvex.closure2 (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 (cl₂ K) := sorry

end SecondVariable

end

end SaddleFunction
