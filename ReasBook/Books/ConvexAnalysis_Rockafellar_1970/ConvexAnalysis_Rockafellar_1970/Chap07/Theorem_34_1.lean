import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary33_1_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_34_0_1

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

open SaddleFunction

section Closedness

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U] [TopologicalSpace U]
variable [AddCommMonoid X] [SMul 𝕜 X] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 34.1 concerns saddle-functions. The text fixes the
  concave-convex orientation for definiteness; this file keeps those direct branch theorems and
  records the convex-concave branch through the canonical symmetry bridge `Function.swap`.
- `core/canonical`: the closure representatives are the Chapter 34 owners
  `Bifunction.lowerClosure` and `Bifunction.upperClosure`; the closedness owners are
  `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from
  `Definition33_0_42`.
- `bridge/view`: the saddle-shape part is expressed through the canonical Chapter 33 owners
  `SaddleFunction.IsConcaveConvex 𝕜` and `SaddleFunction.IsConvexConcave 𝕜`, related by
  `Function.swap`; no surrogate wrapper owner is introduced.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex` and `SaddleFunction.IsConvexConcave` from
  `Definition33_0_1`;
- `SaddleFunction.IsConcaveConvex.closure1_closed` and
  `SaddleFunction.IsConcaveConvex.closure2_closed` from `Corollary33_1_1`;
- `Bifunction.lowerClosure`, `Bifunction.upperClosure`, `Bifunction.lowerClosure_idem`, and
  `Bifunction.upperClosure_idem` from `Text_34_0_1`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from `Definition33_0_42`;
- `Function.swap` as the canonical symmetry bridge.

Layer target: `source-facing`, with atomic owner-level consequences for the lower and upper
closures and the branchwise source-facing conjunction clauses.
-/

/-- The lower closure of a concave-convex saddle-function is lower closed. -/
theorem lowerClosure_isLowerClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsLowerClosed K̲ := by
  exact (isLowerClosed_iff K̲).2 (lowerClosure_idem hK)

/-- The upper closure of a concave-convex saddle-function is upper closed. -/
theorem upperClosure_isUpperClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsUpperClosed K̅ := by
  exact (isUpperClosed_iff K̅).2 (upperClosure_idem hK)

end Closedness

section Shape

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [TopologicalSpace U] [TopologicalSpace X]

/-- The lower closure of a concave-convex saddle-function is again concave-convex. -/
theorem lowerClosure_isConcaveConvex
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̲ := by
  change IsConcaveConvex 𝕜 (cl₂ (cl₁ K))
  exact (hK.closure1.closure2_closed).1

/-- The upper closure of a concave-convex saddle-function is again concave-convex. -/
theorem upperClosure_isConcaveConvex
    [IsOrderedAddMonoid 𝕜]
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̅ := by
  change IsConcaveConvex 𝕜 (cl₁ (cl₂ K))
  exact (hK.closure2.closure1_closed).1

section WithClosedness

/-- Theorem 34.1 (1): if `K` is a concave-convex saddle-function, then its lower closure is again
a concave-convex saddle-function and is lower closed. -/
theorem lowerClosure_isConcaveConvex_and_isLowerClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̲ ∧ IsLowerClosed K̲ := by
  exact ⟨lowerClosure_isConcaveConvex hK, lowerClosure_isLowerClosed hK⟩

/-- Theorem 34.1 (2): if `K` is a concave-convex saddle-function, then its upper closure is again
a concave-convex saddle-function and is upper closed. -/
theorem upperClosure_isConcaveConvex_and_isUpperClosed
    [IsOrderedAddMonoid 𝕜]
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̅ ∧ IsUpperClosed K̅ := by
  exact ⟨upperClosure_isConcaveConvex hK, upperClosure_isUpperClosed hK⟩

/-- The convex-concave symmetry companion to Theorem 34.1 (1): if `K` is convex-concave, then the
lower closure of `Function.swap K` is again concave-convex and lower closed. By the terminology
swap of `Definition33_0_42`, this is the upper-closed branch for the original orientation. -/
theorem swap_lowerClosure_isConcaveConvex_and_isLowerClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConvexConcave 𝕜 K) :
    IsConcaveConvex 𝕜 ((Function.swap K)̲) ∧ IsLowerClosed ((Function.swap K)̲) := by
  have hK' : IsConcaveConvex 𝕜 (Function.swap K) := hK.swap
  exact lowerClosure_isConcaveConvex_and_isLowerClosed hK'

/-- The convex-concave symmetry companion to Theorem 34.1 (2): if `K` is convex-concave, then the
upper closure of `Function.swap K` is again concave-convex and upper closed. By the terminology
swap of `Definition33_0_42`, this is the lower-closed branch for the original orientation. -/
theorem swap_upperClosure_isConcaveConvex_and_isUpperClosed
    [IsOrderedAddMonoid 𝕜]
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConvexConcave 𝕜 K) :
    IsConcaveConvex 𝕜 ((Function.swap K)̅) ∧ IsUpperClosed ((Function.swap K)̅) := by
  have hK' : IsConcaveConvex 𝕜 (Function.swap K) := hK.swap
  exact upperClosure_isConcaveConvex_and_isUpperClosed hK'

end WithClosedness

end Shape

end Bifunction
