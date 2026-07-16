import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_5
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42

noncomputable section

universe u v w

open scoped Rockafellar

namespace SaddleFunction

open Bifunction

section

variable {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary33.3.2 says that lower closed concave-convex saddle-functions and
  upper closed concave-convex saddle-functions correspond through the partial closures.
- `core/canonical`: the owner layer is the Chapter 33 closure API
  `cl₁`, `cl₂`, `SaddleFunction.IsConcaveConvex`,
  `SaddleFunction.IsLowerClosed`, and `SaddleFunction.IsUpperClosed` on
  `WithBotTop 𝕜`, together with the set-theoretic correspondence owners `Set.InvOn` and
  `Set.BijOn`.
- `bridge/view`: no new owner wrapper is introduced; the correspondence is stated directly on the
  canonical owner predicates.

Domain-style sampling used here:
- `cl₁` and `cl₂`;
- `SaddleFunction.IsConcaveConvex.closure1` and `SaddleFunction.IsConcaveConvex.closure2`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed`;
- `Bifunction.lowerClosure` and `Bifunction.upperClosure`.

Primitive data vs derived API:
- primitive datum: a saddle-function `K : U → X → WithBotTop 𝕜`;
- derived API: the inverse-on statement for the fixed-point closure classes, and the
  source-facing bijection statement obtained by intersecting those classes with the
  concave-convex owner predicate.

Layer target: `source-facing`, expressed directly as the closure-operator correspondence on the
existing Chapter 7 owner surface without local set-comprehension owners.
-/

-- Proof sketch: the fixed-point equations `K̲ = K` and `K̅ = K` are exactly the owner predicates
-- `IsLowerClosed K` and `IsUpperClosed K`, so the closure identities alone give the two
-- inverse-on-subsets equalities.
/-- The first and second partial closures are inverse on the lower-closed and upper-closed
fixed-point classes. -/
theorem closure1_closure2_invOn_lowerClosed_upperClosed :
    Set.InvOn
      (cl₂ ·)
      (cl₁ ·)
      {K : U → X → WithBotTop 𝕜 | IsLowerClosed K}
      {K : U → X → WithBotTop 𝕜 | IsUpperClosed K} := by
  constructor
  · intro K hK
    simpa [SaddleFunction.IsLowerClosed, Bifunction.lowerClosure] using hK
  · intro K hK
    simpa [SaddleFunction.IsUpperClosed, Bifunction.upperClosure] using hK

end

-- Proof sketch: use the inverse-on-subsets statement for `cl₁` and `cl₂`, then apply
-- `Set.InvOn.bijOn` to obtain the corresponding bijection between the two closure classes.
section Bijection

variable {𝕜 : Type w}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]
variable [AddCommGroup U] [Module 𝕜 U] [IsTopologicalAddGroup U] [ContinuousConstSMul 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X] [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]

/-- Corollary33.3.2: the relation `Kbar = cl₁ K`, equivalently `K = cl₂ Kbar`, gives a one-to-one
correspondence between lower closed concave-convex saddle-functions and upper closed
concave-convex saddle-functions on `U × X`. -/
theorem closure1_bijOn_lowerClosedConcaveConvex_upperClosedConcaveConvex :
    Set.BijOn
      (cl₁ ·)
      ({K : U → X → WithBotTop 𝕜 | IsConcaveConvex 𝕜 K} ∩
        {K : U → X → WithBotTop 𝕜 | IsLowerClosed K})
      ({K : U → X → WithBotTop 𝕜 | IsConcaveConvex 𝕜 K} ∩
        {K : U → X → WithBotTop 𝕜 | IsUpperClosed K}) := sorry

end Bijection

end SaddleFunction
