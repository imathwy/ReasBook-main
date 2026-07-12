import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary33_1_1

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

open SaddleFunction

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.4 records the relations between the Chapter 34 lower closure
  `K̲ = cl₂ (cl₁ K)` and upper closure `K̅ = cl₁ (cl₂ K)`.
- `core/canonical`: the owner level is the Chapter 34 API `Bifunction.lowerClosure`,
  `Bifunction.upperClosure`, and the partial closures `Bifunction.closure1`, `Bifunction.closure2`
  already introduced upstream.
- `bridge/view`: this item only records the two closure identities relating those canonical
  Chapter 34 owners.

Domain-style sampling used here:
- `Bifunction.lowerClosure` from `Defn_34_1`;
- `Bifunction.upperClosure` from `Defn_34_1`;
- `Bifunction.closure1` from `Definition33_0_4`;
- `Bifunction.closure2` from `Definition33_0_4`.

Primitive data vs derived API:
- primitive source datum: a concave-convex saddle bifunction `K : U → X → WithBotTop 𝕜`;
- primitive owner API reused here: the Chapter 34 partial closures `cl₁`, `cl₂` and the
  canonical closure representatives `lowerClosure`, `upperClosure`;
- derived API: the two displayed relations of Text 34.1.4.

Layer target: `bridge/view`, stated directly on the canonical Chapter 34 closure owners.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U] [TopologicalSpace U]
variable [AddCommMonoid X] [SMul 𝕜 X] [TopologicalSpace X]

-- This is the first mixed closure relation between the canonical Chapter 34 iterated closures.
-- It is the bridge used immediately downstream to prove idempotence of `lowerClosure` and
-- `upperClosure`.
/-- Text 34.1.4: applying `cl₁` to the lower closure `K̲ = cl₂ (cl₁ K)` gives the upper closure
`K̅ = cl₁ (cl₂ K)`. This is the first displayed relation of the text, and the companion theorem
below records the symmetric second relation. -/
@[simp] theorem _root_.SaddleFunction.IsConcaveConvex.closure1_lowerClosure_eq_upperClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₁ K̲ = K̅ := by
  sorry

@[simp] theorem closure1_lowerClosure_eq_upperClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₁ K̲ = K̅ :=
  hK.closure1_lowerClosure_eq_upperClosure

-- This is the symmetric mixed closure relation paired with the preceding theorem.
/-- Applying `cl₂` to the upper closure `K̅ = cl₁ (cl₂ K)` gives back the lower closure
`K̲ = cl₂ (cl₁ K)`. This is the symmetric second displayed relation from the text. -/
@[simp] theorem _root_.SaddleFunction.IsConcaveConvex.closure2_upperClosure_eq_lowerClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₂ K̅ = K̲ := by
  sorry

@[simp] theorem closure2_upperClosure_eq_lowerClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₂ K̅ = K̲ :=
  hK.closure2_upperClosure_eq_lowerClosure

end

end Bifunction
