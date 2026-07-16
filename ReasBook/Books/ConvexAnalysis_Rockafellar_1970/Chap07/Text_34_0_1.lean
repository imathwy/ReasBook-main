import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_34_1_4

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

open SaddleFunction

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.0.1 says that the Chapter 34 lower and upper closure operators are
  idempotent.
- `core/canonical`: the owner level is the Chapter 34 API `Bifunction.lowerClosure` and
  `Bifunction.upperClosure`.
- `bridge/view`: the partial-closure relations from `Text_34_1_4`,
  `cl₁ K̲ = K̅` and `cl₂ K̅ = K̲`, are the canonical bridge used to prove the operator
  idempotence equations `K̲̲ = K̲` and `K̅̅ = K̅`.

Primary mathematical domain:
- iterated closure operators on bifunctions in Chapter 34.

Domain-style sampling used here:
- `Bifunction.closure1_idem` and `Bifunction.closure2_idem` from `Definition33_0_4`;
- `Bifunction.lowerClosure` and `Bifunction.upperClosure` from `Defn_34_1`;
- `Bifunction.closure1_lowerClosure_eq_upperClosure` and
  `Bifunction.closure2_upperClosure_eq_lowerClosure` from `Text_34_1_4`.

Primitive data vs derived API:
- primitive datum: a bifunction `K : U → X → WithBotTop 𝕜`;
- primitive owner API: the Chapter 34 operators `lowerClosure` and `upperClosure`;
- derived bridge API: the mixed partial-closure identities imported from `Text_34_1_4`.

Layer target:
- `source-facing` for the two operator idempotence theorems below.
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

/-- Text 34.0.1: the Chapter 34 lower closure operator is idempotent. -/
@[simp] theorem lowerClosure_idem {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    K̲̲ = K̲ := by
  change cl₂ (cl₁ K̲) = K̲
  rw [closure1_lowerClosure_eq_upperClosure hK, closure2_upperClosure_eq_lowerClosure hK]

/-- Text 34.0.1: the Chapter 34 upper closure operator is idempotent. -/
@[simp] theorem upperClosure_idem {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    K̅̅ = K̅ := by
  change cl₁ (cl₂ K̅) = K̅
  rw [closure2_upperClosure_eq_lowerClosure hK, closure1_lowerClosure_eq_upperClosure hK]

end

end Bifunction
