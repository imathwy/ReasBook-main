import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_38
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42

noncomputable section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section

open Bifunction

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.43 identifies fully closed saddle-functions with those that are both
  lower closed and upper closed.
- `core/canonical`: the owner predicates are `Bifunction.IsFullyClosed`,
  `SaddleFunction.IsLowerClosed`, and `SaddleFunction.IsUpperClosed`, together with the Chapter 34
  operators `K̲` and `K̅`.
- `bridge/view`: this file keeps only the equivalence between those existing owner predicates; it
  does not introduce a parallel closure wrapper.

Domain-style sampling used here:
- `Bifunction.IsFullyClosed` from `Definition33_0_38`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from `Definition33_0_42`;
- `Bifunction.lowerClosure` and `Bifunction.upperClosure` from `Defn_34_1`;
- `Bifunction.isConvexClosed_iff_closure2_eq` and
  `Bifunction.isConcaveClosed_iff_closure1_eq` from `Definition33_0_4`.

Primitive data vs derived API:
- primitive datum: a saddle-function `K : U → X → WithTopBot 𝕜`;
- source-facing statement layer: fixed-point equations `K̲ = K` and `K̅ = K`;
- derived API: the bridge theorem below relating those equations to the canonical closedness
  owners `IsLowerClosed` and `IsUpperClosed`.

Layer target: `source-facing`, stated directly on the canonical owner predicates.
-/

/-- Lemma33.0.43: a saddle-function is fully closed if and only if it is both lower closed and
upper closed. -/
@[simp] theorem isFullyClosed_iff
    (K : U → X → WithTopBot 𝕜) :
    IsFullyClosed K ↔ IsLowerClosed K ∧ IsUpperClosed K := by
  constructor
  · intro hK
    have hcl2 : cl₂ K = K := hK.convexClosed.closure2_eq
    have hcl1 : cl₁ K = K := hK.concaveClosed.closure1_eq
    refine ⟨(isLowerClosed_iff K).2 ?_, (isUpperClosed_iff K).2 ?_⟩
    · simp [Bifunction.lowerClosure, hcl1, hcl2]
    · simp [Bifunction.upperClosure, hcl1, hcl2]
  · rintro ⟨hLower, hUpper⟩
    have hLowerEq : K̲ = K := (isLowerClosed_iff K).1 hLower
    have hUpperEq : K̅ = K := (isUpperClosed_iff K).1 hUpper
    have hConvex : IsConvexClosed K := by
      simpa [hLowerEq] using (Bifunction.lowerClosure_isConvexClosed (K := K))
    have hConcave : IsConcaveClosed K := by
      simpa [hUpperEq] using (Bifunction.upperClosure_isConcaveClosed (K := K))
    exact ⟨hConvex, hConcave⟩

/-- Lemma33.0.43 in notation surface: a saddle-function is fully closed exactly when both closure
fixed-point equations `K̲ = K` and `K̅ = K` hold. -/
theorem isFullyClosed_iff_lowerClosure_eq_and_upperClosure_eq
    (K : U → X → WithTopBot 𝕜) :
    IsFullyClosed K ↔ K̲ = K ∧ K̅ = K := by
  simpa [isLowerClosed_iff, isUpperClosed_iff] using
    (isFullyClosed_iff K)

/-- Bridge direction from Lemma33.0.43: a fully closed saddle-function is lower closed. -/
theorem IsFullyClosed.isLowerClosed
    {K : U → X → WithTopBot 𝕜} (hK : IsFullyClosed K) :
    IsLowerClosed K := by
  exact (isFullyClosed_iff K).1 hK |>.1

/-- Bridge direction from Lemma33.0.43: a fully closed saddle-function is upper closed. -/
theorem IsFullyClosed.isUpperClosed
    {K : U → X → WithTopBot 𝕜} (hK : IsFullyClosed K) :
    IsUpperClosed K := by
  exact (isFullyClosed_iff K).1 hK |>.2

/-- Bridge direction from Lemma33.0.43: lower and upper closedness imply full closedness. -/
theorem IsLowerClosed.isFullyClosed
    {K : U → X → WithTopBot 𝕜} (hLower : IsLowerClosed K) (hUpper : IsUpperClosed K) :
    IsFullyClosed K := by
  exact (isFullyClosed_iff K).2 ⟨hLower, hUpper⟩

end

end SaddleFunction
