import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1

noncomputable section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section LowerUpperClosed

open Bifunction

variable {𝕜 : Type*}
variable [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [Neg 𝕜]
variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Definition33.0.42 introduces lower closedness and upper closedness for a
  concave-convex saddle-function.
- `core/canonical`: both notions are stated on the Chapter 34 owner equations
  `K̲ = K` and `K̅ = K`, where `K̲`, `K̅` are the iterated partial-closure composites from
  `Bifunction.lowerClosure` and `Bifunction.upperClosure`.
- `bridge/view`: for a convex-concave bifunction, the textbook convention swaps these fixed-point
  equations; this is bookkeeping at the same owner layer, not a new owner.

Domain-style sampling used here:
- `Bifunction.lowerClosure`, written `K̲`, from `Defn_34_1`;
- `Bifunction.upperClosure`, written `K̅`, from `Defn_34_1`;
- `Bifunction.closure1`, written `cl₁`, from `Definition33_0_4`;
- `Bifunction.closure2`, written `cl₂`, from `Definition33_0_4`;
- `Bifunction.concaveClosure_eq_neg_lowerSemicontinuousHull_neg`;
- `lowerSemicontinuousHull`, written `cl(·)`.

Primitive data vs derived API:
- primitive datum: a saddle-function `K : U → X → WithBotTop 𝕜`;
- primitive owner surface reused here: the iterated closure operators `K ↦ K̲` and `K ↦ K̅`;
- derived API kept minimal: only the owner-equation simp bridges used by immediate downstream
  statements.

Layer target: `source-facing`, stated directly on the existing iterated-closure owner surface.
-/

/-- Definition33.0.42: for a concave-convex saddle-function, `K` is lower closed when its lower
closure `K̲` is equal to `K`; for a convex-concave bifunction, the textbook lower/upper
terminology is interchanged with `IsUpperClosed`/`IsLowerClosed`. -/
def IsLowerClosed (K : U → X → WithBotTop 𝕜) : Prop :=
  K̲ = K

/-- Lower closedness is exactly the fixed-point predicate for the lower-closure owner
`K ↦ K̲`. -/
@[simp] theorem isLowerClosed_fixedPt_iff (K : U → X → WithBotTop 𝕜) :
    IsLowerClosed K ↔ Function.IsFixedPt lowerClosure K :=
  Iff.rfl

/-- Lower closedness is exactly the fixed-point equation for the lower-closure owner `K ↦ K̲`. -/
@[simp] theorem isLowerClosed_iff (K : U → X → WithBotTop 𝕜) :
    IsLowerClosed K ↔ K̲ = K :=
  Iff.rfl

/-- A saddle-function is lower closed exactly when `lowerClosure` fixes it. -/
@[simp] theorem isLowerClosed_def (K : U → X → WithBotTop 𝕜) :
    IsLowerClosed K ↔ lowerClosure K = K :=
  Iff.rfl

/-- A lower-closed saddle-function is fixed by the lower-closure operator. -/
@[simp] theorem IsLowerClosed.lowerClosure_eq {K : U → X → WithBotTop 𝕜}
    (hK : IsLowerClosed K) :
    K̲ = K :=
  hK

/-- Upper closedness for a concave-convex saddle-function is the fixed-point condition `K̅ = K`;
for a convex-concave bifunction, this is the textbook lower-closed equation. -/
def IsUpperClosed (K : U → X → WithBotTop 𝕜) : Prop :=
  K̅ = K

/-- Upper closedness is exactly the fixed-point predicate for the upper-closure owner
`K ↦ K̅`. -/
@[simp] theorem isUpperClosed_fixedPt_iff (K : U → X → WithBotTop 𝕜) :
    IsUpperClosed K ↔ Function.IsFixedPt upperClosure K :=
  Iff.rfl

-- Proof sketch: unfold `SaddleFunction.IsUpperClosed`; this is exactly the defining fixed-point
-- equation for the canonical owner `upperClosure`.
/-- A saddle-function is upper closed exactly when `upperClosure` fixes it. -/
@[simp] theorem isUpperClosed_def (K : U → X → WithBotTop 𝕜) :
    IsUpperClosed K ↔ upperClosure K = K :=
  Iff.rfl

/-- An upper-closed saddle-function is fixed by the upper-closure operator. -/
@[simp] theorem IsUpperClosed.upperClosure_eq {K : U → X → WithBotTop 𝕜}
    (hK : IsUpperClosed K) :
    K̅ = K :=
  hK

/-- Upper closedness is exactly the fixed-point equation for the upper-closure owner `K ↦ K̅`. -/
@[simp] theorem isUpperClosed_iff_upperClosure_eq (K : U → X → WithBotTop 𝕜) :
    IsUpperClosed K ↔ K̅ = K :=
  Iff.rfl

/-- Upper closedness is exactly the upper-closure fixed-point equation. -/
@[simp] theorem isUpperClosed_iff (K : U → X → WithBotTop 𝕜) :
    IsUpperClosed K ↔ K̅ = K :=
  isUpperClosed_iff_upperClosure_eq K

end LowerUpperClosed

end SaddleFunction
