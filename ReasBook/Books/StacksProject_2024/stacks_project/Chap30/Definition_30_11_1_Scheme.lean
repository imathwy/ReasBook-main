import Mathlib.AlgebraicGeometry.Scheme
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap30.Lemma_30_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the scheme-side owners in Definition 30.11.1 are source-facing stalkwise
-- conditions on the structure sheaf, so they are kept here as lightweight direct owners separate
-- from the heavier coherent-module API.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Definition 30.11.1 (2): a locally Noetherian scheme `X` has depth `k` at a point `x` if
`depth(\mathcal O_{X, x}) = k`. -/
def hasDepthAt (x : X) (k : ℕ) : Prop :=
  moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) = k

/-- Unfold the depth-at-a-point condition for a locally Noetherian scheme. -/
theorem hasDepthAt_def (x : X) (k : ℕ) :
    hasDepthAt X x k =
      (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) = k) :=
  rfl

/-- Unfold the depth-at-a-point condition for a locally Noetherian scheme. -/
@[simp] theorem hasDepthAt_iff (x : X) (k : ℕ) :
    hasDepthAt X x k ↔
      moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) = k :=
  Iff.rfl

/-- Definition 30.11.1 (4): a locally Noetherian scheme `X` satisfies `(S_k)` if every stalk
`\mathcal O_{X, x}` satisfies the corresponding stalkwise depth inequality. -/
def satisfiesSerreConditionS (k : ℕ) : Prop :=
  ∀ x : X,
    WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
      min (k : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x))

/-- Unfold the stalkwise `(S_k)` condition for a locally Noetherian scheme. -/
theorem satisfiesSerreConditionS_def (k : ℕ) :
    satisfiesSerreConditionS X k =
      (∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
          min (k : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x))) :=
  rfl

/-- Unfold the stalkwise `(S_k)` condition for a locally Noetherian scheme. -/
@[simp] theorem satisfiesSerreConditionS_iff (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      ∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
          min (k : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x)) :=
  Iff.rfl

end AlgebraicGeometry.Scheme
