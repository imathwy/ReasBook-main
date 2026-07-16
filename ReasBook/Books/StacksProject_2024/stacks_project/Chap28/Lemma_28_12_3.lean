import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_8_1
import StacksProject_2024.stacks_project.Chap30.Definition_30_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` did not surface a pre-existing scheme-level iff for this
-- Stacks item, while the local Chapter 28/30 owners are already fixed as the Cohen-Macaulay
-- affine-local condition from `Definition_28_8_1` and `satisfiesSerreConditionS X k`. The source
-- quantifier `k ≥ 0` is therefore represented by `∀ k : ℕ`.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 28.12.3: let `X` be a locally Noetherian scheme. Then `X` is Cohen-Macaulay if and only
if `X` has `(S_k)` for every natural number `k`. -/
@[stacks 0342]
theorem cohenMacaulay_iff_forall_satisfiesSerreConditionS :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) ↔
      ∀ k : ℕ, satisfiesSerreConditionS X k := sorry

end AlgebraicGeometry.Scheme
