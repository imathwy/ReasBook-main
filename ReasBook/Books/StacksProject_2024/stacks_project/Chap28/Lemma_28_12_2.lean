import Mathlib
import StacksProject_2024.Chap28.Definition_28_12_1
import StacksProject_2024.Chap28.Lemma_28_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` only surfaced the general scheme-side Noetherian API, while
-- the chapter-local owner/interface for this item is already fixed by `Regular X`
-- (`Lemma_28_9_2`) and `satisfiesSerreConditionR X k` (`Definition_28_12_1`). Since the source
-- quantifies over `k ≥ 0`, the natural-number index makes the scheme statement canonically
-- `∀ k : ℕ, satisfiesSerreConditionR X k`.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 28.12.2: let `X` be a locally Noetherian scheme. Then `X` is regular if and only if `X`
has `(R_k)` for every natural number `k`. -/
@[stacks 0B3C]
theorem regular_iff_forall_satisfiesSerreConditionR :
    Regular X ↔ ∀ k : ℕ, satisfiesSerreConditionR X k := sorry

end AlgebraicGeometry.Scheme
