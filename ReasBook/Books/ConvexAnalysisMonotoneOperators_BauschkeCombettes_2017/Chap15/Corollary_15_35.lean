import Mathlib
import BauschkeLean.Chap15.Corollary_15_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: specialize Corollary 15.33 to the identity operator on `H`; then `U.map id = U`
-- and the adjoint of the identity is the identity, so the criterion becomes exactly the
-- equivalence between closedness of `U ⊔ V` and of `Uᗮ ⊔ Vᗮ`.
/-- Corollary 15.35: for closed linear subspaces `U` and `V` of a real Hilbert space, the sum
`U + V` is closed if and only if the sum of the orthogonal complements `Uᗮ + Vᗮ` is closed. -/
theorem isClosed_sup_iff_isClosed_orthogonal_sup_orthogonal
    (U V : Submodule ℝ H) (hU_closed : IsClosed (U : Set H)) (hV_closed : IsClosed (V : Set H)) :
    IsClosed ((U ⊔ V : Submodule ℝ H) : Set H) ↔
      IsClosed (((Uᗮ) ⊔ Vᗮ : Submodule ℝ H) : Set H) := by
  simpa using
    isClosed_map_sup_iff_isClosed_orthogonal_sup_adjoint_map_orthogonal
      U V (ContinuousLinearMap.id ℝ H) hU_closed hV_closed
