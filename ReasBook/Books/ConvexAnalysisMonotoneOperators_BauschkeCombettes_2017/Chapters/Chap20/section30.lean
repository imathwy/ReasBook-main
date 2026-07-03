import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_30 (from Chap20) -/
open scoped InnerProductSpace

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: an `α`-averaged self-map with `α ≤ 1 / 2` gives a monotone singleton-valued
-- operator by the canonical owner theorem from Example 20.6, and every averaged map is
-- `1`-Lipschitz, hence continuous. Apply Corollary 20.28 to the associated singleton-valued
-- operator.
/-- Example 20.30: if `T : H → H` is `α`-averaged with `α ≤ 1 / 2`, then the associated
singleton-valued set-valued operator of `T` is maximally monotone. -/
theorem toSetValuedOperator_isMaximallyMonotone_of_averaged_le_half
    {α : ℝ} {T : H → H}
    (hT : Averaged α T) (hα : α ≤ (1 / 2 : ℝ)) :
    Maximal SetValuedOperator.IsMonotone T.toSetValuedOperator := by
  have hT_mono : T.toSetValuedOperator.IsMonotone := by
    simpa [Function.toSetValuedOperator] using
      (SetValuedOperator.ofFunction_isMonotone_of_averagedWith_le_half hT hα)
  have hT_lipschitz_univ : LipschitzWith 1 (fun x : (Set.univ : Set H) ↦ T x) :=
    lipschitzWith_one_of_averagedWith hT
  have hT_lipschitz : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa using hT_lipschitz_univ.dist_le_mul ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩
  exact toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous T hT_mono
    hT_lipschitz.continuous

end Function
