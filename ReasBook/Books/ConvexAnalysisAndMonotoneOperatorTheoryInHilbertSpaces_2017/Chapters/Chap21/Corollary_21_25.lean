import Mathlib
import BauschkeLean.Chap21.Corollary_21_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: Corollary 21.25 is the bounded-domain surjectivity criterion for a maximally
--   monotone set-valued operator.
-- - `core/canonical`: the Chapter 21 owner theorem is
--   `range_eq_univ_iff_inverse_isLocallyBounded`.
-- - `bridge/view`: the canonical inverse-range identity `range_inverse` identifies `(A⁻¹).range`
--   with `A.dom`, and every image of `A⁻¹` is contained in that range.

/-- Corollary 21.25: if `A : H → 2^H` is maximally monotone and has bounded domain, then `A` is
surjective, i.e. `A.range = Set.univ`. -/
theorem range_eq_univ_of_maximal_of_bounded_dom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hdom_bounded : Bornology.IsBounded A.dom) :
    A.range = Set.univ := by
  refine (range_eq_univ_iff_inverse_isLocallyBounded A hA).2 ?_
  intro u
  refine ⟨1, zero_lt_one, ?_⟩
  have hrange_bounded : Bornology.IsBounded (A⁻¹).range := by
    simpa [range_inverse] using hdom_bounded
  refine hrange_bounded.subset ?_
  intro x hx
  rcases (mem_image _ _ _).1 hx with ⟨y, -, hyx⟩
  exact (mem_range_iff _ _).2 ⟨y, hyx⟩

end SetValuedOperator
