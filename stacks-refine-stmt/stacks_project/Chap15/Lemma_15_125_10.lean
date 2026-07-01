import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Bezout

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain-style sampling:
- primary domain: unimodular rows over Bézout domains and their completion to invertible matrices;
- sampled owner declarations:
  `IsBezout`,
  `span_range_eq_top_iff_surjective_fintypeLinearCombination`,
  `Matrix.GL`;
- best owner abstraction: `Matrix.GL (Fin (n + 1)) R` for the completion object, with
  `Fintype.linearCombination R f` as the canonical core map behind the unit-ideal hypothesis;
- primitive data: a finite row `f : Fin (n + 1) → R`;
- derived API: the condition that `f` generates the unit ideal and the resulting invertible
  completion with first row `f`, indexed canonically by `0`, together with the operational
  surjective-`linearCombination` bridge;
- source/core/bridge triage:
  `source-facing`: completion of a unimodular row to an invertible square matrix;
  `core/canonical`: `Matrix.GL (Fin (n + 1)) R` and `Fintype.linearCombination R f`;
  `bridge/view`: `Ideal.span (Set.range f) = ⊤`, via
  `span_range_eq_top_iff_surjective_fintypeLinearCombination`. -/

section

open Matrix

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]

-- Proof sketch: argue by induction on `n`. For `n = 1`, the hypothesis that `f 0` generates the
-- unit ideal says `f 0` is a unit, so the `1 × 1` matrix `[f 0]` is invertible. For `n > 1`,
-- replace the first `n - 1` entries by a single generator of their ideal using the Bézout
-- property, apply the induction hypothesis to complete that shorter row, and then compose with a
-- `2 × 2` unimodular block sending `(f, fₙ)` to a row generating `1`.
/-- Lemma 15.125.10: over a Bézout domain, any finite row generating the unit ideal is the first
row of an invertible square matrix. -/
theorem exists_invertible_matrix_first_row_eq_of_span_range_eq_top
    {n : ℕ} (f : Fin (n + 1) → R) (hunit : Ideal.span (Set.range f) = ⊤) :
    ∃ A : GL (Fin (n + 1)) R, A 0 = f := sorry

/-- Canonical `Fintype.linearCombination` bridge view of
`exists_invertible_matrix_first_row_eq_of_span_range_eq_top`. -/
theorem exists_invertible_matrix_first_row_eq_of_surjective_fintypeLinearCombination
    {n : ℕ} (f : Fin (n + 1) → R)
    (hsurj : Function.Surjective (Fintype.linearCombination R f)) :
    ∃ A : GL (Fin (n + 1)) R, A 0 = f := by
  apply exists_invertible_matrix_first_row_eq_of_span_range_eq_top
  simpa using (span_range_eq_top_iff_surjective_fintypeLinearCombination R f).2 hsurj

end
