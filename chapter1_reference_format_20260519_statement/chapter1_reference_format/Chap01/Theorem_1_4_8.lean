import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Submodule

universe u v w

section

variable {R : Type u} {M : Type v} [Semiring R] [StrongRankCondition R]
  [AddCommMonoid M] [Module R M]

/-- Theorem 1.4.8: if an `R`-module `M` over a semiring satisfying `StrongRankCondition` is
spanned by `n` vectors, then every linearly independent family in `M` has cardinality at most
`n`. -/
-- Proof sketch: apply `linearIndependent_le_span` to the spanning set `Set.range s`; since `s` is
-- indexed by `Fin n`, the range has cardinality at most `n`, giving the desired cardinal bound.
theorem linearIndependent_cardinal_le_of_span_eq_top
    {n : ℕ} {s : Fin n → M} (hs : span R (range s) = ⊤) {ι : Type w}
    (v : ι → M) (hv : LinearIndependent R v) :
    Cardinal.mk ι ≤ n := by
  classical
  exact (linearIndependent_le_span v hv (range s) hs).trans <| by
    simpa using (Fintype.card_range_le s : Fintype.card (range s) ≤ Fintype.card (Fin n))

/-- A finitely indexed linearly independent family in an `R`-module spanned by `n` vectors has at
most `n` elements. -/
-- Proof sketch: combine `linearIndependent_cardinal_le_of_span_eq_top` with the identification of
-- `Cardinal.mk ι` and `Fintype.card ι` for a finite index type.
theorem linearIndependent_fintype_card_le_of_span_eq_top
    {n : ℕ} {s : Fin n → M} (hs : span R (range s) = ⊤)
    {ι : Type w} [Fintype ι] (v : ι → M) (hv : LinearIndependent R v) :
    Fintype.card ι ≤ n := by
  simpa [Cardinal.mk_fintype] using
    linearIndependent_cardinal_le_of_span_eq_top hs v hv

end
