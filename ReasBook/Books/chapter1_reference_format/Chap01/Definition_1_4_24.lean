import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Definition 1.4.24: for a finite-dimensional `K`-vector space, its dimension is the canonical
natural number `Module.finrank K V`; by the preceding uniqueness-of-basis-cardinality result, this
is the number of vectors in any basis. -/
recall Module.finrank (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ

/- For any finitely indexed basis, `Module.finrank R M` is the number of basis vectors. In the
finite-dimensional `K`-vector-space setting of the source, every basis has this form. -/
recall Module.finrank_eq_card_basis {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M]
  [Module R M] [StrongRankCondition R] {ι : Type w} [Fintype ι] (b : Module.Basis ι R M) :
  Module.finrank R M = Fintype.card ι
