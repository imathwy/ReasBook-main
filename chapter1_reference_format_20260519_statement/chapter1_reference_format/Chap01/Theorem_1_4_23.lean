import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Theorem 1.4.23: the source's finite-dimensional vector-space statement is the field special
case of the canonical basis-cardinality theorem `mk_eq_mk_of_basis'`; the finite-dimensionality
hypothesis is redundant once two bases are given. -/
recall mk_eq_mk_of_basis' {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
  {ι : Type w} [InvariantBasisNumber R] {ι' : Type w} (b : Module.Basis ι R M)
  (b' : Module.Basis ι' R M) :
  Cardinal.mk ι = Cardinal.mk ι'

section

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
  [InvariantBasisNumber R] {ι ι' : Type w} [Fintype ι] [Fintype ι']

/-- In particular, two finitely indexed bases of the same module have the same number of
elements. -/
theorem basis_fintype_card_eq (b : Module.Basis ι R M) (b' : Module.Basis ι' R M) :
    Fintype.card ι = Fintype.card ι' := by
  simpa [Cardinal.mk_fintype] using mk_eq_mk_of_basis' b b'

end
