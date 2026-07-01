import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap11.Definition_11_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling for Lemma 11.8.6:
- primary domain: finite-dimensional central simple algebras and their splitting criteria;
- sampled owner declarations:
  `CSA.IsSplitBy`,
  `CSA.baseChange`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `CSA.finrank_isSquare`;
- best owner abstraction: the numbered TFAE statement is `source-facing` on an arbitrary
  `k`-algebra `A`, while the canonical owner for the splitting clauses is `CSA k`;
- primitive data: for the main TFAE, only the ambient `k`-algebra structure on `A`; for the
  companion statements below, only a representative `A : CSA k`;
- derived API: the algebraic-closure, separable-closure, and finite-Galois splitting statements on
  `CSA`; the degree API belongs upstream with `CSA.finrank_isSquare` rather than in this later
  TFAE file.

Source/core/bridge triage:
- `source-facing`: `finite_central_simple_tfae`;
- `core/canonical`: `CSA k` together with `CSA.IsSplitBy`;
- `bridge/view`: the owner-level companion splitness theorems below, which package the explicit
  matrix-algebra clauses of the TFAE in the canonical `IsSplitBy` language. -/

/-- Lemma 11.8.6: for a `k`-algebra `A`, the following are equivalent: `A` is finite-dimensional,
central, and simple; it has center exactly `k` and only trivial two-sided ideals; it becomes a
matrix algebra after scalar extension to the algebraic closure or to the separable closure; it is
split by a finite Galois extension of `k`; and it is a full matrix algebra over a finite central
division `k`-algebra. -/
theorem finite_central_simple_tfae :
    List.TFAE
      [ FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
        FiniteDimensional k A ∧ Subalgebra.center k A = ⊥ ∧
          Nontrivial A ∧ ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤,
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
            Matrix (Fin n) (Fin n) (AlgebraicClosure k)),
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] SeparableClosure k) ≃ₐ[SeparableClosure k]
            Matrix (Fin n) (Fin n) (SeparableClosure k)),
        ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
          (_ : IsGalois k k') (n : ℕ),
          n ≠ 0 ∧ Nonempty ((A ⊗[k] k') ≃ₐ[k'] Matrix (Fin n) (Fin n) k'),
        ∃ (n : ℕ), n ≠ 0 ∧ ∃ (D : Type w) (_ : DivisionRing D) (_ : Algebra k D)
          (_ : FiniteDimensional k D) (_ : Algebra.IsCentral k D),
          Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) ] := sorry

end

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

/- Layer note: `finite_central_simple_tfae` is the `source-facing` statement for an arbitrary
`k`-algebra. The declarations below move to the `core/canonical` owner abstraction `CSA k` for
representative-level splitness and degree data, rather than keeping parallel ad hoc wrappers. -/

-- Proof sketch: a finite central simple algebra becomes a matrix algebra after scalar extension to
-- an algebraic closure by the splitting criterion.
/-- Companion statement: every finite central simple `k`-algebra splits over `AlgebraicClosure k`.
-/
theorem isSplitBy_algebraicClosure : A.IsSplitBy (AlgebraicClosure k) := sorry

-- Proof sketch: a finite central simple algebra splits over the separable closure because the
-- algebraic-closure splitting descends along Lemma 11.4.5.
/-- Companion statement: every finite central simple `k`-algebra splits over `SeparableClosure k`.
-/
theorem isSplitBy_separableClosure : A.IsSplitBy (SeparableClosure k) := sorry

-- Proof sketch: Proposition 11.8.5 gives a finite separable splitting field, and a finite Galois
-- closure of that field yields the Galois form.
/-- Companion statement: every finite central simple `k`-algebra admits a finite Galois splitting
field. -/
theorem exists_finite_galois_splitting_field :
    ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (_ : IsGalois k k'),
      A.IsSplitBy k' := sorry

end CSA
