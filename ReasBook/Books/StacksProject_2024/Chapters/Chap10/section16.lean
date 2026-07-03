import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.OrzechProperty
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_16_1 (from Chap10) -/
/- Domain-style sampling for Lemma 10.16.1:
- primary domain: characteristic polynomials of square matrices and the Cayley-Hamilton theorem;
- sampled owner declarations:
  `Matrix.charpoly`,
  `Matrix.eval_charpoly`,
  `Matrix.aeval_self_charpoly`,
  `LinearMap.aeval_self_charpoly`;
- best owner abstraction: `Matrix.aeval_self_charpoly` is the canonical matrix-level owner of the
  statement that the characteristic polynomial annihilates the matrix itself;
- primitive data: a commutative ring `R`, a finite square index type `n`, and a matrix
  `A : Matrix n n R`;
- derived API: the linear-map version and the various coefficient/root consequences of the
  characteristic polynomial.

Source/core/bridge triage:
- `source-facing`: the textbook Cayley-Hamilton statement for a square matrix;
- `core/canonical`: `Matrix.aeval_self_charpoly`;
- `bridge/view`: `LinearMap.aeval_self_charpoly` after passing from a matrix to an endomorphism.

This item introduces no new mathematical data, so the refined file should recall the canonical
owner theorem directly rather than keep a duplicate local alias or restatement.
-/

/- Lemma 10.16.1: for a square matrix `A` over a ring `R`, the characteristic polynomial of `A`,
defined as `det (X • 1 - A)`, annihilates `A`. In Lean this is the canonical matrix
Cayley-Hamilton theorem `Matrix.aeval_self_charpoly`, stated over a commutative ring as required
for characteristic polynomials. -/
recall Matrix.aeval_self_charpoly

/-! ### Lemma_10_16_2 (from Chap10) -/
/- Lemma 10.16.2: let `R` be a ring, let `M` be a finite `R`-module, and let `φ : M → M` be an
endomorphism. Then there exists a monic polynomial over `R` that annihilates `φ`. This is exactly
the canonical finite-module Cayley-Hamilton theorem
`LinearMap.exists_monic_and_aeval_eq_zero`. -/
recall LinearMap.exists_monic_and_aeval_eq_zero

/-! ### Lemma_10_16_3 (from Chap10) -/
universe u v

open Polynomial

/-
Lemma 10.16.3 lives in the finite-module Cayley-Hamilton / ideal-power coefficient domain.
Its core/canonical owner is mathlib's
`LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul`; the source wording
below is a bridge/view that reindexes the coefficients into textbook order.
-/
recall LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul

namespace LinearMap

section

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

/-- Source-facing bridge for Lemma 10.16.3: reindex the canonical owner theorem into the textbook
coefficient order `aⱼ ∈ I ^ j`. -/
theorem exists_monic_and_coeff_natDegree_sub_mem_pow_and_aeval_eq_zero_of_range_le_smul
    (φ : Module.End R M) (I : Ideal R) (hI : range φ ≤ I • ⊤) :
    ∃ p : R[X], p.Monic ∧ (∀ j ≤ p.natDegree, p.coeff (p.natDegree - j) ∈ I ^ j) ∧ aeval φ p = 0 := by
  obtain ⟨p, hpM, hpC, hpA⟩ :=
    exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R φ I hI
  refine ⟨p, hpM, ?_, hpA⟩
  intro j hj
  simpa [Nat.sub_sub_self hj] using hpC (p.natDegree - j)

end

end LinearMap

/-! ### Lemma_10_16_4 (from Chap10) -/
import Mathlib.Tactic.Recall

universe u v

section

variable {R : Type u} {M : Type v} [Semiring R] [OrzechProperty R]
variable [AddCommMonoid M] [Module R M] [Module.Finite R M]

/- Lemma 10.16.4: for a commutative ring `R`, any surjective endomorphism of a finite
`R`-module is bijective. Mathlib states this canonically over any semiring satisfying
`OrzechProperty`; the Stacks-project commutative-ring case is recovered via
`CommRing.orzechProperty`. -/
recall OrzechProperty.bijective_of_surjective_endomorphism

end
