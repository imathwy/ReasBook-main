import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
