import Mathlib.Tactic.Recall
import Nesterov.Chap01.Proposition_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

/- Proposition 1.4.5 lies in the finite-dimensional inner-product linear algebra domain.

Relevant owner-style declarations sampled before refining:
* `LinearMap.adjoint`, the canonical adjoint owner for linear maps on Euclidean spaces
* `LinearMap.adjoint_inner_right`, the owner adjointness identity
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the canonical matrix-to-adjoint bridge
* `matrix_transpose_adjointness` in `Nesterov/Chap01/Proposition_1_4_5.lean`, the exact
  source-facing chapter theorem already owning this proposition

Best owner abstraction:
* source-facing owner in the project: `matrix_transpose_adjointness`
* core/canonical owner: `LinearMap.adjoint`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

Primitive data:
* a real matrix `A`
* vectors `x` and `y`

Derived API:
* the source-facing transpose identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`
* its canonical proof route through `LinearMap.adjoint`

Source/core/bridge triage:
* source-facing: the textbook transpose identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`
* core/canonical: `LinearMap.adjoint`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

The exact source-facing theorem already exists in the chapter file with the right interface, so
this item is recall-only rather than a second theorem body duplicating the same owner surface. -/

/- Proposition 1.4.5: for a real `m × n` matrix, the standard Euclidean inner products on
`ℝ^n` and `ℝ^m` satisfy the adjointness identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`. -/
recall matrix_transpose_adjointness
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (A.toEuclideanLin x) y =
      inner ℝ x (Aᵀ.toEuclideanLin y)
