import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Domain-style sampling for this item:
-- - primary domain: commutative algebra of tensor-product equalizer criteria, expressed through
--   finite matrices over the base ring;
-- - `source-facing`: a finite matrix witness for the relation `g ⊗ 1 = 1 ⊗ g`;
-- - `core/canonical`: the tensor-product owner API from Lemma `10.107.10`, organized around
--   `TensorProduct.VanishesTrivially`;
-- - `bridge/view`: the standard `Matrix`, `Matrix.map`, `ᵥ*`, `*ᵥ`, and `⬝ᵥ` operations rather
--   than an ad hoc `Fin`-indexed matrix encoding.

/-- A finite matrix expression for `g` whose row sums and column sums come from the image of
`R` in `S`. -/
structure IsFiniteMatrixExpression (g : S) (n : ℕ) (y z : Fin n → S)
    (P : Matrix (Fin n) (Fin n) R) : Prop where
  /-- The matrix expression evaluates to `g`. -/
  eq_repr :
    g = dotProduct (Matrix.vecMul y (P.map (algebraMap R S))) z
  /-- Each row sum lies in the image of `R` in `S`. -/
  row_mem_range :
    ∀ j : Fin n,
      Matrix.vecMul y (P.map (algebraMap R S)) j ∈ Set.range (algebraMap R S)
  /-- Each column sum lies in the image of `R` in `S`. -/
  col_mem_range :
    ∀ i : Fin n,
      Matrix.mulVec (P.map (algebraMap R S)) z i ∈ Set.range (algebraMap R S)

-- Proof sketch: for the forward implication, choose an `R`-module generating family of `S`
-- containing `1` and `g`, apply Lemma `10.107.10` to the tensor relation
-- `g ⊗ₜ[R] 1 - 1 ⊗ₜ[R] g = 0`, and rewrite the resulting coefficient data into the stated matrix
-- form. For the reverse implication, expand the displayed sum in `S ⊗[R] S` and use the
-- assumptions that each row sum and column sum lies in the image of `algebraMap R S` to move the
-- scalar coefficients across the tensor factors.
/-- Lemma 10.107.11: for an element `g : S`, the tensor relation `g ⊗ 1 = 1 ⊗ g` in `S ⊗[R] S`
is equivalent to the existence of a finite matrix expression
`g = ∑ i, ∑ j, φ(x i j) y i z j` whose row sums and column sums lie in the image of `R` in `S`. -/
theorem tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression (g : S) :
    g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g ↔
      ∃ n : ℕ,
        ∃ y z : Fin n → S,
          ∃ P : Matrix (Fin n) (Fin n) R,
            IsFiniteMatrixExpression g n y z P := sorry

end
