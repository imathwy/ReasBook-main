import stacks_proof.stacks_project.Chap10.Lemma_10_107_11
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Matrix

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Domain-style sampling for this item:
-- - primary domain: commutative algebra of tensor-product equalizer criteria, expressed through
--   finite matrix witnesses over the base ring;
-- - sampled owner API: `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression`,
--   `replicateRow`, `replicateCol`, and the canonical vector/matrix operations `ᵥ*`, `*ᵥ`, `⬝ᵥ`;
-- - `source-facing`: the associated matrix triple `(P, U, V)` from the remark;
-- - `core/canonical`: Lemma `10.107.11`, which packages the same tensor relation by a finite
--   matrix expression;
-- - `bridge/view`: row and column vectors realized canonically as `replicateRow` and
--   `replicateCol`.

/-- Remark 10.107.12: an `n`-triple `(P, U, V)` is associated to `g` if there are a row vector
`Y` and a column vector `Z` over `S` such that `g = Y P Z`, `U = Y P`, and `V = P Z`, with `P`
defined over `R` and `U`, `V` landing in the image of `R`. -/
@[stacks 04VZ]
def is_associated_matrix_triple (g : S) (n : ℕ) (P : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin 1) (Fin n) R) (V : Matrix (Fin n) (Fin 1) R) : Prop :=
  ∃ y z : Fin n → S,
    g = y ᵥ* P.map (algebraMap R S) ⬝ᵥ z ∧
      U.map (algebraMap R S) = replicateRow (Fin 1) (y ᵥ* P.map (algebraMap R S)) ∧
      V.map (algebraMap R S) = replicateCol (Fin 1) (P.map (algebraMap R S) *ᵥ z)

/-- If `g` lies in the epicenter, then some finite matrix triple is associated to `g`. -/
-- Proof sketch: apply
-- `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression` to obtain coefficient data
-- `x`, `y`, `z`. Package `x` as the matrix `P`, package `y` and `z` as matrices `Y` and `Z`,
-- and choose `U` and `V` from the row-sum and column-sum image conditions.
theorem exists_associated_matrix_triple_of_tmul_one_eq_one_tmul (g : S)
    (hg : g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g) :
    ∃ n : ℕ,
      ∃ P : Matrix (Fin n) (Fin n) R,
        ∃ U : Matrix (Fin 1) (Fin n) R,
          ∃ V : Matrix (Fin n) (Fin 1) R,
            is_associated_matrix_triple g n P U V := by
  classical
  rcases (tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression g).1 hg with
    ⟨n, y, z, P, hgP, hy, hz⟩
  let u : Fin n → R := fun j ↦ Classical.choose (hy j)
  let v : Fin n → R := fun i ↦ Classical.choose (hz i)
  refine ⟨n, P, replicateRow (Fin 1) u, replicateCol (Fin 1) v, ?_⟩
  refine ⟨y, z, hgP, ?_, ?_⟩
  · ext i j
    simp [u, Classical.choose_spec (hy j)]
  · ext i j
    simp [v, Classical.choose_spec (hz i)]

end
