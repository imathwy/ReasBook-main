import Nesterov.Chap06.Example_6_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin (m : ℕ))
local notation "G" => Fin (m : ℕ) ⊕ Fin (m : ℕ)

/- Proposition 6.20 lies in the finite max-type / simplex-duality domain.

Sampled owner-style declarations:
- `Matrix.fromRows` and `Matrix.fromRows_mulVec`, the canonical signed row stack;
- `piecewiseLinearObjective` and `piecewiseLinearObjective_eq_simplexSup` in `Example_6_1_1`, the
  project owner for a finite maximum of affine functionals and its simplex representation;
- `StdSimplex`, the canonical simplex owner used by that representation theorem.

Best owner abstraction:
- source-facing: Proposition 6.20's absolute row-maximum written through a signed row family;
- core/canonical: `piecewiseLinearObjective` specialized to `Matrix.fromRows A (-A)`;
- bridge/view: the duplicated offset `Sum.elim b b` on the signed row index.

Primitive data:
- the row matrix `A`;
- the offset vector `b`;
- the evaluation point `x`.

Derived API:
- the signed row family `Matrix.fromRows A (-A)`;
- the signed offset `Sum.elim b b`;
- the simplex-supremum representation.

Source/core/bridge triage:
- source-facing: `max_abs_row_pairing_sub_offset_eq_sSup_signed_simplex`;
- core/canonical: `piecewiseLinearObjective_eq_simplexSup`;
- bridge/view: the signed-row specialization connecting the absolute-value formula to that owner.

The previous file introduced local wrapper names for the stacked matrix and its evaluation, even
though the owner-level row stack already exists canonically as `Matrix.fromRows`, and the simplex
representation already exists canonically as `piecewiseLinearObjective_eq_simplexSup`. This
refinement deletes that duplicate layer and states Proposition 6.20 directly on the canonical
signed-row/simplex surface.
-/

/-- Proposition 6.20: stacking `A` and `-A` and duplicating `b` identifies
`max_j (|⟪a_j, x⟫| - b_j)` with the supremum of the corresponding affine functional over the
standard simplex on the signed row index set. -/
theorem max_abs_row_pairing_sub_offset_eq_sSup_signed_simplex
    (A : Matrix (Fin (m : ℕ)) (Fin n) ℝ) (b : F) (x : E) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ |dotProduct (A j) x| - b j) =
      sSup (Set.range fun u : StdSimplex ℝ G ↦
        dotProduct ((Matrix.fromRows A (-A)).mulVec x) u.weights -
          dotProduct (Sum.elim b b) u.weights) := sorry

end
