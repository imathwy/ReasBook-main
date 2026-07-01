import Nesterov.Chap01.Definition_1_3_2
import Nesterov.Chap02.Definition_2_32
import Nesterov.Chap02.Proposition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace
open scoped BigOperators SeminormOperatorNorm

/- Proposition 6.15 lies in the finite-dimensional `ℓ₁`/`ℓ∞` matrix-game norm domain.

Sampled owner declarations:
* `Seminorm.primalDualOperatorNorm`, the chapter owner for induced norms between separated source
  and target seminorm geometries;
* `EuclideanSpace.l1Seminorm`, the project owner for the coordinate `ℓ₁` seminorm on `ℝⁿ`;
* `Matrix.toEuclideanLin`, the canonical Euclidean realization of a matrix action;
* `dotProduct`, the source-facing row-pairing expression for matrix rows.

Best owner abstraction:
* source-facing: the supremum of the maximal absolute row pairing over the `ℓ₁` unit ball;
* core/canonical: `Seminorm.primalDualOperatorNorm` applied to
  `((InnerProductSpace.toDual ℝ _).toLinearMap.comp A.toEuclideanLin)`;
* bridge/view: the passage from the canonical operator norm to the entrywise maximum
  `max_{i,j} |A^{(i,j)}|`.

Primitive data:
* the real matrix `A`.

Derived API:
* the row-pairing supremum formula;
* the evaluation of the canonical `ℓ₁ → ℓ∞` operator norm by the maximal absolute entry;
* the entropy-distance rewrite of the primal-dual gap estimate from the norm form to the
  max-entry form.
-/

universe u v

variable {m n : ℕ+}

local notation "EN" => EuclideanSpace ℝ (Fin (n : ℕ))
local notation "EM" => EuclideanSpace ℝ (Fin (m : ℕ))

/-- The supremum of the maximal absolute row pairing over the `ℓ₁` unit ball equals the largest
absolute entry of the matrix. -/
-- Proof sketch: for any `x` in the `ℓ₁` unit ball, each row pairing `dotProduct (A j) x` is
-- bounded by the maximal absolute entry of `A`. For the reverse inequality, use a signed
-- standard basis vector supported at a column where `A` attains that maximal absolute entry.
theorem matrix_l1_rowPairing_sSup_eq_max_abs_entry
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) :
    sSup ((fun x : EN ↦
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        Real.nnabs (dotProduct (A j) x))) ''
      {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := sorry

/-- The canonical `ℓ₁ → ℓ∞` operator norm of a real matrix is the largest absolute value of its
entries. -/
-- Proof sketch: rewrite the canonical operator norm as the source-facing supremum of the maximal
-- absolute row pairing over the `ℓ₁` unit ball, then apply
-- `matrix_l1_rowPairing_sSup_eq_max_abs_entry`.
theorem matrix_l1_to_linfty_operatorNorm_eq_max_abs_entry
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) :
    ‖(toDual ℝ EM).toLinearMap.comp A.toEuclideanLin‖[EuclideanSpace.l1Seminorm (n : ℕ) ⇀
        EuclideanSpace.l1Seminorm (m : ℕ),*] =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := sorry

/-- Proposition 6.15 [Chapter6_1.json:39]: if the entropy-distance matrix-game gap estimate is
written with the canonical `ℓ₁ → ℓ∞` operator norm of `A`, then the same estimate can be written
with the largest absolute matrix entry `max_{i,j} |A^{(i,j)}|`. -/
-- Proof sketch: keep the lower endpoint `0` unchanged and rewrite only the operator-norm factor
-- in the assumed upper bound using `matrix_l1_to_linfty_operatorNorm_eq_max_abs_entry`.
theorem matrix_game_entropy_gap_mem_Icc_max_abs_entry_bound
    {X : Type u} {U : Type v}
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ)
    (f : X → ℝ) (φ : U → ℝ) (xHat : X) (uHat : U) (N : ℕ+)
    (hnonneg : 0 ≤ f xHat - φ uHat)
    (hgap_le :
      f xHat - φ uHat ≤
        ((4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ))) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ‖(toDual ℝ EM).toLinearMap.comp A.toEuclideanLin‖[EuclideanSpace.l1Seminorm (n : ℕ) ⇀
            EuclideanSpace.l1Seminorm (m : ℕ),*]) :
    f xHat - φ uHat ∈
      Set.Icc 0
        (((4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ))) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
            (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i))) := sorry

end
