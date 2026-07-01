import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField
open Module

universe u v

namespace Algebra

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Lemma 9.20.2:
- `source-facing`: the characteristic polynomial of multiplication by `α` on a finite extension
  `L/K`
- `core/canonical`: `Algebra.lmul K L α` is the primitive endomorphism, and
  `IntermediateField.adjoin.finrank` owns the simple-extension degree
- `bridge/view`: `Matrix.charpoly_leftMulMatrix` computes the simple-extension `charpoly`, while
  `Module.finrank_mul_finrank` supplies the textbook exponent

Primitive data is the pair `(Algebra.lmul K L α, minpoly K α)`. The degree formula below is
derived API, so the displayed exponent should be proved directly from the existing owner theorems
instead of being treated as an independent local wheel.
-/

/-- Helper for Lemma 9.20.2: the characteristic polynomial of a block diagonal matrix with a
constant square block `A` repeated `e` times is `A.charpoly ^ e`. -/
lemma charpoly_blockDiagonal_const {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (e : ℕ) :
    (Matrix.blockDiagonal (fun _ : Fin e => A)).charpoly = A.charpoly ^ e := by
  -- Rewrite the characteristic matrix blockwise so that the determinant factors over the blocks.
  rw [Matrix.charpoly]
  have hcharmatrix :
      (Matrix.blockDiagonal (fun _ : Fin e => A)).charmatrix =
        Matrix.blockDiagonal (fun _ : Fin e => A.charmatrix) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    by_cases h : k = k'
    · subst h
      by_cases hij : i = j
      · subst hij
        simp [Matrix.charmatrix_apply_eq, Matrix.blockDiagonal_apply_eq]
      · simp [Matrix.charmatrix_apply_ne, Matrix.blockDiagonal_apply_eq, hij]
    · simp [Matrix.charmatrix, Matrix.blockDiagonal_apply_ne, h]
  rw [hcharmatrix, Matrix.det_blockDiagonal]
  simp [Matrix.charpoly]

/-- Helper for Lemma 9.20.2: the simple-extension left-multiplication block attached to the
canonical power basis of `K⟮α⟯/K` has characteristic polynomial `minpoly K α`. -/
lemma charpoly_leftMulMatrix_adjoin_gen (α : L) (hα : IsIntegral K α) :
    let pb : PowerBasis K K⟮α⟯ := IntermediateField.adjoin.powerBasis hα
    (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = minpoly K α := by
  -- This is exactly the owner theorem for a power basis, specialized to the adjoin power basis.
  simpa [IntermediateField.minpoly_gen] using
    (charpoly_leftMulMatrix (R := K) (IntermediateField.adjoin.powerBasis hα))

/-- Lemma 9.20.2: for a finite field extension `L/K`, the characteristic polynomial of the
`K`-linear endomorphism of `L` given by multiplication by `α` is the minimal polynomial of `α`
over `K` raised to the power `[L : K(α)]`. This is the canonical Lean form of the textbook
statement that the characteristic polynomial is `P ^ e` with
`e * deg(P) = [L : K]`. -/
-- Proof sketch: choose a `K(α)`-basis of `L`, use the induced `K`-basis from `Basis.smulTower`,
-- identify the resulting matrix of `Algebra.lmul K L α` with a block diagonal matrix whose blocks
-- are the simple-extension left-multiplication matrix, and then combine
-- `charpoly_leftMulMatrix` with the tower-law exponent
-- `finrank K⟮α⟯ L * (minpoly K α).natDegree = finrank K L`.

theorem charpoly_lmul_eq_minpoly_pow_finrank_adjoin (α : L) :
    (lmul K L α).charpoly = (minpoly K α) ^ finrank K⟮α⟯ L := by
  let hα : IsIntegral K α := .of_finite K α
  let pb : PowerBasis K K⟮α⟯ := IntermediateField.adjoin.powerBasis hα
  let b : Basis (Fin (finrank K⟮α⟯ L)) K⟮α⟯ L := Module.finBasis K⟮α⟯ L
  -- Pass to the scalar-tower basis so the `K(α)`-linear structure becomes visible over `K`.
  rw [← LinearMap.charpoly_toMatrix (lmul K L α) (pb.basis.smulTower b)]
  have hmatrix :
      LinearMap.toMatrix (pb.basis.smulTower b) (pb.basis.smulTower b) (lmul K L α) =
        Matrix.blockDiagonal
          (fun _ : Fin (finrank K⟮α⟯ L) => Algebra.leftMulMatrix pb.basis pb.gen) := by
    -- Rewrite `α` as the image of the simple-extension generator and apply the tower basis lemma.
    calc
      LinearMap.toMatrix (pb.basis.smulTower b) (pb.basis.smulTower b) (lmul K L α)
          = Algebra.leftMulMatrix (pb.basis.smulTower b) α := by
              simpa using
                (Algebra.leftMulMatrix_apply (b := pb.basis.smulTower b) (R := K) (S := L)
                  α).symm
      _ = Algebra.leftMulMatrix (pb.basis.smulTower b)
            (algebraMap K⟮α⟯ L (AdjoinSimple.gen K α)) := by
            rw [IntermediateField.AdjoinSimple.algebraMap_gen]
      _ = Matrix.blockDiagonal
            (fun _ : Fin (finrank K⟮α⟯ L) =>
              Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α)) := by
            simpa [pb, b] using
              Algebra.smulTower_leftMulMatrix_algebraMap pb.basis b (AdjoinSimple.gen K α)
      _ = Matrix.blockDiagonal
            (fun _ : Fin (finrank K⟮α⟯ L) => Algebra.leftMulMatrix pb.basis pb.gen) := by
            simp [pb]
  rw [hmatrix, charpoly_blockDiagonal_const]
  -- Each block is the simple-extension companion block, whose charpoly is the minimal polynomial.
  rw [charpoly_leftMulMatrix_adjoin_gen (K := K) (L := L) α hα]

end Algebra
