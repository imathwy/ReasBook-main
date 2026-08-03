module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.ZMod

public section

namespace InvarianceOfDomainSupport

-- Route correction: expose the finite dual-incidence calculation first, instead of
-- hiding the full Alexander-duality construction behind one paired topological theorem.

/-- Helper for Theorem 62.1: a square-zero finite matrix complex is exact in its
middle term exactly when the ranks of its two differentials fill that term. -/
lemma matrixExact_iff_rank_add_rank_eq_card
    {R I J K : Type*} [Field R] [Fintype I] [Fintype J]
    (d₀ : Matrix J I R) (d₁ : Matrix K J R) (hSquare : d₁ * d₀ = 0) :
    Function.Exact d₀.mulVecLin d₁.mulVecLin ↔
      d₀.rank + d₁.rank = Fintype.card J := by
  constructor
  · intro hExact
    -- Exactness replaces the first range by the second kernel, so rank-nullity closes.
    rw [Matrix.rank, Matrix.rank, ← hExact.linearMap_ker_eq, add_comm,
      LinearMap.finrank_range_add_finrank_ker,
      Module.finrank_fintype_fun_eq_card]
  · intro hRank
    -- Square-zero gives range containment; the rank equality upgrades it to equality.
    rw [LinearMap.exact_iff]
    apply Eq.symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, hSquare,
        Matrix.mulVecLin_zero]
    · have hNullity := LinearMap.finrank_range_add_finrank_ker d₁.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at hNullity
      have hDimensions := hRank.trans hNullity.symm
      rw [add_comm d₀.rank d₁.rank] at hDimensions
      simpa only [Matrix.rank] using Nat.add_left_cancel hDimensions

/-- Helper for Theorem 62.1: exactness of a finite three-term matrix complex is
preserved when both differentials are transposed and their order is reversed. -/
lemma matrixExact_iff_transposeExact
    {R I J K : Type*} [Field R] [Fintype I] [Fintype J] [Fintype K]
    (d₀ : Matrix J I R) (d₁ : Matrix K J R) (hSquare : d₁ * d₀ = 0) :
    Function.Exact d₀.mulVecLin d₁.mulVecLin ↔
      Function.Exact d₁.transpose.mulVecLin d₀.transpose.mulVecLin := by
  have hTransposeSquare : d₀.transpose * d₁.transpose = 0 := by
    -- Transposition reverses the zero product.
    rw [← Matrix.transpose_mul, hSquare, Matrix.transpose_zero]
  -- Both exactness assertions are the same rank-sum equality.
  rw [matrixExact_iff_rank_add_rank_eq_card d₀ d₁ hSquare,
    matrixExact_iff_rank_add_rank_eq_card d₁.transpose d₀.transpose
      hTransposeSquare,
    Matrix.rank_transpose, Matrix.rank_transpose, add_comm]

/-- Helper for Theorem 62.1: reindexing the transpose of a finite incidence matrix
along degree-reversing cell correspondences gives its dual incidence matrix. -/
def dualIncidenceMatrix {R low high dualLow dualHigh : Type*}
    (boundary : Matrix low high R) (lowDual : low ≃ dualHigh)
    (highDual : high ≃ dualLow) : Matrix dualLow dualHigh R :=
  Matrix.reindex highDual lowDual boundary.transpose

/-- Helper for Theorem 62.1: corresponding primal and dual cells have the same
incidence coefficient in the dual incidence matrix. -/
lemma dualIncidenceMatrix_apply {R low high dualLow dualHigh : Type*}
    (boundary : Matrix low high R) (lowDual : low ≃ dualHigh)
    (highDual : high ≃ dualLow) (i : high) (j : low) :
    dualIncidenceMatrix boundary lowDual highDual (highDual i) (lowDual j) =
      boundary j i := by
  -- Reindexing returns the original cells, and transposition reverses their order.
  simp only [dualIncidenceMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.transpose_apply, Equiv.symm_apply_apply]

/-- Helper for Theorem 62.1: under the dual-cell reindexing, multiplication of
incidence matrices is carried to multiplication in the reversed order. -/
lemma dualIncidenceMatrix_mul {R low middle high dualLow dualMiddle dualHigh : Type*}
    [CommSemiring R] [Fintype middle] [Fintype dualMiddle]
    (lowerBoundary : Matrix low middle R) (upperBoundary : Matrix middle high R)
    (lowDual : low ≃ dualHigh) (middleDual : middle ≃ dualMiddle)
    (highDual : high ≃ dualLow) :
    dualIncidenceMatrix upperBoundary middleDual highDual *
        dualIncidenceMatrix lowerBoundary lowDual middleDual =
      dualIncidenceMatrix (lowerBoundary * upperBoundary) lowDual highDual := by
  -- Matrix reindexing respects products, while transposition reverses their order.
  simpa only [dualIncidenceMatrix, Matrix.coe_reindexLinearEquiv,
    Matrix.transpose_mul] using
    (Matrix.reindexLinearEquiv_mul R R highDual middleDual lowDual
      upperBoundary.transpose lowerBoundary.transpose)

/-- Helper for Theorem 62.1: a pair of consecutive finite boundary matrices that
composes to zero yields a degree-reversed dual pair that also composes to zero. -/
lemma dualIncidenceMatrix_mul_eq_zero
    {R low middle high dualLow dualMiddle dualHigh : Type*}
    [CommSemiring R] [Fintype middle] [Fintype dualMiddle]
    (lowerBoundary : Matrix low middle R) (upperBoundary : Matrix middle high R)
    (lowDual : low ≃ dualHigh) (middleDual : middle ≃ dualMiddle)
    (highDual : high ≃ dualLow) (hBoundary : lowerBoundary * upperBoundary = 0) :
    dualIncidenceMatrix upperBoundary middleDual highDual *
        dualIncidenceMatrix lowerBoundary lowDual middleDual = 0 := by
  -- First reverse the incidence product, then use the primal boundary-square relation.
  rw [dualIncidenceMatrix_mul, hBoundary]
  rfl

/-- Helper for Theorem 62.1: on finite coefficient vectors, the dual incidence
boundary is the transposed primal boundary conjugated by the two cell reindexings. -/
lemma dualIncidenceMatrix_mulVecLin {R low high dualLow dualHigh : Type*}
    [CommSemiring R] [Fintype low] [Fintype dualHigh]
    (boundary : Matrix low high R) (lowDual : low ≃ dualHigh)
    (highDual : high ≃ dualLow) :
    (dualIncidenceMatrix boundary lowDual highDual).mulVecLin =
      (LinearEquiv.funCongrLeft R R highDual.symm).toLinearMap ∘ₗ
        boundary.transpose.mulVecLin ∘ₗ
          (LinearEquiv.funCongrLeft R R lowDual).toLinearMap := by
  -- Apply the canonical linear-map formula for a reindexed matrix.
  simpa only [dualIncidenceMatrix] using
    (Matrix.mulVecLin_reindex highDual lowDual boundary.transpose)

/-- Helper for Theorem 62.1: degree-reversing cell equivalences transport
exactness of a finite matrix complex to exactness of its dual incidence complex. -/
lemma dualIncidenceMatrix_exact_iff
    {R low middle high dualLow dualMiddle dualHigh : Type*}
    [Field R] [Fintype low] [Fintype middle] [Fintype high]
    [Fintype dualLow] [Fintype dualMiddle] [Fintype dualHigh]
    (lower : Matrix middle low R) (upper : Matrix high middle R)
    (lowDual : low ≃ dualHigh) (middleDual : middle ≃ dualMiddle)
    (highDual : high ≃ dualLow) (hSquare : upper * lower = 0) :
    Function.Exact lower.mulVecLin upper.mulVecLin ↔
      Function.Exact
        (dualIncidenceMatrix upper highDual middleDual).mulVecLin
        (dualIncidenceMatrix lower middleDual lowDual).mulVecLin := by
  have hReindex :
      Function.Exact
          (dualIncidenceMatrix upper highDual middleDual).mulVecLin
          (dualIncidenceMatrix lower middleDual lowDual).mulVecLin ↔
        Function.Exact upper.transpose.mulVecLin lower.transpose.mulVecLin := by
    -- Normalize both dual maps to transposes conjugated by function reindexings.
    rw [dualIncidenceMatrix_mulVecLin, dualIncidenceMatrix_mulVecLin]
    rw [← LinearMap.comp_assoc,
      LinearEquiv.precomp_exact_iff_exact,
      LinearEquiv.postcomp_exact_iff_exact]
    simpa only [LinearEquiv.funCongrLeft_symm, Equiv.symm_symm] using
      LinearEquiv.conj_exact_iff_exact upper.transpose.mulVecLin
        lower.transpose.mulVecLin (LinearEquiv.funCongrLeft R R middleDual.symm)
  -- Transposition handles the algebra; the preceding equivalence handles cell names.
  exact (matrixExact_iff_transposeExact lower upper hSquare).trans hReindex.symm

/-- Helper for Theorem 62.1: the mod-two specialization of finite dual-incidence
exactness used by relative cell models. -/
lemma dualIncidenceMatrix_exact_iff_modTwo
    {low middle high dualLow dualMiddle dualHigh : Type*}
    [fintypeLow : Fintype low] [fintypeMiddle : Fintype middle]
    [fintypeHigh : Fintype high] [fintypeDualLow : Fintype dualLow]
    [fintypeDualMiddle : Fintype dualMiddle]
    [fintypeDualHigh : Fintype dualHigh]
    (lower : Matrix middle low (ZMod 2)) (upper : Matrix high middle (ZMod 2))
    (lowDual : low ≃ dualHigh) (middleDual : middle ≃ dualMiddle)
    (highDual : high ≃ dualLow) (hSquare : upper * lower = 0) :
    Function.Exact lower.mulVecLin upper.mulVecLin ↔
      Function.Exact
        (dualIncidenceMatrix upper highDual middleDual).mulVecLin
        (dualIncidenceMatrix lower middleDual lowDual).mulVecLin := by
  -- Discharge the coefficient-field specialization once at the construction owner.
  exact @dualIncidenceMatrix_exact_iff (ZMod 2) low middle high dualLow dualMiddle
    dualHigh inferInstance fintypeLow fintypeMiddle fintypeHigh fintypeDualLow
    fintypeDualMiddle fintypeDualHigh lower upper lowDual middleDual highDual hSquare

end InvarianceOfDomainSupport

end
