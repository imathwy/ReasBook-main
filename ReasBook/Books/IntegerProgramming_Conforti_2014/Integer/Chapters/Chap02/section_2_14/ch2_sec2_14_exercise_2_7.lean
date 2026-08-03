import Mathlib

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so this item uses
-- explicit local `Matrix`/`Finset` formulations verified against mathlib surface APIs.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A `0,1` matrix has only `0` and `1` as entries. -/
def IsZeroOneMatrix (A : Matrix m n ℤ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- The support of a row of a matrix, viewed as the set of columns where the entry is nonzero. -/
def rowSupport (A : Matrix m n ℤ) (i : m) : Finset n :=
  Finset.univ.filter fun j ↦ A i j ≠ 0

/-- The finite set of distinct row supports of a matrix. -/
def rowSupports (A : Matrix m n ℤ) : Finset (Finset n) :=
  Finset.univ.image (rowSupport A)

/-- The inclusion-maximal row supports of a matrix. -/
def maximalRowSupports (A : Matrix m n ℤ) : Finset (Finset n) :=
  (rowSupports A).filter fun s ↦
    ∀ t ∈ rowSupports A, s ⊆ t → t ⊆ s

/-- The inclusion-minimal row supports of a matrix. -/
def minimalRowSupports (A : Matrix m n ℤ) : Finset (Finset n) :=
  (rowSupports A).filter fun s ↦
    ∀ t ∈ rowSupports A, t ⊆ s → s ⊆ t

/-- The canonical `0,1` row with prescribed support. -/
def rowOfSupport (s : Finset n) : n → ℤ :=
  fun j ↦ if j ∈ s then 1 else 0

/-- The matrix whose rows are the canonical `0,1` rows with the prescribed supports. -/
def matrixOfRowSupports (S : Finset (Finset n)) : Matrix S n ℤ :=
  fun s j ↦ rowOfSupport s.1 j

/-- Multiplying a support-row matrix by a vector evaluates the corresponding subset sum. -/
theorem matrixOfRowSupports_mulVec_apply
    {R : Type*} [Ring R]
    (S : Finset (Finset n)) (x : n → R) (s : S) :
    ((((matrixOfRowSupports S : Matrix S n ℤ).map (Int.castRingHom R)) *ᵥ x) s) =
      (s : Finset n).sum x := by
  simp [Matrix.mulVec, dotProduct, matrixOfRowSupports, rowOfSupport]

/-- The row-deduplicated matrix whose rows are exactly the inclusion-maximal row supports of `A`. -/
def Amax (A : Matrix m n ℤ) : Matrix (maximalRowSupports A) n ℤ :=
  matrixOfRowSupports (maximalRowSupports A)

/-- The row-deduplicated matrix whose rows are exactly the inclusion-minimal row supports of `A`. -/
def Amin (A : Matrix m n ℤ) : Matrix (minimalRowSupports A) n ℤ :=
  matrixOfRowSupports (minimalRowSupports A)

/-- A binary vector has only `0` and `1` as entries. -/
def IsZeroOneVector (x : n → ℤ) : Prop :=
  ∀ j, x j = 0 ∨ x j = 1

/-- The `i`-th row sum of `A` against an integer vector `x`. -/
def integerRowSum (A : Matrix m n ℤ) (i : m) (x : n → ℤ) : ℤ :=
  ∑ j, A i j * x j

/-- The `i`-th row sum of `A` against a real vector `x`. -/
def realRowSum (A : Matrix m n ℤ) (i : m) (x : n → ℝ) : ℝ :=
  ∑ j, (A i j : ℝ) * x j

/-- The packing set associated to a `0,1` matrix. -/
def packingSet (A : Matrix m n ℤ) : Set (n → ℤ) :=
  {x | IsZeroOneVector x ∧ ∀ i, integerRowSum A i x ≤ 1}

/-- The covering set associated to a `0,1` matrix. -/
def coveringSet (A : Matrix m n ℤ) : Set (n → ℤ) :=
  {x | IsZeroOneVector x ∧ ∀ i, 1 ≤ integerRowSum A i x}

/-- The standard linear relaxation of the packing set associated to a `0,1` matrix. -/
def packingLinearRelaxation (A : Matrix m n ℤ) : Set (n → ℝ) :=
  {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∀ i, realRowSum A i x ≤ 1}

/-- The standard linear relaxation of the covering set associated to a `0,1` matrix. -/
def coveringLinearRelaxation (A : Matrix m n ℤ) : Set (n → ℝ) :=
  {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∀ i, 1 ≤ realRowSum A i x}

/-- Exercise 2.7 (1): removing non-maximal row supports does not change the packing set. -/
theorem packingSet_eq_Amax_packingSet (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    packingSet A = packingSet (Amax A) := sorry

/-- Exercise 2.7 (2): removing non-maximal row supports does not change the linear relaxation of the
packing set. -/
theorem packingLinearRelaxation_eq_Amax (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    packingLinearRelaxation A = packingLinearRelaxation (Amax A) := sorry

/-- Exercise 2.7 (3): removing non-minimal row supports does not change the covering set. -/
theorem coveringSet_eq_Amin_coveringSet (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    coveringSet A = coveringSet (Amin A) := sorry

/-- Exercise 2.7 (4): removing non-minimal row supports does not change the linear relaxation of the
covering set. -/
theorem coveringLinearRelaxation_eq_Amin (A : Matrix m n ℤ) (hA : IsZeroOneMatrix A) :
    coveringLinearRelaxation A = coveringLinearRelaxation (Amin A) := sorry
