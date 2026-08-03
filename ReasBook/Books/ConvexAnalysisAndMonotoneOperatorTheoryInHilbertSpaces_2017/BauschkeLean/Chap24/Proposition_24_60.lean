import Mathlib.Analysis.Matrix.Spectrum
import BauschkeLean.Chap02.Example_2_4
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap24.CoordinatePermutationInvariant
import BauschkeLean.Chap24.Fact_24_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped InnerProductSpace

/-- The ambient real Euclidean space of `N × N` matrices, identified with `ℝ^(N×N)`. -/
abbrev SquareMatrixSpace (N : ℕ) : Type := EuclideanSpace ℝ (Fin N × Fin N)

/-- The Euclidean vectorization of a real `N × N` matrix. -/
abbrev matrixToEuclidean {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    SquareMatrixSpace N :=
  (EuclideanSpace.equiv (Fin N × Fin N) ℝ).symm (fun p ↦ A p.1 p.2)

/-- The matrix represented by a vector in the Euclidean coordinate model `ℝ^(N×N)`. -/
abbrev euclideanToMatrix {N : ℕ} (x : SquareMatrixSpace N) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ (EuclideanSpace.equiv (Fin N × Fin N) ℝ x) (i, j)

/-- The source symmetric-matrix locus inside the ambient Euclidean model `SquareMatrixSpace N`. -/
def symmetricMatrixLocus (N : ℕ) : Set (SquareMatrixSpace N) :=
  {x | (euclideanToMatrix x).IsHermitian}

@[simp] theorem mem_symmetricMatrixLocus_iff {N : ℕ} {x : SquareMatrixSpace N} :
    x ∈ symmetricMatrixLocus N ↔ (euclideanToMatrix x).IsHermitian :=
  Iff.rfl

@[simp] theorem matrixToEuclidean_apply {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (p : Fin N × Fin N) :
    matrixToEuclidean A p = A p.1 p.2 := by
  simp [matrixToEuclidean]

@[simp] theorem euclideanToMatrix_apply {N : ℕ} (x : SquareMatrixSpace N)
    (i j : Fin N) :
    euclideanToMatrix x i j = x (i, j) := by
  simp [euclideanToMatrix]

@[simp] theorem euclideanToMatrix_matrixToEuclidean {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) :
    euclideanToMatrix (matrixToEuclidean A) = A := by
  ext i j
  simp

@[simp] theorem matrixToEuclidean_euclideanToMatrix {N : ℕ}
    (x : SquareMatrixSpace N) :
    matrixToEuclidean (euclideanToMatrix x) = x := by
  apply (EuclideanSpace.equiv (Fin N × Fin N) ℝ).injective
  funext p
  simp

/-- The canonical decreasing eigenvalue list of a real symmetric matrix, viewed in
`EuclideanSpace ℝ (Fin N)`. -/
abbrev symmetricMatrixEigenvalues {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm hA.eigenvalues

@[simp] theorem symmetricMatrixEigenvalues_apply {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (i : Fin N) :
    symmetricMatrixEigenvalues hA i = hA.eigenvalues i := by
  simp [symmetricMatrixEigenvalues]

/-- The pullback of `φ` along the canonical eigenvalue map on symmetric matrices, extended by
`⊤` outside the symmetric locus of the ambient Euclidean matrix model. -/
def symmetricMatrixSpectralPullback {N : ℕ}
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)) :
    SquareMatrixSpace N → EReal :=
  fun x ↦
    let A := euclideanToMatrix x
    if hA : A.IsHermitian then φ (symmetricMatrixEigenvalues hA) else ⊤

@[simp] theorem symmetricMatrixSpectralPullback_apply_of_isHermitian {N : ℕ}
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)) {x : SquareMatrixSpace N}
    (hx : (euclideanToMatrix x).IsHermitian) :
    symmetricMatrixSpectralPullback φ x = φ (symmetricMatrixEigenvalues hx) := by
  simp [symmetricMatrixSpectralPullback, hx]

@[simp] theorem symmetricMatrixSpectralPullback_apply_of_not_isHermitian {N : ℕ}
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)) {x : SquareMatrixSpace N}
    (hx : ¬(euclideanToMatrix x).IsHermitian) :
    symmetricMatrixSpectralPullback φ x = ⊤ := by
  simp [symmetricMatrixSpectralPullback, hx]

@[simp] theorem symmetricMatrixSpectralPullback_matrixToEuclidean_apply {N : ℕ}
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    symmetricMatrixSpectralPullback φ (matrixToEuclidean A) =
      φ (symmetricMatrixEigenvalues hA) := by
  let x : SquareMatrixSpace N := matrixToEuclidean A
  have hx : (euclideanToMatrix x).IsHermitian := by
    simpa [x] using hA
  simpa [x] using symmetricMatrixSpectralPullback_apply_of_isHermitian φ hx

-- Semantic recall/local precedent: `lean_leansearch` did not surface a ready-made spectral
-- conjugacy theorem, so this item uses a local coordinate-permutation invariance predicate on
-- `EuclideanSpace ℝ (Fin N)` and Mathlib's canonical matrix owner `Matrix.IsHermitian.eigenvalues`.

/-- Helper for Proposition 24.60: the Chapter 2 nonincreasing rearrangement transported to
`EuclideanSpace ℝ (Fin N)`. -/
private noncomputable abbrev euclideanNonincreasingRearrangement {N : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm <|
    nonincreasingRearrangement ((EuclideanSpace.equiv (Fin N) ℝ) x)

/-- Helper for Proposition 24.60: the transported nonincreasing rearrangement is coordinatewise
the Chapter 2 rearrangement. -/
private theorem euclideanNonincreasingRearrangement_eq
    {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    (euclideanNonincreasingRearrangement x : Fin N → ℝ) =
      nonincreasingRearrangement ((EuclideanSpace.equiv (Fin N) ℝ) x) := by
  -- This is the defining coordinate description of the transported rearrangement.
  rfl

/-- Helper for Proposition 24.60: every Euclidean vector can be permuted to its sorted
nonincreasing rearrangement. -/
private theorem exists_permuteCoordVec_eq_nonincreasingRearrangement
    {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    ∃ σ : Equiv.Perm (Fin N),
      permuteCoordVec σ x = euclideanNonincreasingRearrangement x := by
  -- Choose the sorting permutation from the Chapter 2 rearrangement owner.
  refine ⟨(Tuple.sort (OrderDual.toDual ∘ ((EuclideanSpace.equiv (Fin N) ℝ) x))).symm, ?_⟩
  ext i
  simp [permuteCoordVec, euclideanNonincreasingRearrangement, nonincreasingRearrangement]

/-- Helper for Proposition 24.60: a coordinate-permutation invariant function has the same value
at `x` and at its nonincreasing rearrangement. -/
private theorem coordinatePermutationInvariant_eq_nonincreasingRearrangement
    {N : ℕ} {α : Type*} {φ : EuclideanSpace ℝ (Fin N) → α}
    (hφ : CoordinatePermutationInvariant φ) (x : EuclideanSpace ℝ (Fin N)) :
    φ (euclideanNonincreasingRearrangement x) = φ x := by
  -- Apply the symmetry hypothesis to a permutation that sorts `x`.
  obtain ⟨σ, hσ⟩ := exists_permuteCoordVec_eq_nonincreasingRearrangement x
  rw [← hσ]
  exact hφ σ x

/-- Helper for Proposition 24.60: the Euclidean inner product is the coordinate dot product. -/
private theorem euclidean_inner_eq_dotProduct
    {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) :
    ⟪x, y⟫_ℝ =
      dotProduct ((EuclideanSpace.equiv (Fin N) ℝ) x)
        ((EuclideanSpace.equiv (Fin N) ℝ) y) := by
  -- The canonical Euclidean model already identifies its inner product with the coordinate dot
  -- product.
  simpa [EuclideanSpace.equiv, dotProduct_comm] using EuclideanSpace.inner_eq_star_dotProduct x y

/-- Helper for Proposition 24.60: sorting both Euclidean vectors cannot decrease their inner
product. -/
private theorem inner_le_inner_nonincreasingRearrangement
    {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) :
    ⟪x, y⟫_ℝ ≤
      ⟪euclideanNonincreasingRearrangement x,
        euclideanNonincreasingRearrangement y⟫_ℝ := by
  let xCoords : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) x
  let yCoords : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) y
  -- This is exactly the Hardy-Littlewood-Polya inequality in Euclidean coordinates.
  rw [euclidean_inner_eq_dotProduct, euclidean_inner_eq_dotProduct]
  simpa [xCoords, yCoords, euclideanNonincreasingRearrangement_eq] using
    (hardy_littlewood_polya_inequality :
      dotProduct xCoords yCoords ≤
        dotProduct (nonincreasingRearrangement xCoords)
          (nonincreasingRearrangement yCoords))

/-- Helper for Proposition 24.60: an antitone finite real vector is already its own canonical
nonincreasing rearrangement. -/
private theorem nonincreasingRearrangement_eq_self_of_antitone
    {N : ℕ} {x : Fin N → ℝ} (hx : Antitone x) :
    nonincreasingRearrangement x = x := by
  -- The sorted tuple is the unique antitone permutation of `x`.
  simpa [nonincreasingRearrangement, Function.comp] using
    (Tuple.unique_antitone
      (f := x)
      (σ := Tuple.sort (OrderDual.toDual ∘ x))
      (τ := Equiv.refl (Fin N))
      (by
        simpa [nonincreasingRearrangement, Function.comp_assoc] using
          (antitone_nonincreasingRearrangement (x := x)))
      (by simpa [Function.comp] using hx))

/-- Helper for Proposition 24.60: an antitone Euclidean vector is fixed by
`euclideanNonincreasingRearrangement`. -/
private theorem euclideanNonincreasingRearrangement_eq_self_of_antitone
    {N : ℕ} {x : EuclideanSpace ℝ (Fin N)}
    (hx : Antitone ((EuclideanSpace.equiv (Fin N) ℝ) x)) :
    euclideanNonincreasingRearrangement x = x := by
  -- Reduce to the coordinate statement and use uniqueness of the sorted antitone tuple.
  ext i
  simp [euclideanNonincreasingRearrangement_eq,
    nonincreasingRearrangement_eq_self_of_antitone hx]

/-- Helper for Proposition 24.60: the Euclidean coordinate function of
`symmetricMatrixEigenvalues hA` is the public `eigenvalues` function. -/
private theorem symmetricMatrixEigenvalues_coords_eq_eigenvalues
    {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    (EuclideanSpace.equiv (Fin N) ℝ) (symmetricMatrixEigenvalues hA) =
      hA.eigenvalues := by
  -- This is the defining coordinate description of the Euclidean eigenvalue vector.
  funext i
  simp [symmetricMatrixEigenvalues]

/-- Helper for Proposition 24.60: for a Hermitian left factor, the Euclidean matrix pairing is the
trace pairing `trace (A * B)`. -/
private theorem matrixToEuclidean_inner_eq_trace_mul_of_isHermitian
    {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℝ) :
    ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ = Matrix.trace (A * B) := by
  have hAT : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  -- Rewrite the Euclidean inner product as the coordinate dot product on `Fin N × Fin N`.
  calc
    ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ
        = dotProduct
            ((EuclideanSpace.equiv (Fin N × Fin N) ℝ) (matrixToEuclidean A))
            ((EuclideanSpace.equiv (Fin N × Fin N) ℝ) (matrixToEuclidean B)) := by
            simpa [EuclideanSpace.equiv, dotProduct_comm] using
              (EuclideanSpace.inner_eq_star_dotProduct
                (matrixToEuclidean A) (matrixToEuclidean B))
    _ = Matrix.trace (Aᵀ * B) := by
          calc
            dotProduct
                ((EuclideanSpace.equiv (Fin N × Fin N) ℝ) (matrixToEuclidean A))
                ((EuclideanSpace.equiv (Fin N × Fin N) ℝ) (matrixToEuclidean B))
                = ∑ p : Fin N × Fin N, A p.1 p.2 * B p.1 p.2 := by
                    simp [dotProduct, matrixToEuclidean]
            _ = ∑ i, ∑ j, A i j * B i j := by
                  rw [← Finset.univ_product_univ, Finset.sum_product]
            _ = ∑ j, ∑ i, A i j * B i j := by rw [Finset.sum_comm]
            _ = Matrix.trace (Aᵀ * B) := by
                  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = Matrix.trace (A * B) := by rw [hAT]

/-- Helper for Proposition 24.60: orthogonal conjugates of real diagonal matrices are Hermitian. -/
private theorem orthogonalDiagonal_isHermitian
    {N : ℕ} (U : Matrix.orthogonalGroup (Fin N) ℝ) (a : Fin N → ℝ) :
    ((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) : Matrix (Fin N) (Fin N) ℝ).IsHermitian := by
  -- Hermitianity is preserved under `B * A * Bᵀ`, and a real diagonal matrix is Hermitian.
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
    (Matrix.isHermitian_mul_mul_conjTranspose
      (B := (U : Matrix (Fin N) (Fin N) ℝ))
      (A := Matrix.diagonal a)
      (Matrix.isHermitian_diagonal a))

/-- Helper for Proposition 24.60: orthogonal conjugation preserves the characteristic polynomial
of a real diagonal matrix. -/
private theorem orthogonalDiagonal_charpoly_eq_diagonal
    {N : ℕ} (U : Matrix.orthogonalGroup (Fin N) ℝ) (a : Fin N → ℝ) :
    ((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) : Matrix (Fin N) (Fin N) ℝ).charpoly =
      (Matrix.diagonal a).charpoly := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUtU : UMᵀ * UM = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := UM)).mp U.prop
  -- Collapse the orthogonal basis inside the characteristic polynomial by cyclicity.
  calc
    (((UM * Matrix.diagonal a) * UMᵀ) : Matrix (Fin N) (Fin N) ℝ).charpoly
        = (UMᵀ * (UM * Matrix.diagonal a) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
            rw [Matrix.charpoly_mul_comm]
    _ = (((UMᵀ * UM) * Matrix.diagonal a) : Matrix (Fin N) (Fin N) ℝ).charpoly := by
          simp [Matrix.mul_assoc]
    _ = (Matrix.diagonal a).charpoly := by
          simp [hUtU]

/-- Helper for Proposition 24.60: the sorted real roots of the diagonal characteristic polynomial
recover the canonical nonincreasing rearrangement. -/
private theorem diagonalCharpoly_sortRoots_eq_nonincreasingRearrangement
    {N : ℕ} (d : Fin N → ℝ) :
    ((Matrix.diagonal d).charpoly.roots.sort (· ≥ ·)) =
      List.ofFn (nonincreasingRearrangement d) := by
  classical
  have hpermMerge :
      List.Perm ((List.ofFn d).mergeSort (· ≥ ·)) (List.ofFn d) :=
    List.mergeSort_perm _ _
  have hpermSort :
      List.Perm (List.ofFn (nonincreasingRearrangement d)) (List.ofFn d) := by
    -- The sorted tuple is still a permutation of the original tuple.
    simpa [nonincreasingRearrangement] using
      (Equiv.Perm.ofFn_comp_perm (Tuple.sort (OrderDual.toDual ∘ d)) d)
  have hsortedSort :
      (List.ofFn (nonincreasingRearrangement d)).SortedGE := by
    -- The canonical rearrangement is antitone by construction.
    simpa [nonincreasingRearrangement] using
      (antitone_nonincreasingRearrangement (x := d)).sortedGE_ofFn
  have hsortEq :
      ((List.ofFn d).mergeSort (· ≥ ·)) = List.ofFn (nonincreasingRearrangement d) :=
    List.Perm.eq_of_sortedGE List.sortedGE_mergeSort hsortedSort
      (hpermMerge.trans hpermSort.symm)
  -- Expand the diagonal characteristic polynomial into linear factors and identify the sorted roots.
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simpa [Multiset.coe_sort] using hsortEq
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Helper for Proposition 24.60: an orthogonal diagonal witness has the same sorted spectrum as
its diagonal data. -/
private theorem orthogonalDiagonal_nonincreasingRearrangement_eigenvalues_eq
    {N : ℕ} (U : Matrix.orthogonalGroup (Fin N) ℝ) (a : Fin N → ℝ) :
    let A : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
    let hA : A.IsHermitian := orthogonalDiagonal_isHermitian U a
    nonincreasingRearrangement hA.eigenvalues = nonincreasingRearrangement a := by
  let A : Matrix (Fin N) (Fin N) ℝ :=
    (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
      (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
  let hA : A.IsHermitian := orthogonalDiagonal_isHermitian U a
  have hcharDiag : (Matrix.diagonal hA.eigenvalues).charpoly = A.charpoly := by
    -- Rewrite the witness characteristic polynomial through the public `eigenvalues` API.
    rw [Matrix.charpoly_diagonal]
    simpa using hA.charpoly_eq.symm
  -- Compare both sorted lists through the common characteristic polynomial.
  exact List.ofFn_inj.mp <|
    calc
      List.ofFn (nonincreasingRearrangement hA.eigenvalues)
          = (A.charpoly.roots.sort (· ≥ ·)) := by
              rw [← hcharDiag]
              symm
              exact diagonalCharpoly_sortRoots_eq_nonincreasingRearrangement hA.eigenvalues
      _ = (Matrix.diagonal a).charpoly.roots.sort (· ≥ ·) := by
            rw [orthogonalDiagonal_charpoly_eq_diagonal U a]
      _ = List.ofFn (nonincreasingRearrangement a) :=
            diagonalCharpoly_sortRoots_eq_nonincreasingRearrangement a

/-- Helper for Proposition 24.60: in a common orthogonal basis, the trace pairing of diagonal
conjugates is the coordinate dot product of their diagonals. -/
private theorem trace_orthogonalDiagonal_mul_eq_dotProduct
    {N : ℕ} (U : Matrix.orthogonalGroup (Fin N) ℝ) (a b : Fin N → ℝ) :
    Matrix.trace
        (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
            (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)) :
          Matrix (Fin N) (Fin N) ℝ) =
      dotProduct a b := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUtU : UMᵀ * UM = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := UM)).mp U.prop
  -- Cycle the common orthogonal basis through the trace until only the diagonal core remains.
  calc
    Matrix.trace
        (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
            (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)) :
          Matrix (Fin N) (Fin N) ℝ)
        = Matrix.trace ((UM * (Matrix.diagonal a * (UMᵀ * UM) * Matrix.diagonal b)) * UMᵀ) := by
            simp [UM, Matrix.mul_assoc]
    _ = Matrix.trace ((UM * (Matrix.diagonal a * Matrix.diagonal b)) * UMᵀ) := by
          simp [hUtU, Matrix.mul_assoc]
    _ = Matrix.trace ((Matrix.diagonal a) * (Matrix.diagonal b)) := by
          calc
            Matrix.trace ((UM * (Matrix.diagonal a * Matrix.diagonal b)) * UMᵀ)
                = Matrix.trace (UMᵀ * (UM * (Matrix.diagonal a * Matrix.diagonal b))) := by
                    simpa [Matrix.mul_assoc] using
                      (Matrix.trace_mul_cycle UM (Matrix.diagonal a * Matrix.diagonal b) UMᵀ)
            _ = Matrix.trace ((Matrix.diagonal a) * (Matrix.diagonal b)) := by
                  rw [show UMᵀ * (UM * (Matrix.diagonal a * Matrix.diagonal b)) =
                      (UMᵀ * UM) * (Matrix.diagonal a * Matrix.diagonal b) by
                        simp [Matrix.mul_assoc]]
                  simp [hUtU]
    _ = dotProduct a b := by
          simp [Matrix.trace, Matrix.mul_apply, dotProduct]

/-- Helper for Proposition 24.60: the spectral pullback of an orthogonal diagonal witness depends
only on the diagonal data, by permutation invariance of `φ`. -/
private theorem symmetricMatrixSpectralPullback_orthogonalDiagonal_apply
    {N : ℕ} (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (hφ : CoordinatePermutationInvariant φ)
    (U : Matrix.orthogonalGroup (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    let a : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) x
    let A : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
    let hA : A.IsHermitian := orthogonalDiagonal_isHermitian U a
    symmetricMatrixSpectralPullback φ (matrixToEuclidean A) = φ x := by
  let a : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) x
  let A : Matrix (Fin N) (Fin N) ℝ :=
    (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
      (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
  let hA : A.IsHermitian := orthogonalDiagonal_isHermitian U a
  have hRearr :
      nonincreasingRearrangement
          ((EuclideanSpace.equiv (Fin N) ℝ) (symmetricMatrixEigenvalues hA)) =
        nonincreasingRearrangement ((EuclideanSpace.equiv (Fin N) ℝ) x) := by
    -- Route correction: compare the witness spectrum and the input coordinates only after sorting,
    -- so the proof stays in the public `eigenvalues` API.
    rw [symmetricMatrixEigenvalues_coords_eq_eigenvalues hA]
    simpa [a, A, hA] using
      orthogonalDiagonal_nonincreasingRearrangement_eigenvalues_eq U a
  have hSorted :
      euclideanNonincreasingRearrangement (symmetricMatrixEigenvalues hA) =
        euclideanNonincreasingRearrangement x := by
    -- Transport the sorted coordinate equality back to the Euclidean model.
    apply (EuclideanSpace.equiv (Fin N) ℝ).injective
    simpa [euclideanNonincreasingRearrangement] using hRearr
  -- Evaluate the pullback on the witness and use symmetry of `φ` on both endpoints.
  calc
    symmetricMatrixSpectralPullback φ (matrixToEuclidean A)
        = φ (symmetricMatrixEigenvalues hA) := by
            simpa [A, hA] using
              symmetricMatrixSpectralPullback_matrixToEuclidean_apply φ A hA
    _ = φ (euclideanNonincreasingRearrangement (symmetricMatrixEigenvalues hA)) := by
          exact congrArg (fun t : Set.Ioi (⊥ : EReal) ↦ (t : EReal))
            (coordinatePermutationInvariant_eq_nonincreasingRearrangement
              hφ (symmetricMatrixEigenvalues hA)).symm
    _ = φ (euclideanNonincreasingRearrangement x) := by rw [hSorted]
    _ = φ x := by
          exact congrArg (fun t : Set.Ioi (⊥ : EReal) ↦ (t : EReal))
            (coordinatePermutationInvariant_eq_nonincreasingRearrangement hφ x)

/-- Helper for Proposition 24.60: in a common orthogonal basis, the ambient Euclidean pairing of
the two diagonal witnesses is the Euclidean pairing of their diagonal data. -/
private theorem orthogonalDiagonal_pairing_eq_inner
    {N : ℕ} (U : Matrix.orthogonalGroup (Fin N) ℝ) (a b : Fin N → ℝ) :
    let A : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
    let B : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
    let hA : A.IsHermitian := orthogonalDiagonal_isHermitian U a
    ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ =
      ⟪(EuclideanSpace.equiv (Fin N) ℝ).symm a,
        (EuclideanSpace.equiv (Fin N) ℝ).symm b⟫_ℝ := by
  let A : Matrix (Fin N) (Fin N) ℝ :=
    (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
      (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
  let B : Matrix (Fin N) (Fin N) ℝ :=
    (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
      (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
  let hA : A.IsHermitian := orthogonalDiagonal_isHermitian U a
  -- Identify both pairings with the same diagonal dot product.
  calc
    ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ = Matrix.trace (A * B) :=
      matrixToEuclidean_inner_eq_trace_mul_of_isHermitian hA B
    _ = dotProduct a b := by
          simpa [A, B] using trace_orthogonalDiagonal_mul_eq_dotProduct U a b
    _ = ⟪(EuclideanSpace.equiv (Fin N) ℝ).symm a,
          (EuclideanSpace.equiv (Fin N) ℝ).symm b⟫_ℝ := by
            symm
            simpa [dotProduct_comm] using
              euclidean_inner_eq_dotProduct
                ((EuclideanSpace.equiv (Fin N) ℝ).symm a)
                ((EuclideanSpace.equiv (Fin N) ℝ).symm b)

/-- Proposition 24.60 (Lewis): if `φ : ℝ^N → ]-∞,+∞]` is symmetric, then the Fenchel conjugate of
its pullback along the canonical eigenvalue map on real symmetric matrices, viewed in the ambient
Euclidean matrix model by setting it equal to `⊤` off the symmetric locus, evaluates at every real
symmetric matrix `B` to the conjugate of `φ` at the eigenvalue vector of `B`. -/
theorem conjugate_symmetricMatrixSpectralPullback_apply_eq_conjugate_apply_eigenvalues
    {N : ℕ} (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (hφsymm : CoordinatePermutationInvariant φ)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.IsHermitian) :
    ERealFunction.conjugate (symmetricMatrixSpectralPullback φ) (matrixToEuclidean B) =
      ERealFunction.conjugate (Function.asEReal φ) (symmetricMatrixEigenvalues hB) := by
  rw [ERealFunction.conjugate_apply, ERealFunction.conjugate_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    by_cases hA : (euclideanToMatrix x).IsHermitian
    · let A : Matrix (Fin N) (Fin N) ℝ := euclideanToMatrix x
      have hxA : x = matrixToEuclidean A := by
        simp [A]
      have htrace_eq :
          ((⟪x, matrixToEuclidean B⟫_ℝ : ℝ) : EReal) =
            ((Matrix.trace (A * B) : ℝ) : EReal) := by
        -- Rewrite the ambient Euclidean pairing as the trace pairing of the Hermitian matrix core.
        rw [hxA]
        exact congrArg (fun t : ℝ ↦ (t : EReal))
          (matrixToEuclidean_inner_eq_trace_mul_of_isHermitian hA B)
      have hdot_eq :
          ((⟪symmetricMatrixEigenvalues hA, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) =
            ((dotProduct hA.eigenvalues hB.eigenvalues : ℝ) : EReal) := by
        -- The Euclidean eigenvalue model uses the coordinate dot product.
        exact congrArg (fun t : ℝ ↦ (t : EReal))
          (euclidean_inner_eq_dotProduct
            (symmetricMatrixEigenvalues hA) (symmetricMatrixEigenvalues hB))
      have htrace_le :
          ((Matrix.trace (A * B) : ℝ) : EReal) ≤
            ((⟪symmetricMatrixEigenvalues hA, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) := by
        rw [hdot_eq]
        exact_mod_cast theobald_trace_le_eigenvalues_dotProduct hA hB
      -- Compare each Hermitian matrix affine defect with the scalar affine defect at its spectrum.
      calc
        (((⟪x, matrixToEuclidean B⟫_ℝ : ℝ) : EReal) - symmetricMatrixSpectralPullback φ x)
            ≤ (((⟪symmetricMatrixEigenvalues hA, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) -
                (φ (symmetricMatrixEigenvalues hA) : EReal)) := by
                  rw [htrace_eq, symmetricMatrixSpectralPullback_apply_of_isHermitian φ hA]
                  exact EReal.sub_le_sub htrace_le le_rfl
        _ ≤ ⨆ y : EuclideanSpace ℝ (Fin N),
              (((⟪y, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) - Function.asEReal φ y) := by
                simpa [Function.asEReal_apply] using
                  (le_iSup
                    (fun y : EuclideanSpace ℝ (Fin N) ↦
                      (((⟪y, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) -
                        Function.asEReal φ y))
                    (symmetricMatrixEigenvalues hA))
    · -- Outside the symmetric locus, the pullback is `⊤`, so the affine defect is `⊥`.
      simp [symmetricMatrixSpectralPullback_apply_of_not_isHermitian, hA]
  · let hUorth :
        ((hB.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) ∈
          Matrix.orthogonalGroup (Fin N) ℝ) := by
        simpa using hB.eigenvectorUnitary.prop
    let U : Matrix.orthogonalGroup (Fin N) ℝ := ⟨hB.eigenvectorUnitary, hUorth⟩
    have hBdiag :
        B =
          (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hB.eigenvalues) *
            (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) := by
      -- Use the canonical spectral theorem basis of `B`.
      simpa [U, hUorth, Matrix.conjTranspose_eq_transpose_of_trivial,
        Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using hB.spectral_theorem
    refine iSup_le ?_
    intro x
    let a : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) x
    let A : Matrix (Fin N) (Fin N) ℝ :=
      (((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)
    let hA : A.IsHermitian := orthogonalDiagonal_isHermitian U a
    have hspectral :
        symmetricMatrixSpectralPullback φ (matrixToEuclidean A) = (φ x : EReal) := by
      -- Evaluate the witness by comparing its spectrum with the diagonal data after sorting.
      simpa [A, a, hA] using
        symmetricMatrixSpectralPullback_orthogonalDiagonal_apply φ hφsymm U x
    have hpair_inner :
        ((⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ : ℝ) : EReal) =
          ((⟪x, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) := by
      -- Compare the witness pairing with the scalar pairing in the common eigenbasis of `B`.
      have hpair_inner_real :
          ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ =
            ⟪x, symmetricMatrixEigenvalues hB⟫_ℝ := by
        calc
          ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ
              = ⟪matrixToEuclidean A,
                  matrixToEuclidean
                    ((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hB.eigenvalues) *
                        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) : Matrix (Fin N) (Fin N) ℝ)⟫_ℝ := by
                    simpa [hBdiag]
          _ = ⟪(EuclideanSpace.equiv (Fin N) ℝ).symm a,
                (EuclideanSpace.equiv (Fin N) ℝ).symm hB.eigenvalues⟫_ℝ := by
                  simpa [A, a] using orthogonalDiagonal_pairing_eq_inner U a hB.eigenvalues
          _ = ⟪x, symmetricMatrixEigenvalues hB⟫_ℝ := by
                simp [a, symmetricMatrixEigenvalues]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hpair_inner_real
    -- Compare the scalar affine defect with the exact matrix witness built in the eigenbasis of `B`.
    calc
      (((⟪x, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) - Function.asEReal φ x)
          = (((⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ : ℝ) : EReal) -
            symmetricMatrixSpectralPullback φ (matrixToEuclidean A)) := by
              rw [hpair_inner, hspectral, Function.asEReal_apply]
      _ ≤ ⨆ y : SquareMatrixSpace N,
            (((⟪y, matrixToEuclidean B⟫_ℝ : ℝ) : EReal) - symmetricMatrixSpectralPullback φ y) := by
              exact
                le_iSup
                  (fun y : SquareMatrixSpace N ↦
                    (((⟪y, matrixToEuclidean B⟫_ℝ : ℝ) : EReal) -
                      symmetricMatrixSpectralPullback φ y))
                  (matrixToEuclidean A)
