import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap24.Proposition_24_58
import BauschkeLean.Chap24.Proposition_24_60

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open Matrix
open scoped InnerProductSpace

-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic convexity and
-- semicontinuity lemmas, so this item follows the local Chapter 9 `properIoi`/`Γ₀` packaging and
-- the Chapter 24 owner `symmetricMatrixSpectralPullback`.

section

variable {N : ℕ}
variable (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
variable (hproper : (effectiveDomain φ).Nonempty)
variable (hφsymm : CoordinatePermutationInvariant φ)

/-- Helper for Corollary 24.61: an antitone finite real vector is already fixed by the canonical
nonincreasing rearrangement. -/
private theorem nonincreasingRearrangement_eq_self_of_antitone
    {x : Fin N → ℝ} (hx : Antitone x) :
    nonincreasingRearrangement x = x := by
  -- The sorted tuple is the unique antitone permutation of the original coordinates.
  simpa [nonincreasingRearrangement, Function.comp] using
    (Tuple.unique_antitone
      (f := x)
      (σ := Tuple.sort (OrderDual.toDual ∘ x))
      (τ := Equiv.refl (Fin N))
      (by
        simpa [nonincreasingRearrangement, Function.comp_assoc] using
          (antitone_nonincreasingRearrangement (x := x)))
      (by simpa [Function.comp] using hx))

/-- Helper for Corollary 24.61: the sorted real roots of the characteristic polynomial of a real
diagonal matrix recover the canonical nonincreasing rearrangement of its diagonal entries. -/
private theorem diagonalCharpoly_sortRoots_eq_nonincreasingRearrangement
    (d : Fin N → ℝ) :
    ((Matrix.diagonal d).charpoly.roots.sort (· ≥ ·)) =
      List.ofFn (nonincreasingRearrangement d) := by
  classical
  have hpermMerge :
      List.Perm ((List.ofFn d).mergeSort (· ≥ ·)) (List.ofFn d) :=
    List.mergeSort_perm _ _
  have hpermSort :
      List.Perm (List.ofFn (nonincreasingRearrangement d)) (List.ofFn d) := by
    -- The canonical rearrangement is still just a permutation of the original tuple.
    simpa [nonincreasingRearrangement] using
      (Equiv.Perm.ofFn_comp_perm (Tuple.sort (OrderDual.toDual ∘ d)) d)
  have hsortedSort :
      (List.ofFn (nonincreasingRearrangement d)).SortedGE := by
    -- The rearrangement is antitone by construction, hence descending-sorted.
    simpa [nonincreasingRearrangement] using
      (antitone_nonincreasingRearrangement (x := d)).sortedGE_ofFn
  have hsortEq :
      ((List.ofFn d).mergeSort (· ≥ ·)) = List.ofFn (nonincreasingRearrangement d) :=
    List.Perm.eq_of_sortedGE List.sortedGE_mergeSort hsortedSort
      (hpermMerge.trans hpermSort.symm)
  -- Expand the diagonal characteristic polynomial and identify its sorted roots.
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simpa [Multiset.coe_sort] using hsortEq
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Helper for Corollary 24.61: the real-part version of the sorted diagonal-root formula matches
the Hermitian-spectrum API used later in the proof. -/
private theorem diagonalCharpoly_sortRootsMapRe_eq_nonincreasingRearrangement
    (d : Fin N → ℝ) :
    (((Matrix.diagonal d).charpoly.roots.map RCLike.re).sort (· ≥ ·)) =
      List.ofFn (nonincreasingRearrangement d) := by
  -- Over `ℝ`, taking real parts of the roots is the identity.
  simpa using diagonalCharpoly_sortRoots_eq_nonincreasingRearrangement (N := N) d

/-- Helper for Corollary 24.61: the canonical nonincreasing rearrangement of the ordered spectrum
of a real diagonal matrix with antitone diagonal entries recovers that diagonal vector. -/
private theorem nonincreasingRearrangement_eigenvalues_diagonal_eq_of_antitone
    (d : Fin N → ℝ) (hd : Antitone d) :
    nonincreasingRearrangement (Matrix.isHermitian_diagonal d).eigenvalues = d := by
  have hchar :
      (Matrix.diagonal ((Matrix.isHermitian_diagonal d).eigenvalues)).charpoly =
        (Matrix.diagonal d).charpoly := by
    -- The diagonal matrix built from the ordered spectrum has the same characteristic polynomial.
    rw [Matrix.charpoly_diagonal]
    simpa using (Matrix.isHermitian_diagonal d).charpoly_eq.symm
  exact List.ofFn_inj.mp <|
    calc
      List.ofFn (nonincreasingRearrangement (Matrix.isHermitian_diagonal d).eigenvalues)
          = (((Matrix.diagonal ((Matrix.isHermitian_diagonal d).eigenvalues)).charpoly.roots.map
              RCLike.re).sort (· ≥ ·)) := by
                symm
                exact
                  diagonalCharpoly_sortRootsMapRe_eq_nonincreasingRearrangement (N := N)
                    (Matrix.isHermitian_diagonal d).eigenvalues
      _ = ((Matrix.diagonal d).charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
            rw [hchar]
      _ = List.ofFn (nonincreasingRearrangement d) := by
            simpa using
              diagonalCharpoly_sortRootsMapRe_eq_nonincreasingRearrangement (N := N) d
      _ = List.ofFn d := by
            rw [nonincreasingRearrangement_eq_self_of_antitone (N := N) hd]

/-- Helper for Corollary 24.61: after transporting the diagonal spectrum to Euclidean
coordinates, its canonical nonincreasing rearrangement is exactly the original antitone diagonal
vector. -/
private theorem euclideanNonincreasingRearrangement_symmetricMatrixEigenvalues_diagonal_eq_of_antitone
    (d : Fin N → ℝ) (hd : Antitone d) :
    euclideanNonincreasingRearrangement (symmetricMatrixEigenvalues (Matrix.isHermitian_diagonal d)) =
      (EuclideanSpace.equiv (Fin N) ℝ).symm d := by
  -- Read the Euclidean rearrangement coordinatewise and use the scalar diagonal-spectrum identity.
  ext i
  rw [euclideanNonincreasingRearrangement_eq]
  simpa [symmetricMatrixEigenvalues] using
    congrFun
      (nonincreasingRearrangement_eigenvalues_diagonal_eq_of_antitone (N := N) d hd)
      i

/-- The spectral pullback of a proper coordinate-permutation invariant function is proper on the
ambient Euclidean model of real symmetric matrices. -/
theorem symmetricMatrixSpectralPullback_isProper_of_effectiveDomain_nonempty
    (hproper : (effectiveDomain φ).Nonempty)
    (hφsymm : CoordinatePermutationInvariant φ) :
    IsProper (symmetricMatrixSpectralPullback φ) := by
  refine ⟨?_, ?_⟩
  · intro x
    -- The spectral pullback is finite on the symmetric locus and equal to `⊤` off it.
    by_cases hx : (euclideanToMatrix x).IsHermitian
    · rw [symmetricMatrixSpectralPullback_apply_of_isHermitian φ hx]
      exact ne_of_gt (φ (symmetricMatrixEigenvalues hx)).2
    · rw [symmetricMatrixSpectralPullback_apply_of_not_isHermitian φ hx]
      exact top_ne_bot
  · rcases hproper with ⟨x, hx⟩
    let xs := euclideanNonincreasingRearrangement x
    let d : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) xs
    have hd : Antitone d := by
      -- The canonical rearrangement has nonincreasing coordinates.
      simpa [d, xs, euclideanNonincreasingRearrangement_eq] using
        (antitone_nonincreasingRearrangement (x := (EuclideanSpace.equiv (Fin N) ℝ) x))
    refine ⟨matrixToEuclidean (Matrix.diagonal d), ?_⟩
    rw [mem_dom_iff_ne_top]
    -- Evaluate the diagonal witness through its ordered spectrum and then use symmetry of `φ`.
    rw [symmetricMatrixSpectralPullback_matrixToEuclidean_apply φ (Matrix.diagonal d)
      (Matrix.isHermitian_diagonal d)]
    rw [← CoordinatePermutationInvariant.eq_nonincreasingRearrangement hφsymm
      (symmetricMatrixEigenvalues (Matrix.isHermitian_diagonal d))]
    rw [euclideanNonincreasingRearrangement_symmetricMatrixEigenvalues_diagonal_eq_of_antitone
      (N := N) d hd]
    have hxs : (EuclideanSpace.equiv (Fin N) ℝ).symm d = xs := by
      simp [d, xs]
    rw [hxs]
    change (φ xs : EReal) ≠ ⊤
    rw [CoordinatePermutationInvariant.eq_nonincreasingRearrangement hφsymm x]
    exact ne_of_lt (mem_effectiveDomain_iff.mp hx)

/-- Helper for Corollary 24.61: the packaged Fenchel conjugate of a proper symmetric function is
again coordinate-permutation invariant. -/
private theorem properConjugateIoi_coordinatePermutationInvariant
    (hφsymm : CoordinatePermutationInvariant φ) :
    CoordinatePermutationInvariant (properConjugateIoi φ hproper) := by
  intro σ x
  -- Compare the packaged values through the raw conjugate symmetry theorem.
  apply Subtype.ext
  simpa [properConjugateIoi_apply] using
    ERealFunction.conjugate_coordinatePermutationInvariant hφsymm σ x

/-- Helper for Corollary 24.61: two coordinate-permutation invariant functions that agree on the
canonical nonincreasing rearrangements agree everywhere. -/
private theorem coordinatePermutationInvariant_eq_of_eq_nonincreasingRearrangement
    {α : Type*} {ψ χ : EuclideanSpace ℝ (Fin N) → α}
    (hψ : CoordinatePermutationInvariant ψ)
    (hχ : CoordinatePermutationInvariant χ)
    (hEq :
      ∀ x : EuclideanSpace ℝ (Fin N),
        ψ (euclideanNonincreasingRearrangement x) =
          χ (euclideanNonincreasingRearrangement x)) :
    ψ = χ := by
  funext x
  -- Both sides reduce to the same value on the canonical ordered representative of `x`.
  calc
    ψ x = ψ (euclideanNonincreasingRearrangement x) := by
      symm
      exact CoordinatePermutationInvariant.eq_nonincreasingRearrangement hψ x
    _ = χ (euclideanNonincreasingRearrangement x) := hEq x
    _ = χ x := CoordinatePermutationInvariant.eq_nonincreasingRearrangement hχ x

/-- Helper for Corollary 24.61: for a Hermitian left factor, the Euclidean matrix pairing is the
trace pairing `trace (A * B)`. -/
private theorem matrixToEuclidean_inner_eq_trace_mul_of_isHermitian
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℝ) :
    ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ = Matrix.trace (A * B) := by
  have hAT : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  -- Rewrite the Euclidean pairing entrywise and then collapse it to the trace formula.
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
            _ = ∑ j, ∑ i, A i j * B i j := by
                  rw [Finset.sum_comm]
            _ = Matrix.trace (Aᵀ * B) := by
                  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = Matrix.trace (A * B) := by
          rw [hAT]

/-- Helper for Corollary 24.61: Hermitian primal matrices only see the Hermitian symmetrization of
the dual variable in the ambient Euclidean pairing. -/
private theorem trace_mul_eq_trace_mul_transpose_right_of_isHermitian
    {A Y : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    Matrix.trace (A * Yᵀ) = Matrix.trace (A * Y) := by
  have hAT : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  -- Transpose the trace and cycle the factors until the Hermitian left factor reappears.
  calc
    Matrix.trace (A * Yᵀ) = Matrix.trace ((A * Yᵀ)ᵀ) := by
      rw [Matrix.trace_transpose]
    _ = Matrix.trace (Y * Aᵀ) := by
      simp [Matrix.transpose_mul]
    _ = Matrix.trace (Aᵀ * Y) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (A * Y) := by
      rw [hAT]

/-- Helper for Corollary 24.61: the Euclidean matrix pairing against a matrix singleton reads off
the corresponding entry. -/
private theorem matrixToEuclidean_inner_single
    (X : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    ⟪matrixToEuclidean X, matrixToEuclidean (Matrix.single i j (1 : ℝ))⟫_ℝ = X i j := by
  -- In coordinates the singleton basis matrix contributes exactly one summand to the dot product.
  calc
    ⟪matrixToEuclidean X, matrixToEuclidean (Matrix.single i j (1 : ℝ))⟫_ℝ
        = dotProduct
            ((EuclideanSpace.equiv (Fin N × Fin N) ℝ) (matrixToEuclidean X))
            ((EuclideanSpace.equiv (Fin N × Fin N) ℝ)
              (matrixToEuclidean (Matrix.single i j (1 : ℝ)))) := by
              simpa [EuclideanSpace.equiv, dotProduct_comm] using
                (EuclideanSpace.inner_eq_star_dotProduct
                  (matrixToEuclidean X)
                  (matrixToEuclidean (Matrix.single i j (1 : ℝ))))
    _ = ∑ p : Fin N × Fin N, X p.1 p.2 * Matrix.single i j (1 : ℝ) p.1 p.2 := by
          simp [dotProduct, matrixToEuclidean]
    _ = X i j := by
      calc
        ∑ q : Fin N × Fin N, X q.1 q.2 * Matrix.single i j (1 : ℝ) q.1 q.2
            = ∑ q : Fin N × Fin N, if q = (i, j) then X i j else 0 := by
                refine Finset.sum_congr rfl ?_
                intro q hq
                by_cases hqij : q = (i, j)
                · subst q
                  simp
                · rcases q with ⟨a, b⟩
                  by_cases hi : i = a
                  · by_cases hj : j = b
                    · exfalso
                      apply hqij
                      cases hi
                      cases hj
                      rfl
                    · have hsingle : Matrix.single i j (1 : ℝ) a b = 0 := by
                          exact Matrix.single_apply_of_col_ne i a hj (1 : ℝ)
                      simp [hsingle, hqij]
                  · have hsingle : Matrix.single i j (1 : ℝ) a b = 0 := by
                        exact Matrix.single_apply_of_row_ne hi j b (1 : ℝ)
                    simp [hsingle, hqij]
        _ = X i j := by
          rw [Finset.sum_eq_single (i, j)]
          · simp
          · intro q hq hqp
            simp [hqp]
          · intro hqp
            simp at hqp

/-- Helper for Corollary 24.61: a two-point singleton difference is skew-symmetric. -/
private theorem transpose_single_sub_single
    (i j : Fin N) :
    (Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ))ᵀ =
      -(Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ)) := by
  -- Transposing swaps the two singleton entries, which is exactly negation of the skew witness.
  calc
    (Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ))ᵀ
        = (Matrix.single i j (1 : ℝ))ᵀ - (Matrix.single j i (1 : ℝ))ᵀ := by
            rw [Matrix.transpose_sub]
    _ = Matrix.single j i (1 : ℝ) - Matrix.single i j (1 : ℝ) := by
          simp
    _ = -(Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ)) := by
          abel_nf

/-- Helper for Corollary 24.61: a Hermitian left factor only sees the Hermitian half
symmetrization of the right factor through the trace pairing. -/
private theorem trace_mul_half_symmetrization_eq_of_isHermitian
    {A Y : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    Matrix.trace (A * ((Y + Yᵀ) / 2)) = Matrix.trace (A * Y) := by
  -- Expand the half-symmetrization in the trace and separate the `Y` and `Yᵀ` contributions.
  calc
    Matrix.trace (A * ((Y + Yᵀ) / 2))
        = Matrix.trace (A * (((1 / 2 : ℝ) • Y) + ((1 / 2 : ℝ) • Yᵀ))) := by
            simp [div_eq_mul_inv, smul_add]
    _ = Matrix.trace (((1 / 2 : ℝ) • (A * Y)) + ((1 / 2 : ℝ) • (A * Yᵀ))) := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
    _ = (1 / 2 : ℝ) • Matrix.trace (A * Y) + (1 / 2 : ℝ) • Matrix.trace (A * Yᵀ) := by
          rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    _ = (1 / 2 : ℝ) * Matrix.trace (A * Y) + (1 / 2 : ℝ) * Matrix.trace (A * Yᵀ) := by
          simp
    _ = (1 / 2 : ℝ) * Matrix.trace (A * Y) + (1 / 2 : ℝ) * Matrix.trace (A * Y) := by
          rw [trace_mul_eq_trace_mul_transpose_right_of_isHermitian hA]
    _ = Matrix.trace (A * Y) := by
          ring

/-- Helper for Corollary 24.61: Hermitian matrices pair equally with a matrix and with its
transpose in the ambient Euclidean model. -/
private theorem matrixToEuclidean_inner_eq_symmetrization_right_of_isHermitian
    {A Y : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    ⟪matrixToEuclidean A, matrixToEuclidean Y⟫_ℝ =
      ⟪matrixToEuclidean A, matrixToEuclidean ((Y + Yᵀ) / 2)⟫_ℝ := by
  -- Rewrite both inner products as trace pairings so the Hermitian normalization happens on the
  -- matrix side instead of in Euclidean coordinates.
  rw [matrixToEuclidean_inner_eq_trace_mul_of_isHermitian hA,
    matrixToEuclidean_inner_eq_trace_mul_of_isHermitian hA]
  -- The standalone trace bridge is the exact normalization needed by the conjugate proof below.
  exact (trace_mul_half_symmetrization_eq_of_isHermitian (N := N) (A := A) (Y := Y) hA).symm

/-- Helper for Corollary 24.61: the conjugate of the spectral pullback only depends on the
Hermitian symmetrization of the dual matrix argument. -/
private theorem conjugate_symmetricMatrixSpectralPullback_matrix_eq_conjugate_symmetrization
    (Y : Matrix (Fin N) (Fin N) ℝ) :
    ERealFunction.conjugate (symmetricMatrixSpectralPullback φ) (matrixToEuclidean Y) =
      ERealFunction.conjugate (symmetricMatrixSpectralPullback φ)
        (matrixToEuclidean ((Y + Yᵀ) / 2)) := by
  rw [ERealFunction.conjugate_apply, ERealFunction.conjugate_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    by_cases hx : (euclideanToMatrix x).IsHermitian
    · let A : Matrix (Fin N) (Fin N) ℝ := euclideanToMatrix x
      have hxA : x = matrixToEuclidean A := by
        simp [A]
      have hinner :
          ⟪x, matrixToEuclidean Y⟫_ℝ =
            ⟪x, matrixToEuclidean ((Y + Yᵀ) / 2)⟫_ℝ := by
        rw [hxA]
        simpa [A] using
          matrixToEuclidean_inner_eq_symmetrization_right_of_isHermitian
            (N := N) (A := A) (Y := Y) hx
      have hinnerE :
          (((⟪x, matrixToEuclidean Y⟫_ℝ : ℝ) : EReal)) =
            (((⟪x, matrixToEuclidean ((Y + Yᵀ) / 2)⟫_ℝ : ℝ) : EReal)) :=
        congrArg (fun t : ℝ ↦ (t : EReal)) hinner
      rw [hinnerE]
      exact
        le_iSup
          (fun z : SquareMatrixSpace N ↦
            (((⟪z, matrixToEuclidean ((Y + Yᵀ) / 2)⟫_ℝ : ℝ) : EReal) -
              symmetricMatrixSpectralPullback φ z))
          x
    · -- Off the Hermitian locus, the spectral pullback is `⊤`, so both affine defects are `⊥`.
      simp [symmetricMatrixSpectralPullback_apply_of_not_isHermitian, hx]
  · refine iSup_le ?_
    intro x
    by_cases hx : (euclideanToMatrix x).IsHermitian
    · let A : Matrix (Fin N) (Fin N) ℝ := euclideanToMatrix x
      have hxA : x = matrixToEuclidean A := by
        simp [A]
      have hinner :
          ⟪x, matrixToEuclidean ((Y + Yᵀ) / 2)⟫_ℝ =
            ⟪x, matrixToEuclidean Y⟫_ℝ := by
        rw [hxA]
        simpa [A] using
          (matrixToEuclidean_inner_eq_symmetrization_right_of_isHermitian
            (N := N) (A := A) (Y := Y) hx).symm
      have hinnerE :
          (((⟪x, matrixToEuclidean ((Y + Yᵀ) / 2)⟫_ℝ : ℝ) : EReal)) =
            (((⟪x, matrixToEuclidean Y⟫_ℝ : ℝ) : EReal)) :=
        congrArg (fun t : ℝ ↦ (t : EReal)) hinner
      rw [hinnerE]
      exact
        le_iSup
          (fun z : SquareMatrixSpace N ↦
            (((⟪z, matrixToEuclidean Y⟫_ℝ : ℝ) : EReal) -
              symmetricMatrixSpectralPullback φ z))
          x
    · -- The nonsymmetric branch is again immediately `⊥`.
      simp [symmetricMatrixSpectralPullback_apply_of_not_isHermitian, hx]

/-- Helper for Corollary 24.61: a non-Hermitian matrix has a skew part that pairs nontrivially
with it in the ambient Euclidean matrix model. -/
private theorem exists_skew_pairing_ne_zero_of_not_isHermitian
    {X : Matrix (Fin N) (Fin N) ℝ} (hX : ¬ X.IsHermitian) :
    ∃ K : Matrix (Fin N) (Fin N) ℝ,
      Kᵀ = -K ∧
        ⟪matrixToEuclidean X, matrixToEuclidean K⟫_ℝ ≠ 0 := by
  have hentries : ∃ i j : Fin N, X i j ≠ X j i := by
    by_contra hcontra
    push_neg at hcontra
    apply hX
    -- Over `ℝ`, Hermitianity is just equality with the transpose.
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using show Xᵀ = X from by
      ext i j
      exact hcontra j i
  rcases hentries with ⟨i, j, hij⟩
  have hij_ne : i ≠ j := by
    intro hij_eq
    apply hij
    simpa [hij_eq]
  let K : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ)
  refine ⟨K, ?_, ?_⟩
  · -- The singleton-difference witness is skew-symmetric by construction.
    simpa [K] using transpose_single_sub_single (N := N) i j
  · have hinner :
        ⟪matrixToEuclidean X, matrixToEuclidean K⟫_ℝ = X i j - X j i := by
      calc
        ⟪matrixToEuclidean X, matrixToEuclidean K⟫_ℝ
            = ⟪matrixToEuclidean X, matrixToEuclidean (Matrix.single i j (1 : ℝ))⟫_ℝ -
              ⟪matrixToEuclidean X, matrixToEuclidean (Matrix.single j i (1 : ℝ))⟫_ℝ := by
                simpa [K] using
                  (inner_sub_right
                    (matrixToEuclidean X)
                    (matrixToEuclidean (Matrix.single i j (1 : ℝ)))
                    (matrixToEuclidean (Matrix.single j i (1 : ℝ))))
        _ = X i j - X j i := by
              rw [matrixToEuclidean_inner_single (N := N) X i j,
                matrixToEuclidean_inner_single (N := N) X j i]
    show ⟪matrixToEuclidean X, matrixToEuclidean K⟫_ℝ ≠ 0
    rw [hinner]
    exact sub_ne_zero.mpr hij

/-- The canonical `]-∞,+∞]`-valued spectral pullback attached to a proper symmetric `φ`. -/
noncomputable abbrev properSymmetricMatrixSpectralPullback
    (hproper : (effectiveDomain φ).Nonempty)
    (hφsymm : CoordinatePermutationInvariant φ) :
    SquareMatrixSpace N → Set.Ioi (⊥ : EReal) :=
  properIoi (symmetricMatrixSpectralPullback φ)
    (symmetricMatrixSpectralPullback_isProper_of_effectiveDomain_nonempty φ hproper hφsymm)

/-- Coercing `properSymmetricMatrixSpectralPullback` back to `EReal` recovers the underlying
spectral pullback owner. -/
@[simp] theorem properSymmetricMatrixSpectralPullback_apply (x : SquareMatrixSpace N) :
    (properSymmetricMatrixSpectralPullback φ hproper hφsymm x : EReal) =
      symmetricMatrixSpectralPullback φ x :=
  rfl

/-- Corollary 24.61 (Davis): for a proper symmetric `φ : ℝ^N → ]-∞,+∞]`, the canonical spectral
pullback of `φ` along the ordered eigenvalue map belongs to `Γ₀(S^N)` if and only if `φ` belongs
to `Γ₀(ℝ^N)`, represented here on the ambient Euclidean matrix model by the packaged owner
`properSymmetricMatrixSpectralPullback φ hproper hφsymm`. -/
theorem symmetricMatrixSpectralPullback_mem_gammaZero_iff
    :
    properSymmetricMatrixSpectralPullback φ hproper hφsymm ∈ Γ₀(SquareMatrixSpace N) ↔
      φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  -- Route correction: the naive identity
  -- `conjugate (symmetricMatrixSpectralPullback φ) =
  --    symmetricMatrixSpectralPullback (properConjugateIoi φ hproper)`
  -- is false off the symmetric locus, so the proof has to separate the Hermitian bridge from the
  -- off-symmetric branch.
  --
  -- TODO: the symmetrization bridge is now available above. The remaining proof has to package it
  -- into two branch lemmas for the biconjugate: on Hermitian matrices, compare with
  -- `φ.asEReal∗∗` through Proposition 24.60; off the Hermitian locus, use the skew witness to
  -- force the biconjugate to `⊤`. After that, Fenchel--Moreau on both sides finishes the iff.
  sorry

/-- If `φ ∈ Γ₀(ℝ^N)` is symmetric and proper, then its canonical packaged spectral pullback
belongs to `Γ₀(S^N)`. -/
theorem properSymmetricMatrixSpectralPullback_mem_gammaZero
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N))) :
    properSymmetricMatrixSpectralPullback φ hproper hφsymm ∈ Γ₀(SquareMatrixSpace N) :=
  (symmetricMatrixSpectralPullback_mem_gammaZero_iff φ hproper hφsymm).2 hφ

end
