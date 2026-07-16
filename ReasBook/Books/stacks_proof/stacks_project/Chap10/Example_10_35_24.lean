import Mathlib
import stacks_proof.stacks_project.Chap05.Lemma_5_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix MvPolynomial Polynomial PrimeSpectrum

universe u

/-- Helper for Chap10 Example 10 35 24: the full finset on `Fin 3` has cardinality three. -/
private theorem finsetUnivFinThree_card :
    (Finset.univ : Finset (Fin 3)).card = 3 := by
  -- This records the cardinality proof used to name the unique top exterior-power basis vector.
  simp

section

variable {k : Type u} [Semiring k]

/-- The diagonal idempotent matrix with `r` ones followed by `n - r` zeros. -/
def rankProjectionMatrix (k : Type u) [Semiring k] (n : ℕ) (r : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) k :=
  diagonal fun i ↦ if i.1 < r then 1 else 0

/-- Helper for Chap10 Example 10 35 24: a standard rank projection matrix is idempotent. -/
private theorem rankProjectionMatrix_isIdempotent (n : ℕ) (r : Fin (n + 1)) :
    IsIdempotentElem (rankProjectionMatrix k n r) := by
  -- The diagonal entries are all idempotents, so the diagonal matrix squares entrywise.
  rw [rankProjectionMatrix, IsIdempotentElem, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i.1 < r <;> simp [hi]
  · simp [Matrix.diagonal, hij]

/-- Helper for Chap10 Example 10 35 24: conjugating an idempotent matrix by a unit preserves
idempotency. -/
private theorem matrix_isIdempotentElem_units_conj {R : Type u} [Semiring R] {n : ℕ}
    (U : (Matrix (Fin n) (Fin n) R)ˣ) {P : Matrix (Fin n) (Fin n) R}
    (hP : IsIdempotentElem P) :
    IsIdempotentElem
      ((U : Matrix (Fin n) (Fin n) R) * P * (↑(U⁻¹) : Matrix (Fin n) (Fin n) R)) := by
  -- Conjugation is the `ConjAct` semiring action, and that action preserves multiplication.
  change IsIdempotentElem (ConjAct.toConjAct U • P)
  exact hP.map
    (MulSemiringAction.toRingHom (ConjAct (Matrix (Fin n) (Fin n) R)ˣ)
      (Matrix (Fin n) (Fin n) R) (ConjAct.toConjAct U))

end

section

variable {k : Type u} [CommRing k]

private noncomputable def idempotentMatrixRelationEntry (k : Type u) [CommRing k] (n : ℕ)
    (ij : Fin n × Fin n) :
    MvPolynomial (Fin n × Fin n) k :=
  (∑ l : Fin n, X (ij.1, l) * X (l, ij.2)) - X (ij.1, ij.2)

private noncomputable def idempotentMatrixIdeal (k : Type u) [CommRing k] (n : ℕ) :
    Ideal (MvPolynomial (Fin n × Fin n) k) :=
  Ideal.span (Set.range (idempotentMatrixRelationEntry k n))

/-- The coordinate ring `k[{t_ij}]/(T^2 - T)` of the idempotent-matrix locus from
Example 10.35.24. -/
noncomputable abbrev idempotentMatrixCoordinateRing (k : Type u) [CommRing k] (n : ℕ) :=
  MvPolynomial (Fin n × Fin n) k ⧸ idempotentMatrixIdeal k n

/-- The ideal cutting out the fixed-rank locus inside the idempotent-matrix coordinate ring by
forcing the characteristic polynomial to agree with that of the standard rank-`r` idempotent. -/
private noncomputable def idempotentRankComponentIdeal (k : Type u) [CommRing k] (n : ℕ)
    (r : Fin (n + 1)) :
    Ideal (idempotentMatrixCoordinateRing k n) :=
  Ideal.span <| Set.range fun i : Fin n ↦
    Ideal.Quotient.mk (idempotentMatrixIdeal k n)
      ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
        MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))

/-- The closed subset of `Spec(k[{t_ij}]/(T^2 - T))` on which the generic idempotent matrix has the
same characteristic polynomial as the standard rank-`r` projection. On closed points, this is the
rank-`r` idempotent locus. -/
noncomputable def idempotentRankComponent (k : Type u) [CommRing k] (n : ℕ) (r : Fin (n + 1)) :
    Set (PrimeSpectrum (idempotentMatrixCoordinateRing k n)) :=
  zeroLocus (idempotentRankComponentIdeal k n r : Set (idempotentMatrixCoordinateRing k n))

/-- Helper for Chap10 Example 10 35 24: the universal matrix over the idempotent-matrix
coordinate ring. -/
private noncomputable def genericIdempotentMatrix (k : Type u) [CommRing k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (idempotentMatrixCoordinateRing k n) :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) k).map (Ideal.Quotient.mk (idempotentMatrixIdeal k n))

/-- Helper for Chap10 Example 10 35 24: the coordinate ring of the generic general linear
matrix, obtained by inverting the determinant of the generic matrix. -/
private noncomputable abbrev generalLinearCoordinateRing (k : Type u) [CommRing k] (n : ℕ) :=
  Localization.Away ((Matrix.mvPolynomialX (Fin n) (Fin n) k).det)

/-- Helper for Chap10 Example 10 35 24: the generic matrix over the determinant localization. -/
private noncomputable def genericGeneralLinearMatrix (k : Type u) [CommRing k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n) :=
  (algebraMap (MvPolynomial (Fin n × Fin n) k)
    (generalLinearCoordinateRing k n)).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) k)

/-- Helper for Chap10 Example 10 35 24: the generic determinant is a unit after localizing
away from it. -/
private theorem genericGeneralLinearMatrix_det_isUnit (n : ℕ) :
    IsUnit (genericGeneralLinearMatrix k n).det := by
  -- Determinants commute with coefficient maps, so the determinant is the inverted element.
  rw [genericGeneralLinearMatrix, ← RingHom.map_det]
  exact
    (IsLocalization.Away.algebraMap_isUnit
      ((Matrix.mvPolynomialX (Fin n) (Fin n) k).det) :
        IsUnit ((algebraMap (MvPolynomial (Fin n × Fin n) k)
          (generalLinearCoordinateRing k n))
            ((Matrix.mvPolynomialX (Fin n) (Fin n) k).det)))

/-- Helper for Chap10 Example 10 35 24: the generic localized matrix as an element of `GL_n`. -/
private noncomputable def genericGeneralLinearUnit (k : Type u) [CommRing k] (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (generalLinearCoordinateRing k n) :=
  Matrix.GeneralLinearGroup.mk'' (genericGeneralLinearMatrix k n)
    (genericGeneralLinearMatrix_det_isUnit (k := k) n)

/-- Helper for Chap10 Example 10 35 24: the universal `GL_n`-orbit matrix
`U P_r U⁻¹` over the determinant localization. -/
private noncomputable def idempotentOrbitMatrix (k : Type u) [CommRing k] (n : ℕ)
    (r : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n) :=
  (genericGeneralLinearUnit k n :
      Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n)) *
    rankProjectionMatrix (generalLinearCoordinateRing k n) n r *
    ((genericGeneralLinearUnit k n)⁻¹ :
      Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n))

/-- Helper for Chap10 Example 10 35 24: polynomial-coordinate evaluation at the universal
`GL_n`-orbit matrix. -/
private noncomputable def idempotentOrbitMvPolynomialEval (k : Type u) [CommRing k] (n : ℕ)
    (r : Fin (n + 1)) :
    MvPolynomial (Fin n × Fin n) k →+* generalLinearCoordinateRing k n :=
  MvPolynomial.eval₂Hom (algebraMap k (generalLinearCoordinateRing k n))
    fun ij ↦ idempotentOrbitMatrix k n r ij.1 ij.2

/-- Helper for Chap10 Example 10 35 24: the orbit evaluation sends each coordinate variable to
the corresponding entry of `U P_r U⁻¹`. -/
private theorem idempotentOrbitMvPolynomialEval_X (n : ℕ) (r : Fin (n + 1))
    (ij : Fin n × Fin n) :
    idempotentOrbitMvPolynomialEval k n r (MvPolynomial.X ij) =
      idempotentOrbitMatrix k n r ij.1 ij.2 := by
  -- This is the defining computation rule for the polynomial evaluation map.
  simp [idempotentOrbitMvPolynomialEval]

/-- Helper for Chap10 Example 10 35 24: the universal `GL_n`-orbit matrix is idempotent. -/
private theorem idempotentOrbitMatrix_isIdempotent (n : ℕ) (r : Fin (n + 1)) :
    IsIdempotentElem (idempotentOrbitMatrix k n r) := by
  -- The orbit matrix is the conjugate of the standard idempotent projection.
  change IsIdempotentElem
    (((genericGeneralLinearUnit k n :
        Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n)) *
      rankProjectionMatrix (generalLinearCoordinateRing k n) n r *
      ((genericGeneralLinearUnit k n)⁻¹ :
        Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n))))
  exact matrix_isIdempotentElem_units_conj (genericGeneralLinearUnit k n)
    (rankProjectionMatrix_isIdempotent (k := generalLinearCoordinateRing k n) n r)

/-- Helper for Chap10 Example 10 35 24: idempotent-matrix relation entries vanish on the
universal orbit matrix. -/
private theorem idempotentOrbitRelationEntry_eval_eq_zero (n : ℕ) (r : Fin (n + 1))
    (ij : Fin n × Fin n) :
    idempotentOrbitMvPolynomialEval k n r (idempotentMatrixRelationEntry k n ij) = 0 := by
  -- Evaluation turns the universal relation into the corresponding entry of `(U P U⁻¹)^2-U P U⁻¹`.
  have hentry :=
    congrArg
      (fun A : Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n) ↦ A ij.1 ij.2)
      (idempotentOrbitMatrix_isIdempotent (k := k) n r).eq
  have hsub :
      (∑ x : Fin n,
          idempotentOrbitMatrix k n r ij.1 x * idempotentOrbitMatrix k n r x ij.2) -
        idempotentOrbitMatrix k n r ij.1 ij.2 = 0 := by
    simpa [Matrix.mul_apply] using sub_eq_zero.mpr hentry
  simpa [idempotentOrbitMvPolynomialEval, idempotentMatrixRelationEntry] using hsub

/-- Helper for Chap10 Example 10 35 24: the idempotent-matrix ideal is killed by the universal
orbit evaluation. -/
private theorem idempotentMatrixIdeal_le_idempotentOrbitEval_ker (n : ℕ) (r : Fin (n + 1)) :
    idempotentMatrixIdeal k n ≤ RingHom.ker (idempotentOrbitMvPolynomialEval k n r) := by
  -- The ideal is generated by the relation entries, each of which vanishes on the orbit matrix.
  rw [idempotentMatrixIdeal]
  refine Ideal.span_le.mpr ?_
  rintro f ⟨ij, rfl⟩
  exact RingHom.mem_ker.mpr (idempotentOrbitRelationEntry_eval_eq_zero (k := k) n r ij)

/-- Helper for Chap10 Example 10 35 24: the universal orbit map from the idempotent-matrix
coordinate ring to the generic `GL_n` parameter ring. -/
private noncomputable def idempotentOrbitParamHom (k : Type u) [CommRing k] (n : ℕ)
    (r : Fin (n + 1)) :
    idempotentMatrixCoordinateRing k n →+* generalLinearCoordinateRing k n :=
  Ideal.Quotient.lift (idempotentMatrixIdeal k n) (idempotentOrbitMvPolynomialEval k n r)
    (idempotentMatrixIdeal_le_idempotentOrbitEval_ker (k := k) n r)

/-- Helper for Chap10 Example 10 35 24: the orbit quotient map sends each coordinate to the
corresponding entry of the universal orbit matrix. -/
private theorem idempotentOrbitParamHom_mk_X (n : ℕ) (r : Fin (n + 1))
    (ij : Fin n × Fin n) :
    idempotentOrbitParamHom k n r
      (Ideal.Quotient.mk (idempotentMatrixIdeal k n) (MvPolynomial.X ij)) =
        idempotentOrbitMatrix k n r ij.1 ij.2 := by
  -- The quotient lift computes by the orbit evaluation on representatives.
  simp [idempotentOrbitParamHom, idempotentOrbitMvPolynomialEval_X]

/-- Helper for Chap10 Example 10 35 24: the universal idempotent matrix maps to the universal
orbit matrix under the orbit parametrization. -/
private theorem genericIdempotentMatrix_map_idempotentOrbitParamHom (n : ℕ)
    (r : Fin (n + 1)) :
    (genericIdempotentMatrix k n).map (idempotentOrbitParamHom k n r) =
      idempotentOrbitMatrix k n r := by
  -- Matrix extensionality reduces the comparison to the quotient-lift computation on variables.
  ext i j
  simp [genericIdempotentMatrix, idempotentOrbitParamHom_mk_X]

/-- Helper for Chap10 Example 10 35 24: the universal matrix in the coordinate ring is
idempotent. -/
private theorem genericIdempotentMatrix_isIdempotent (n : ℕ) :
    IsIdempotentElem (genericIdempotentMatrix k n) := by
  rw [IsIdempotentElem]
  ext i j
  -- Each matrix entry of `T ^ 2 - T` is one of the generators killed by the quotient.
  have hmem : idempotentMatrixRelationEntry k n (i, j) ∈ idempotentMatrixIdeal k n := by
    exact Ideal.subset_span ⟨(i, j), rfl⟩
  have hzero :
      Ideal.Quotient.mk (idempotentMatrixIdeal k n)
        (idempotentMatrixRelationEntry k n (i, j)) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hentry :
      (∑ x : Fin n,
          Ideal.Quotient.mk (idempotentMatrixIdeal k n) (MvPolynomial.X (i, x)) *
            Ideal.Quotient.mk (idempotentMatrixIdeal k n) (MvPolynomial.X (x, j))) -
        Ideal.Quotient.mk (idempotentMatrixIdeal k n) (MvPolynomial.X (i, j)) = 0 := by
    simpa [idempotentMatrixRelationEntry] using hzero
  simpa [genericIdempotentMatrix, Matrix.mul_apply] using sub_eq_zero.mp hentry

/-- Helper for Chap10 Example 10 35 24: evaluation of the polynomial matrix coordinates at a
standard projection matrix. -/
private noncomputable def rankProjectionMvPolynomialEval (k : Type u) [CommRing k] (n : ℕ)
    (r : Fin (n + 1)) :
    MvPolynomial (Fin n × Fin n) k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) fun ij ↦ rankProjectionMatrix k n r ij.1 ij.2

/-- Helper for Chap10 Example 10 35 24: the idempotent-matrix relations vanish on a standard
rank projection. -/
private theorem rankProjectionRelationEntry_eval_eq_zero (n : ℕ) (r : Fin (n + 1))
    (ij : Fin n × Fin n) :
    rankProjectionMvPolynomialEval k n r (idempotentMatrixRelationEntry k n ij) = 0 := by
  -- Evaluation turns the relation entry into the corresponding entry of `P ^ 2 - P`.
  have hentry :=
    congrArg (fun A : Matrix (Fin n) (Fin n) k ↦ A ij.1 ij.2)
      (rankProjectionMatrix_isIdempotent (k := k) n r).eq
  have hsub :
      (∑ x : Fin n,
          rankProjectionMatrix k n r ij.1 x * rankProjectionMatrix k n r x ij.2) -
        rankProjectionMatrix k n r ij.1 ij.2 = 0 := by
    simpa [Matrix.mul_apply] using sub_eq_zero.mpr hentry
  simpa [rankProjectionMvPolynomialEval, idempotentMatrixRelationEntry] using hsub

/-- Helper for Chap10 Example 10 35 24: the idempotent-matrix ideal is killed by evaluation at a
standard rank projection. -/
private theorem idempotentMatrixIdeal_le_rankProjectionEval_ker (n : ℕ) (r : Fin (n + 1)) :
    idempotentMatrixIdeal k n ≤ RingHom.ker (rankProjectionMvPolynomialEval k n r) := by
  -- It is enough to check the spanning relation entries, already handled entrywise.
  rw [idempotentMatrixIdeal]
  refine Ideal.span_le.mpr ?_
  rintro f ⟨ij, rfl⟩
  exact RingHom.mem_ker.mpr (rankProjectionRelationEntry_eval_eq_zero (k := k) n r ij)

/-- Helper for Chap10 Example 10 35 24: evaluation at the standard rank projection descends to
the idempotent-matrix coordinate ring. -/
private noncomputable def rankProjectionCoordinateEvalHom (k : Type u) [CommRing k] (n : ℕ)
    (r : Fin (n + 1)) :
    idempotentMatrixCoordinateRing k n →+* k :=
  Ideal.Quotient.lift (idempotentMatrixIdeal k n) (rankProjectionMvPolynomialEval k n r)
    (idempotentMatrixIdeal_le_rankProjectionEval_ker (k := k) n r)

/-- Helper for Chap10 Example 10 35 24: the descended evaluation hom sends a coordinate to the
corresponding entry of the standard projection. -/
private theorem rankProjectionCoordinateEvalHom_mk_X (n : ℕ) (r : Fin (n + 1))
    (ij : Fin n × Fin n) :
    rankProjectionCoordinateEvalHom k n r
      (Ideal.Quotient.mk (idempotentMatrixIdeal k n) (MvPolynomial.X ij)) =
        rankProjectionMatrix k n r ij.1 ij.2 := by
  -- The quotient lift computes by the original polynomial evaluation map on representatives.
  simp [rankProjectionCoordinateEvalHom, rankProjectionMvPolynomialEval]

/-- Helper for Chap10 Example 10 35 24: evaluating the universal polynomial matrix at a standard
projection gives that standard projection. -/
private theorem mvPolynomialX_map_rankProjectionEval (n : ℕ) (r : Fin (n + 1)) :
    (Matrix.mvPolynomialX (Fin n) (Fin n) k).map (rankProjectionMvPolynomialEval k n r) =
      rankProjectionMatrix k n r := by
  -- Matrix extensionality reduces the claim to the definition of `eval₂Hom` on variables.
  ext i j
  simp [rankProjectionMvPolynomialEval]

/-- Helper for Chap10 Example 10 35 24: the generic idempotent matrix specializes to the standard
projection under the standard projection point. -/
private theorem genericIdempotentMatrix_map_rankProjectionCoordinateEvalHom
    (n : ℕ) (r : Fin (n + 1)) :
    (genericIdempotentMatrix k n).map (rankProjectionCoordinateEvalHom k n r) =
      rankProjectionMatrix k n r := by
  -- The descended quotient evaluation agrees with the polynomial evaluation on each coordinate.
  ext i j
  simp [genericIdempotentMatrix, rankProjectionCoordinateEvalHom_mk_X]

end

section

variable {k : Type u} [Field k]

/-- Helper for Chap10 Example 10 35 24: each fixed-rank idempotent locus is closed in the
prime spectrum of the idempotent-matrix coordinate ring. -/
private theorem idempotentRankComponent_isClosed (n : ℕ) (r : Fin (n + 1)) :
    IsClosed (idempotentRankComponent k n r) := by
  -- The fixed-rank locus is defined as a zero locus.
  rw [idempotentRankComponent]
  exact PrimeSpectrum.isClosed_zeroLocus
    (idempotentRankComponentIdeal k n r : Set (idempotentMatrixCoordinateRing k n))

/-- Helper for Chap10 Example 10 35 24: the kernel of the standard projection evaluation is a
prime ideal. -/
private theorem rankProjectionCoordinateEvalHom_ker_isPrime (n : ℕ) (r : Fin (n + 1)) :
    (RingHom.ker (rankProjectionCoordinateEvalHom k n r)).IsPrime := by
  -- A homomorphism to a field has prime kernel.
  exact RingHom.ker_isPrime (rankProjectionCoordinateEvalHom k n r)

/-- Helper for Chap10 Example 10 35 24: the prime-spectrum point defined by evaluating the
generic idempotent matrix at the standard rank projection. -/
private noncomputable def rankProjectionPoint (k : Type u) [Field k] (n : ℕ)
    (r : Fin (n + 1)) :
    PrimeSpectrum (idempotentMatrixCoordinateRing k n) :=
  ⟨RingHom.ker (rankProjectionCoordinateEvalHom k n r),
    rankProjectionCoordinateEvalHom_ker_isPrime (k := k) n r⟩

/-- Helper for Chap10 Example 10 35 24: the standard rank-`r` point lies in the rank-`r`
component. -/
private theorem rankProjectionPoint_mem_rankComponent_self (n : ℕ) (r : Fin (n + 1)) :
    rankProjectionPoint k n r ∈ idempotentRankComponent k n r := by
  rw [idempotentRankComponent, PrimeSpectrum.mem_zeroLocus, rankProjectionPoint]
  change idempotentRankComponentIdeal k n r ≤
    RingHom.ker (rankProjectionCoordinateEvalHom k n r)
  rw [idempotentRankComponentIdeal]
  refine Ideal.span_le.mpr ?_
  rintro f ⟨i, rfl⟩
  change rankProjectionCoordinateEvalHom k n r
      (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
        ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
          MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) = 0
  -- Compare characteristic polynomials after evaluating the universal polynomial matrix.
  have hpoly :
      ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.map
          (rankProjectionMvPolynomialEval k n r)) =
        (rankProjectionMatrix k n r).charpoly := by
    rw [← Matrix.charpoly_map, mvPolynomialX_map_rankProjectionEval]
  have hcoeff :
      rankProjectionMvPolynomialEval k n r
          ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i) =
        (rankProjectionMatrix k n r).charpoly.coeff i := by
    simpa using congrArg (fun p : Polynomial k ↦ p.coeff i) hpoly
  have hconst :
      rankProjectionMvPolynomialEval k n r
        (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i)) =
          (rankProjectionMatrix k n r).charpoly.coeff i := by
    simp [rankProjectionMvPolynomialEval]
  simpa [rankProjectionCoordinateEvalHom, hcoeff, hconst]

/-- Helper for Example 10.35.24: reindexing a basis reindexes the corresponding matrix on both
rows and columns. -/
private theorem linearMap_toMatrix_reindex_eq_submatrix
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {V : Type*} [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) (e : ι ≃ ι') (f : V →ₗ[k] V) :
    LinearMap.toMatrix (b.reindex e) (b.reindex e) f =
      (LinearMap.toMatrix b b f).submatrix e.symm e.symm := by
  -- Transport both coordinates through the reindexed basis before comparing entries.
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.submatrix_apply]

/-- Helper for Example 10.35.24: on the unreindexed product basis, the projection onto the first
summand is the diagonal matrix with ones on the `Fin r` block and zeros on the complement. -/
private theorem prod_projection_toMatrix_eq_sum_diagonal
    {n : ℕ} {r : Fin (n + 1)} {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (b₁ : Module.Basis (Fin r) k V) (b₂ : Module.Basis (Fin (n - r)) k W) :
    LinearMap.toMatrix (b₁.prod b₂) (b₁.prod b₂)
      (LinearMap.prodMap (LinearMap.id : V →ₗ[k] V) (0 : W →ₗ[k] W)) =
        Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : k)) (fun _ : Fin (n - r) => 0)) := by
  -- Compute the projection matrix as a block diagonal matrix, then collapse the blocks.
  rw [LinearMap.toMatrix_prodMap, LinearMap.toMatrix_id]
  simpa [Matrix.diagonal_one, Matrix.diagonal_zero] using
    (Matrix.fromBlocks_diagonal (fun _ : Fin r => (1 : k)) (fun _ : Fin (n - r) => 0))

/-- Helper for Example 10.35.24: reindexing the `Sum`-indexed diagonal projection along
`Fin n ≃ Fin r ⊕ Fin (n - r)` produces `rankProjectionMatrix`. -/
private theorem sum_diagonal_submatrix_eq_rankProjection
    {n : ℕ} (r : Fin (n + 1)) :
    (Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : k)) (fun _ : Fin (n - r) => 0))).submatrix
        ((finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le))).symm)
        ((finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le))).symm) =
      rankProjectionMatrix k n r := by
  let e : Fin n ≃ Fin r ⊕ Fin (n - r) :=
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le))).symm
  let E : Fin r ⊕ Fin (n - r) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le))
  -- First remove the transport through the equivalence, leaving a diagonal comparison.
  change (Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : k)) (fun _ : Fin (n - r) => 0))).submatrix e e =
    rankProjectionMatrix k n r
  rw [show e = E.symm by rfl, Matrix.submatrix_diagonal_equiv, rankProjectionMatrix]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    -- Split according to whether the index lies in the first `r` coordinates or not.
    rcases lt_or_ge i.1 r.1 with hi | hi
    · have hei : E.symm i = Sum.inl ⟨i.1, hi⟩ := by
        apply E.injective
        simp [E]
      simp [Function.comp, hei, hi]
    · have hlt : i.1 - r.1 < n - r.1 := by
        omega
      have hei : E.symm i = Sum.inr ⟨i.1 - r.1, hlt⟩ := by
        apply E.injective
        ext
        simp [E]
        omega
      simp [Function.comp, hei, Nat.not_lt.mpr hi]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

/-- Helper for Example 10.35.24: the product-basis matrix of the standard projection on
`V × W` becomes `rankProjectionMatrix` after reindexing `Fin r ⊕ Fin (n - r)` to `Fin n`. -/
private theorem projection_matrix_in_reindexed_prod_basis_eq_rankProjection
    {n : ℕ} {r : Fin (n + 1)} {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (b₁ : Module.Basis (Fin r) k V) (b₂ : Module.Basis (Fin (n - r)) k W) :
    LinearMap.toMatrix
      ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le))))
      ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le))))
      (LinearMap.prodMap (LinearMap.id : V →ₗ[k] V) (0 : W →ₗ[k] W)) =
        rankProjectionMatrix k n r := by
  let e : Fin r ⊕ Fin (n - r) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le))
  -- Route correction: compute on the unreindexed product basis first, then reindex the matrix.
  calc
    LinearMap.toMatrix ((b₁.prod b₂).reindex e) ((b₁.prod b₂).reindex e)
        (LinearMap.prodMap (LinearMap.id : V →ₗ[k] V) (0 : W →ₗ[k] W))
        = (LinearMap.toMatrix (b₁.prod b₂) (b₁.prod b₂)
            (LinearMap.prodMap (LinearMap.id : V →ₗ[k] V) (0 : W →ₗ[k] W))).submatrix e.symm e.symm := by
            simpa [e] using
              linearMap_toMatrix_reindex_eq_submatrix (b := b₁.prod b₂) e
                (LinearMap.prodMap (LinearMap.id : V →ₗ[k] V) (0 : W →ₗ[k] W))
    _ = (Matrix.diagonal
          (Sum.elim (fun _ : Fin r => (1 : k)) (fun _ : Fin (n - r) => 0))).submatrix e.symm e.symm := by
          rw [prod_projection_toMatrix_eq_sum_diagonal]
    _ = rankProjectionMatrix k n r := by
          simpa [e] using sum_diagonal_submatrix_eq_rankProjection (k := k) r

/-- Example 10.35.24 (2): an idempotent matrix is conjugate to a
standard diagonal projection `diag(1, …, 1, 0, …, 0)`, indexed by its rank. -/
-- Proof sketch: every idempotent matrix is conjugate to some `rankProjectionMatrix n r`, so the
-- idempotent locus is stratified by rank. An idempotent matrix is diagonalizable with eigenvalues
-- in `{0, 1}`, hence is conjugate to some `rankProjectionMatrix n r`.
@[stacks 00GG]
theorem isIdempotentElem_iff_exists_isConj_rankProjectionMatrix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} :
    IsIdempotentElem A ↔ ∃ r : Fin (n + 1), IsConj (rankProjectionMatrix k n r) A :=
  by
    constructor
    · intro hA
      classical
      -- View an idempotent matrix as a projection onto its range along its kernel.
      have hAtoLin : IsIdempotentElem A.toLin' := by
        simpa [Matrix.toLin'_mul] using congrArg Matrix.toLin' hA.eq
      let hproj : LinearMap.IsProj (LinearMap.range A.toLin') A.toLin' :=
        LinearMap.IsIdempotentElem.isProj_range _ hAtoLin
      let r : Fin (n + 1) :=
        ⟨Module.finrank k (LinearMap.range A.toLin'),
          Nat.lt_succ_of_le <| by
            simpa using LinearMap.finrank_range_le A.toLin'⟩
      have hsum : r + Module.finrank k (LinearMap.ker A.toLin') = n := by
        simpa [r] using LinearMap.finrank_range_add_finrank_ker A.toLin'
      have hker :
          Module.finrank k (LinearMap.ker A.toLin') = n - r := by
        omega
      let b₁ : Module.Basis (Fin r) k (LinearMap.range A.toLin') :=
        Module.finBasisOfFinrankEq k (LinearMap.range A.toLin') (by rfl)
      let b₂ : Module.Basis (Fin (n - r)) k (LinearMap.ker A.toLin') :=
        Module.finBasisOfFinrankEq k (LinearMap.ker A.toLin') hker
      let e :
          (LinearMap.range A.toLin' × LinearMap.ker A.toLin') ≃ₗ[k] (Fin n → k) :=
        (LinearMap.range A.toLin').prodEquivOfIsCompl (LinearMap.ker A.toLin') hproj.isCompl
      let prodBasis :
          Module.Basis (Fin n) k (LinearMap.range A.toLin' × LinearMap.ker A.toLin') :=
        (b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_le)))
      let base : Module.Basis (Fin n) k (Fin n → k) := prodBasis.map e
      have hprojEq :
          A.toLin' = e.conj (LinearMap.prodMap (LinearMap.id : _ →ₗ[k] _) (0 : _ →ₗ[k] _)) := by
        simpa [e] using hproj.eq_conj_prodMap
      have hmatrix :
          LinearMap.toMatrix base base A.toLin' = rankProjectionMatrix k n r := by
        -- Route correction: transport the projection normal form through the chosen basis first,
        -- then use the explicit reindexing lemma instead of changing coordinates by hand.
        calc
          LinearMap.toMatrix base base A.toLin'
              = LinearMap.toMatrix base base (e.conj (LinearMap.prodMap (LinearMap.id : _ →ₗ[k] _) 0)) := by
                  exact congrArg (LinearMap.toMatrix base base) hprojEq
          _ = LinearMap.toMatrix prodBasis prodBasis
                (LinearMap.prodMap (LinearMap.id : _ →ₗ[k] _) (0 : _ →ₗ[k] _)) := by
                rw [LinearEquiv.conj_apply, LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
                ext i j
                simp [LinearMap.toMatrix_apply]
          _ = rankProjectionMatrix k n r := by
                exact projection_matrix_in_reindexed_prod_basis_eq_rankProjection (k := k) b₁ b₂
      let U : Matrix (Fin n) (Fin n) k := (Pi.basisFun k (Fin n)).toMatrix base
      let V : Matrix (Fin n) (Fin n) k := base.toMatrix (Pi.basisFun k (Fin n))
      have hchange : U * rankProjectionMatrix k n r * V = A := by
        -- Change from the adapted basis back to the standard basis.
        calc
          U * rankProjectionMatrix k n r * V
              = U * LinearMap.toMatrix base base A.toLin' * V := by rw [hmatrix]
          _ = LinearMap.toMatrix (Pi.basisFun k (Fin n)) (Pi.basisFun k (Fin n)) A.toLin' := by
            simpa [U, V] using
              (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
                (Pi.basisFun k (Fin n)) (base) (Pi.basisFun k (Fin n)) A.toLin')
          _ = A := by simp
      have hUV : U * V = 1 := by
        simpa [U, V] using
          (Module.Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun k (Fin n)) base)
      have hVU : V * U = 1 := by
        simpa [U, V] using
          (Module.Basis.toMatrix_mul_toMatrix_flip base (Pi.basisFun k (Fin n)))
      have hsemiconj : SemiconjBy U (rankProjectionMatrix k n r) A := by
        -- The basis-change matrix semiconjugates the standard projection to `A`.
        calc
          U * rankProjectionMatrix k n r = (U * rankProjectionMatrix k n r) * (V * U) := by
            rw [hVU, mul_one]
          _ = (U * rankProjectionMatrix k n r * V) * U := by simp [mul_assoc]
          _ = A * U := by rw [hchange]
      refine ⟨r, ⟨⟨U, V, hUV, hVU⟩, hsemiconj⟩⟩
    · rintro ⟨r, hconj⟩
      rcases hconj with ⟨u, hu⟩
      have hproj :
          IsIdempotentElem (rankProjectionMatrix k n r) := by
        -- The standard diagonal projection squares to itself entrywise.
        rw [rankProjectionMatrix, IsIdempotentElem, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases hij : i = j
        · subst hij
          by_cases hi : i.1 < r <;> simp [hi]
        · simp [Matrix.diagonal, hij]
      let U : Matrix (Fin n) (Fin n) k := u
      have hAeq : A = U * rankProjectionMatrix k n r * U⁻¹ := by
        have hu' := congrArg (fun X : Matrix (Fin n) (Fin n) k => X * U⁻¹) hu.eq
        simpa [U, mul_assoc, Units.val_inv_eq_inv_val] using hu'.symm
      rw [hAeq, IsIdempotentElem]
      calc
        (U * rankProjectionMatrix k n r * U⁻¹) * (U * rankProjectionMatrix k n r * U⁻¹)
            = U * (rankProjectionMatrix k n r * rankProjectionMatrix k n r) * U⁻¹ := by
                simp [mul_assoc]
        _ = U * rankProjectionMatrix k n r * U⁻¹ := by rw [hproj.eq]

/-- Helper for Chap10 Example 10 35 24: conjugate matrices over a field have the same
characteristic polynomial. -/
private theorem matrix_charpoly_eq_of_isConj {K : Type u} [Field K] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) K} (h : IsConj A B) :
    B.charpoly = A.charpoly := by
  rcases h with ⟨u, hu⟩
  let U : Matrix (Fin n) (Fin n) K := u
  -- Put conjugacy into the explicit unit-conjugation form used by the matrix charpoly API.
  have hB : B = U * A * U⁻¹ := by
    have hu' := congrArg (fun X : Matrix (Fin n) (Fin n) K => X * U⁻¹) hu.eq
    simpa [U, mul_assoc, Units.val_inv_eq_inv_val] using hu'.symm
  rw [hB]
  simpa [U, Units.val_inv_eq_inv_val] using Matrix.charpoly_units_conj u A

/-- Helper for Chap10 Example 10 35 24: two `n × n` characteristic polynomials are equal once
their coefficients below degree `n` agree. -/
private theorem matrix_charpoly_eq_of_coeff_fin {K : Type u} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K)
    (hcoeff : ∀ i : Fin n, A.charpoly.coeff i = B.charpoly.coeff i) :
    A.charpoly = B.charpoly := by
  -- The lower coefficients are hypotheses; monicity supplies coefficient `n`, and higher
  -- coefficients vanish by the characteristic-polynomial degree bound.
  apply Polynomial.ext
  intro m
  by_cases hm_lt : m < n
  · exact hcoeff ⟨m, hm_lt⟩
  · by_cases hm_eq : m = n
    · subst m
      calc
        A.charpoly.coeff n = 1 := by
          simpa [Matrix.charpoly_natDegree_eq_dim] using A.charpoly_monic.coeff_natDegree
        _ = B.charpoly.coeff n := by
          simpa [Matrix.charpoly_natDegree_eq_dim] using B.charpoly_monic.coeff_natDegree.symm
    · have hn_lt_m : n < m := by omega
      rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
      · simpa [Matrix.charpoly_natDegree_eq_dim] using hn_lt_m
      · simpa [Matrix.charpoly_natDegree_eq_dim] using hn_lt_m

/-- Helper for Chap10 Example 10 35 24: mapping a standard projection matrix maps its
characteristic polynomial coefficients. -/
private theorem rankProjectionMatrix_charpoly_coeff_map {K : Type u} [CommRing K] [Algebra k K] (n : ℕ)
    (r : Fin (n + 1)) (i : ℕ) :
    algebraMap k K ((rankProjectionMatrix k n r).charpoly.coeff i) =
      (rankProjectionMatrix K n r).charpoly.coeff i := by
  -- Matrix-map compatibility for characteristic polynomials reduces this to the diagonal entries.
  have hmatrix :
      (rankProjectionMatrix k n r).map (algebraMap k K) =
        rankProjectionMatrix K n r := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases ha : a.1 < r <;> simp [rankProjectionMatrix, ha]
    · simp [rankProjectionMatrix, Matrix.diagonal, hab]
  have hpoly :
      (rankProjectionMatrix k n r).charpoly.map (algebraMap k K) =
        (rankProjectionMatrix K n r).charpoly := by
    rw [← Matrix.charpoly_map, hmatrix]
  simpa using congrArg (fun p : Polynomial K ↦ p.coeff i) hpoly

/-- Helper for Chap10 Example 10 35 24: mapping a universal characteristic-polynomial
coefficient out of the quotient agrees with taking the characteristic polynomial after mapping the
generic idempotent matrix. -/
private theorem genericIdempotentMatrix_charpoly_coeff_map {S : Type u} [CommRing S] (n : ℕ)
    (f : idempotentMatrixCoordinateRing k n →+* S) (i : ℕ) :
    f (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
        ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) =
      ((genericIdempotentMatrix k n).map f).charpoly.coeff i := by
  -- First identify the coefficient in the quotient, then use `Matrix.charpoly_map`.
  have hquotPoly :
      (Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.map
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)) =
        (genericIdempotentMatrix k n).charpoly := by
    rw [← Matrix.charpoly_map]
    rfl
  have hquotCoeff :
      Ideal.Quotient.mk (idempotentMatrixIdeal k n)
          ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i) =
        (genericIdempotentMatrix k n).charpoly.coeff i := by
    simpa using congrArg (fun q : Polynomial (idempotentMatrixCoordinateRing k n) ↦ q.coeff i)
      hquotPoly
  have hmapPoly :
      (genericIdempotentMatrix k n).charpoly.map f =
        ((genericIdempotentMatrix k n).map f).charpoly := by
    rw [← Matrix.charpoly_map]
  calc
    f (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
        ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) =
        f ((genericIdempotentMatrix k n).charpoly.coeff i) := by
          rw [hquotCoeff]
    _ = ((genericIdempotentMatrix k n).charpoly.map f).coeff i := by
          simp
    _ = ((genericIdempotentMatrix k n).map f).charpoly.coeff i := by
          rw [hmapPoly]

/-- Helper for Chap10 Example 10 35 24: constants in the idempotent-matrix quotient map to
constants in a residue field. -/
private theorem algebraMap_residueField_quotient_mk_C (n : ℕ)
    (p : PrimeSpectrum (idempotentMatrixCoordinateRing k n)) (a : k) :
    (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
        (Ideal.Quotient.mk (idempotentMatrixIdeal k n) (MvPolynomial.C a)) =
      algebraMap k p.asIdeal.ResidueField a := by
  -- This is the scalar-tower computation for `k → coordinate ring → κ(p)`.
  rfl

/-- Helper for Chap10 Example 10 35 24: every point in the universal `GL_n` orbit maps into the
matching fixed-rank component. -/
private theorem idempotentOrbitParam_mem_rankComponent (n : ℕ) (r : Fin (n + 1))
    (q : PrimeSpectrum (generalLinearCoordinateRing k n)) :
    PrimeSpectrum.comap (idempotentOrbitParamHom k n r) q ∈ idempotentRankComponent k n r := by
  rw [idempotentRankComponent, PrimeSpectrum.mem_zeroLocus, idempotentRankComponentIdeal]
  refine Ideal.span_le.mpr ?_
  rintro f ⟨i, rfl⟩
  change idempotentOrbitParamHom k n r
      (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
        ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
          MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) ∈ q.asIdeal
  -- The image of each coefficient generator is zero because `U P_r U⁻¹` has the same
  -- characteristic polynomial as `P_r`.
  suffices
      idempotentOrbitParamHom k n r
        (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
          ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
            MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) = 0 by
    rw [this]
    exact q.asIdeal.zero_mem
  have horbitChar :
      (idempotentOrbitMatrix k n r).charpoly =
        (rankProjectionMatrix (generalLinearCoordinateRing k n) n r).charpoly := by
    -- Characteristic polynomials are invariant under conjugation by a unit.
    simpa [idempotentOrbitMatrix] using
      Matrix.charpoly_units_conj (genericGeneralLinearUnit k n)
        (rankProjectionMatrix (generalLinearCoordinateRing k n) n r)
  have horbitCoeff :
      (idempotentOrbitMatrix k n r).charpoly.coeff i =
        (rankProjectionMatrix (generalLinearCoordinateRing k n) n r).charpoly.coeff i :=
    congrArg (fun P : Polynomial (generalLinearCoordinateRing k n) ↦ P.coeff i) horbitChar
  have hleft :
      idempotentOrbitParamHom k n r
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) =
        (idempotentOrbitMatrix k n r).charpoly.coeff i := by
    calc
      idempotentOrbitParamHom k n r
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) =
          ((genericIdempotentMatrix k n).map
            (idempotentOrbitParamHom k n r)).charpoly.coeff i := by
            exact genericIdempotentMatrix_charpoly_coeff_map (k := k) n
              (idempotentOrbitParamHom k n r) i
      _ = (idempotentOrbitMatrix k n r).charpoly.coeff i := by
            rw [genericIdempotentMatrix_map_idempotentOrbitParamHom]
  have hright :
      idempotentOrbitParamHom k n r
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) =
        algebraMap k (generalLinearCoordinateRing k n)
          ((rankProjectionMatrix k n r).charpoly.coeff i) := by
    simp [idempotentOrbitParamHom, idempotentOrbitMvPolynomialEval]
  have hprojectionCoeff :
      algebraMap k (generalLinearCoordinateRing k n)
          ((rankProjectionMatrix k n r).charpoly.coeff i) =
        (rankProjectionMatrix (generalLinearCoordinateRing k n) n r).charpoly.coeff i :=
    rankProjectionMatrix_charpoly_coeff_map (k := k) n r i
  calc
    idempotentOrbitParamHom k n r
        (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
          ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
            MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) =
        idempotentOrbitParamHom k n r
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) -
          idempotentOrbitParamHom k n r
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) := by
          exact map_sub (idempotentOrbitParamHom k n r)
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i))
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i)))
    _ =
        (idempotentOrbitMatrix k n r).charpoly.coeff i -
          algebraMap k (generalLinearCoordinateRing k n)
            ((rankProjectionMatrix k n r).charpoly.coeff i) := by
          rw [hleft, hright]
    _ =
        (idempotentOrbitMatrix k n r).charpoly.coeff i -
          (rankProjectionMatrix (generalLinearCoordinateRing k n) n r).charpoly.coeff i := by
          rw [hprojectionCoeff]
    _ = 0 := by
          exact sub_eq_zero.mpr horbitCoeff

/-- Helper for Chap10 Example 10 35 24: residue-field characteristic-polynomial equality implies
membership in the corresponding fixed-rank component. -/
private theorem mem_idempotentRankComponent_of_residueField_charpoly_eq (n : ℕ)
    (p : PrimeSpectrum (idempotentMatrixCoordinateRing k n)) (r : Fin (n + 1))
    (hchar :
      ((genericIdempotentMatrix k n).map
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly =
        (rankProjectionMatrix p.asIdeal.ResidueField n r).charpoly) :
    p ∈ idempotentRankComponent k n r := by
  rw [idempotentRankComponent, PrimeSpectrum.mem_zeroLocus, idempotentRankComponentIdeal]
  refine Ideal.span_le.mpr ?_
  rintro f ⟨i, rfl⟩
  change
    Ideal.Quotient.mk (idempotentMatrixIdeal k n)
      ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
        MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i)) ∈ p.asIdeal
  rw [← Ideal.algebraMap_residueField_eq_zero (I := p.asIdeal)]
  have hprojectionCoeff :
      algebraMap k p.asIdeal.ResidueField ((rankProjectionMatrix k n r).charpoly.coeff i) =
        (rankProjectionMatrix p.asIdeal.ResidueField n r).charpoly.coeff i :=
    rankProjectionMatrix_charpoly_coeff_map (k := k) n r i
  have hleft :
      (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) =
        ((genericIdempotentMatrix k n).map
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly.coeff i :=
    genericIdempotentMatrix_charpoly_coeff_map (k := k) n
      (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField) i
  have hright :
      (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) =
        algebraMap k p.asIdeal.ResidueField ((rankProjectionMatrix k n r).charpoly.coeff i) :=
    algebraMap_residueField_quotient_mk_C (k := k) n p
      ((rankProjectionMatrix k n r).charpoly.coeff i)
  have hcharCoeff :=
    congrArg (fun q : Polynomial p.asIdeal.ResidueField ↦ q.coeff i) hchar
  calc
    (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
        (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
          ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
            MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) =
        (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i) -
            Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) := by
          rfl
    _ =
        (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) -
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) := by
          rw [map_sub]
    _ =
        ((genericIdempotentMatrix k n).map
            (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly.coeff i -
          algebraMap k p.asIdeal.ResidueField
            ((rankProjectionMatrix k n r).charpoly.coeff i) := by
          rw [hleft, hright]
    _ =
        ((genericIdempotentMatrix k n).map
            (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly.coeff i -
          (rankProjectionMatrix p.asIdeal.ResidueField n r).charpoly.coeff i := by
          rw [hprojectionCoeff]
    _ = 0 := by
          exact sub_eq_zero.mpr hcharCoeff

/-- Helper for Chap10 Example 10 35 24: membership in a fixed-rank component recovers the
residue-field characteristic polynomial of that rank. -/
private theorem residueField_charpoly_eq_of_mem_idempotentRankComponent (n : ℕ)
    (p : PrimeSpectrum (idempotentMatrixCoordinateRing k n)) (r : Fin (n + 1))
    (hmem : p ∈ idempotentRankComponent k n r) :
    ((genericIdempotentMatrix k n).map
        (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly =
      (rankProjectionMatrix p.asIdeal.ResidueField n r).charpoly := by
  rw [idempotentRankComponent, PrimeSpectrum.mem_zeroLocus] at hmem
  -- The zero-locus condition says each characteristic-polynomial coefficient generator
  -- vanishes in the residue field at `p`.
  refine matrix_charpoly_eq_of_coeff_fin _ _ ?_
  intro i
  have hgen :
      Ideal.Quotient.mk (idempotentMatrixIdeal k n)
        ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
          MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i)) ∈
        p.asIdeal := by
    apply hmem
    rw [idempotentRankComponentIdeal]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hzero :
      (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
        (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
          ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
            MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) = 0 := by
    rwa [Ideal.algebraMap_residueField_eq_zero (I := p.asIdeal)]
  have hleft :
      (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) =
        ((genericIdempotentMatrix k n).map
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly.coeff i :=
    genericIdempotentMatrix_charpoly_coeff_map (k := k) n
      (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField) i
  have hright :
      (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) =
        algebraMap k p.asIdeal.ResidueField ((rankProjectionMatrix k n r).charpoly.coeff i) :=
    algebraMap_residueField_quotient_mk_C (k := k) n p
      ((rankProjectionMatrix k n r).charpoly.coeff i)
  have hprojectionCoeff :
      algebraMap k p.asIdeal.ResidueField ((rankProjectionMatrix k n r).charpoly.coeff i) =
        (rankProjectionMatrix p.asIdeal.ResidueField n r).charpoly.coeff i :=
    rankProjectionMatrix_charpoly_coeff_map (k := k) n r i
  have hsub :
      ((genericIdempotentMatrix k n).map
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly.coeff i -
        (rankProjectionMatrix p.asIdeal.ResidueField n r).charpoly.coeff i = 0 := by
    calc
      ((genericIdempotentMatrix k n).map
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)).charpoly.coeff i -
        (rankProjectionMatrix p.asIdeal.ResidueField n r).charpoly.coeff i =
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
              (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
                ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) -
            algebraMap k p.asIdeal.ResidueField
              ((rankProjectionMatrix k n r).charpoly.coeff i) := by
            rw [hleft, hprojectionCoeff]
      _ =
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
              (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
                ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i)) -
            (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
              (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
                (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) := by
            rw [hright]
      _ =
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
                MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i))) := by
            exact
              (map_sub (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)
                (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
                  ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i))
                (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
                  (MvPolynomial.C ((rankProjectionMatrix k n r).charpoly.coeff i)))).symm
      _ = 0 := hzero
  exact sub_eq_zero.mp hsub

/-- Helper for Chap10 Example 10 35 24: the standard projection has characteristic polynomial
`(X - 1)^r X^(n-r)`. -/
private theorem rankProjectionMatrix_charpoly_eq {K : Type u} [Field K] (n : ℕ)
    (r : Fin (n + 1)) :
    (rankProjectionMatrix K n r).charpoly =
      (Polynomial.X - Polynomial.C (1 : K)) ^ (r : ℕ) *
        Polynomial.X ^ (n - (r : ℕ)) := by
  classical
  have hfiltercard :
      (Finset.univ.filter fun i : Fin n => i.1 < r).card = r := by
    calc
      (Finset.univ.filter fun i : Fin n => i.1 < r).card =
          Fintype.card {x : Fin n // x.1 < r} := by
        symm
        exact Fintype.card_ofFinset (p := {i : Fin n | i.1 < r})
          (Finset.univ.filter fun i : Fin n => i.1 < r) (by
            intro x
            simp)
      _ = r := by
        simpa using Fintype.card_fin_lt_of_le (n := n) (m := r) r.is_le
  have hfilterNotCard :
      (Finset.univ.filter fun i : Fin n => ¬ i.1 < r).card = n - (r : ℕ) := by
    have hsplit :=
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (p := fun i : Fin n => i.1 < r)
    have hrle : (r : ℕ) ≤ n := r.is_le
    have hsplit' :
        (r : ℕ) + (Finset.univ.filter fun i : Fin n => ¬ i.1 < r).card = n := by
      simpa [hfiltercard] using hsplit
    omega
  have hleft :
      ((Finset.univ.filter (fun i : Fin n => i.1 < r)).prod
          fun i ↦ (Polynomial.X - Polynomial.C (if i.1 < r then (1 : K) else 0))) =
        (Polynomial.X - Polynomial.C (1 : K)) ^ (r : ℕ) := by
    calc
      ((Finset.univ.filter (fun i : Fin n => i.1 < r)).prod
          fun i ↦ (Polynomial.X - Polynomial.C (if i.1 < r then (1 : K) else 0))) =
          (Finset.univ.filter (fun i : Fin n => i.1 < r)).prod
            (fun _i ↦ (Polynomial.X - Polynomial.C (1 : K))) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        simp at hi
        simp [hi]
      _ = (Polynomial.X - Polynomial.C (1 : K)) ^ (r : ℕ) := by
        rw [Finset.prod_const, hfiltercard]
  have hright :
      ((Finset.univ.filter (fun i : Fin n => ¬ i.1 < r)).prod
          fun i ↦ (Polynomial.X - Polynomial.C (if i.1 < r then (1 : K) else 0))) =
        Polynomial.X ^ (n - (r : ℕ)) := by
    calc
      ((Finset.univ.filter (fun i : Fin n => ¬ i.1 < r)).prod
          fun i ↦ (Polynomial.X - Polynomial.C (if i.1 < r then (1 : K) else 0))) =
          (Finset.univ.filter (fun i : Fin n => ¬ i.1 < r)).prod
            (fun _i ↦ (Polynomial.X : K[X])) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        simp at hi
        simp [hi]
      _ = Polynomial.X ^ (n - (r : ℕ)) := by
        rw [Finset.prod_const, hfilterNotCard]
  rw [rankProjectionMatrix, Matrix.charpoly_diagonal]
  calc
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (if i.1 < r then (1 : K) else 0))) =
        ((Finset.univ.filter (fun i : Fin n => i.1 < r)).prod
            fun i ↦ (Polynomial.X - Polynomial.C (if i.1 < r then (1 : K) else 0))) *
          ((Finset.univ.filter (fun i : Fin n => ¬ i.1 < r)).prod
            fun i ↦ (Polynomial.X - Polynomial.C (if i.1 < r then (1 : K) else 0))) := by
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ = (Polynomial.X - Polynomial.C (1 : K)) ^ (r : ℕ) *
          Polynomial.X ^ (n - (r : ℕ)) := by
      rw [hleft, hright]

/-- Helper for Chap10 Example 10 35 24: the root multiplicity at `1` of the standard projection
characteristic polynomial is its rank. -/
private theorem rankProjectionMatrix_rootMultiplicity_one {K : Type u} [Field K] (n : ℕ)
    (r : Fin (n + 1)) :
    ((rankProjectionMatrix K n r).charpoly).rootMultiplicity (1 : K) = (r : ℕ) := by
  -- The factor `X^(n-r)` does not vanish at `1`, so all multiplicity comes from `(X - 1)^r`.
  rw [rankProjectionMatrix_charpoly_eq, mul_comm]
  have hXpow_ne : (Polynomial.X ^ (n - (r : ℕ)) : K[X]) ≠ 0 :=
    (monic_X_pow (R := K) (n - (r : ℕ))).ne_zero
  rw [rootMultiplicity_mul_X_sub_C_pow (a := (1 : K)) hXpow_ne]
  have hnotroot : ¬ IsRoot (Polynomial.X ^ (n - (r : ℕ)) : K[X]) (1 : K) := by
    simp [IsRoot]
  rw [rootMultiplicity_eq_zero hnotroot, zero_add]

/-- Helper for Chap10 Example 10 35 24: standard projection characteristic polynomials determine
the rank. -/
private theorem rankProjectionMatrix_charpoly_injective {K : Type u} [Field K] (n : ℕ) :
    Function.Injective fun r : Fin (n + 1) ↦ (rankProjectionMatrix K n r).charpoly := by
  intro r s hchar
  -- Compare root multiplicities at `1` to recover the rank index.
  have hmult :=
    congrArg (fun q : Polynomial K ↦ q.rootMultiplicity (1 : K)) hchar
  have hr :
      (fun q : Polynomial K ↦ q.rootMultiplicity (1 : K))
          ((fun r : Fin (n + 1) ↦ (rankProjectionMatrix K n r).charpoly) r) =
        (r : ℕ) :=
    rankProjectionMatrix_rootMultiplicity_one (K := K) n r
  have hs :
      (fun q : Polynomial K ↦ q.rootMultiplicity (1 : K))
          ((fun r : Fin (n + 1) ↦ (rankProjectionMatrix K n r).charpoly) s) =
        (s : ℕ) :=
    rankProjectionMatrix_rootMultiplicity_one (K := K) n s
  rw [hr, hs] at hmult
  exact Fin.ext hmult

/-- Helper for Chap10 Example 10 35 24: a standard projection point lies on exactly its matching
rank component. -/
private theorem rankProjectionPoint_mem_rankComponent_iff (n : ℕ) (r s : Fin (n + 1)) :
    rankProjectionPoint k n r ∈ idempotentRankComponent k n s ↔ r = s := by
  constructor
  · intro hmem
    rw [idempotentRankComponent, PrimeSpectrum.mem_zeroLocus] at hmem
    have hcoeff :
        ∀ i : Fin n,
          (rankProjectionMatrix k n r).charpoly.coeff i =
            (rankProjectionMatrix k n s).charpoly.coeff i := by
      intro i
      have hgen :
          Ideal.Quotient.mk (idempotentMatrixIdeal k n)
            ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
              MvPolynomial.C ((rankProjectionMatrix k n s).charpoly.coeff i)) ∈
            (rankProjectionPoint k n r).asIdeal := by
        apply hmem
        rw [idempotentRankComponentIdeal]
        exact Ideal.subset_span ⟨i, rfl⟩
      have hzero :
          rankProjectionCoordinateEvalHom k n r
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n)
              ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i -
                MvPolynomial.C ((rankProjectionMatrix k n s).charpoly.coeff i))) = 0 := by
        simpa [rankProjectionPoint] using RingHom.mem_ker.mp hgen
      have hpoly :
          ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.map
              (rankProjectionMvPolynomialEval k n r)) =
            (rankProjectionMatrix k n r).charpoly := by
        rw [← Matrix.charpoly_map, mvPolynomialX_map_rankProjectionEval]
      have hleft :
          rankProjectionMvPolynomialEval k n r
              ((Matrix.mvPolynomialX (Fin n) (Fin n) k).charpoly.coeff i) =
            (rankProjectionMatrix k n r).charpoly.coeff i := by
        simpa using congrArg (fun q : Polynomial k ↦ q.coeff i) hpoly
      have hright :
          rankProjectionMvPolynomialEval k n r
              (MvPolynomial.C ((rankProjectionMatrix k n s).charpoly.coeff i)) =
            (rankProjectionMatrix k n s).charpoly.coeff i := by
        simp [rankProjectionMvPolynomialEval]
      have hsub :
          (rankProjectionMatrix k n r).charpoly.coeff i -
              (rankProjectionMatrix k n s).charpoly.coeff i = 0 := by
        simpa [rankProjectionCoordinateEvalHom, hleft, hright] using hzero
      exact sub_eq_zero.mp hsub
    exact rankProjectionMatrix_charpoly_injective (K := k) n
      (matrix_charpoly_eq_of_coeff_fin (rankProjectionMatrix k n r)
        (rankProjectionMatrix k n s) hcoeff)
  · intro hrs
    subst hrs
    -- The reverse implication is the already-constructed standard point in its own component.
    exact rankProjectionPoint_mem_rankComponent_self (k := k) n r

/-- Helper for Chap10 Example 10 35 24: the fixed-rank idempotent loci cover the idempotent
matrix spectrum. -/
private theorem idempotentRankComponents_cover (n : ℕ) :
    ⋃₀ Set.range (idempotentRankComponent k n) =
      (Set.univ : Set (PrimeSpectrum (idempotentMatrixCoordinateRing k n))) := by
  ext p
  constructor
  · intro _hp
    trivial
  · intro _hp
    let K := p.asIdeal.ResidueField
    let A : Matrix (Fin n) (Fin n) K :=
      (genericIdempotentMatrix k n).map
        (algebraMap (idempotentMatrixCoordinateRing k n) K)
    have hA : IsIdempotentElem A := by
      rw [IsIdempotentElem]
      -- The universal idempotency relation remains true after specialization to the residue field.
      simpa [A, Matrix.map_mul] using
        congrArg
          (fun M : Matrix (Fin n) (Fin n) (idempotentMatrixCoordinateRing k n) ↦
            M.map (algebraMap (idempotentMatrixCoordinateRing k n) K))
          (genericIdempotentMatrix_isIdempotent (k := k) n).eq
    obtain ⟨r, hconj⟩ :=
      (isIdempotentElem_iff_exists_isConj_rankProjectionMatrix (k := K) (A := A)).mp hA
    refine Set.mem_sUnion.mpr ?_
    refine ⟨idempotentRankComponent k n r, ⟨r, rfl⟩, ?_⟩
    -- Route correction: use the residue-field characteristic polynomial directly, avoiding the
    -- earlier quotient-to-fraction-field transport.
    -- Conjugacy identifies the residue-field characteristic polynomial with a standard one.
    exact mem_idempotentRankComponent_of_residueField_charpoly_eq (k := k) n p r
      (by
        simpa [A] using matrix_charpoly_eq_of_isConj hconj)

/-- Helper for Chap10 Example 10 35 24: the prime spectrum of the generic general-linear
coordinate ring is irreducible. -/
private theorem generalLinearPrimeSpectrum_isIrreducible (n : ℕ) :
    IsIrreducible (Set.univ : Set (PrimeSpectrum (generalLinearCoordinateRing k n))) := by
  have hdet :
      (Matrix.mvPolynomialX (Fin n) (Fin n) k).det ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin n) k
  have hpow :
      Submonoid.powers ((Matrix.mvPolynomialX (Fin n) (Fin n) k).det) ≤
        nonZeroDivisors (MvPolynomial (Fin n × Fin n) k) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hdet
  letI : IsDomain (generalLinearCoordinateRing k n) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (generalLinearCoordinateRing k n) hpow
  -- The localized coordinate ring is a domain, hence its prime spectrum is irreducible.
  exact IrreducibleSpace.isIrreducible_univ
    (PrimeSpectrum (generalLinearCoordinateRing k n))

/-- Helper for Chap10 Example 10 35 24: evaluating polynomial matrix coordinates at a chosen
invertible matrix. -/
private noncomputable def conjugatingMatrixMvPolynomialEval {K : Type u} [CommRing K]
    [Algebra k K] (n : ℕ) (u : Matrix.GeneralLinearGroup (Fin n) K) :
    MvPolynomial (Fin n × Fin n) k →+* K :=
  MvPolynomial.eval₂Hom (algebraMap k K)
    fun ij ↦ (u : Matrix (Fin n) (Fin n) K) ij.1 ij.2

/-- Helper for Chap10 Example 10 35 24: the polynomial generic matrix evaluates to the chosen
invertible matrix. -/
private theorem conjugatingMatrixEval_mvPolynomialX {K : Type u} [CommRing K] [Algebra k K]
    (n : ℕ) (u : Matrix.GeneralLinearGroup (Fin n) K) :
    (Matrix.mvPolynomialX (Fin n) (Fin n) k).map
        (conjugatingMatrixMvPolynomialEval (k := k) n u) =
      (u : Matrix (Fin n) (Fin n) K) := by
  -- The coordinate evaluation sends each universal variable to the corresponding entry of `u`.
  simpa [conjugatingMatrixMvPolynomialEval] using
    Matrix.mvPolynomialX_map_eval₂ (algebraMap k K)
      (u : Matrix (Fin n) (Fin n) K)

/-- Helper for Chap10 Example 10 35 24: the generic determinant evaluates to a unit at an
invertible matrix. -/
private theorem conjugatingMatrixEval_det_isUnit {K : Type u} [CommRing K] [Algebra k K]
    (n : ℕ) (u : Matrix.GeneralLinearGroup (Fin n) K) :
    IsUnit ((conjugatingMatrixMvPolynomialEval (k := k) n u)
      ((Matrix.mvPolynomialX (Fin n) (Fin n) k).det)) := by
  -- Determinants commute with coordinate evaluation, and the chosen matrix is a unit.
  have hmatrix :
      (conjugatingMatrixMvPolynomialEval (k := k) n u).mapMatrix
          (Matrix.mvPolynomialX (Fin n) (Fin n) k) =
        (u : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp [conjugatingMatrixMvPolynomialEval, Matrix.mvPolynomialX_apply]
  rw [RingHom.map_det, hmatrix]
  exact Matrix.isUnits_det_units u

/-- Helper for Chap10 Example 10 35 24: evaluation of the determinant localization at a chosen
invertible residue-field matrix. -/
private noncomputable def residueFieldGeneralLinearEval {K : Type u} [CommRing K]
    [Algebra k K] (n : ℕ) (u : Matrix.GeneralLinearGroup (Fin n) K) :
    generalLinearCoordinateRing k n →+* K :=
  Localization.awayLift (conjugatingMatrixMvPolynomialEval (k := k) n u)
    ((Matrix.mvPolynomialX (Fin n) (Fin n) k).det)
    (conjugatingMatrixEval_det_isUnit (k := k) n u)

/-- Helper for Chap10 Example 10 35 24: the localized generic `GL_n` matrix evaluates to the
chosen invertible matrix. -/
private theorem genericGeneralLinearUnit_map_residueFieldGeneralLinearEval {K : Type u}
    [CommRing K] [Algebra k K] (n : ℕ) (u : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix.GeneralLinearGroup.map (residueFieldGeneralLinearEval (k := k) n u)
        (genericGeneralLinearUnit k n) =
      u := by
  -- It is enough to compare entries; the localization lift computes on base variables.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [genericGeneralLinearUnit, genericGeneralLinearMatrix, residueFieldGeneralLinearEval,
    conjugatingMatrixMvPolynomialEval, Matrix.mvPolynomialX_apply]

/-- Helper for Chap10 Example 10 35 24: mapping a standard projection matrix along a ring
homomorphism preserves its rank-indexed diagonal form. -/
private theorem rankProjectionMatrix_map {K L : Type u} [CommRing K] [CommRing L]
    (f : K →+* L) (n : ℕ) (r : Fin (n + 1)) :
    (rankProjectionMatrix K n r).map f = rankProjectionMatrix L n r := by
  -- The diagonal entries are only `0` and `1`, both preserved by every ring homomorphism.
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i.1 < r <;> simp [rankProjectionMatrix, hi]
  · simp [rankProjectionMatrix, Matrix.diagonal, hij]

/-- Helper for Chap10 Example 10 35 24: evaluating the universal orbit matrix at a chosen unit
gives the corresponding conjugate of the standard projection. -/
private theorem idempotentOrbitMatrix_map_residueFieldGeneralLinearEval {K : Type u}
    [Field K] [Algebra k K] (n : ℕ) (r : Fin (n + 1))
    (u : Matrix.GeneralLinearGroup (Fin n) K) :
    (idempotentOrbitMatrix k n r).map (residueFieldGeneralLinearEval (k := k) n u) =
      (u : Matrix (Fin n) (Fin n) K) *
        rankProjectionMatrix K n r *
        ((u⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
  -- The previous helper identifies the generic unit after evaluation; multiplication and inverse
  -- are then transported by the `GL_n` map functoriality.
  have hU :=
    genericGeneralLinearUnit_map_residueFieldGeneralLinearEval (k := k) n u
  let ψ : generalLinearCoordinateRing k n →+* K :=
    residueFieldGeneralLinearEval (k := k) n u
  have hUmat :
      ((genericGeneralLinearUnit k n :
          Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n)).map ψ) =
        (u : Matrix (Fin n) (Fin n) K) := by
    -- The underlying matrix of `GL_n(ψ)(U)` is obtained by mapping entries of `U`.
    ext i j
    simpa [ψ] using congrArg
      (fun g : Matrix.GeneralLinearGroup (Fin n) K ↦
        (g : Matrix (Fin n) (Fin n) K) i j) hU
  have hUinvMat :
      ((((genericGeneralLinearUnit k n)⁻¹ :
          Matrix.GeneralLinearGroup (Fin n) (generalLinearCoordinateRing k n)) :
            Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n)).map ψ) =
        ((u⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
    -- The same entrywise comparison applies to the inverse, using functoriality of `GL_n`.
    ext i j
    have hinv :
        Matrix.GeneralLinearGroup.map ψ ((genericGeneralLinearUnit k n)⁻¹) = u⁻¹ := by
      rw [Matrix.GeneralLinearGroup.map_inv, hU]
    change
      ((Matrix.GeneralLinearGroup.map ψ ((genericGeneralLinearUnit k n)⁻¹) :
        Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        ((u⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j
    rw [hinv]
  calc
    (idempotentOrbitMatrix k n r).map (residueFieldGeneralLinearEval (k := k) n u) =
        ((genericGeneralLinearUnit k n :
            Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n))).map
            (residueFieldGeneralLinearEval (k := k) n u) *
          (rankProjectionMatrix (generalLinearCoordinateRing k n) n r).map
            (residueFieldGeneralLinearEval (k := k) n u) *
          (((genericGeneralLinearUnit k n)⁻¹ :
            Matrix.GeneralLinearGroup (Fin n) (generalLinearCoordinateRing k n)) :
              Matrix (Fin n) (Fin n) (generalLinearCoordinateRing k n)).map
            (residueFieldGeneralLinearEval (k := k) n u) := by
          simp [idempotentOrbitMatrix, Matrix.map_mul]
    _ =
        (u : Matrix (Fin n) (Fin n) K) *
          rankProjectionMatrix K n r *
          ((u⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by
          rw [show residueFieldGeneralLinearEval (k := k) n u = ψ by rfl,
            hUmat, hUinvMat, rankProjectionMatrix_map]

/-- Helper for Chap10 Example 10 35 24: a point of a fixed-rank component gives a residue-field
matrix conjugate to the matching standard projection. -/
private theorem residueField_generic_isConj_rankProjection_of_mem (n : ℕ)
    (p : PrimeSpectrum (idempotentMatrixCoordinateRing k n)) (r : Fin (n + 1))
    (hmem : p ∈ idempotentRankComponent k n r) :
    IsConj (rankProjectionMatrix p.asIdeal.ResidueField n r)
      ((genericIdempotentMatrix k n).map
        (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField)) := by
  let K := p.asIdeal.ResidueField
  let A : Matrix (Fin n) (Fin n) K :=
    (genericIdempotentMatrix k n).map
      (algebraMap (idempotentMatrixCoordinateRing k n) K)
  have hA : IsIdempotentElem A := by
    rw [IsIdempotentElem]
    -- Specialize the universal idempotency equation to the residue field.
    simpa [A, Matrix.map_mul] using
      congrArg
        (fun M : Matrix (Fin n) (Fin n) (idempotentMatrixCoordinateRing k n) ↦
          M.map (algebraMap (idempotentMatrixCoordinateRing k n) K))
        (genericIdempotentMatrix_isIdempotent (k := k) n).eq
  obtain ⟨s, hs⟩ :=
    (isIdempotentElem_iff_exists_isConj_rankProjectionMatrix (k := K) (A := A)).mp hA
  have htarget :
      A.charpoly = (rankProjectionMatrix K n r).charpoly := by
    simpa [A, K] using
      residueField_charpoly_eq_of_mem_idempotentRankComponent (k := k) n p r hmem
  have hchosen :
      A.charpoly = (rankProjectionMatrix K n s).charpoly := by
    simpa [A, K] using matrix_charpoly_eq_of_isConj hs
  have hsr : s = r :=
    rankProjectionMatrix_charpoly_injective (K := K) n (hchosen.symm.trans htarget)
  -- Characteristic polynomials determine the rank index, so the chosen conjugacy has rank `r`.
  subst hsr
  simpa [A, K] using hs

/-- Helper for Chap10 Example 10 35 24: the residue-field `GL_n` evaluation composed with the
orbit parametrization is the residue-field specialization map. -/
private theorem residueFieldGeneralLinearEval_comp_idempotentOrbitParamHom (n : ℕ)
    (p : PrimeSpectrum (idempotentMatrixCoordinateRing k n)) (r : Fin (n + 1))
    (u : Matrix.GeneralLinearGroup (Fin n) p.asIdeal.ResidueField)
    (hu :
      (genericIdempotentMatrix k n).map
          (algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField) =
        (u : Matrix (Fin n) (Fin n) p.asIdeal.ResidueField) *
          rankProjectionMatrix p.asIdeal.ResidueField n r *
          ((u⁻¹ : Matrix.GeneralLinearGroup (Fin n) p.asIdeal.ResidueField) :
            Matrix (Fin n) (Fin n) p.asIdeal.ResidueField)) :
    (residueFieldGeneralLinearEval (k := k) n u).comp (idempotentOrbitParamHom k n r) =
      algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField := by
  -- Compare the two maps out of the quotient on constants and matrix-coordinate variables.
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    calc
      ((residueFieldGeneralLinearEval (k := k) n u).comp
            (idempotentOrbitParamHom k n r)).comp
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)) (MvPolynomial.C a) =
          (residueFieldGeneralLinearEval (k := k) n u)
            ((algebraMap k (generalLinearCoordinateRing k n)) a) := by
            simp [idempotentOrbitParamHom, idempotentOrbitMvPolynomialEval]
      _ =
          (residueFieldGeneralLinearEval (k := k) n u)
            ((algebraMap (MvPolynomial (Fin n × Fin n) k)
              (generalLinearCoordinateRing k n)) (MvPolynomial.C a)) := by
            rfl
      _ =
          (conjugatingMatrixMvPolynomialEval (k := k) n u) (MvPolynomial.C a) := by
            simp [residueFieldGeneralLinearEval]
      _ = algebraMap k p.asIdeal.ResidueField a := by
            simp [conjugatingMatrixMvPolynomialEval]
      _ =
          ((algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField).comp
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n))) (MvPolynomial.C a) := by
            rfl
  · intro ij
    have horbit :
        ((idempotentOrbitMatrix k n r).map
            (residueFieldGeneralLinearEval (k := k) n u)) ij.1 ij.2 =
          ((genericIdempotentMatrix k n).map
            (algebraMap (idempotentMatrixCoordinateRing k n)
              p.asIdeal.ResidueField)) ij.1 ij.2 := by
      rw [idempotentOrbitMatrix_map_residueFieldGeneralLinearEval, ← hu]
    calc
      ((residueFieldGeneralLinearEval (k := k) n u).comp
            (idempotentOrbitParamHom k n r)).comp
          (Ideal.Quotient.mk (idempotentMatrixIdeal k n)) (MvPolynomial.X ij) =
          (residueFieldGeneralLinearEval (k := k) n u)
            (idempotentOrbitMatrix k n r ij.1 ij.2) := by
            simp [idempotentOrbitParamHom_mk_X]
      _ =
          ((genericIdempotentMatrix k n).map
            (algebraMap (idempotentMatrixCoordinateRing k n)
              p.asIdeal.ResidueField)) ij.1 ij.2 := by
            exact horbit
      _ =
          ((algebraMap (idempotentMatrixCoordinateRing k n) p.asIdeal.ResidueField).comp
            (Ideal.Quotient.mk (idempotentMatrixIdeal k n))) (MvPolynomial.X ij) := by
            simp [genericIdempotentMatrix]

/-- Chap10 Example 10 35 24: every point of the fixed-rank component lifts to the
universal `GL_n` orbit parameter space. -/
private theorem idempotentOrbitParam_surjectiveToRankComponent (n : ℕ) (r : Fin (n + 1)) :
    ∀ p : PrimeSpectrum (idempotentMatrixCoordinateRing k n),
      p ∈ idempotentRankComponent k n r →
        ∃ q : PrimeSpectrum (generalLinearCoordinateRing k n),
          PrimeSpectrum.comap (idempotentOrbitParamHom k n r) q = p := by
  intro p hp
  let K := p.asIdeal.ResidueField
  let α : idempotentMatrixCoordinateRing k n →+* K := algebraMap _ _
  obtain ⟨u, hu⟩ :=
    residueField_generic_isConj_rankProjection_of_mem (k := k) n p r hp
  let ψ : generalLinearCoordinateRing k n →+* K :=
    residueFieldGeneralLinearEval (k := k) n u
  let q : PrimeSpectrum (generalLinearCoordinateRing k n) :=
    ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  refine ⟨q, ?_⟩
  have huMatrix :
      (genericIdempotentMatrix k n).map α =
        (u : Matrix (Fin n) (Fin n) K) *
          rankProjectionMatrix K n r *
          ((u⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by
    let U : Matrix (Fin n) (Fin n) K := u
    -- Put the semiconjugacy witness into the explicit unit-conjugation form.
    have hu' := congrArg (fun X : Matrix (Fin n) (Fin n) K => X * U⁻¹) hu.eq
    simpa [K, α, U, mul_assoc, Units.val_inv_eq_inv_val] using hu'.symm
  have hcomp :
      ψ.comp (idempotentOrbitParamHom k n r) = α := by
    simpa [ψ, α, K] using
      residueFieldGeneralLinearEval_comp_idempotentOrbitParamHom (k := k) n p r u huMatrix
  -- The constructed prime has the same contracted ideal as `p`, because the composed map is the
  -- residue-field map of `p`.
  ext x
  rw [PrimeSpectrum.comap_asIdeal]
  change x ∈ Ideal.comap (idempotentOrbitParamHom k n r) (RingHom.ker ψ) ↔ x ∈ p.asIdeal
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have happly : ψ (idempotentOrbitParamHom k n r x) = α x :=
    RingHom.congr_fun hcomp x
  rw [happly]
  exact Ideal.algebraMap_residueField_eq_zero

/-- Helper for Chap10 Example 10 35 24: each fixed-rank idempotent locus is irreducible. -/
private theorem idempotentRankComponent_isIrreducible (n : ℕ) (r : Fin (n + 1)) :
    IsIrreducible (idempotentRankComponent k n r) := by
  have hrange :
      Set.range (PrimeSpectrum.comap (idempotentOrbitParamHom k n r)) =
        idempotentRankComponent k n r := by
    apply Set.Subset.antisymm
    · rintro p ⟨q, rfl⟩
      -- The direct image inclusion is the characteristic-polynomial invariance of `U P_r U⁻¹`.
      exact idempotentOrbitParam_mem_rankComponent (k := k) n r q
    · intro p hp
      -- The reverse inclusion is the remaining residue-field lifting statement.
      exact idempotentOrbitParam_surjectiveToRankComponent (k := k) n r p hp
  -- The component is the continuous image of the irreducible generic `GL_n` parameter spectrum.
  rw [← hrange]
  simpa [Set.image_univ] using
    (generalLinearPrimeSpectrum_isIrreducible (k := k) n).image
      (PrimeSpectrum.comap (idempotentOrbitParamHom k n r))
      (PrimeSpectrum.continuous_comap (idempotentOrbitParamHom k n r)).continuousOn

/-- Helper for Chap10 Example 10 35 24: no fixed-rank locus is contained in the union of the
other fixed-rank loci. -/
private theorem idempotentRankComponents_irredundant (n : ℕ) :
    ∀ Z ∈ Set.range (idempotentRankComponent k n),
      ¬ Z ⊆ ⋃₀ (Set.range (idempotentRankComponent k n) \ {Z}) := by
  rintro Z ⟨r, rfl⟩ hsubset
  -- The rank-`r` standard point is in the `r` component, so containment in the union of the
  -- other components would place it in some different rank component.
  have hp_other :
      rankProjectionPoint k n r ∈
        ⋃₀ (Set.range (idempotentRankComponent k n) \ {idempotentRankComponent k n r}) :=
    hsubset (rankProjectionPoint_mem_rankComponent_self (k := k) n r)
  rcases Set.mem_sUnion.mp hp_other with ⟨W, hW, hpW⟩
  rcases hW.1 with ⟨s, rfl⟩
  have hrs : r = s :=
    (rankProjectionPoint_mem_rankComponent_iff (k := k) n r s).mp hpW
  -- Exact rank separation contradicts that the component came from the punctured family.
  exact hW.2 (by simp [hrs])

/-- Helper for Chap10 Example 10 35 24: the irreducible components of
`Spec(k[{t_ij}]/(T^2 - T))` are the fixed-rank loci `idempotentRankComponent k n r`; on closed
points these are the `GL(n, k)`-orbits of the standard diagonal idempotents. -/
@[stacks 00GG]
theorem idempotentMatrixCoordinateRing_irreducibleComponents (n : ℕ) :
    irreducibleComponents (PrimeSpectrum (idempotentMatrixCoordinateRing k n)) =
      Set.range (idempotentRankComponent k n) :=
  by
    let S : Set (Set (PrimeSpectrum (idempotentMatrixCoordinateRing k n))) :=
      Set.range (idempotentRankComponent k n)
    have hS : S.Finite := by
      exact Set.finite_range (idempotentRankComponent k n)
    have hcover : ⋃₀ S = Set.univ := by
      simpa [S] using idempotentRankComponents_cover (k := k) n
    have hclosed : ∀ Z ∈ S, IsClosed Z := by
      rintro Z ⟨r, rfl⟩
      exact idempotentRankComponent_isClosed (k := k) n r
    have hirr : ∀ Z ∈ S, IsIrreducible Z := by
      rintro Z ⟨r, rfl⟩
      exact idempotentRankComponent_isIrreducible (k := k) n r
    have hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z}) := by
      simpa [S] using idempotentRankComponents_irredundant (k := k) n
    -- Lemma 5.8.4 turns this finite irredundant closed irreducible cover into the component set.
    simpa [S] using
      irreducibleComponents_eq_of_finite_irreducible_closed_cover
        S hS hcover hclosed hirr hirredundant

/-- Helper for Example 10.35.24: conjugate square matrices over a field have the same rank. -/
private theorem matrix_rank_eq_of_isConj {n : ℕ} {A B : Matrix (Fin n) (Fin n) k}
    (h : IsConj A B) :
    A.rank = B.rank := by
  classical
  rcases h with ⟨u, hu⟩
  let U : Matrix (Fin n) (Fin n) k := u
  have hUdet : IsUnit U.det := by
    simpa [U] using Matrix.isUnits_det_units u
  have hUinvdet : IsUnit (U⁻¹).det := by
    simpa [U, Units.val_inv_eq_inv_val] using Matrix.isUnits_det_units (u⁻¹)
  -- Rewrite the conjugate matrix in the explicit `U * A * U⁻¹` form.
  have hB : B = U * A * U⁻¹ := by
    have hu' := congrArg (fun X : Matrix (Fin n) (Fin n) k => X * U⁻¹) hu.eq
    simpa [U, mul_assoc, Units.val_inv_eq_inv_val] using hu'.symm
  -- Rank is invariant under left and right multiplication by invertible matrices.
  calc
    A.rank = (A * U⁻¹).rank := by
      symm
      exact Matrix.rank_mul_eq_left_of_isUnit_det U⁻¹ A hUinvdet
    _ = (U * (A * U⁻¹)).rank := by
      symm
      exact Matrix.rank_mul_eq_right_of_isUnit_det U (A * U⁻¹) hUdet
    _ = B.rank := by rw [hB, mul_assoc]

/-- Helper for Example 10.35.24: the standard rank-`r` projection matrix has rank `r`. -/
private theorem rankProjectionMatrix_rank_eq (n : ℕ) (r : Fin (n + 1)) :
    Matrix.rank (rankProjectionMatrix k n r) = r := by
  classical
  -- The diagonal entries are `1` exactly on the first `r` coordinates.
  rw [rankProjectionMatrix, Matrix.rank_diagonal]
  simpa [one_ne_zero] using Fintype.card_fin_lt_of_le (n := n) (m := r) r.is_le

/-- Helper for Example 10.35.24: the standard rank-`r` projection matrix has trace `r`. -/
private theorem rankProjectionMatrix_trace_eq (n : ℕ) [CharZero k] (r : Fin (n + 1)) :
    (rankProjectionMatrix k n r).trace = (r : k) := by
  classical
  have hfiltercard :
      (Finset.univ.filter fun i : Fin n => i.1 < r).card = r := by
    calc
      (Finset.univ.filter fun i : Fin n => i.1 < r).card = Fintype.card {x : Fin n // x.1 < r} := by
        symm
        exact Fintype.card_ofFinset (p := {i : Fin n | i.1 < r})
          (Finset.univ.filter fun i : Fin n => i.1 < r) (by
          intro x
          simp)
      _ = r := by
        simpa using Fintype.card_fin_lt_of_le (n := n) (m := r) r.is_le
  -- The trace is the sum of the diagonal entries, namely one on the first `r` indices.
  rw [rankProjectionMatrix, Matrix.trace_diagonal]
  have hsum :
      (∑ i : Fin n, if i.1 < r then (1 : k) else 0) =
        (Finset.univ.filter (fun i : Fin n => i.1 < r)).sum (fun _ => (1 : k)) := by
    symm
    simpa using (Finset.sum_filter (s := Finset.univ)
      (p := fun i : Fin n => i.1 < r) (f := fun _ : Fin n => (1 : k)))
  calc
    (∑ i : Fin n, if i.1 < r then (1 : k) else 0)
        = (Finset.univ.filter (fun i : Fin n => i.1 < r)).sum (fun _ => (1 : k)) := hsum
    _ = (((Finset.univ.filter fun i : Fin n => i.1 < r).card : ℕ) : k) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (r : k) := by
      exact congrArg (fun t : ℕ => (t : k)) hfiltercard

/-- Example 10.35.24 (3): orbit-set formulation of the rank stratification. -/
@[stacks 00GG]
theorem idempotentMatrix_eq_iUnion_rankProjectionConjugates (n : ℕ) :
    { A : Matrix (Fin n) (Fin n) k | IsIdempotentElem A } =
      ⋃ r : Fin (n + 1), conjugatesOf (rankProjectionMatrix k n r) :=
  by
    ext A
    simp [isIdempotentElem_iff_exists_isConj_rankProjectionMatrix, conjugatesOf]

/-- Different standard rank-projection orbits are disjoint. -/
-- Proof sketch: conjugation preserves rank. The standard projection `rankProjectionMatrix n r`
-- has rank `r`, so a matrix conjugate to both `rankProjectionMatrix n r` and
-- `rankProjectionMatrix n s` forces `r = s`.
theorem disjoint_rankProjectionConjugates (n : ℕ) {r s : Fin (n + 1)} (hrs : r ≠ s) :
    Disjoint (conjugatesOf (rankProjectionMatrix k n r))
      (conjugatesOf (rankProjectionMatrix k n s)) :=
  by
    rw [Set.disjoint_left]
    intro A hA hB
    -- A common point would force the two standard projections to be conjugate.
    have hconj : IsConj (rankProjectionMatrix k n r) (rankProjectionMatrix k n s) :=
      hA.trans hB.symm
    have hrank :
        Matrix.rank (rankProjectionMatrix k n r) = Matrix.rank (rankProjectionMatrix k n s) :=
      matrix_rank_eq_of_isConj hconj
    rw [rankProjectionMatrix_rank_eq, rankProjectionMatrix_rank_eq] at hrank
    exact hrs (Fin.ext hrank)

/-- Example 10.35.24 (4): over a field of characteristic zero, trace separates the fixed-rank
conjugacy classes of idempotent matrices. -/
@[stacks 00GG]
theorem trace_separates_rankProjectionConjugates (n : ℕ) [CharZero k]
    {A B : Matrix (Fin n) (Fin n) k} {r s : Fin (n + 1)}
    (hA : IsConj (rankProjectionMatrix k n r) A)
    (hB : IsConj (rankProjectionMatrix k n s) B)
    (hrs : r ≠ s) :
    A.trace ≠ B.trace := by
  have htraceA : A.trace = (r : k) := by
    rcases hA with ⟨u, hu⟩
    let U : Matrix (Fin n) (Fin n) k := u
    have hUunit : IsUnit U := by
      simpa [U] using (u.isUnit : IsUnit ((u : (Matrix (Fin n) (Fin n) k)ˣ) : Matrix (Fin n) (Fin n) k))
    -- Conjugation preserves matrix trace.
    have hAeq : A = U * rankProjectionMatrix k n r * U⁻¹ := by
      have hu' := congrArg (fun X : Matrix (Fin n) (Fin n) k => X * U⁻¹) hu.eq
      simpa [U, mul_assoc, Units.val_inv_eq_inv_val] using hu'.symm
    rw [hAeq, Matrix.trace_conj (M := U) hUunit]
    exact rankProjectionMatrix_trace_eq (k := k) n r
  have htraceB : B.trace = (s : k) := by
    rcases hB with ⟨u, hu⟩
    let U : Matrix (Fin n) (Fin n) k := u
    have hUunit : IsUnit U := by
      simpa [U] using (u.isUnit : IsUnit ((u : (Matrix (Fin n) (Fin n) k)ˣ) : Matrix (Fin n) (Fin n) k))
    -- The same conjugacy-invariance argument applies to `B`.
    have hBeq : B = U * rankProjectionMatrix k n s * U⁻¹ := by
      have hu' := congrArg (fun X : Matrix (Fin n) (Fin n) k => X * U⁻¹) hu.eq
      simpa [U, mul_assoc, Units.val_inv_eq_inv_val] using hu'.symm
    rw [hBeq, Matrix.trace_conj (M := U) hUunit]
    exact rankProjectionMatrix_trace_eq (k := k) n s
  rw [htraceA, htraceB]
  intro h
  apply hrs
  exact Fin.ext <| Nat.cast_injective h

/-- Helper for Chap10 Example 10 35 24: conjugate square matrices have the same determinant. -/
private theorem matrix_det_eq_of_isConj {n : ℕ} {A B : Matrix (Fin n) (Fin n) k}
    (h : IsConj A B) :
    B.det = A.det := by
  rcases h with ⟨u, hu⟩
  let U : Matrix (Fin n) (Fin n) k := u
  -- Put conjugacy into the explicit `U * A * U⁻¹` form expected by `det_units_conj`.
  have hBeq : B = U * A * U⁻¹ := by
    have hu' := congrArg (fun X : Matrix (Fin n) (Fin n) k => X * U⁻¹) hu.eq
    simpa [U, mul_assoc, Units.val_inv_eq_inv_val] using hu'.symm
  rw [hBeq]
  -- Determinants are invariant under conjugation by a unit.
  simpa [U, Units.val_inv_eq_inv_val] using Matrix.det_units_conj u A

-- Proof sketch: conjugation commutes with `exteriorPower.map`, so the third exterior-power trace
-- is constant on each orbit. For the standard diagonal idempotent of rank `r`, the induced action
-- on `⋀[k]^3 (Fin n → k)` is diagonal with one-dimensional eigenspaces indexed by `3`-element
-- subsets of the `r`-dimensional image, so its trace is `Nat.choose r 3`.
/-- Helper for Example 10.35.24: on `⋀[k]^3 (Fin 3 → k)`, the induced map has trace equal to the
determinant of the original `3 × 3` matrix. -/
private theorem top_exterior_trace_eq_det_fin3 (A : Matrix (Fin 3) (Fin 3) k) :
    LinearMap.trace k _ (exteriorPower.map 3 A.toLin') = A.det := by
  let top : Set.powersetCard (Fin 3) 3 :=
    Set.powersetCard.ofCard (s := Finset.univ) finsetUnivFinThree_card
  have hsub : Subsingleton (Set.powersetCard (Fin 3) 3) := by
    apply Finite.card_le_one_iff_subsingleton.mp
    rw [Set.powersetCard.card]
    norm_num
  have htopEmb : Set.powersetCard.ofFinEmbEquiv.symm top =
      (OrderIso.refl (Fin 3)).toOrderEmbedding := by
    simp only [top, Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp
  -- Compute the trace in the exterior-power basis; the top exterior basis has one vector.
  rw [LinearMap.trace_eq_matrix_trace k ((Pi.basisFun k (Fin 3)).exteriorPower 3)]
  rw [Matrix.trace, @Fintype.sum_subsingleton k (Set.powersetCard (Fin 3) 3) _ _ hsub _ top]
  suffices hdet :
      (∑ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ • ∏ i : Fin 3, A i (σ i)) =
        A.det by
    simpa [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
      exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti, htopEmb] using hdet
  -- The remaining scalar is the determinant of the transpose, hence the determinant of `A`.
  rw [← Matrix.det_transpose A]
  simp [Matrix.det_apply]

/-- Helper for Example 10.35.24: among the standard `3 × 3` rank projections, only the rank-`3`
projection has determinant `1`; the others have determinant `0`. -/
private theorem rankProjectionMatrix_det_fin3 (r : Fin 4) :
    Matrix.det (rankProjectionMatrix k 3 r) = if r = 3 then 1 else 0 := by
  -- Evaluate the determinant as the product of the diagonal entries and split the four ranks.
  rw [rankProjectionMatrix, Matrix.det_diagonal, Fin.prod_univ_three]
  fin_cases r <;> simp

/-- In characteristic `3`, for `3 × 3` idempotent matrices the invariant `tr(∧^3 T)` separates the
rank-`3` orbit from all other standard rank-projection orbits. -/
theorem thirdExteriorPowerTrace_separates_rankThreeProjectionConjugates [CharP k 3]
    {A B : Matrix (Fin 3) (Fin 3) k} {r : Fin 4}
    (hA : IsConj (rankProjectionMatrix k 3 3) A)
    (hB : IsConj (rankProjectionMatrix k 3 r) B)
    (hr : r ≠ 3) :
    LinearMap.trace k _ (exteriorPower.map 3 A.toLin') ≠
      LinearMap.trace k _ (exteriorPower.map 3 B.toLin') := by
  intro htrace
  -- Rewrite the exterior-power traces as ordinary determinants.
  have hdetEq : A.det = B.det := by
    simpa [top_exterior_trace_eq_det_fin3] using htrace
  have hdetA : A.det = Matrix.det (rankProjectionMatrix k 3 3) :=
    matrix_det_eq_of_isConj hA
  have hdetB : B.det = Matrix.det (rankProjectionMatrix k 3 r) :=
    matrix_det_eq_of_isConj hB
  -- The rank-three projection has determinant `1`, while all lower projections have determinant
  -- `0`, contradicting equality of determinants.
  rw [hdetA, hdetB, rankProjectionMatrix_det_fin3, rankProjectionMatrix_det_fin3] at hdetEq
  simp [hr] at hdetEq

end
