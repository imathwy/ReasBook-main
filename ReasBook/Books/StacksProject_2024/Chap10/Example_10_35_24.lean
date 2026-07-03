import Mathlib
import stacks_project.Chap05.Lemma_5_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix MvPolynomial Polynomial PrimeSpectrum

universe u

section

variable {k : Type u} [Semiring k]

/-- The diagonal idempotent matrix with `r` ones followed by `n - r` zeros. -/
def rankProjectionMatrix (k : Type u) [Semiring k] (n : ℕ) (r : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) k :=
  diagonal fun i ↦ if i.1 < r then 1 else 0

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

end

section

variable {k : Type u} [Field k]

/-- Example 10.35.24 (1): the irreducible components of
`Spec(k[{t_ij}]/(T^2 - T))` are the fixed-rank loci `idempotentRankComponent k n r`; on closed
points these are the `GL(n, k)`-orbits of the standard diagonal idempotents. -/
@[stacks 00GG]
theorem idempotentMatrixCoordinateRing_irreducibleComponents (n : ℕ) :
    irreducibleComponents (PrimeSpectrum (idempotentMatrixCoordinateRing k n)) =
      Set.range (idempotentRankComponent k n) :=
  by
    -- TODO: Package the fixed-rank loci as a finite closed cover using theorem (2), then reduce
    -- the remaining frontier to irreducibility of each `idempotentRankComponent k n r`.
    sorry

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
        simp [E, e, hi]
      simp [Function.comp, hei, hi]
    · have hlt : i.1 - r.1 < n - r.1 := by
        omega
      have hei : E.symm i = Sum.inr ⟨i.1 - r.1, hlt⟩ := by
        apply E.injective
        ext
        simp [E, e]
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

-- Proof sketch: conjugation commutes with `exteriorPower.map`, so the third exterior-power trace
-- is constant on each orbit. For the standard diagonal idempotent of rank `r`, the induced action
-- on `⋀[k]^3 (Fin n → k)` is diagonal with one-dimensional eigenspaces indexed by `3`-element
-- subsets of the `r`-dimensional image, so its trace is `Nat.choose r 3`.
/-- Helper for Example 10.35.24: on `⋀[k]^3 (Fin 3 → k)`, the induced map has trace equal to the
determinant of the original `3 × 3` matrix. -/
private theorem top_exterior_trace_eq_det_fin3 (A : Matrix (Fin 3) (Fin 3) k) :
    LinearMap.trace k _ (exteriorPower.map 3 A.toLin') = A.det := by
  -- TODO: Identify `⋀[k]^3 (Fin 3 → k)` with the determinant line and compute the scalar action
  -- of `exteriorPower.map 3 A.toLin'` on the top wedge of the standard basis.
  sorry

/-- Helper for Example 10.35.24: among the standard `3 × 3` rank projections, only the rank-`3`
projection has determinant `1`; the others have determinant `0`. -/
private theorem rankProjectionMatrix_det_fin3 (r : Fin 4) :
    Matrix.det (rankProjectionMatrix k 3 r) = if r = 3 then 1 else 0 := by
  -- TODO: Evaluate the determinant of the four standard diagonal projections directly.
  sorry

/-- In characteristic `3`, for `3 × 3` idempotent matrices the invariant `tr(∧^3 T)` separates the
rank-`3` orbit from all other standard rank-projection orbits. -/
theorem thirdExteriorPowerTrace_separates_rankThreeProjectionConjugates [CharP k 3]
    {A B : Matrix (Fin 3) (Fin 3) k} {r : Fin 4}
    (hA : IsConj (rankProjectionMatrix k 3 3) A)
    (hB : IsConj (rankProjectionMatrix k 3 r) B)
    (hr : r ≠ 3) :
    LinearMap.trace k _ (exteriorPower.map 3 A.toLin') ≠
      LinearMap.trace k _ (exteriorPower.map 3 B.toLin') := by
  -- TODO: Rewrite both traces using `top_exterior_trace_eq_det_fin3`, then separate the
  -- standard rank-`3` projection from the lower-rank projections by determinant.
  sorry

end
