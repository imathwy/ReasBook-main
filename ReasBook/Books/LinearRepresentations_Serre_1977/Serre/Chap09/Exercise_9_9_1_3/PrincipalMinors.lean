import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.InvariantCharpoly

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem exteriorPower_map_basis_repr_diag_eq_submatrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (b : Module.Basis ι k V) (A : V →ₗ[k] V) (n : ℕ)
    (s : Set.powersetCard ι n) :
    Module.Basis.repr (b.exteriorPower n)
        ((exteriorPower.map n A) ((b.exteriorPower n) s)) s =
      Matrix.det (Matrix.of fun i j ↦
        (LinearMap.toMatrix b b A) ((Set.powersetCard.ofFinEmbEquiv.symm s) i)
          ((Set.powersetCard.ofFinEmbEquiv.symm s) j) : Matrix (Fin n) (Fin n) k) := by
  -- Expand the wedge-basis coordinate through the universal pairing; on the diagonal, the resulting
  -- determinant is the principal minor of the matrix of `A`.
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  rw [exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
  simp [LinearMap.toMatrix_apply]
  convert (Matrix.det_transpose
      (Matrix.of fun i j ↦
        (b.repr (A (b ((Set.powersetCard.ofFinEmbEquiv.symm s) i))))
          ((Set.powersetCard.ofFinEmbEquiv.symm s) j) : Matrix (Fin n) (Fin n) k)).symm using 1

/-- Helper for Exercise 9-9.1-3: the trace of `exteriorPower.map n A` is the sum of the principal
`n × n` minors of any matrix representing `A`. -/
theorem trace_exteriorPower_map_eq_sum_principal_submatrix_det
    (A : V →ₗ[k] V) (n : ℕ) :
    LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A) =
      let b : Module.Basis (Fin (Module.finrank k V)) k V := Module.finBasis k V
      ∑ s : Set.powersetCard (Fin (Module.finrank k V)) n,
        Matrix.det (Matrix.of fun i j ↦
          (LinearMap.toMatrix b b A) ((Set.powersetCard.ofFinEmbEquiv.symm s) i)
            ((Set.powersetCard.ofFinEmbEquiv.symm s) j) : Matrix (Fin n) (Fin n) k) := by
  let b : Module.Basis (Fin (Module.finrank k V)) k V := Module.finBasis k V
  let B := b.exteriorPower n
  -- Compute the trace in the canonical wedge basis and rewrite each diagonal entry as a principal
  -- minor of the matrix of `A`.
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  apply Fintype.sum_congr
  intro s
  have hs := exteriorPower_map_basis_repr_diag_eq_submatrix_det (b := b) (A := A) (n := n) s
  simpa [Matrix.diag, LinearMap.toMatrix_apply, B, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family] using hs

/-- Helper for Exercise 9-9.1-3: replacing the columns indexed by `s` with those of `M` and
leaving all other columns as those of the identity matrix isolates the principal minor on `s`. -/
def principalMinorColumns
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (M : Matrix ι ι R) (s : Finset ι) : Matrix ι ι R :=
  fun i j ↦ if j ∈ s then M i j else if i = j then 1 else 0

/-- Helper for Exercise 9-9.1-3: replacing the rows indexed by `s` with those of `M` and
leaving all other rows as those of the identity matrix isolates the same principal minor. -/
def principalMinorRows
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (M : Matrix ι ι R) (s : Finset ι) : Matrix ι ι R :=
  fun i j ↦ if i ∈ s then M i j else if i = j then 1 else 0

/-- Helper for Exercise 9-9.1-3: transposing the row-replacement matrix for `M` turns it into the
column-replacement matrix for `Mᵀ`. -/
theorem principalMinorRows_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (M : Matrix ι ι R) (s : Finset ι) :
    (principalMinorRows M s).transpose = principalMinorColumns M.transpose s := by
  -- Check entries directly: transposition swaps the chosen rows into the chosen columns.
  ext i j
  by_cases hj : j ∈ s
  · simp [principalMinorRows, principalMinorColumns, hj]
  · by_cases hij : i = j
    · subst hij
      simp [principalMinorRows, principalMinorColumns, hj]
    · have hji : j ≠ i := by
        simpa [eq_comm] using hij
      simp [principalMinorRows, principalMinorColumns, hj, hij, hji]

/-- Helper for Exercise 9-9.1-3: replacing rows by those of `M` commutes with mapping matrix
entries through a ring homomorphism. -/
theorem principalMinorRows_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix ι ι R) (s : Finset ι) :
    principalMinorRows (M.map f) s = (principalMinorRows M s).map f := by
  -- Each row is either copied from `M` or from the identity matrix, and `f` preserves both
  -- constructions entrywise.
  ext i j
  by_cases hi : i ∈ s
  · simp [principalMinorRows, hi]
  · by_cases hij : i = j
    · subst hij
      simp [principalMinorRows, hi]
    · simp [principalMinorRows, hi, hij]

/-- Helper for Exercise 9-9.1-3: choosing the `X M`-row on the subset `s` and the identity row on
the complement is the same as scaling the selected rows of the principal-row matrix by `X`. -/
theorem row_piecewise_eq_diagonal_mul_principalMinorRows_map
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k) (s : Finset ι) :
    (s.piecewise ((Polynomial.X : Polynomial k) • M.map Polynomial.C)
      (1 : Matrix ι ι (Polynomial k))) =
      Matrix.diagonal (fun i : ι ↦ if i ∈ s then (Polynomial.X : Polynomial k) else 1) *
        principalMinorRows (M.map Polynomial.C) s := by
  -- Compute the product row-by-row: only the diagonal entry of the scaling matrix contributes.
  ext i j
  by_cases hi : i ∈ s
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.piecewise, principalMinorRows, hi,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro b _ hib
      have h : i ≠ b := by simpa [eq_comm] using hib
      simp [h]
    · simp
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.piecewise, principalMinorRows, hi,
      Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro b _ hib
      have h : i ≠ b := by simpa [eq_comm] using hib
      simp [h]
    · simp

/-- Helper for Exercise 9-9.1-3: each selected row contributes one factor of `X`, so the
determinant of the row-piecewise expansion is `X^|s|` times the determinant of the principal-row
matrix on `s`. -/
theorem det_row_piecewise_eq_X_pow_mul_det_principalMinorRows
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k) (s : Finset ι) :
    Matrix.det (s.piecewise ((Polynomial.X : Polynomial k) • M.map Polynomial.C)
      (1 : Matrix ι ι (Polynomial k))) =
      (Polynomial.X : Polynomial k) ^ s.card * Polynomial.C ((principalMinorRows M s).det) := by
  -- After factoring the selected rows, multiplicativity of determinant and `map_det` finish.
  rw [row_piecewise_eq_diagonal_mul_principalMinorRows_map]
  rw [Matrix.det_mul, Matrix.det_diagonal]
  rw [principalMinorRows_map, RingHom.map_det]
  rw [Finset.prod_ite_mem]
  simp

/-- Helper for Exercise 9-9.1-3: on each row-choice summand, the degree-`m` coefficient survives
exactly when the chosen subset has cardinality `m`. -/
theorem coeff_det_row_piecewise_eq_ite
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k) (s : Finset ι) (m : ℕ) :
    (Matrix.det (s.piecewise ((Polynomial.X : Polynomial k) • M.map Polynomial.C)
      (1 : Matrix ι ι (Polynomial k)))).coeff m =
      if s.card = m then (principalMinorRows M s).det else 0 := by
  -- Rewrite the summand as `X^|s| * C(det ...)`, then read off the coefficient of `X^m`.
  rw [det_row_piecewise_eq_X_pow_mul_det_principalMinorRows]
  rw [mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hmn : m = s.card
  · rw [if_pos hmn, if_pos hmn.symm]
    simp
  · rw [if_neg hmn, if_neg fun h ↦ hmn h.symm]
    simp

/-- Helper for Exercise 9-9.1-3: expanding `det (1 + X M)` rowwise and then taking the degree-`m`
coefficient produces the sum of all principal row minors of size `m`. -/
theorem coeff_det_one_add_X_smul_eq_sum_principalMinorRows_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k) (m : ℕ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C)).coeff m =
      Finset.sum ((Finset.univ : Finset ι).powersetCard m) fun s ↦ (principalMinorRows M s).det := by
  classical
  -- Expand the determinant as a sum over row choices, then keep only the subsets of size `m`.
  calc
    (Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C)).coeff m
        = (∑ s : Finset ι,
            Matrix.det (s.piecewise ((Polynomial.X : Polynomial k) • M.map Polynomial.C)
              (1 : Matrix ι ι (Polynomial k)))).coeff m := by
            congr 1
            calc
              Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C)
                  = Matrix.det ((Polynomial.X : Polynomial k) • M.map Polynomial.C + 1) := by
                      rw [add_comm]
              _ = ∑ s : Finset ι,
                    Matrix.det (s.piecewise ((Polynomial.X : Polynomial k) • M.map Polynomial.C)
                      (1 : Matrix ι ι (Polynomial k))) := by
                    simpa [Matrix.det] using
                      (Matrix.detRowAlternating.map_add_univ
                        (m := (Polynomial.X : Polynomial k) • M.map Polynomial.C)
                        (m' := (1 : Matrix ι ι (Polynomial k))))
    _ = ∑ s : Finset ι, if s.card = m then (principalMinorRows M s).det else 0 := by
          simp [coeff_det_row_piecewise_eq_ite]
    _ =
        Finset.sum (((Finset.univ : Finset ι).powerset).filter fun s : Finset ι ↦ s.card = m)
          fun s ↦ (principalMinorRows M s).det := by
          simp [Finset.sum_ite]
    _ = Finset.sum ((Finset.univ : Finset ι).powersetCard m) fun s ↦ (principalMinorRows M s).det := by
          rw [Finset.powersetCard_eq_filter]

/-- Helper for Exercise 9-9.1-3: the determinant of the column-replacement matrix attached to a
subset `s` is exactly the determinant of the principal block of `M` indexed by `s`. -/
theorem det_principalMinorColumns_eq_block_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (M : Matrix ι ι k) (n : ℕ) (s : Set.powersetCard ι n) :
    (principalMinorColumns M (s : Finset ι)).det =
      @Matrix.det {i // i ∈ (s : Finset ι)}
        (fun a b ↦ a.instDecidableEq b)
        (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
        k Field.toEuclideanDomain.toCommRing
        (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))) := by
  classical
  have htri :
      ∀ i, i ∈ (s : Finset ι) → ∀ j, j ∉ (s : Finset ι) →
        principalMinorColumns M (s : Finset ι) i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := by
      intro hij
      exact hj (hij ▸ hi)
    simp [principalMinorColumns, hj, hij]
  have hdet :=
    Matrix.twoBlockTriangular_det'
      (M := principalMinorColumns M (s : Finset ι))
      (p := fun i ↦ i ∈ (s : Finset ι)) htri
  have hdet' :
      (principalMinorColumns M (s : Finset ι)).det =
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp
            (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∈ (s : Finset ι))) *
          (Matrix.toSquareBlockProp
            (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∉ (s : Finset ι))).det := by
    simpa [not_not] using hdet
  have hcompl :
      Matrix.toSquareBlockProp
        (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∉ (s : Finset ι)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hi : (i : ι) ∉ (s : Finset ι) := i.2
      simp [Matrix.toSquareBlockProp, Matrix.toBlock, principalMinorColumns, hi]
    · have hval : (i : ι) ≠ j := fun h ↦ hij (Subtype.ext h)
      have hj : (j : ι) ∉ (s : Finset ι) := j.2
      simp [Matrix.toSquareBlockProp, Matrix.toBlock, principalMinorColumns, hj, hval, hij]
  have hblock :
      Matrix.toSquareBlockProp
        (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∈ (s : Finset ι)) =
        Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι)) := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock, principalMinorColumns, j.2]
  have hblockDet :
      @Matrix.det {i // i ∈ (s : Finset ι)}
        (fun a b ↦ a.instDecidableEq b)
        (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
        k Field.toEuclideanDomain.toCommRing
        (Matrix.toSquareBlockProp
          (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∈ (s : Finset ι))) =
      @Matrix.det {i // i ∈ (s : Finset ι)}
        (fun a b ↦ a.instDecidableEq b)
        (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
        k Field.toEuclideanDomain.toCommRing
        (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))) := by
    simpa using congrArg
      (fun N ↦
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing N)
      hblock
  -- The complement block is the identity, so the determinant comes entirely from the principal
  -- block indexed by `s`.
  calc
    (principalMinorColumns M (s : Finset ι)).det =
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp
            (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∈ (s : Finset ι))) *
          (Matrix.toSquareBlockProp
            (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∉ (s : Finset ι))).det := hdet'
    _ =
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp
            (principalMinorColumns M (s : Finset ι)) (fun i ↦ i ∈ (s : Finset ι))) := by
          rw [hcompl]
          simp
    _ =
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))) := hblockDet

/-- Helper for Exercise 9-9.1-3: the determinant of the principal-row matrix attached to `s`
coincides with the determinant of the corresponding principal submatrix written on `Fin n`. -/
theorem det_principalMinorRows_eq_submatrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (M : Matrix ι ι k) (n : ℕ) (s : Set.powersetCard ι n) :
    (principalMinorRows M (s : Finset ι)).det =
      Matrix.det (Matrix.of fun i j ↦
        M ((Set.powersetCard.ofFinEmbEquiv.symm s) i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j) :
          Matrix (Fin n) (Fin n) k) := by
  -- Transpose turns row replacement into the already-handled column replacement, and the selected
  -- square block is unchanged up to transpose.
  have hblockTranspose :
      Matrix.toSquareBlockProp M.transpose (fun i ↦ i ∈ (s : Finset ι)) =
        (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))).transpose := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock]
  have hSubtypeFintype :
      (Subtype.fintype fun i ↦ i ∈ (s : Finset ι)) = Finset.Subtype.fintype (s : Finset ι) := by
    apply Subsingleton.elim
  have hblockDetEq :
      @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))) =
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Finset.Subtype.fintype (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))) := by
    exact congrArg
      (fun I =>
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          I k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))))
      hSubtypeFintype
  have hblockTransposeDetEq :
      @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          ((Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))).transpose) =
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Finset.Subtype.fintype (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          ((Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))).transpose) := by
    exact congrArg
      (fun I =>
        @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          I k Field.toEuclideanDomain.toCommRing
          ((Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))).transpose))
      hSubtypeFintype
  calc
    (principalMinorRows M (s : Finset ι)).det
        = (principalMinorRows M (s : Finset ι)).transpose.det := by
            symm
            exact Matrix.det_transpose (principalMinorRows M (s : Finset ι))
    _ = (principalMinorColumns M.transpose (s : Finset ι)).det := by
          rw [principalMinorRows_transpose]
    _ = @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp M.transpose (fun i ↦ i ∈ (s : Finset ι))) := by
            exact det_principalMinorColumns_eq_block_det (M := M.transpose) (n := n) s
    _ = @Matrix.det {i // i ∈ (s : Finset ι)}
          (fun a b ↦ a.instDecidableEq b)
          (Subtype.fintype fun i ↦ i ∈ (s : Finset ι))
          k Field.toEuclideanDomain.toCommRing
          (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι))) := by
          rw [hblockTranspose]
          rw [hblockTransposeDetEq]
          rw [hblockDetEq]
          exact Matrix.det_transpose (Matrix.toSquareBlockProp M (fun i ↦ i ∈ (s : Finset ι)))
    _ = Matrix.det (Matrix.of fun i j ↦
          M ((Set.powersetCard.ofFinEmbEquiv.symm s) i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j) :
            Matrix (Fin n) (Fin n) k) := by
          symm
          rw [hblockDetEq]
          exact principal_submatrix_det_eq_block_det (M := M) (n := n) s

/-- Helper for Exercise 9-9.1-3: the degree-`m` coefficient of `det (1 + X M)` can be written as
the sum of the principal `m × m` minors indexed by `Set.powersetCard`. -/
theorem coeff_det_one_add_X_smul_eq_sum_principal_minor_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (M : Matrix ι ι k) (m : ℕ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C)).coeff m =
      (∑ s : Set.powersetCard ι m,
        Matrix.det (Matrix.of fun i j ↦
          M ((Set.powersetCard.ofFinEmbEquiv.symm s) i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j) :
            Matrix (Fin m) (Fin m) k)) := by
  -- First rewrite the rowwise determinant expansion as an attach sum over all `m`-subsets.
  calc
    (Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C)).coeff m
        = Finset.sum (((Finset.univ : Finset ι).powersetCard m).attach) fun t ↦
            (principalMinorRows M t.1).det := by
              rw [coeff_det_one_add_X_smul_eq_sum_principalMinorRows_det (M := M) (m := m)]
              symm
              exact Finset.sum_attach ((Finset.univ : Finset ι).powersetCard m)
                (fun t ↦ (principalMinorRows M t).det)
    _ = Finset.sum (((Finset.univ : Finset ι).powersetCard m).attach) fun t ↦
          Matrix.det (Matrix.of fun i j ↦
            M ((Set.powersetCard.ofFinEmbEquiv.symm
              ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩) i)
              ((Set.powersetCard.ofFinEmbEquiv.symm
                ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩) j) :
              Matrix (Fin m) (Fin m) k) := by
            apply Finset.sum_congr rfl
            intro t ht
            simpa using
              det_principalMinorRows_eq_submatrix_det (M := M) (n := m)
                (s := ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩)
    _ = (∑ s : Set.powersetCard ι m,
          Matrix.det (Matrix.of fun i j ↦
            M ((Set.powersetCard.ofFinEmbEquiv.symm s) i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j) :
              Matrix (Fin m) (Fin m) k)) := by
            symm
            exact sum_powersetCard_eq_sum_attach_powersetCard (n := m) fun s ↦
              Matrix.det (Matrix.of fun i j ↦
                M ((Set.powersetCard.ofFinEmbEquiv.symm s) i)
                  ((Set.powersetCard.ofFinEmbEquiv.symm s) j) : Matrix (Fin m) (Fin m) k)

end

end Representation
