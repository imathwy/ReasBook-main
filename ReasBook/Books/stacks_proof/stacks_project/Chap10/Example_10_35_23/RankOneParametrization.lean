import stacks_proof.stacks_project.Chap10.Example_10_35_23.MatrixAmbientIdeals

open Matrix MvPolynomial PrimeSpectrum

universe u

noncomputable section

section

variable (k : Type u) [Field k]

/-- Helper for Chap10 Example 10 35 23: a `2 × 2` matrix over a field with zero determinant is
an outer product of a column vector and a row vector. -/
theorem exists_outerProduct_of_det_fin_two_eq_zero
    {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = 0) :
    ∃ u v : Fin 2 → K, ∀ i j, A i j = u i * v j := by
  classical
  -- Split according to the first row.  A nonzero first entry lets us divide by it; otherwise a
  -- nonzero second entry does, and if the row vanishes the second row itself is the row vector.
  by_cases h00 : A 0 0 = 0
  · by_cases h01 : A 0 1 = 0
    · refine ⟨fun i ↦ if i = 0 then 0 else 1, fun j ↦ A 1 j, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01]
    · have hmul : A 0 1 * A 1 0 = 0 := by
        have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by
          simpa [Matrix.det_fin_two] using hdet
        have hneg : -(A 0 1 * A 1 0) = 0 := by
          simpa [h00] using hdet'
        exact neg_eq_zero.mp hneg
      have h10 : A 1 0 = 0 := (mul_eq_zero.mp hmul).resolve_left h01
      refine ⟨fun i ↦ if i = 0 then 1 else A 1 1 / A 0 1, fun j ↦ A 0 j, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j
      · simp
      · simp
      · simp [h00, h10]
      · simp [h01]
  · have hrel : A 0 0 * A 1 1 = A 0 1 * A 1 0 := by
      simpa [Matrix.det_fin_two, sub_eq_zero] using hdet
    refine ⟨fun i ↦ if i = 0 then 1 else A 1 0 / A 0 0, fun j ↦ A 0 j, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · simp
    · simp
    · simp [h00]
    · have h11 : A 1 1 = (A 1 0 / A 0 0) * A 0 1 := by
        field_simp [h00]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hrel
      simpa using h11

/-- Helper for Chap10 Example 10 35 23: a determinant-zero pair `X,Y` satisfying `XY = 0` is
represented by `X = u vᵀ` and `Y = (-v₁,v₀) zᵀ`. -/
theorem exists_matrixProductKernelParameters
    {K : Type*} [Field K] (X Y : Matrix (Fin 2) (Fin 2) K)
    (hXY : X * Y = 0) (hdetX : X.det = 0) (hdetY : Y.det = 0) :
    ∃ u v z : Fin 2 → K,
      (∀ i j, X i j = u i * v j) ∧
      (∀ j, Y 0 j = -v 1 * z j) ∧
      (∀ j, Y 1 j = v 0 * z j) := by
  classical
  -- If `X` vanishes, factor `Y` and choose `v` perpendicular to its column factor.
  by_cases hXzero : X = 0
  · obtain ⟨a, b, hY⟩ := exists_outerProduct_of_det_fin_two_eq_zero Y hdetY
    refine ⟨fun _ ↦ 0, fun i ↦ if i = 0 then a 1 else -a 0, b, ?_, ?_, ?_⟩
    · intro i j
      simp [hXzero]
    · intro j
      simpa using hY 0 j
    · intro j
      simpa using hY 1 j
  · obtain ⟨u, v, hX⟩ := exists_outerProduct_of_det_fin_two_eq_zero X hdetX
    have hv_nonzero : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hv
      push Not at hv
      apply hXzero
      ext i j
      fin_cases j
      · simp [hX i 0, hv.1]
      · simp [hX i 1, hv.2]
    have hu_nonzero : ∃ i : Fin 2, u i ≠ 0 := by
      by_contra hu
      have hu_zero : ∀ i : Fin 2, u i = 0 := by
        intro i
        exact not_not.mp (not_exists.mp hu i)
      apply hXzero
      ext i j
      simp [hX i j, hu_zero i]
    have hdot (j : Fin 2) : v 0 * Y 0 j + v 1 * Y 1 j = 0 := by
      obtain ⟨i, hi⟩ := hu_nonzero
      have hentry : (X * Y) i j = 0 := by
        simpa [hXY] using congrFun (congrFun hXY i) j
      rw [Matrix.mul_apply, Fin.sum_univ_two, hX i 0, hX i 1] at hentry
      have hmul : u i * (v 0 * Y 0 j + v 1 * Y 1 j) = 0 := by
        simpa [mul_add, mul_assoc] using hentry
      exact (mul_eq_zero.mp hmul).resolve_left hi
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        rcases hv_nonzero with hv0' | hv1
        · exact False.elim (hv0' hv0)
        · exact hv1
      refine ⟨u, v, fun j ↦ -Y 0 j / v 1, hX, ?_, ?_⟩
      · intro j
        field_simp [hv1]
      · intro j
        have hy1 : Y 1 j = 0 := by
          have hmul : v 1 * Y 1 j = 0 := by
            simpa [hv0] using hdot j
          exact (mul_eq_zero.mp hmul).resolve_left hv1
        simp [hv0, hy1]
    · refine ⟨u, v, fun j ↦ Y 1 j / v 0, hX, ?_, ?_⟩
      · intro j
        have hleft : v 0 * Y 0 j = -(v 1 * Y 1 j) := by
          rw [eq_neg_iff_add_eq_zero]
          simpa [add_comm, add_left_comm, add_assoc] using hdot j
        field_simp [hv0]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hleft
      · intro j
        field_simp [hv0]

/-- Helper for Chap10 Example 10 35 23: the polynomial parameter ring with coordinates
`u₀,u₁,v₀,v₁,z₀,z₁` used for the rank-one stratum. -/
abbrev matrixProductRankOneParamRing :=
  MvPolynomial (Fin 3 × Fin 2) k

/-- Helper for Chap10 Example 10 35 23: the ambient polynomial map for the parametrization
`X = u vᵀ` and `Y = (-v₁,v₀) zᵀ`. -/
def matrixProductRankOneParamEval :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →+* matrixProductRankOneParamRing k :=
  MvPolynomial.eval₂Hom (C : k →+* matrixProductRankOneParamRing k) fun a ↦
    match a with
    | (0, i, j) => X ((0 : Fin 3), i) * X ((1 : Fin 3), j)
    | (1, 0, j) => -X ((1 : Fin 3), 1) * X ((2 : Fin 3), j)
    | (1, 1, j) => X ((1 : Fin 3), 0) * X ((2 : Fin 3), j)

/-- Helper for Chap10 Example 10 35 23: the rank-one parametrization kills the four entries of
the product `XY`, so it descends to the matrix-product quotient ring. -/
theorem matrixProductCoordinateRingIdeal_le_rankOneParamEval_ker :
    matrixProductCoordinateRingIdeal k ≤ RingHom.ker (matrixProductRankOneParamEval k) := by
  -- Each entry becomes `uᵢ (v₀(-v₁) + v₁v₀) zⱼ`, hence vanishes.
  rw [matrixProductCoordinateRingIdeal]
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases hf with ⟨⟨i, j⟩, rfl⟩
  change matrixProductRankOneParamEval k
      ((matrixProductPolynomialMatrix k 0 * matrixProductPolynomialMatrix k 1) i j) = 0
  fin_cases i <;> fin_cases j <;>
    simp [matrixProductRankOneParamEval, matrixProductPolynomialMatrix, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    ring

/-- Helper for Chap10 Example 10 35 23: the descended rank-one parametrization from the
matrix-product coordinate ring. -/
def matrixProductRankOneParamHom :
    matrixProductCoordinateRing k →+* matrixProductRankOneParamRing k :=
  Ideal.Quotient.lift (matrixProductCoordinateRingIdeal k)
    (matrixProductRankOneParamEval k)
    (matrixProductCoordinateRingIdeal_le_rankOneParamEval_ker (k := k))

/-- Helper for Chap10 Example 10 35 23: under the parametrization the `X` entries are `uᵢvⱼ`. -/
theorem matrixProductRankOneParamHom_xEntry (i j : Fin 2) :
    matrixProductRankOneParamHom k ((matrixProductGenericMatrix k 0) i j) =
      X ((0 : Fin 3), i) * X ((1 : Fin 3), j) := by
  -- Reduce the quotient class to the corresponding ambient variable and evaluate it.
  fin_cases i <;> fin_cases j <;>
    simp [matrixProductRankOneParamHom, matrixProductGenericMatrix,
      matrixProductPolynomialMatrix, matrixProductRankOneParamEval, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X]

/-- Helper for Chap10 Example 10 35 23: under the parametrization the first row of `Y` is
`-v₁ zⱼ`. -/
theorem matrixProductRankOneParamHom_yZeroEntry (j : Fin 2) :
    matrixProductRankOneParamHom k ((matrixProductGenericMatrix k 1) 0 j) =
      -X ((1 : Fin 3), 1) * X ((2 : Fin 3), j) := by
  -- Reduce the quotient class to the corresponding ambient variable and evaluate it.
  fin_cases j <;>
    simp [matrixProductRankOneParamHom, matrixProductGenericMatrix,
      matrixProductPolynomialMatrix, matrixProductRankOneParamEval, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X]

/-- Helper for Chap10 Example 10 35 23: under the parametrization the second row of `Y` is
`v₀ zⱼ`. -/
theorem matrixProductRankOneParamHom_yOneEntry (j : Fin 2) :
    matrixProductRankOneParamHom k ((matrixProductGenericMatrix k 1) 1 j) =
      X ((1 : Fin 3), 0) * X ((2 : Fin 3), j) := by
  -- Reduce the quotient class to the corresponding ambient variable and evaluate it.
  fin_cases j <;>
    simp [matrixProductRankOneParamHom, matrixProductGenericMatrix,
      matrixProductPolynomialMatrix, matrixProductRankOneParamEval, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X]

/-- Helper for Chap10 Example 10 35 23: the parametrized `X` matrix has determinant zero. -/
theorem matrixProductRankOneParamHom_detX :
    matrixProductRankOneParamHom k (matrixProductGenericMatrix k 0).det = 0 := by
  -- The two rows of `X = u vᵀ` are proportional, so the `2 × 2` determinant cancels.
  rw [RingHom.map_det]
  simp [Matrix.det_fin_two, matrixProductRankOneParamHom_xEntry]
  ring

/-- Helper for Chap10 Example 10 35 23: the parametrized `Y` matrix has determinant zero. -/
theorem matrixProductRankOneParamHom_detY :
    matrixProductRankOneParamHom k (matrixProductGenericMatrix k 1).det = 0 := by
  -- The two rows of `Y = (-v₁,v₀) zᵀ` are proportional, so the determinant cancels.
  rw [RingHom.map_det]
  simp [Matrix.det_fin_two, matrixProductRankOneParamHom_yZeroEntry,
    matrixProductRankOneParamHom_yOneEntry]
  ring

/-- Helper for Chap10 Example 10 35 23: every point in the spectral image of the rank-one
parametrization lies in the determinant-zero component. -/
theorem matrixProductRankOneParam_range_subset_determinantZeroComponent :
    Set.range (PrimeSpectrum.comap (matrixProductRankOneParamHom k)) ⊆
      matrixProductDeterminantZeroComponent k := by
  -- Pull membership in the zero locus back along `Spec` and use the determinant-killing lemmas.
  rintro p ⟨q, rfl⟩
  rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus]
  rw [matrixProductDeterminantIdeal]
  refine Ideal.span_le.mpr ?_
  intro z hz
  rcases hz with ⟨s, rfl⟩
  fin_cases s
  · change matrixProductRankOneParamHom k (matrixProductGenericMatrix k 0).det ∈ q.asIdeal
    simpa [matrixProductRankOneParamHom_detX] using
      (q.asIdeal.zero_mem : (0 : matrixProductRankOneParamRing k) ∈ q.asIdeal)
  · change matrixProductRankOneParamHom k (matrixProductGenericMatrix k 1).det ∈ q.asIdeal
    simpa [matrixProductRankOneParamHom_detY] using
      (q.asIdeal.zero_mem : (0 : matrixProductRankOneParamRing k) ∈ q.asIdeal)

/-- Helper for Chap10 Example 10 35 23: in the matrix-product coordinate ring the two generic
matrices multiply to zero. -/
theorem matrixProductGenericMatrices_mul_eq_zero :
    matrixProductGenericMatrix k 0 * matrixProductGenericMatrix k 1 = 0 := by
  -- Each product entry is one of the generators of the defining quotient ideal.
  ext i j
  change Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)
      ((matrixProductPolynomialMatrix k 0 * matrixProductPolynomialMatrix k 1) i j) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, j), rfl⟩)

/-- Helper for Chap10 Example 10 35 23: a determinant-component prime lifts to the parameter
space under the rank-one parametrization. -/
theorem matrixProductRankOneParam_lifts_residuePoint
    (p : PrimeSpectrum (matrixProductCoordinateRing k))
    (hp : p ∈ matrixProductDeterminantZeroComponent k) :
    ∃ q : PrimeSpectrum (matrixProductRankOneParamRing k),
      PrimeSpectrum.comap (matrixProductRankOneParamHom k) q = p := by
  classical
  -- Work over the residue field of `p`; the generic matrices there satisfy the three equations
  -- needed by the field-level parametrization lemma.
  let K := p.asIdeal.ResidueField
  let α : matrixProductCoordinateRing k →+* K := algebraMap _ _
  let Xbar : Matrix (Fin 2) (Fin 2) K := (matrixProductGenericMatrix k 0).map α
  let Ybar : Matrix (Fin 2) (Fin 2) K := (matrixProductGenericMatrix k 1).map α
  have hXY : Xbar * Ybar = 0 := by
    rw [← Matrix.map_mul]
    simp [matrixProductGenericMatrices_mul_eq_zero]
  have hdetX_mem : (matrixProductGenericMatrix k 0).det ∈ p.asIdeal := by
    rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
    rw [matrixProductDeterminantIdeal] at hp
    exact hp (Ideal.subset_span ⟨0, rfl⟩)
  have hdetY_mem : (matrixProductGenericMatrix k 1).det ∈ p.asIdeal := by
    rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
    rw [matrixProductDeterminantIdeal] at hp
    exact hp (Ideal.subset_span ⟨1, rfl⟩)
  have hdetX : Xbar.det = 0 := by
    have hzero : α (matrixProductGenericMatrix k 0).det = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hdetX_mem
    simpa [Xbar, Matrix.det_fin_two] using hzero
  have hdetY : Ybar.det = 0 := by
    have hzero : α (matrixProductGenericMatrix k 1).det = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hdetY_mem
    simpa [Ybar, Matrix.det_fin_two] using hzero
  obtain ⟨u, v, z, hX, hY0, hY1⟩ :=
    exists_matrixProductKernelParameters Xbar Ybar hXY hdetX hdetY
  let paramValue : Fin 3 × Fin 2 → K := fun a ↦
    match a with
    | (0, i) => u i
    | (1, i) => v i
    | (2, i) => z i
  let ψ : matrixProductRankOneParamRing k →+* K :=
    MvPolynomial.eval₂Hom (algebraMap k K) paramValue
  let q : PrimeSpectrum (matrixProductRankOneParamRing k) :=
    ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  refine ⟨q, ?_⟩
  have hcomp : ψ.comp (matrixProductRankOneParamHom k) = α := by
    -- Compare the two maps out of the quotient on ambient constants and variables.
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      calc
        ((ψ.comp (matrixProductRankOneParamHom k)).comp
            (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))) (C r) =
            (algebraMap k K) r := by
              simp [ψ, matrixProductRankOneParamHom, matrixProductRankOneParamEval]
        _ = (α.comp (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))) (C r) := rfl
    · intro a
      rcases a with ⟨s, i, j⟩
      fin_cases s
      · have hxvar :
            α (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k) (X (0, i, j))) =
              Xbar i j := by
          simp [α, Xbar, matrixProductGenericMatrix, matrixProductPolynomialMatrix,
            Matrix.mvPolynomialX_apply, MvPolynomial.rename_X]
        calc
          (ψ.comp (matrixProductRankOneParamHom k)).comp
                (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)) (X (0, i, j)) =
              u i * v j := by
                fin_cases i <;> fin_cases j <;>
                  simp [ψ, paramValue, matrixProductRankOneParamHom,
                    matrixProductRankOneParamEval]
          _ = Xbar i j := (hX i j).symm
          _ = (α.comp (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))) (X (0, i, j)) :=
            hxvar.symm
      · fin_cases i
        · have hyvar :
              α (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k) (X (1, 0, j))) =
                Ybar 0 j := by
            simp [α, Ybar, matrixProductGenericMatrix, matrixProductPolynomialMatrix,
              Matrix.mvPolynomialX_apply, MvPolynomial.rename_X]
          have hy : -(v 1 * z j) = Ybar 0 j := by
            rw [← neg_mul]
            exact (hY0 j).symm
          calc
            (ψ.comp (matrixProductRankOneParamHom k)).comp
                  (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)) (X (1, 0, j)) =
                -(v 1 * z j) := by
                  fin_cases j <;>
                    simp [ψ, paramValue, matrixProductRankOneParamHom,
                      matrixProductRankOneParamEval]
            _ = Ybar 0 j := hy
            _ = (α.comp (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))) (X (1, 0, j)) :=
              hyvar.symm
        · have hyvar :
              α (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k) (X (1, 1, j))) =
                Ybar 1 j := by
            simp [α, Ybar, matrixProductGenericMatrix, matrixProductPolynomialMatrix,
              Matrix.mvPolynomialX_apply, MvPolynomial.rename_X]
          calc
            (ψ.comp (matrixProductRankOneParamHom k)).comp
                  (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)) (X (1, 1, j)) =
                v 0 * z j := by
                  fin_cases j <;>
                    simp [ψ, paramValue, matrixProductRankOneParamHom,
                      matrixProductRankOneParamEval]
            _ = Ybar 1 j := (hY1 j).symm
            _ = (α.comp (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))) (X (1, 1, j)) :=
              hyvar.symm
  ext r
  rw [PrimeSpectrum.comap_asIdeal]
  change (r ∈ Ideal.comap (matrixProductRankOneParamHom k) (RingHom.ker ψ)) ↔
    r ∈ p.asIdeal
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have happly : ψ (matrixProductRankOneParamHom k r) = α r := by
    exact RingHom.congr_fun hcomp r
  rw [happly]
  exact Ideal.algebraMap_residueField_eq_zero

/-- Helper for Chap10 Example 10 35 23: the determinant-zero component is exactly the spectral
image of the rank-one parametrization. -/
theorem matrixProductRankOneParam_range_eq_determinantZeroComponent :
    Set.range (PrimeSpectrum.comap (matrixProductRankOneParamHom k)) =
      matrixProductDeterminantZeroComponent k := by
  -- One inclusion is determinant killing; the other is the residue-field lift.
  apply Set.Subset.antisymm
  · exact matrixProductRankOneParam_range_subset_determinantZeroComponent (k := k)
  · intro p hp
    exact matrixProductRankOneParam_lifts_residuePoint (k := k) p hp

/-- Helper for Chap10 Example 10 35 23: the determinant-zero component is irreducible because it
is the image of the irreducible parameter affine space. -/
theorem matrixProductDeterminantZeroComponent_isIrreducible :
    IsIrreducible (matrixProductDeterminantZeroComponent k) := by
  -- Rewrite the component as an image and apply irreducibility of the prime spectrum of a domain.
  rw [← matrixProductRankOneParam_range_eq_determinantZeroComponent (k := k)]
  simpa [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ
      (X := PrimeSpectrum (matrixProductRankOneParamRing k))).image
        (PrimeSpectrum.comap (matrixProductRankOneParamHom k))
        (PrimeSpectrum.continuous_comap (matrixProductRankOneParamHom k)).continuousOn

end
