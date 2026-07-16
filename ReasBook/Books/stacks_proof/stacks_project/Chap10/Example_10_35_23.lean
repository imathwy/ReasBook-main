import Mathlib
import stacks_proof.stacks_project.Chap05.Lemma_5_8_4
import stacks_proof.stacks_project.Chap10.Example_10_35_23.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix MvPolynomial PrimeSpectrum

universe u

noncomputable section

section

variable (k : Type u) [CommRing k] [IsDomain k]

-- Proof sketch: irreducible components of `Spec` correspond to minimal primes via
-- `minimalPrimes.equivIrreducibleComponents`. For `k[x, y]/(xy)` over a domain, the minimal
-- primes are the images of `(x)` and `(y)`.
/-- Example 10.35.23 (1): `Spec(k[x, y]/(xy))` has two irreducible components, namely the `x`-axis
and the `y`-axis. -/
@[stacks 00GF]
theorem nodeCoordinateRing_irreducibleComponents :
    irreducibleComponents (PrimeSpectrum (nodeCoordinateRing k)) =
      {nodeXAxis k, nodeYAxis k} :=
  by
    classical
    -- Follow the source proof by covering the node with the two coordinate axes.
    refine irreducibleComponents_eq_of_finite_irreducible_closed_cover
      {nodeXAxis k, nodeYAxis k} ?_ ?_ ?_ ?_ ?_
    · simpa using Set.finite_insert (nodeXAxis k) (Set.finite_singleton (nodeYAxis k))
    · ext p
      constructor
      · intro _
        simp
      · intro _
        have hxy : nodeCoordinate k 0 * nodeCoordinate k 1 ∈ p.asIdeal := by
          simpa [node_coordinate_mul_eq_zero (k := k)] using (p.asIdeal.zero_mem :
            (0 : nodeCoordinateRing k) ∈ p.asIdeal)
        have hor : p ∈ nodeXAxis k ∨ p ∈ nodeYAxis k := by
          rcases p.isPrime.mem_or_mem hxy with hx | hy
          · right
            simpa [nodeYAxis, PrimeSpectrum.mem_zeroLocus] using hx
          · left
            simpa [nodeXAxis, PrimeSpectrum.mem_zeroLocus] using hy
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hor
    · intro Z hZ
      have hZmem : Z = nodeXAxis k ∨ Z = nodeYAxis k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
      rcases hZmem with rfl | rfl
      · simpa [nodeXAxis] using PrimeSpectrum.isClosed_zeroLocus
          ({nodeCoordinate k 1} : Set (nodeCoordinateRing k))
      · simpa [nodeYAxis] using PrimeSpectrum.isClosed_zeroLocus
          ({nodeCoordinate k 0} : Set (nodeCoordinateRing k))
    · intro Z hZ
      have hZmem : Z = nodeXAxis k ∨ Z = nodeYAxis k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
      rcases hZmem with rfl | rfl
      · exact nodeXAxis_isIrreducible (k := k)
      · exact nodeYAxis_isIrreducible (k := k)
    · intro Z hZ
      have hZmem : Z = nodeXAxis k ∨ Z = nodeYAxis k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
      rcases hZmem with rfl | rfl
      · rintro hsubset
        obtain ⟨p, hpX, hpY⟩ := node_xAxis_has_off_yAxis_point (k := k)
        have hpUnion : p ∈ ⋃₀ ({nodeXAxis k, nodeYAxis k} \ {nodeXAxis k}) := hsubset hpX
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem : t = nodeXAxis k ∨ t = nodeYAxis k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ nodeXAxis k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl
        · exact False.elim (htNe rfl)
        · exact hpY hpt
      · rintro hsubset
        obtain ⟨p, hpY, hpX⟩ := node_yAxis_has_off_xAxis_point (k := k)
        have hpUnion : p ∈ ⋃₀ ({nodeXAxis k, nodeYAxis k} \ {nodeYAxis k}) := hsubset hpY
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem : t = nodeXAxis k ∨ t = nodeYAxis k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ nodeYAxis k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl
        · exact hpX hpt
        · exact False.elim (htNe rfl)

end

section

variable (k : Type u) [Field k]

/-- Helper for Example 10.35.23: the image of the ambient `Y = 0` ideal in the quotient coordinate
ring is exactly the entry ideal defining `matrixProductYZeroComponent`. -/
private theorem matrixProductAmbientYIdeal_map_eq :
    Ideal.map (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))
      (matrixProductAmbientYIdeal k) = matrixProductEntryIdeal k 1 := by
  -- Map the ambient generators through the quotient map and rewrite the image of a range as a
  -- range of quotient classes.
  rw [matrixProductAmbientYIdeal, matrixProductEntryIdeal, Ideal.map_span]
  rw [← Set.range_comp]
  simp [Function.comp_def, matrixProductGenericMatrix]

/-- Helper for Example 10.35.23: the image of the ambient `X = 0` ideal in the quotient coordinate
ring is exactly the entry ideal defining `matrixProductXZeroComponent`. -/
private theorem matrixProductAmbientXIdeal_map_eq :
    Ideal.map (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))
      (matrixProductAmbientXIdeal k) = matrixProductEntryIdeal k 0 := by
  -- Map the ambient generators through the quotient map and rewrite the image of a range as a
  -- range of quotient classes.
  rw [matrixProductAmbientXIdeal, matrixProductEntryIdeal, Ideal.map_span]
  rw [← Set.range_comp]
  simp [Function.comp_def, matrixProductGenericMatrix]

/-- Helper for Example 10.35.23: each entry ideal in the matrix-product coordinate ring is prime. -/
private theorem matrixProductEntryIdeal_isPrime (s : Fin 2) :
    (matrixProductEntryIdeal k s).IsPrime := by
  -- Split the two matrix factors and push the corresponding ambient prime ideal through the
  -- quotient by the defining `XY = 0` ideal.
  fin_cases s
  · have hle : matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientXIdeal k :=
      matrixProductCoordinateRingIdeal_le_ambientXIdeal (k := k)
    let p : Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) := matrixProductAmbientXIdeal k
    let _ : p.IsPrime := matrixProductAmbientXIdeal_isPrime (k := k)
    have hmap : (Ideal.map (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)) p).IsPrime := by
      exact Ideal.isPrime_map_quotientMk_of_isPrime hle
    simpa [p, matrixProductAmbientXIdeal_map_eq (k := k)] using hmap
  · have hle : matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientYIdeal k :=
      matrixProductCoordinateRingIdeal_le_ambientYIdeal (k := k)
    let p : Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) := matrixProductAmbientYIdeal k
    let _ : p.IsPrime := matrixProductAmbientYIdeal_isPrime (k := k)
    have hmap : (Ideal.map (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)) p).IsPrime := by
      exact Ideal.isPrime_map_quotientMk_of_isPrime hle
    simpa [p, matrixProductAmbientYIdeal_map_eq (k := k)] using hmap

/-- Helper for Example 10.35.23: both axis-type components are irreducible because they are zero
loci of prime ideals. -/
private theorem matrix_product_entry_component_irreducible (s : Fin 2) :
    IsIrreducible (zeroLocus (matrixProductEntryIdeal k s : Set (matrixProductCoordinateRing k))) := by
  -- A prime ideal is radical, so the standard zero-locus criterion gives irreducibility.
  have hprime : (matrixProductEntryIdeal k s).IsPrime :=
    matrixProductEntryIdeal_isPrime (k := k) s
  have hrad : (matrixProductEntryIdeal k s).IsRadical := hprime.isRadical
  exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _ hrad).2 hprime

/-- Helper for Example 10.35.23: in the matrix-product coordinate ring the universal relation is
`XY = 0`. -/
private theorem matrixProductGenericMatrix_mul_eq_zero :
    matrixProductGenericMatrix k 0 * matrixProductGenericMatrix k 1 = 0 := by
  -- Each entry of the product is one of the generators of the defining quotient ideal.
  ext i j
  change Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)
      ((matrixProductPolynomialMatrix k 0 * matrixProductPolynomialMatrix k 1) i j) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, j), rfl⟩)

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x00_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 0 0 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₁₁ det(Y)` through the two first-row relations of `XY = 0`.
  calc
    X 0 0 * Y.det = (X * Y) 0 0 * Y 1 1 - (X * Y) 0 1 * Y 1 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x01_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 0 1 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₁₂ det(Y)` through the two first-row relations of `XY = 0`.
  calc
    X 0 1 * Y.det = (X * Y) 0 1 * Y 0 0 - (X * Y) 0 0 * Y 0 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x10_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 1 0 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₂₁ det(Y)` through the two second-row relations of `XY = 0`.
  calc
    X 1 0 * Y.det = (X * Y) 1 0 * Y 1 1 - (X * Y) 1 1 * Y 1 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x11_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 1 1 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₂₂ det(Y)` through the two second-row relations of `XY = 0`.
  calc
    X 1 1 * Y.det = (X * Y) 1 1 * Y 0 0 - (X * Y) 1 0 * Y 0 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y00_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 0 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₁₁` through the first-column relations of `XY = 0`.
  calc
    X.det * Y 0 0 = X 1 1 * (X * Y) 0 0 - X 0 1 * (X * Y) 1 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y01_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 1 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₁₂` through the second-column relations of `XY = 0`.
  calc
    X.det * Y 0 1 = X 1 1 * (X * Y) 0 1 - X 0 1 * (X * Y) 1 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y10_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 0 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₂₁` through the first-column relations of `XY = 0`.
  calc
    X.det * Y 1 0 = X 0 0 * (X * Y) 1 0 - X 1 0 * (X * Y) 0 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y11_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 1 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₂₂` through the second-column relations of `XY = 0`.
  calc
    X.det * Y 1 1 = X 0 0 * (X * Y) 1 1 - X 1 0 * (X * Y) 0 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every prime of the matrix-product coordinate ring lies either on
`Y = 0`, on `X = 0`, or on the determinant component. -/
private theorem matrix_product_prime_lies_in_axis_or_determinant_component
    (p : PrimeSpectrum (matrixProductCoordinateRing k)) :
    p ∈ matrixProductYZeroComponent k ∨
      p ∈ matrixProductDeterminantZeroComponent k ∨
      p ∈ matrixProductXZeroComponent k := by
  by_cases hY : p ∈ matrixProductYZeroComponent k
  · exact Or.inl hY
  by_cases hX : p ∈ matrixProductXZeroComponent k
  · exact Or.inr (Or.inr hX)
  have hY' : ∃ ij : Fin 2 × Fin 2, (matrixProductGenericMatrix k 1) ij.1 ij.2 ∉ p.asIdeal := by
    by_contra hcontra
    apply hY
    rw [matrixProductYZeroComponent, PrimeSpectrum.mem_zeroLocus]
    rw [matrixProductEntryIdeal]
    refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨ij, rfl⟩
    by_contra hz'
    exact hcontra ⟨ij, hz'⟩
  have hX' : ∃ ij : Fin 2 × Fin 2, (matrixProductGenericMatrix k 0) ij.1 ij.2 ∉ p.asIdeal := by
    by_contra hcontra
    apply hX
    rw [matrixProductXZeroComponent, PrimeSpectrum.mem_zeroLocus]
    rw [matrixProductEntryIdeal]
    refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨ij, rfl⟩
    by_contra hz'
    exact hcontra ⟨ij, hz'⟩
  obtain ⟨ijY, hijY⟩ := hY'
  obtain ⟨ijX, hijX⟩ := hX'
  have hdetX : (matrixProductGenericMatrix k 0).det ∈ p.asIdeal := by
    rcases ijY with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    ·
      have hy00 : (matrixProductGenericMatrix k 1) 0 0 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 0 ∈
            p.asIdeal := by
        simpa [matrixProduct_detX_mul_y00_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy00
    ·
      have hy01 : (matrixProductGenericMatrix k 1) 0 1 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 1 ∈
            p.asIdeal := by
        simpa [mul_comm, matrixProduct_detX_mul_y01_eq_zero (k := k)] using
          (p.asIdeal.zero_mem : (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy01
    ·
      have hy10 : (matrixProductGenericMatrix k 1) 1 0 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 0 ∈
            p.asIdeal := by
        simpa [mul_comm, matrixProduct_detX_mul_y10_eq_zero (k := k)] using
          (p.asIdeal.zero_mem : (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy10
    ·
      have hy11 : (matrixProductGenericMatrix k 1) 1 1 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 1 ∈
            p.asIdeal := by
        simpa [mul_comm, matrixProduct_detX_mul_y11_eq_zero (k := k)] using
          (p.asIdeal.zero_mem : (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy11
  have hdetY : (matrixProductGenericMatrix k 1).det ∈ p.asIdeal := by
    rcases ijX with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    ·
      have hx00 : (matrixProductGenericMatrix k 0) 0 0 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 0 0 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x00_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx00
    ·
      have hx01 : (matrixProductGenericMatrix k 0) 0 1 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 0 1 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x01_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx01
    ·
      have hx10 : (matrixProductGenericMatrix k 0) 1 0 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 1 0 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x10_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx10
    ·
      have hx11 : (matrixProductGenericMatrix k 0) 1 1 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 1 1 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x11_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx11
  -- Once both determinants lie in `p`, the point lies on the determinant component.
  exact Or.inr (Or.inl (by
    rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus]
    rw [matrixProductDeterminantIdeal]
    refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨s, rfl⟩
    fin_cases s
    · simpa using hdetX
    · simpa using hdetY))

/-- Helper for Example 10.35.23: the generic point of the `Y = 0` component is the prime ideal
generated by the `Y`-entries. -/
private def matrixProductYZeroGenericPoint :
    PrimeSpectrum (matrixProductCoordinateRing k) :=
  ⟨matrixProductEntryIdeal k 1, matrixProductEntryIdeal_isPrime (k := k) 1⟩

/-- Helper for Example 10.35.23: the generic point of the `X = 0` component is the prime ideal
generated by the `X`-entries. -/
private def matrixProductXZeroGenericPoint :
    PrimeSpectrum (matrixProductCoordinateRing k) :=
  ⟨matrixProductEntryIdeal k 0, matrixProductEntryIdeal_isPrime (k := k) 0⟩

/-- Helper for Example 10.35.23: the `x₁₁`-coordinate survives modulo the ambient `Y = 0` ideal. -/
private theorem matrixProduct_x00_not_mem_ambientYIdeal :
    (matrixProductPolynomialMatrix k 0) 0 0 ∉ matrixProductAmbientYIdeal k := by
  -- Push forward along `matrixProductKeepX`; membership in the ambient `Y`-ideal would kill the
  -- surviving `X (0, 0)` variable.
  intro hx
  have hxker :
      (matrixProductPolynomialMatrix k 0) 0 0 ∈ RingHom.ker (matrixProductKeepX k) := by
    simpa [matrixProductKeepX_ker (k := k)] using hx
  have hxzero : (matrixProductKeepX k) ((matrixProductPolynomialMatrix k 0) 0 0) = 0 :=
    RingHom.mem_ker.mp hxker
  have hXzero : (X (0, 0) : MvPolynomial (Fin 2 × Fin 2) k) = 0 := by
    simpa [matrixProductKeepX, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X, MvPolynomial.killCompl, matrixProductXVariableEmbedding] using hxzero
  exact (MvPolynomial.X_ne_zero (σ := Fin 2 × Fin 2) (R := k) (0, 0)) hXzero

/-- Helper for Example 10.35.23: the `y₁₁`-coordinate survives modulo the ambient `X = 0` ideal. -/
private theorem matrixProduct_y00_not_mem_ambientXIdeal :
    (matrixProductPolynomialMatrix k 1) 0 0 ∉ matrixProductAmbientXIdeal k := by
  -- Push forward along `matrixProductKeepY`; membership in the ambient `X`-ideal would kill the
  -- surviving `Y (0, 0)` variable.
  intro hy
  have hyker :
      (matrixProductPolynomialMatrix k 1) 0 0 ∈ RingHom.ker (matrixProductKeepY k) := by
    simpa [matrixProductKeepY_ker (k := k)] using hy
  have hyzero : (matrixProductKeepY k) ((matrixProductPolynomialMatrix k 1) 0 0) = 0 :=
    RingHom.mem_ker.mp hyker
  have hYzero : (X (0, 0) : MvPolynomial (Fin 2 × Fin 2) k) = 0 := by
    simpa [matrixProductKeepY, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X, MvPolynomial.killCompl, matrixProductYVariableEmbedding] using hyzero
  exact (MvPolynomial.X_ne_zero (σ := Fin 2 × Fin 2) (R := k) (0, 0)) hYzero

/-- Helper for Example 10.35.23: the determinant polynomial of `X` survives modulo the ambient
`Y = 0` ideal. -/
private theorem matrixProduct_detX_not_mem_ambientYIdeal :
    (matrixProductPolynomialMatrix k 0).det ∉ matrixProductAmbientYIdeal k := by
  -- Evaluate the ambient polynomial ring at `X = I` and `Y = 0`; every `Y`-generator dies while
  -- `det X` evaluates to `1`.
  let φ : MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) fun a : Fin 2 × Fin 2 × Fin 2 ↦
      if a.1 = 0 then if a.2.1 = a.2.2 then 1 else 0 else 0
  have hle : matrixProductAmbientYIdeal k ≤ RingHom.ker φ := by
    rw [matrixProductAmbientYIdeal]
    refine Ideal.span_le.mpr ?_
    intro f hf
    rcases hf with ⟨⟨i, j⟩, rfl⟩
    fin_cases i <;> fin_cases j <;>
      simp [φ, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply, MvPolynomial.rename_X]
  intro hdet
  have hzero : φ ((matrixProductPolynomialMatrix k 0).det) = 0 :=
    RingHom.mem_ker.mp (hle hdet)
  have hval : φ ((matrixProductPolynomialMatrix k 0).det) = 1 := by
    simp [φ, matrixProductPolynomialMatrix, Matrix.det_fin_two, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X]
  have h10 : (1 : k) = 0 := by
    rw [← hval]
    exact hzero
  exact one_ne_zero h10

/-- Helper for Example 10.35.23: the determinant polynomial of `Y` survives modulo the ambient
`X = 0` ideal. -/
private theorem matrixProduct_detY_not_mem_ambientXIdeal :
    (matrixProductPolynomialMatrix k 1).det ∉ matrixProductAmbientXIdeal k := by
  -- Evaluate the ambient polynomial ring at `Y = I` and `X = 0`; every `X`-generator dies while
  -- `det Y` evaluates to `1`.
  let φ : MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) fun a : Fin 2 × Fin 2 × Fin 2 ↦
      if a.1 = 1 then if a.2.1 = a.2.2 then 1 else 0 else 0
  have hle : matrixProductAmbientXIdeal k ≤ RingHom.ker φ := by
    rw [matrixProductAmbientXIdeal]
    refine Ideal.span_le.mpr ?_
    intro f hf
    rcases hf with ⟨⟨i, j⟩, rfl⟩
    fin_cases i <;> fin_cases j <;>
      simp [φ, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply, MvPolynomial.rename_X]
  intro hdet
  have hzero : φ ((matrixProductPolynomialMatrix k 1).det) = 0 :=
    RingHom.mem_ker.mp (hle hdet)
  have hval : φ ((matrixProductPolynomialMatrix k 1).det) = 1 := by
    simp [φ, matrixProductPolynomialMatrix, Matrix.det_fin_two, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X]
  have h10 : (1 : k) = 0 := by
    rw [← hval]
    exact hzero
  exact one_ne_zero h10

/-- Helper for Example 10.35.23: the generic `Y = 0` point does not lie on the determinant or
`X = 0` components. -/
private theorem matrixProductYZeroGenericPoint_off_other_components :
    matrixProductYZeroGenericPoint k ∈ matrixProductYZeroComponent k ∧
      matrixProductYZeroGenericPoint k ∉ matrixProductDeterminantZeroComponent k ∧
      matrixProductYZeroGenericPoint k ∉ matrixProductXZeroComponent k := by
  -- Pull quotient membership back to the ambient `Y = 0` ideal; the determinant and one `X` entry
  -- survive there, so the generic `Y = 0` point avoids the other two components.
  refine ⟨?_, ?_, ?_⟩
  · simpa [matrixProductYZeroGenericPoint, matrixProductYZeroComponent,
      PrimeSpectrum.mem_zeroLocus]
  · intro hp
    have hdetXq : (matrixProductGenericMatrix k 0).det ∈ matrixProductEntryIdeal k 1 := by
      rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
      rw [matrixProductDeterminantIdeal] at hp
      exact hp (Ideal.subset_span ⟨0, rfl⟩)
    have hdetXmap :
        Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)
          ((matrixProductPolynomialMatrix k 0).det) ∈ matrixProductEntryIdeal k 1 := by
      simpa [matrixProductGenericMatrix] using hdetXq
    have hdetXambient : (matrixProductPolynomialMatrix k 0).det ∈ matrixProductAmbientYIdeal k := by
      rw [← matrixProductAmbientYIdeal_map_eq (k := k)] at hdetXmap
      exact (Ideal.mem_quotient_iff_mem
        (matrixProductCoordinateRingIdeal_le_ambientYIdeal (k := k))).1 hdetXmap
    exact matrixProduct_detX_not_mem_ambientYIdeal (k := k) hdetXambient
  · intro hp
    have hx00q : (matrixProductGenericMatrix k 0) 0 0 ∈ matrixProductEntryIdeal k 1 := by
      rw [matrixProductXZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
      rw [matrixProductEntryIdeal] at hp
      exact hp (Ideal.subset_span ⟨(0, 0), rfl⟩)
    have hx00map :
        Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)
          ((matrixProductPolynomialMatrix k 0) 0 0) ∈ matrixProductEntryIdeal k 1 := by
      simpa [matrixProductGenericMatrix] using hx00q
    have hx00ambient :
        (matrixProductPolynomialMatrix k 0) 0 0 ∈ matrixProductAmbientYIdeal k := by
      rw [← matrixProductAmbientYIdeal_map_eq (k := k)] at hx00map
      exact (Ideal.mem_quotient_iff_mem
        (matrixProductCoordinateRingIdeal_le_ambientYIdeal (k := k))).1 hx00map
    exact matrixProduct_x00_not_mem_ambientYIdeal (k := k) hx00ambient

/-- Helper for Example 10.35.23: the generic `X = 0` point does not lie on the determinant or
`Y = 0` components. -/
private theorem matrixProductXZeroGenericPoint_off_other_components :
    matrixProductXZeroGenericPoint k ∈ matrixProductXZeroComponent k ∧
      matrixProductXZeroGenericPoint k ∉ matrixProductDeterminantZeroComponent k ∧
      matrixProductXZeroGenericPoint k ∉ matrixProductYZeroComponent k := by
  -- Pull quotient membership back to the ambient `X = 0` ideal; the determinant and one `Y` entry
  -- survive there, so the generic `X = 0` point avoids the other two components.
  refine ⟨?_, ?_, ?_⟩
  · simpa [matrixProductXZeroGenericPoint, matrixProductXZeroComponent,
      PrimeSpectrum.mem_zeroLocus]
  · intro hp
    have hdetYq : (matrixProductGenericMatrix k 1).det ∈ matrixProductEntryIdeal k 0 := by
      rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
      rw [matrixProductDeterminantIdeal] at hp
      exact hp (Ideal.subset_span ⟨1, rfl⟩)
    have hdetYmap :
        Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)
          ((matrixProductPolynomialMatrix k 1).det) ∈ matrixProductEntryIdeal k 0 := by
      simpa [matrixProductGenericMatrix] using hdetYq
    have hdetYambient : (matrixProductPolynomialMatrix k 1).det ∈ matrixProductAmbientXIdeal k := by
      rw [← matrixProductAmbientXIdeal_map_eq (k := k)] at hdetYmap
      exact (Ideal.mem_quotient_iff_mem
        (matrixProductCoordinateRingIdeal_le_ambientXIdeal (k := k))).1 hdetYmap
    exact matrixProduct_detY_not_mem_ambientXIdeal (k := k) hdetYambient
  · intro hp
    have hy00q : (matrixProductGenericMatrix k 1) 0 0 ∈ matrixProductEntryIdeal k 0 := by
      rw [matrixProductYZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
      rw [matrixProductEntryIdeal] at hp
      exact hp (Ideal.subset_span ⟨(0, 0), rfl⟩)
    have hy00map :
        Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)
          ((matrixProductPolynomialMatrix k 1) 0 0) ∈ matrixProductEntryIdeal k 0 := by
      simpa [matrixProductGenericMatrix] using hy00q
    have hy00ambient :
        (matrixProductPolynomialMatrix k 1) 0 0 ∈ matrixProductAmbientXIdeal k := by
      rw [← matrixProductAmbientXIdeal_map_eq (k := k)] at hy00map
      exact (Ideal.mem_quotient_iff_mem
        (matrixProductCoordinateRingIdeal_le_ambientXIdeal (k := k))).1 hy00map
    exact matrixProduct_y00_not_mem_ambientXIdeal (k := k) hy00ambient

/-- Helper for Chap10 Example 10 35 23: the ambient evaluation for the concrete rank-one pair
`X = [[1,0],[1,0]]`, `Y = [[0,0],[1,0]]`. -/
private def matrixProductDeterminantWitnessEval :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) fun a : Fin 2 × Fin 2 × Fin 2 ↦
    match a with
    | (0, 0, 0) => 1
    | (0, 0, 1) => 0
    | (0, 1, 0) => 1
    | (0, 1, 1) => 0
    | (1, 0, 0) => 0
    | (1, 0, 1) => 0
    | (1, 1, 0) => 1
    | (1, 1, 1) => 0

/-- Helper for Chap10 Example 10 35 23: the concrete rank-one pair satisfies `XY = 0`, so the
defining ideal of the matrix-product coordinate ring lies in the evaluation kernel. -/
private theorem matrixProductCoordinateRingIdeal_le_determinantWitnessEval_ker :
    matrixProductCoordinateRingIdeal k ≤ RingHom.ker (matrixProductDeterminantWitnessEval k) := by
  -- Check the four entries of `XY` at the chosen concrete matrices.
  rw [matrixProductCoordinateRingIdeal]
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases hf with ⟨⟨i, j⟩, rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp [matrixProductDeterminantWitnessEval, matrixProductPolynomialMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Helper for Chap10 Example 10 35 23: the quotient evaluation induced by the determinant
witness pair. -/
private def matrixProductDeterminantWitnessHom : matrixProductCoordinateRing k →+* k :=
  Ideal.Quotient.lift (matrixProductCoordinateRingIdeal k)
    (matrixProductDeterminantWitnessEval k)
    (matrixProductCoordinateRingIdeal_le_determinantWitnessEval_ker (k := k))

/-- Helper for Chap10 Example 10 35 23: the kernel of the determinant witness quotient evaluation
is prime. -/
private theorem matrixProductDeterminantWitnessHom_ker_isPrime :
    (RingHom.ker (matrixProductDeterminantWitnessHom k)).IsPrime :=
  RingHom.ker_isPrime (matrixProductDeterminantWitnessHom k)

/-- Helper for Chap10 Example 10 35 23: the concrete rank-one pair determines a prime-spectrum
point of the quotient ring. -/
private def matrixProductDeterminantWitnessPoint :
    PrimeSpectrum (matrixProductCoordinateRing k) :=
  ⟨RingHom.ker (matrixProductDeterminantWitnessHom k),
    matrixProductDeterminantWitnessHom_ker_isPrime (k := k)⟩

/-- Helper for Example 10.35.23: the rank-one witness point lies on the determinant component but
avoids the two axis components. -/
private theorem matrixProductDeterminantWitnessPoint_off_axes :
    matrixProductDeterminantWitnessPoint k ∈ matrixProductDeterminantZeroComponent k ∧
      matrixProductDeterminantWitnessPoint k ∉ matrixProductYZeroComponent k ∧
      matrixProductDeterminantWitnessPoint k ∉ matrixProductXZeroComponent k := by
  -- Evaluate the two determinants and the two surviving entries with the quotient homomorphism
  -- attached to the witness point.
  have hdetX : matrixProductDeterminantWitnessHom k ((matrixProductGenericMatrix k 0).det) = 0 := by
    simp [matrixProductDeterminantWitnessHom, matrixProductDeterminantWitnessEval,
      matrixProductGenericMatrix, matrixProductPolynomialMatrix, Matrix.det_fin_two,
      Matrix.mvPolynomialX_apply, MvPolynomial.rename_X]
  have hdetY : matrixProductDeterminantWitnessHom k ((matrixProductGenericMatrix k 1).det) = 0 := by
    simp [matrixProductDeterminantWitnessHom, matrixProductDeterminantWitnessEval,
      matrixProductGenericMatrix, matrixProductPolynomialMatrix, Matrix.det_fin_two,
      Matrix.mvPolynomialX_apply, MvPolynomial.rename_X]
  have hy10 : matrixProductDeterminantWitnessHom k ((matrixProductGenericMatrix k 1) 1 0) = 1 := by
    simp [matrixProductDeterminantWitnessHom, matrixProductDeterminantWitnessEval,
      matrixProductGenericMatrix, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X]
  have hx00 : matrixProductDeterminantWitnessHom k ((matrixProductGenericMatrix k 0) 0 0) = 1 := by
    simp [matrixProductDeterminantWitnessHom, matrixProductDeterminantWitnessEval,
      matrixProductGenericMatrix, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
      MvPolynomial.rename_X]
  refine ⟨?_, ?_, ?_⟩
  · rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus]
    rw [matrixProductDeterminantIdeal]
    refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨s, rfl⟩
    fin_cases s
    · simpa [matrixProductDeterminantWitnessPoint, RingHom.mem_ker] using hdetX
    · simpa [matrixProductDeterminantWitnessPoint, RingHom.mem_ker] using hdetY
  · intro hp
    have hy10mem :
        (matrixProductGenericMatrix k 1) 1 0 ∈
          RingHom.ker (matrixProductDeterminantWitnessHom k) := by
      have hentry : (matrixProductGenericMatrix k 1) 1 0 ∈ matrixProductEntryIdeal k 1 :=
        Ideal.subset_span ⟨(1, 0), rfl⟩
      rw [matrixProductYZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
      simpa [matrixProductDeterminantWitnessPoint] using hp hentry
    have hy10zero : matrixProductDeterminantWitnessHom k ((matrixProductGenericMatrix k 1) 1 0) = 0 :=
      RingHom.mem_ker.mp hy10mem
    have h10 : (1 : k) = 0 := by
      rw [← hy10]
      exact hy10zero
    exact one_ne_zero h10
  · intro hp
    have hx00mem :
        (matrixProductGenericMatrix k 0) 0 0 ∈
          RingHom.ker (matrixProductDeterminantWitnessHom k) := by
      have hentry : (matrixProductGenericMatrix k 0) 0 0 ∈ matrixProductEntryIdeal k 0 :=
        Ideal.subset_span ⟨(0, 0), rfl⟩
      rw [matrixProductXZeroComponent, PrimeSpectrum.mem_zeroLocus] at hp
      simpa [matrixProductDeterminantWitnessPoint] using hp hentry
    have hx00zero : matrixProductDeterminantWitnessHom k ((matrixProductGenericMatrix k 0) 0 0) = 0 :=
      RingHom.mem_ker.mp hx00mem
    have h10 : (1 : k) = 0 := by
      rw [← hx00]
      exact hx00zero
    exact one_ne_zero h10

/-- Helper for Example 10.35.23: the determinant component is irreducible.
The intended proof follows the source rank-one-chart argument on the basic opens where an
`X`-coordinate is invertible, then takes the closure of their irreducible union. -/
private theorem matrix_product_determinant_component_irreducible :
    IsIrreducible (matrixProductDeterminantZeroComponent k) := by
  -- Route correction: the earlier frontier asked for primeness of the determinant ideal.  The
  -- support API now proves the needed topological statement directly from the rank-one
  -- parametrization image, which is the smaller source-facing invariant.
  exact matrixProductDeterminantZeroComponent_isIrreducible (k := k)

-- Proof sketch: irreducible components of `Spec` correspond to minimal primes via
-- `minimalPrimes.equivIrreducibleComponents`. For the matrix-product quotient, the orbit analysis
-- in the text isolates the three strata `Y = 0`, `det X = det Y = 0`, and `X = 0`; one shows
-- that the corresponding quotient ideals are prime and exhaust the minimal primes.

/-- Chap10 Example 10 35 23 (2): the affine scheme of pairs of `2 × 2` matrices satisfying
`XY = 0` has three irreducible components, namely `Y = 0`, `det X = det Y = 0`, and `X = 0`. -/
@[stacks 00GF]
theorem matrixProductCoordinateRing_irreducibleComponents :
    irreducibleComponents (PrimeSpectrum (matrixProductCoordinateRing k)) =
      {matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
        matrixProductXZeroComponent k} :=
  by
    classical
    -- Follow the source proof by the finite closed cover coming from the three orbit types.
    refine irreducibleComponents_eq_of_finite_irreducible_closed_cover
      {matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
        matrixProductXZeroComponent k} ?_ ?_ ?_ ?_ ?_
    · simpa using Set.toFinite
        ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
          matrixProductXZeroComponent k} :
          Set (Set (PrimeSpectrum (matrixProductCoordinateRing k))))
    · ext p
      constructor
      · intro _
        simp
      · intro _
        rcases matrix_product_prime_lies_in_axis_or_determinant_component (k := k) p with hp | hp | hp
        · simp [hp]
        · simp [hp]
        · simp [hp]
    · intro Z hZ
      have hZmem :
          Z = matrixProductYZeroComponent k ∨
            Z = matrixProductDeterminantZeroComponent k ∨
            Z = matrixProductXZeroComponent k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
      rcases hZmem with rfl | rfl | rfl
      · -- Unfold the component definition and use that zero loci are closed.
        rw [matrixProductYZeroComponent]
        exact PrimeSpectrum.isClosed_zeroLocus
          (matrixProductEntryIdeal k 1 : Set (matrixProductCoordinateRing k))
      · -- Unfold the component definition and use that zero loci are closed.
        rw [matrixProductDeterminantZeroComponent]
        exact PrimeSpectrum.isClosed_zeroLocus
          (matrixProductDeterminantIdeal k : Set (matrixProductCoordinateRing k))
      · -- Unfold the component definition and use that zero loci are closed.
        rw [matrixProductXZeroComponent]
        exact PrimeSpectrum.isClosed_zeroLocus
          (matrixProductEntryIdeal k 0 : Set (matrixProductCoordinateRing k))
    · intro Z hZ
      have hZmem :
          Z = matrixProductYZeroComponent k ∨
            Z = matrixProductDeterminantZeroComponent k ∨
            Z = matrixProductXZeroComponent k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
      rcases hZmem with rfl | rfl | rfl
      · simpa [matrixProductYZeroComponent] using
          matrix_product_entry_component_irreducible (k := k) 1
      · exact matrix_product_determinant_component_irreducible (k := k)
      · simpa [matrixProductXZeroComponent] using
          matrix_product_entry_component_irreducible (k := k) 0
    · intro Z hZ
      have hZmem :
          Z = matrixProductYZeroComponent k ∨
            Z = matrixProductDeterminantZeroComponent k ∨
            Z = matrixProductXZeroComponent k := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hZ
      rcases hZmem with rfl | rfl | rfl
      · rintro hsubset
        obtain ⟨hpY, hpDet, hpX⟩ := matrixProductYZeroGenericPoint_off_other_components (k := k)
        have hpUnion :
            matrixProductYZeroGenericPoint k ∈
              ⋃₀ ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
                matrixProductXZeroComponent k} \ {matrixProductYZeroComponent k}) := hsubset hpY
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem :
            t = matrixProductYZeroComponent k ∨
              t = matrixProductDeterminantZeroComponent k ∨
              t = matrixProductXZeroComponent k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ matrixProductYZeroComponent k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl | rfl
        · exact False.elim (htNe rfl)
        · exact hpDet hpt
        · exact hpX hpt
      · rintro hsubset
        obtain ⟨hpDet, hpY, hpX⟩ := matrixProductDeterminantWitnessPoint_off_axes (k := k)
        have hpUnion :
            matrixProductDeterminantWitnessPoint k ∈
              ⋃₀ ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
                matrixProductXZeroComponent k} \ {matrixProductDeterminantZeroComponent k}) := hsubset hpDet
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem :
            t = matrixProductYZeroComponent k ∨
              t = matrixProductDeterminantZeroComponent k ∨
              t = matrixProductXZeroComponent k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ matrixProductDeterminantZeroComponent k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl | rfl
        · exact hpY hpt
        · exact False.elim (htNe rfl)
        · exact hpX hpt
      · rintro hsubset
        obtain ⟨hpX, hpDet, hpY⟩ := matrixProductXZeroGenericPoint_off_other_components (k := k)
        have hpUnion :
            matrixProductXZeroGenericPoint k ∈
              ⋃₀ ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
                matrixProductXZeroComponent k} \ {matrixProductXZeroComponent k}) := hsubset hpX
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem :
            t = matrixProductYZeroComponent k ∨
              t = matrixProductDeterminantZeroComponent k ∨
              t = matrixProductXZeroComponent k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ matrixProductXZeroComponent k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl | rfl
        · exact hpY hpt
        · exact hpDet hpt
        · exact False.elim (htNe rfl)

end
