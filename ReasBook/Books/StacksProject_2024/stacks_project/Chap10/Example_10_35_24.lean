import Mathlib

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
  sorry

/-- Example 10.35.24 (2): an idempotent matrix is conjugate to a
standard diagonal projection `diag(1, …, 1, 0, …, 0)`, indexed by its rank. -/
-- Proof sketch: every idempotent matrix is conjugate to some `rankProjectionMatrix n r`, so the
-- idempotent locus is stratified by rank. An idempotent matrix is diagonalizable with eigenvalues
-- in `{0, 1}`, hence is conjugate to some `rankProjectionMatrix n r`.
theorem isIdempotentElem_iff_exists_isConj_rankProjectionMatrix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} :
    IsIdempotentElem A ↔ ∃ r : Fin (n + 1), IsConj (rankProjectionMatrix k n r) A :=
  sorry

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
  sorry

/-- Example 10.35.24 (4): over a field of characteristic zero, trace separates the fixed-rank
conjugacy classes of idempotent matrices. -/
theorem trace_separates_rankProjectionConjugates (n : ℕ) [CharZero k]
    {A B : Matrix (Fin n) (Fin n) k} {r s : Fin (n + 1)}
    (hA : IsConj (rankProjectionMatrix k n r) A)
    (hB : IsConj (rankProjectionMatrix k n s) B)
    (hrs : r ≠ s) :
    A.trace ≠ B.trace := by
  have htraceA : A.trace = (r : k) := by
    sorry
  have htraceB : B.trace = (s : k) := by
    sorry
  rw [htraceA, htraceB]
  intro h
  apply hrs
  exact Fin.ext <| Nat.cast_injective h

-- Proof sketch: conjugation commutes with `exteriorPower.map`, so the third exterior-power trace
-- is constant on each orbit. For the standard diagonal idempotent of rank `r`, the induced action
-- on `⋀[k]^3 (Fin n → k)` is diagonal with one-dimensional eigenspaces indexed by `3`-element
-- subsets of the `r`-dimensional image, so its trace is `Nat.choose r 3`.
/-- On the conjugacy class of the standard rank-`r` idempotent, `tr(∧^3 T)` equals
`Nat.choose r 3`. -/
private theorem thirdExteriorPowerTrace_eq_choose_of_isConj_rankProjectionMatrix (n : ℕ)
    {A : Matrix (Fin n) (Fin n) k} {r : Fin (n + 1)}
    (hA : IsConj (rankProjectionMatrix k n r) A) :
    LinearMap.trace k _ (exteriorPower.map 3 A.toLin') = (Nat.choose (r : ℕ) 3 : k) :=
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
  rw [thirdExteriorPowerTrace_eq_choose_of_isConj_rankProjectionMatrix 3 hA,
    thirdExteriorPowerTrace_eq_choose_of_isConj_rankProjectionMatrix 3 hB]
  fin_cases r
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · simp at hr

end
