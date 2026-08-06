import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Corollary_20_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3

open AlgebraicTopology
open scoped Manifold

noncomputable section

section

variable {R : Type} [CommRing R]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = n)]

/-- The unique `R`-fundamental class compatible with the compact oriented manifold `o`. -/
noncomputable def canonicalRFundamentalClass (o : ROrientedManifold R I n M) :
    rSingularHomology R n (TopCat.of M) :=
  Classical.choose
    (ExistsUnique.exists (existsUnique_rFundamentalClassFor_of_representative_rOrientedManifold o))

/-- The canonical compatible `R`-fundamental class satisfies the orientation compatibility
predicate from Proposition 20.1.3. -/
theorem canonicalRFundamentalClass_spec (o : ROrientedManifold R I n M) :
    IsRFundamentalClassFor o (canonicalRFundamentalClass o) := by
  exact
    Classical.choose_spec
      (ExistsUnique.exists
        (existsUnique_rFundamentalClassFor_of_representative_rOrientedManifold o))

end

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {k : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = 4 * k)]

/-- The torsion-free middle-dimensional integral singular cohomology of a compact
`4 * k`-manifold. -/
abbrev middleDimensionalIntegralSingularCohomologyModTorsion
    (M : Type) [TopologicalSpace M] [ChartedSpace H M] :=
  integralSingularCohomologyModTorsion (TopCat.of M) (2 * k)

private theorem two_mul_le_four_mul (k : ℕ) : 2 * k ≤ 4 * k := by
  omega

private theorem four_mul_sub_two_mul (k : ℕ) : 4 * k - 2 * k = 2 * k := by
  omega

private theorem middleCupProductPairing_type
    (M : Type) [TopologicalSpace M] [ChartedSpace H M] :
    ((integralSingularCohomologyModTorsion (TopCat.of M) (2 * k)) →ₗ[ℤ]
        (integralSingularCohomologyModTorsion (TopCat.of M) (4 * k - 2 * k) →ₗ[ℤ] ℤ)) =
      ((middleDimensionalIntegralSingularCohomologyModTorsion (H := H) (k := k) M) →ₗ[ℤ]
        (middleDimensionalIntegralSingularCohomologyModTorsion (H := H) (k := k) M →ₗ[ℤ] ℤ)) := by
  simpa [middleDimensionalIntegralSingularCohomologyModTorsion] using congrArg
    (fun p ↦
      (integralSingularCohomologyModTorsion (TopCat.of M) (2 * k)) →ₗ[ℤ]
        (integralSingularCohomologyModTorsion (TopCat.of M) p →ₗ[ℤ] ℤ))
    (four_mul_sub_two_mul k)

/-- The middle-dimensional cup-product pairing on the torsion-free quotient of integral
cohomology, evaluated on the canonical compatible fundamental class of `o`. -/
noncomputable def middleCupProductPairing
    (o : ROrientedManifold ℤ I (4 * k) M) :
    middleDimensionalIntegralSingularCohomologyModTorsion (H := H) (k := k) M →ₗ[ℤ]
      middleDimensionalIntegralSingularCohomologyModTorsion (H := H) (k := k) M →ₗ[ℤ] ℤ :=
  cast (middleCupProductPairing_type (H := H) M)
    (cupProductFundamentalClassPairingModTorsion
      o
      (canonicalRFundamentalClass o)
      (canonicalRFundamentalClass_spec o)
      (2 * k)
      (two_mul_le_four_mul k))

/-- The quadratic form `x ↦ ⟨x ∪ x, [M]⟩` on the torsion-free middle-dimensional cohomology of a
compact oriented `4 * k`-manifold. -/
abbrev middleCupProductQuadraticForm
    (o : ROrientedManifold ℤ I (4 * k) M) :
    QuadraticForm ℤ
      (middleDimensionalIntegralSingularCohomologyModTorsion (H := H) (k := k) M) :=
  LinearMap.BilinMap.toQuadraticMap (middleCupProductPairing o)

/-- The signature of the middle-dimensional cup-product form of a compact oriented
`4 * k`-manifold. -/
noncomputable def manifoldIndexFourMul (o : ROrientedManifold ℤ I (4 * k) M) : ℤ :=
  (sigPos (middleCupProductQuadraticForm o) : ℤ) -
    sigNeg (middleCupProductQuadraticForm o)

/-- Unfolding `manifoldIndexFourMul` recovers the signature expression attached to the
middle-dimensional cup-product quadratic form. -/
theorem manifoldIndexFourMul_def (o : ROrientedManifold ℤ I (4 * k) M) :
    manifoldIndexFourMul o =
      (sigPos (middleCupProductQuadraticForm o) : ℤ) -
        sigNeg (middleCupProductQuadraticForm o) :=
  rfl

end

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = n)]

private theorem eq_four_mul_div_of_modEq_zero (n : ℕ) (h : n % 4 = 0) :
    n = 4 * (n / 4) := by
  simpa [h] using (Nat.mod_add_div n 4).symm

@[reducible] private def castROrientedManifold
    {m : ℕ} [Fact (Module.finrank ℝ E = m)]
    (h : n = m) (o : ROrientedManifold ℤ I n M) :
    ROrientedManifold ℤ I m M :=
  by
    subst h
    simpa using o

/-- Definition 21.2.2. For a compact oriented manifold `M`, the index `I(M)` is the signature of
the middle-dimensional cup-product form when `dim M = 4 * k`, and `I(M) = 0` in the remaining
dimensions. Here the compatible fundamental class is the canonical one from Proposition 20.1.3.
-/
noncomputable def manifoldIndex (o : ROrientedManifold ℤ I n M) : ℤ :=
  if h : n % 4 = 0 then
    let k := n / 4
    letI : Fact (Module.finrank ℝ E = 4 * k) := ⟨by
      calc
        Module.finrank ℝ E = n := (show Module.finrank ℝ E = n from Fact.out)
        _ = 4 * k := by simpa [k] using eq_four_mul_div_of_modEq_zero n h⟩
    let o' : ROrientedManifold ℤ I (4 * k) M :=
      castROrientedManifold (eq_four_mul_div_of_modEq_zero n h) o
    manifoldIndexFourMul o'
  else
    0

/-- If the dimension of the oriented manifold is not divisible by `4`, then Definition 21.2.2
sets the index equal to `0`. -/
theorem manifoldIndex_eq_zero_of_mod_ne_zero
    (o : ROrientedManifold ℤ I n M) (h : n % 4 ≠ 0) :
    manifoldIndex o = 0 := by
  simp [manifoldIndex, h]

end

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {k : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = 4 * k)]

/-- In the `4 * k`-dimensional case, `manifoldIndex` reduces to the signature of the
middle-dimensional cup-product form. -/
theorem manifoldIndex_eq_manifoldIndexFourMul
    (o : ROrientedManifold ℤ I (4 * k) M) :
    manifoldIndex o = manifoldIndexFourMul o := by
  sorry

end
