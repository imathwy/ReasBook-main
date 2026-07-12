import Mathlib
import StacksProject_2024.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MvPolynomial
open HomogeneousLocalization
open IsLocalization
open scoped AffineBlowupChart

section

variable {R : Type u} [CommRing R]
variable (n : ℕ) [NeZero n]

local notation "P" => MvPolynomial (Fin n) R
local notation "S" => MvPolynomial (Fin (n - 1)) P

local notation "Icoord" => idealOfVars (Fin n) R

/-- The index shift sending the presentation variable `x_{i+2}` to the polynomial variable
`t_{i+2}`. -/
private def polynomialAffineBlowupChartIndex (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by omega⟩

/-- The coordinate variable `t_{i+2}` viewed as an element of `(t_1, \ldots, t_n)`. -/
private noncomputable def polynomialAffineBlowupChartNumerator (i : Fin (n - 1)) : Icoord :=
  ⟨X (polynomialAffineBlowupChartIndex n i),
    Ideal.subset_span (Set.mem_range_self (polynomialAffineBlowupChartIndex n i))⟩

/-- The distinguished denominator `t_1` viewed as an element of `(t_1, \ldots, t_n)`. -/
private noncomputable def polynomialAffineBlowupChartDenominator : Icoord :=
  ⟨X (0 : Fin n), Ideal.subset_span (Set.mem_range_self (0 : Fin n))⟩

local notation "Chart" => affineBlowupChart Icoord (polynomialAffineBlowupChartDenominator n)

/-- The canonical generator `t_{i+2} / t_1` of the affine blowup chart `P[I/t_1]`. -/
private noncomputable def polynomialAffineBlowupChartGenerator (i : Fin (n - 1)) : Chart :=
  affineBlowupChartBasicFraction Icoord (polynomialAffineBlowupChartDenominator n)
    (polynomialAffineBlowupChartNumerator n i)

/-- Helper for Chap10 Example 10 70 5: a power of the chart parameter is a denominator in the
ordinary away-localization. -/
private theorem affineBlowupChartParameterPow_mem (I : Ideal R) (a : I) (m : ℕ) :
    a.1 ^ m ∈ Submonoid.powers a.1 := by
  -- The away submonoid consists exactly of powers of the chosen parameter.
  exact ⟨m, rfl⟩

/-- Helper for Chap10 Example 10 70 5: the chart parameter itself is a denominator in the
ordinary away-localization. -/
private theorem affineBlowupChartParameter_mem (I : Ideal R) (a : I) :
    a.1 ∈ Submonoid.powers a.1 := by
  -- This is the first power of the chosen parameter.
  simpa using affineBlowupChartParameterPow_mem I a 1

/-- Helper for Chap10 Example 10 70 5: the comparison map sends `x/a` in the homogeneous chart
to the ordinary localization fraction `x/a`. -/
private theorem affineBlowupChartToLocalizationAway_basicFraction
    (I : Ideal R) (a x : I) :
    affineBlowupChartToLocalizationAway I a (affineBlowupChartBasicFraction I a x) =
      Localization.mk x.1 ⟨a.1, affineBlowupChartParameter_mem I a⟩ := by
  let denom : Submonoid.powers a.1 := ⟨a.1, affineBlowupChartParameter_mem I a⟩
  let invDenom : Localization.Away a.1 := Localization.mk 1 denom
  let g : reesAlgebra I →+* Localization.Away a.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
      (reesAlgebra I).toSubring.subtype
  have hfrac (r : R) :
      algebraMap R (Localization.Away a.1) r * invDenom =
        Localization.mk r denom := by
    -- Multiplying by `1/a` gives the ordinary fraction with denominator `a`.
    change algebraMap R (Localization.Away a.1) r * Localization.mk 1 denom =
      Localization.mk r denom
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact (Localization.mk_eq_mk'_apply r denom).symm
  have hgDen :
      g (reesAlgebraDegreeOne I a) =
        algebraMap R (Localization.Away a.1) a.1 := by
    -- The Rees degree-one element `a t` evaluates to `a` when `t = 1`.
    simp [g, reesAlgebraDegreeOne]
  have hInv : g (reesAlgebraDegreeOne I a) * invDenom = 1 := by
    -- The selected inverse of the image of `a t` is the usual fraction `1/a`.
    rw [hgDen]
    rw [hfrac]
    exact Localization.mk_self denom
  have h :=
    Localization.awayLift_mk g (reesAlgebraDegreeOne I a) (reesAlgebraDegreeOne I x)
      invDenom hInv 1
  -- Evaluate the homogeneous fraction through the universal property of ordinary localization.
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply]
  simpa [g, invDenom, denom, affineBlowupChartBasicFraction, reesAlgebraDegreeOne, pow_one,
    hfrac] using h

/-- Helper for Chap10 Example 10 70 5: a monomial whose coefficient lies in `I^m` belongs to
the matching Rees grade. -/
private theorem reesMonomial_mem_grade
    (I : Ideal R) (m : ℕ) (r : ↥(I ^ m)) :
    (⟨Polynomial.monomial m r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I m := by
  -- The grade is the range of the degree-`m` monomial map.
  change (⟨Polynomial.monomial m r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      LinearMap.range _
  exact ⟨r, rfl⟩

/-- Helper for Chap10 Example 10 70 5: the same Rees monomial has the degree required for a
chart fraction with denominator `(a^(1))^m`. -/
private theorem reesMonomial_mem_chartGrade
    (I : Ideal R) (m : ℕ) (r : ↥(I ^ m)) :
    (⟨Polynomial.monomial m r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I (m • 1) := by
  -- In the natural-number grading, `m • 1` is definitionally `m` after normalization.
  simpa [nsmul_eq_mul] using reesMonomial_mem_grade I m r

/-- Helper for Chap10 Example 10 70 5: a normalized homogeneous chart fraction maps to the
ordinary fraction `r/a^m`. -/
private theorem affineBlowupChartToLocalizationAway_fraction_of_monomial
    (I : Ideal R) (a : I) (m : ℕ) (r : ↥(I ^ m)) :
    affineBlowupChartToLocalizationAway I a
      (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) m
        (⟨Polynomial.monomial m r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
        (reesMonomial_mem_chartGrade I m r)) =
      Localization.mk r.1 ⟨a.1 ^ m, affineBlowupChartParameterPow_mem I a m⟩ := by
  let denom : Submonoid.powers a.1 := ⟨a.1, affineBlowupChartParameter_mem I a⟩
  let denomPow : Submonoid.powers a.1 :=
    ⟨a.1 ^ m, affineBlowupChartParameterPow_mem I a m⟩
  let invDenom : Localization.Away a.1 := Localization.mk 1 denom
  let s : reesAlgebra I :=
    ⟨Polynomial.monomial m r.1, (reesAlgebra.monomial_mem).2 r.2⟩
  let g : reesAlgebra I →+* Localization.Away a.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
      (reesAlgebra I).toSubring.subtype
  have hfrac_one (y : R) :
      algebraMap R (Localization.Away a.1) y * invDenom =
        Localization.mk y denom := by
    -- Multiplication by the chosen inverse of `a` gives denominator `a`.
    change algebraMap R (Localization.Away a.1) y * Localization.mk 1 denom =
      Localization.mk y denom
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact (Localization.mk_eq_mk'_apply y denom).symm
  have hfrac_pow (y : R) :
      algebraMap R (Localization.Away a.1) y *
          Localization.mk 1 denomPow =
        Localization.mk y denomPow := by
    -- The same calculation works for the denominator `a^m`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact (Localization.mk_eq_mk'_apply y denomPow).symm
  have hgDen :
      g (reesAlgebraDegreeOne I a) =
        algebraMap R (Localization.Away a.1) a.1 := by
    -- The Rees degree-one element `a t` evaluates to `a`.
    simp [g, reesAlgebraDegreeOne]
  have hInv : g (reesAlgebraDegreeOne I a) * invDenom = 1 := by
    -- The inverse used by the away lift is the standard fraction `1/a`.
    rw [hgDen]
    rw [hfrac_one]
    exact Localization.mk_self denom
  have h :=
    Localization.awayLift_mk g (reesAlgebraDegreeOne I a) s invDenom hInv m
  have hpow : invDenom ^ m = Localization.mk 1 denomPow := by
    -- Powers of `1/a` are represented by `1/a^m`.
    rw [Localization.mk_pow, one_pow]
    apply congrArg (fun d : Submonoid.powers a.1 ↦ Localization.mk 1 d)
    ext
    simp [denom, denomPow]
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply]
  rw [hpow] at h
  simpa [g, s, invDenom, denom, denomPow, reesAlgebraDegreeOne, hfrac_pow] using h

/-- Helper for Chap10 Example 10 70 5: if a power of the chart parameter kills the coefficient,
then the corresponding normalized chart fraction is zero. -/
private theorem affineBlowupChartFraction_eq_zero_of_parameterPow_mul_eq_zero
    (I : Ideal R) (a : I) (m k : ℕ) (r : ↥(I ^ m)) (hzero : a.1 ^ k * r.1 = 0) :
    HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) m
      (⟨Polynomial.monomial m r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
      (reesMonomial_mem_chartGrade I m r) = 0 := by
  -- It is enough to compare values in the ordinary localization of the Rees algebra.
  apply (HomogeneousLocalization.ext_iff_val _ _).2
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨reesAlgebraDegreeOne I a ^ k, ⟨k, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hzero' : r.1 * a.1 ^ k = 0 := by
    simpa [mul_comm] using hzero
  -- Multiplying by `(a t)^k` produces the zero Rees monomial.
  simp [reesAlgebraDegreeOne, Polynomial.monomial_mul_monomial, hzero', mul_comm]

/-- Helper for Chap10 Example 10 70 5: the comparison map from an affine blowup chart to the
ordinary localization away from the chart parameter is injective. -/
private theorem affineBlowupChartToLocalizationAway_injective
    (I : Ideal R) (a : I) :
    Function.Injective (affineBlowupChartToLocalizationAway I a) := by
  suffices hker : ∀ z : R[I / a], affineBlowupChartToLocalizationAway I a z = 0 → z = 0 by
    intro z w hzw
    -- Injectivity follows from the triviality of the kernel.
    apply sub_eq_zero.mp
    apply hker
    simpa [map_sub, hzw]
  intro z hz
  -- Normalize an arbitrary chart element to a homogeneous monomial numerator.
  obtain ⟨m, s, hs, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) z
  have hs' : s ∈ reesAlgebraGrade I m := by
    simpa [nsmul_eq_mul] using hs
  change s ∈ LinearMap.range _ at hs'
  rcases hs' with ⟨r, rfl⟩
  change
    affineBlowupChartToLocalizationAway I a
      (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) m
        (⟨Polynomial.monomial m r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
        (reesMonomial_mem_chartGrade I m r)) = 0 at hz
  rw [affineBlowupChartToLocalizationAway_fraction_of_monomial I a m r,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at hz
  rcases hz with ⟨u, hu⟩
  rcases u.2 with ⟨k, hk⟩
  have hz' : a.1 ^ k * r.1 = 0 := by
    simpa [hk] using hu
  -- Pull the ordinary-localization zero criterion back to the homogeneous chart.
  simpa using
    affineBlowupChartFraction_eq_zero_of_parameterPow_mul_eq_zero I a m k r hz'

/-- Helper for Chap10 Example 10 70 5: in the affine blowup chart, `(x/a) * a = x`. -/
private theorem affineBlowupChartBasicFraction_mul_chartParameter
    (I : Ideal R) (a x : I) :
    affineBlowupChartBasicFraction I a x * algebraMap R R[I / a] a.1 =
      algebraMap R R[I / a] x.1 := by
  apply affineBlowupChartToLocalizationAway_injective I a
  -- In ordinary localization this is the standard cancellation of the denominator `a`.
  rw [map_mul, affineBlowupChartToLocalizationAway_basicFraction,
    affineBlowupChartToLocalizationAway_algebraMap,
    affineBlowupChartToLocalizationAway_algebraMap, Localization.mk_eq_mk'_apply,
    ← IsLocalization.mk'_one (M := Submonoid.powers a.1) (Localization.Away a.1) a.1,
    ← IsLocalization.mk'_mul (M := Submonoid.powers a.1) (Localization.Away a.1)]
  simpa using
    (IsLocalization.mk'_mul_cancel_right (M := Submonoid.powers a.1)
      (x := x.1)
      (y := ⟨a.1, affineBlowupChartParameter_mem I a⟩))

/-- The relation `t_1 x_{i+2} - t_{i+2}` in the polynomial presentation of the chart. -/
private noncomputable def polynomialAffineBlowupChartRelation (i : Fin (n - 1)) : S :=
  C (X (0 : Fin n) : P) * X i - C (X (polynomialAffineBlowupChartIndex n i) : P)

/-- The ideal generated by the relations `t_1 x_j - t_j` for `j = 2, \ldots, n`. -/
private noncomputable def polynomialAffineBlowupChartRelationIdeal : Ideal S :=
  Ideal.span (Set.range fun i : Fin (n - 1) ↦ polynomialAffineBlowupChartRelation n i)

/-- The quotient `P[x_2, \ldots, x_n] / (t_1 x_2 - t_2, \ldots, t_1 x_n - t_n)`. -/
private abbrev polynomialAffineBlowupChartQuotient :=
  S ⧸ polynomialAffineBlowupChartRelationIdeal n

local notation "Q" => @polynomialAffineBlowupChartQuotient R _ n _

/-- The canonical `P`-algebra map sending each `x_{i+2}` to `t_{i+2} / t_1`. -/
private noncomputable def polynomialAffineBlowupChartToAffineBlowup : S →ₐ[P] Chart :=
  aeval (polynomialAffineBlowupChartGenerator n)

/-- Each defining relation `t_1 x_{i+2} - t_{i+2}` maps to zero in `P[I/t_1]`. -/
private theorem polynomialAffineBlowupChartRelation_map_eq_zero (i : Fin (n - 1)) :
    polynomialAffineBlowupChartToAffineBlowup n (polynomialAffineBlowupChartRelation n i) =
      (0 : Chart) :=
  by
    -- Evaluation sends the relation to `t_1 * (t_{i+2}/t_1) - t_{i+2}`.
    simp only [polynomialAffineBlowupChartToAffineBlowup,
      polynomialAffineBlowupChartRelation, map_sub, map_mul, aeval_C, aeval_X]
    -- The basic fraction identity cancels the chart parameter.
    rw [mul_comm]
    rw [polynomialAffineBlowupChartGenerator]
    have hbasic :
        affineBlowupChartBasicFraction Icoord (polynomialAffineBlowupChartDenominator n)
            (polynomialAffineBlowupChartNumerator n i) *
          (algebraMap P Chart) (X (0 : Fin n)) =
            (algebraMap P Chart) (X (polynomialAffineBlowupChartIndex n i)) := by
      -- The generic chart identity specializes to the displayed coordinate variables.
      simpa [polynomialAffineBlowupChartNumerator, polynomialAffineBlowupChartDenominator] using
        affineBlowupChartBasicFraction_mul_chartParameter Icoord
          (polynomialAffineBlowupChartDenominator n)
          (polynomialAffineBlowupChartNumerator n i)
    rw [hbasic]
    simp

/-- Every element of the relation ideal maps to zero in the affine blowup chart. -/
private theorem polynomialAffineBlowupChartRelationIdeal_map_eq_zero
    (f : S) (hf : f ∈ polynomialAffineBlowupChartRelationIdeal n) :
    polynomialAffineBlowupChartToAffineBlowup n f = (0 : Chart) := by
  -- The relation ideal is contained in the kernel because all displayed generators vanish.
  have hker : polynomialAffineBlowupChartRelationIdeal n ≤
      RingHom.ker
        ((polynomialAffineBlowupChartToAffineBlowup n).toRingHom : S →+* Chart) := by
    rw [polynomialAffineBlowupChartRelationIdeal]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact polynomialAffineBlowupChartRelation_map_eq_zero n i
  exact RingHom.mem_ker.mp (hker hf)

/-- The quotient presentation map from `P[x_2, \ldots, x_n]/(t_1 x_j - t_j)` to `P[I/t_1]`. -/
private noncomputable def polynomialAffineBlowupChartMap :
    Q →ₐ[P] Chart :=
  Ideal.Quotient.liftₐ (polynomialAffineBlowupChartRelationIdeal n)
    (polynomialAffineBlowupChartToAffineBlowup n)
    (polynomialAffineBlowupChartRelationIdeal_map_eq_zero n)

local notation "chartMap" => @polynomialAffineBlowupChartMap R _ n _

/-- Helper for Chap10 Example 10 70 5: the quotient presentation map agrees with the
unquotiented evaluation map on quotient classes. -/
private theorem polynomialAffineBlowupChartMap_apply_mk (f : S) :
    polynomialAffineBlowupChartMap n
        (Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) f) =
      polynomialAffineBlowupChartToAffineBlowup n f := by
  -- The quotient map was defined by `Ideal.Quotient.liftₐ`, so representatives compute directly.
  simp [polynomialAffineBlowupChartMap]

/-- Helper for Chap10 Example 10 70 5: each presentation variable maps to the corresponding
basic fraction `t_{i+2}/t_1`. -/
private theorem polynomialAffineBlowupChartMap_apply_variable (i : Fin (n - 1)) :
    polynomialAffineBlowupChartMap n
        (Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) (X i : S)) =
      polynomialAffineBlowupChartGenerator n i := by
  -- Variables compute through the evaluation map before passing to the quotient.
  simpa [polynomialAffineBlowupChartToAffineBlowup] using
    polynomialAffineBlowupChartMap_apply_mk (R := R) n (X i : S)

/-- Helper for Chap10 Example 10 70 5: every displayed basic fraction lies in the range of the
quotient presentation map. -/
private theorem polynomialAffineBlowupChartGenerator_mem_range (i : Fin (n - 1)) :
    polynomialAffineBlowupChartGenerator n i ∈ (AlgHom.range chartMap : Subalgebra P Chart) := by
  -- The quotient class of the variable `x_{i+2}` is a preimage of this basic fraction.
  refine ⟨Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) (X i : S), ?_⟩
  exact polynomialAffineBlowupChartMap_apply_variable n i

/-- Helper for Chap10 Example 10 70 5: all base-polynomial elements are in the range of the
quotient presentation map. -/
private theorem polynomialAffineBlowupChartMap_algebraMap_mem_range (p : P) :
    algebraMap P Chart p ∈ (AlgHom.range chartMap : Subalgebra P Chart) := by
  -- Since `chartMap` is a `P`-algebra homomorphism, it fixes every element coming from `P`.
  refine ⟨algebraMap P Q p, ?_⟩
  exact (polynomialAffineBlowupChartMap n).commutes p

/-- Helper for Chap10 Example 10 70 5: if the basic fractions generate the affine chart over
`P`, then the quotient presentation map is surjective. -/
private theorem polynomialAffineBlowupChartMap_surjective_of_adjoin_generators
    (hgen : Algebra.adjoin P (Set.range (polynomialAffineBlowupChartGenerator n)) =
      (⊤ : Subalgebra P Chart)) :
    Function.Surjective chartMap := by
  -- The range is a `P`-subalgebra containing every basic fraction, hence it contains their
  -- `P`-algebra closure; the generation hypothesis makes that closure all of the chart.
  refine (AlgHom.range_eq_top chartMap).mp ?_
  apply top_unique
  rw [← hgen]
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact polynomialAffineBlowupChartGenerator_mem_range n i

/-- Helper for Chap10 Example 10 70 5: the degree-one Rees generator attached to a coordinate
variable. -/
private noncomputable def polynomialAffineBlowupCoordinateReesGenerator (i : Fin n) :
    reesAlgebra Icoord :=
  reesAlgebraDegreeOne Icoord ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩

omit [NeZero n] in
/-- Helper for Chap10 Example 10 70 5: a coordinate Rees generator has degree one. -/
private theorem polynomialAffineBlowupCoordinateReesGenerator_mem_grade (i : Fin n) :
    polynomialAffineBlowupCoordinateReesGenerator n i ∈ reesAlgebraGrade Icoord 1 := by
  -- This is the defining degree-one membership theorem for Rees generators.
  exact reesAlgebraDegreeOne_mem Icoord ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩

omit [NeZero n] in
/-- Helper for Chap10 Example 10 70 5: a degree-one monomial with coordinate-ideal coefficient
belongs to the coordinate Rees algebra. -/
private theorem polynomialAffineBlowupCoordinateDegreeOneMonomial_mem
    (r : P) (hr : r ∈ Icoord) :
    Polynomial.monomial 1 r ∈ reesAlgebra Icoord := by
  -- Degree-one Rees membership is exactly membership of the coefficient in the ideal.
  exact (reesAlgebra.monomial_mem).2 (by simpa [pow_one] using hr)

omit [NeZero n] in
/-- Helper for Chap10 Example 10 70 5: a base polynomial gives a degree-zero Rees element. -/
private theorem polynomialAffineBlowupChartGradeZero_mem (p : P) :
    algebraMap P (reesAlgebra Icoord) p ∈ reesAlgebraGrade Icoord 0 := by
  -- The zero-degree piece is the range of constant Rees monomials.
  change algebraMap P (reesAlgebra Icoord) p ∈ LinearMap.range _
  exact ⟨⟨p, by simp⟩, rfl⟩

/-- Helper for Chap10 Example 10 70 5: the degree-zero Rees element associated to a base
polynomial. -/
private noncomputable def polynomialAffineBlowupChartGradeZero (p : P) :
    reesAlgebraGrade Icoord 0 :=
  ⟨algebraMap P (reesAlgebra Icoord) p, polynomialAffineBlowupChartGradeZero_mem n p⟩

omit [NeZero n] in
/-- Helper for Chap10 Example 10 70 5: any degree-one coordinate-ideal Rees monomial lies in the
algebra generated by the coordinate Rees generators over degree zero. -/
private theorem polynomialAffineBlowupCoordinateDegreeOneRees_mem_adjoin
    (r : P) (hr : r ∈ Icoord) (hmem : Polynomial.monomial 1 r ∈ reesAlgebra Icoord) :
    (⟨Polynomial.monomial 1 r, hmem⟩ : reesAlgebra Icoord) ∈
      Algebra.adjoin (reesAlgebraGrade Icoord 0)
        (Set.range (polynomialAffineBlowupCoordinateReesGenerator n) :
          Set (reesAlgebra Icoord)) := by
  let A : Subalgebra (reesAlgebraGrade Icoord 0) (reesAlgebra Icoord) :=
    Algebra.adjoin (reesAlgebraGrade Icoord 0)
      (Set.range (polynomialAffineBlowupCoordinateReesGenerator n) : Set (reesAlgebra Icoord))
  rw [idealOfVars] at hr
  change (⟨Polynomial.monomial 1 r, hmem⟩ : reesAlgebra Icoord) ∈ A
  -- Induct through the span presentation of the coordinate ideal.
  refine Submodule.span_induction
    (p := fun r hr ↦ ∀ hmem : Polynomial.monomial 1 r ∈ reesAlgebra Icoord,
      (⟨Polynomial.monomial 1 r, hmem⟩ : reesAlgebra Icoord) ∈ A)
    ?_ ?_ ?_ ?_ hr hmem
  · intro x hx hmem
    rcases hx with ⟨i, rfl⟩
    change polynomialAffineBlowupCoordinateReesGenerator n i ∈ A
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  · intro hmem
    have hzero : (⟨Polynomial.monomial 1 0, hmem⟩ : reesAlgebra Icoord) = 0 := by
      apply Subtype.ext
      simp
    rw [hzero]
    exact zero_mem A
  · intro x y hx hy hxmem hymem hmem
    have hx' := hxmem (polynomialAffineBlowupCoordinateDegreeOneMonomial_mem n x hx)
    have hy' := hymem (polynomialAffineBlowupCoordinateDegreeOneMonomial_mem n y hy)
    have hxy :
        (⟨Polynomial.monomial 1 (x + y), hmem⟩ : reesAlgebra Icoord) =
          (⟨Polynomial.monomial 1 x,
            polynomialAffineBlowupCoordinateDegreeOneMonomial_mem n x hx⟩ : reesAlgebra Icoord) +
          (⟨Polynomial.monomial 1 y,
            polynomialAffineBlowupCoordinateDegreeOneMonomial_mem n y hy⟩ : reesAlgebra Icoord) := by
      apply Subtype.ext
      simp
    rw [hxy]
    exact add_mem hx' hy'
  · intro a x hx hxmem hmem
    have hx' := hxmem (polynomialAffineBlowupCoordinateDegreeOneMonomial_mem n x hx)
    have hcoeff :
        algebraMap (reesAlgebraGrade Icoord 0) (reesAlgebra Icoord)
          (polynomialAffineBlowupChartGradeZero n a) ∈ A := by
      exact Subalgebra.algebraMap_mem A (polynomialAffineBlowupChartGradeZero n a)
    have hax :
        (⟨Polynomial.monomial 1 (a • x), hmem⟩ : reesAlgebra Icoord) =
          algebraMap (reesAlgebraGrade Icoord 0) (reesAlgebra Icoord)
            (polynomialAffineBlowupChartGradeZero n a) *
          (⟨Polynomial.monomial 1 x,
            polynomialAffineBlowupCoordinateDegreeOneMonomial_mem n x hx⟩ : reesAlgebra Icoord) := by
      apply Subtype.ext
      simp [polynomialAffineBlowupChartGradeZero, smul_eq_mul]
    rw [hax]
    exact mul_mem hcoeff hx'

omit [NeZero n] in
/-- Helper for Chap10 Example 10 70 5: membership in the coordinate degree-one adjoin gives Rees
membership. -/
private theorem polynomialAffineBlowupCoordinateAdjoin_mem_rees {p : Polynomial P}
    (hp : p ∈ Algebra.adjoin P
      (Submodule.map (Polynomial.monomial 1 : P →ₗ[P] Polynomial P) Icoord :
        Set (Polynomial P))) :
    p ∈ reesAlgebra Icoord := by
  -- Mathlib identifies the Rees algebra with the algebra generated by degree-one ideal monomials.
  rw [← adjoin_monomial_eq_reesAlgebra]
  exact hp

omit [NeZero n] in
/-- Helper for Chap10 Example 10 70 5: the coordinate Rees generators generate the Rees algebra
over degree zero. -/
private theorem polynomialAffineBlowupCoordinateReesGenerators_adjoin_eq_top :
    Algebra.adjoin (reesAlgebraGrade Icoord 0)
        (Set.range (polynomialAffineBlowupCoordinateReesGenerator n) :
          Set (reesAlgebra Icoord)) = ⊤ := by
  let A : Subalgebra (reesAlgebraGrade Icoord 0) (reesAlgebra Icoord) :=
    Algebra.adjoin (reesAlgebraGrade Icoord 0)
      (Set.range (polynomialAffineBlowupCoordinateReesGenerator n) : Set (reesAlgebra Icoord))
  rw [← top_le_iff]
  intro y _hy
  change y ∈ A
  have hyadjoin : (y : Polynomial P) ∈
      Algebra.adjoin P
        (Submodule.map (Polynomial.monomial 1 : P →ₗ[P] Polynomial P) Icoord :
          Set (Polynomial P)) := by
    rw [adjoin_monomial_eq_reesAlgebra]
    exact y.2
  -- Induct through the algebra generated by degree-one coordinate-ideal monomials.
  refine Algebra.adjoin_induction
    (p := fun p hp ↦ ∀ hmem : p ∈ reesAlgebra Icoord,
      (⟨p, hmem⟩ : reesAlgebra Icoord) ∈ A)
    ?_ ?_ ?_ ?_ hyadjoin y.2
  · intro p hp hmem
    rcases hp with ⟨r, hr, rfl⟩
    exact polynomialAffineBlowupCoordinateDegreeOneRees_mem_adjoin n r hr hmem
  · intro p hmem
    have hconst : (⟨algebraMap P (Polynomial P) p, hmem⟩ : reesAlgebra Icoord) =
        algebraMap (reesAlgebraGrade Icoord 0) (reesAlgebra Icoord)
          (polynomialAffineBlowupChartGradeZero n p) := by
      rfl
    rw [hconst]
    exact Subalgebra.algebraMap_mem A (polynomialAffineBlowupChartGradeZero n p)
  · intro p q hp hq hpmem hqmem hmem
    have hp_rees : p ∈ reesAlgebra Icoord :=
      polynomialAffineBlowupCoordinateAdjoin_mem_rees n hp
    have hq_rees : q ∈ reesAlgebra Icoord :=
      polynomialAffineBlowupCoordinateAdjoin_mem_rees n hq
    have hp' := hpmem hp_rees
    have hq' := hqmem hq_rees
    have hadd : (⟨p + q, hmem⟩ : reesAlgebra Icoord) =
        (⟨p, hp_rees⟩ : reesAlgebra Icoord) + (⟨q, hq_rees⟩ : reesAlgebra Icoord) := by
      rfl
    rw [hadd]
    exact add_mem hp' hq'
  · intro p q hp hq hpmem hqmem hmem
    have hp_rees : p ∈ reesAlgebra Icoord :=
      polynomialAffineBlowupCoordinateAdjoin_mem_rees n hp
    have hq_rees : q ∈ reesAlgebra Icoord :=
      polynomialAffineBlowupCoordinateAdjoin_mem_rees n hq
    have hp' := hpmem hp_rees
    have hq' := hqmem hq_rees
    have hmul : (⟨p * q, hmem⟩ : reesAlgebra Icoord) =
        (⟨p, hp_rees⟩ : reesAlgebra Icoord) * (⟨q, hq_rees⟩ : reesAlgebra Icoord) := by
      rfl
    rw [hmul]
    exact mul_mem hp' hq'

/-- Helper for Chap10 Example 10 70 5: the `P`-algebra map to the chart is the degree-zero
homogeneous-localization map. -/
private theorem polynomialAffineBlowupChart_algebraMap_eq_fromZero (p : P) :
    algebraMap P Chart p =
      HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade Icoord)
        (Submonoid.powers (reesAlgebraDegreeOne Icoord (polynomialAffineBlowupChartDenominator n)))
        (polynomialAffineBlowupChartGradeZero n p) := by
  -- This unfolds the chart's `P`-algebra structure from Definition 10.70.1.
  rfl

/-- Helper for Chap10 Example 10 70 5: any degree-zero scalar of the homogeneous chart belongs to
every `P`-subalgebra of the chart. -/
private theorem polynomialAffineBlowupChart_gradeZero_algebraMap_mem_adjoin
    (A : Subalgebra P Chart) (r0 : reesAlgebraGrade Icoord 0) :
    algebraMap (reesAlgebraGrade Icoord 0) Chart r0 ∈ A := by
  rcases r0.2 with ⟨p, hp⟩
  have hval : r0 = polynomialAffineBlowupChartGradeZero n p.1 := by
    apply Subtype.ext
    rw [← hp]
    rfl
  have hmap :
      algebraMap (reesAlgebraGrade Icoord 0) Chart r0 = algebraMap P Chart p.1 := by
    rw [polynomialAffineBlowupChart_algebraMap_eq_fromZero]
    change HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade Icoord)
        (Submonoid.powers
          (reesAlgebraDegreeOne Icoord (polynomialAffineBlowupChartDenominator n))) r0 =
      HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade Icoord)
        (Submonoid.powers
          (reesAlgebraDegreeOne Icoord (polynomialAffineBlowupChartDenominator n)))
        (polynomialAffineBlowupChartGradeZero n p.1)
    rw [hval]
  rw [hmap]
  exact Subalgebra.algebraMap_mem A p.1

omit [NeZero n] in
/-- Helper for Chap10 Example 10 70 5: a coordinate Rees generator has the chart fraction degree. -/
private theorem polynomialAffineBlowupCoordinateReesGenerator_mem_chartGrade (i : Fin n) :
    polynomialAffineBlowupCoordinateReesGenerator n i ∈ reesAlgebraGrade Icoord (1 • 1) := by
  -- The chart denominator has degree one, so the one-step numerator degree is also `1 • 1`.
  simpa using polynomialAffineBlowupCoordinateReesGenerator_mem_grade n i

/-- Helper for Chap10 Example 10 70 5: the homogeneous chart fraction attached to an arbitrary
coordinate. -/
private noncomputable def polynomialAffineBlowupChartCoordinateFraction (i : Fin n) : Chart :=
  HomogeneousLocalization.Away.mk (reesAlgebraGrade Icoord)
    (reesAlgebraDegreeOne_mem Icoord (polynomialAffineBlowupChartDenominator n)) 1
    (polynomialAffineBlowupCoordinateReesGenerator n i)
    (polynomialAffineBlowupCoordinateReesGenerator_mem_chartGrade n i)

/-- Helper for Chap10 Example 10 70 5: the denominator coordinate fraction is `1`. -/
private theorem polynomialAffineBlowupChartCoordinateFraction_zero :
    polynomialAffineBlowupChartCoordinateFraction n 0 = (1 : Chart) := by
  -- Compare in the ordinary localization of the Rees algebra, where `f/f = 1`.
  apply (HomogeneousLocalization.ext_iff_val _ _).2
  rw [polynomialAffineBlowupChartCoordinateFraction, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one]
  simpa [polynomialAffineBlowupChartDenominator,
    polynomialAffineBlowupCoordinateReesGenerator] using
    (Localization.mk_self (M := reesAlgebra Icoord)
      (a := (⟨polynomialAffineBlowupCoordinateReesGenerator n 0,
        ⟨1, pow_one (polynomialAffineBlowupCoordinateReesGenerator n 0)⟩⟩ :
        Submonoid.powers (polynomialAffineBlowupCoordinateReesGenerator n 0))))

/-- Helper for Chap10 Example 10 70 5: every coordinate index is either the denominator index or a
shifted chart index. -/
private theorem polynomialAffineBlowupChartIndex_cases (j : Fin n) :
    j = 0 ∨ (∃ i : Fin (n - 1), j = polynomialAffineBlowupChartIndex n i) := by
  by_cases hj : j = 0
  · exact Or.inl hj
  · have hjpos : 0 < j.1 := by
      have hjval : j.1 ≠ 0 := by
        intro hzero
        apply hj
        ext
        simpa using hzero
      omega
    have hlt : j.1 - 1 < n - 1 := by
      omega
    -- A nonzero coordinate index is obtained by subtracting one and applying the chart shift.
    refine Or.inr ⟨⟨j.1 - 1, hlt⟩, ?_⟩
    ext
    simp [polynomialAffineBlowupChartIndex]
    omega

/-- Helper for Chap10 Example 10 70 5: shifted coordinate fractions are the displayed chart
generators. -/
private theorem polynomialAffineBlowupChartCoordinateFraction_index (i : Fin (n - 1)) :
    polynomialAffineBlowupChartCoordinateFraction (R := R) n
        (polynomialAffineBlowupChartIndex n i) =
      polynomialAffineBlowupChartGenerator (R := R) n i := by
  -- Both sides are the same homogeneous fraction `t_{i+2}^{(1)} / t_1^{(1)}`.
  rfl

/-- Helper for Chap10 Example 10 70 5: every coordinate fraction lies in the algebra generated by
the displayed tail fractions. -/
private theorem polynomialAffineBlowupChartCoordinateFraction_mem_adjoin (j : Fin n) :
    polynomialAffineBlowupChartCoordinateFraction n j ∈
      Algebra.adjoin P (Set.range (polynomialAffineBlowupChartGenerator n) : Set Chart) := by
  let A : Subalgebra P Chart :=
    Algebra.adjoin P (Set.range (polynomialAffineBlowupChartGenerator n) : Set Chart)
  -- Split off the denominator coordinate; all other coordinates are shifted tail generators.
  rcases polynomialAffineBlowupChartIndex_cases n j with hzero | hidx
  · subst j
    rw [polynomialAffineBlowupChartCoordinateFraction_zero]
    exact one_mem A
  · rcases hidx with ⟨i, hi⟩
    subst j
    rw [polynomialAffineBlowupChartCoordinateFraction_index]
    exact Algebra.subset_adjoin ⟨i, rfl⟩

/-- Helper for Chap10 Example 10 70 5: the localization value of a finite product is the product
of the localization values. -/
private theorem polynomialAffineBlowupChart_val_finset_prod
    {ι : Type*} (s : Finset ι) (f : ι → Chart) :
    HomogeneousLocalization.val (∏ i ∈ s, f i) =
      ∏ i ∈ s, HomogeneousLocalization.val (f i) := by
  classical
  -- The value map is multiplicative, so the statement follows by finite-product induction.
  induction s using Finset.induction_on with
  | empty =>
      simp [HomogeneousLocalization.val_one]
  | insert a s has ih =>
      simp [has, ih, HomogeneousLocalization.val_mul]

/-- Helper for Chap10 Example 10 70 5: a homogeneous product fraction is the product of the
corresponding coordinate fractions. -/
private theorem polynomialAffineBlowupChartProductFraction_eq
    (a : ℕ) (ai : Fin n → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) :
    HomogeneousLocalization.Away.mk (reesAlgebraGrade Icoord)
      (reesAlgebraDegreeOne_mem Icoord (polynomialAffineBlowupChartDenominator n)) a
      (∏ i, polynomialAffineBlowupCoordinateReesGenerator n i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded (reesAlgebraGrade Icoord)
        (fun _ : Fin n => (1 : ℕ)) (polynomialAffineBlowupCoordinateReesGenerator n) ai
        (fun i _ => polynomialAffineBlowupCoordinateReesGenerator_mem_grade n i)) =
    ∏ i, (polynomialAffineBlowupChartCoordinateFraction (R := R) n i) ^ ai i := by
  -- Compare the two expressions in the ambient localization and collect numerators and denominators.
  apply (HomogeneousLocalization.ext_iff_val _ _).2
  rw [HomogeneousLocalization.Away.val_mk]
  rw [polynomialAffineBlowupChart_val_finset_prod]
  simp only [HomogeneousLocalization.val_pow, polynomialAffineBlowupChartCoordinateFraction,
    HomogeneousLocalization.Away.val_mk]
  simp_rw [Localization.mk_pow]
  rw [Localization.mk_prod]
  congr 1
  have ha : ∑ i, ai i = a := by
    simpa using hai
  ext
  simp [ha, Finset.prod_pow_eq_pow_sum]

/-- Helper for Chap10 Example 10 70 5: every homogeneous product generator from the full
coordinate set lies in the algebra generated by the displayed tail fractions. -/
private theorem polynomialAffineBlowupChartProductFraction_mem_adjoin
    (a : ℕ) (ai : Fin n → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) :
    HomogeneousLocalization.Away.mk (reesAlgebraGrade Icoord)
      (reesAlgebraDegreeOne_mem Icoord (polynomialAffineBlowupChartDenominator n)) a
      (∏ i, polynomialAffineBlowupCoordinateReesGenerator n i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded (reesAlgebraGrade Icoord)
        (fun _ : Fin n => (1 : ℕ)) (polynomialAffineBlowupCoordinateReesGenerator n) ai
        (fun i _ => polynomialAffineBlowupCoordinateReesGenerator_mem_grade n i)) ∈
      Algebra.adjoin P (Set.range (polynomialAffineBlowupChartGenerator n) : Set Chart) := by
  -- Rewrite the product fraction as a product of coordinate fractions, each already in the tail
  -- generator algebra.
  rw [polynomialAffineBlowupChartProductFraction_eq (R := R) n a ai hai]
  exact prod_mem fun i _ =>
    pow_mem (polynomialAffineBlowupChartCoordinateFraction_mem_adjoin n i) (ai i)

/-- Helper for Chap10 Example 10 70 5: the affine chart is generated over `P` by the basic
fractions `t_{i+2}/t_1`. -/
private theorem polynomialAffineBlowupChart_generators_adjoin_eq_top :
    Algebra.adjoin P (Set.range (polynomialAffineBlowupChartGenerator n)) =
      (⊤ : Subalgebra P Chart) := by
  have hfull := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (𝒜 := reesAlgebraGrade Icoord)
    (f := reesAlgebraDegreeOne Icoord (polynomialAffineBlowupChartDenominator n))
    (d := (1 : ℕ))
    (reesAlgebraDegreeOne_mem Icoord (polynomialAffineBlowupChartDenominator n))
    (Fin n) (polynomialAffineBlowupCoordinateReesGenerator n)
    (polynomialAffineBlowupCoordinateReesGenerators_adjoin_eq_top n)
    (fun _ : Fin n => (1 : ℕ))
    (polynomialAffineBlowupCoordinateReesGenerator_mem_grade n)
  let A : Subalgebra P Chart :=
    Algebra.adjoin P (Set.range (polynomialAffineBlowupChartGenerator n) : Set Chart)
  apply top_unique
  intro z _hz
  have hzfull : z ∈ (⊤ : Subalgebra (reesAlgebraGrade Icoord 0) Chart) := by
    trivial
  rw [← hfull] at hzfull
  -- The full homogeneous-localization generators lie in `A`, and the degree-zero scalars are the
  -- ordinary base-polynomial scalars, so the full generated algebra is contained in `A`.
  change z ∈ A
  refine Algebra.adjoin_induction
    (p := fun z _hz ↦ z ∈ A)
    ?_ ?_ ?_ ?_ hzfull
  · rintro _ ⟨a, ai, hai, _hai_le, rfl⟩
    exact polynomialAffineBlowupChartProductFraction_mem_adjoin n a ai hai
  · intro r0
    exact polynomialAffineBlowupChart_gradeZero_algebraMap_mem_adjoin n A r0
  · intro x y _hx _hy hxA hyA
    exact A.add_mem hxA hyA
  · intro x y _hx _hy hxA hyA
    exact A.mul_mem hxA hyA

/-- Helper for Chap10 Example 10 70 5: the quotient presentation map is surjective. -/
private theorem polynomialAffineBlowupChartMap_surjective :
    Function.Surjective chartMap := by
  -- Surjectivity is now reduced to the homogeneous-localization generation statement.
  exact polynomialAffineBlowupChartMap_surjective_of_adjoin_generators n
    (polynomialAffineBlowupChart_generators_adjoin_eq_top n)

/-- Helper for Chap10 Example 10 70 5: a shifted chart index is never the denominator index. -/
private theorem polynomialAffineBlowupChartIndex_ne_zero (i : Fin (n - 1)) :
    polynomialAffineBlowupChartIndex n i ≠ 0 := by
  -- The shifted index has positive underlying value.
  intro h
  have hval : i.1 + 1 = 0 := by
    simpa [polynomialAffineBlowupChartIndex] using congrArg Fin.val h
  omega

/-- Helper for Chap10 Example 10 70 5: the predecessor of a nonzero coordinate index. -/
private def polynomialAffineBlowupChartIndexPred (j : Fin n) (hj : j ≠ 0) : Fin (n - 1) :=
  ⟨j.1 - 1, by
    -- Since `j` is nonzero, subtracting one lands in `Fin (n - 1)`.
    have hjpos : 0 < j.1 := by
      have hjval : j.1 ≠ 0 := by
        intro hval
        apply hj
        ext
        exact hval
      exact Nat.pos_of_ne_zero hjval
    omega⟩

/-- Helper for Chap10 Example 10 70 5: shifting the predecessor of a nonzero index recovers the
original index. -/
private theorem polynomialAffineBlowupChartIndex_pred (j : Fin n) (hj : j ≠ 0) :
    polynomialAffineBlowupChartIndex n (polynomialAffineBlowupChartIndexPred n j hj) = j := by
  -- This is the arithmetic inverse to subtracting one from a nonzero `Fin n` index.
  ext
  simp [polynomialAffineBlowupChartIndex, polynomialAffineBlowupChartIndexPred]
  have hjpos : 0 < j.1 := by
    have hjval : j.1 ≠ 0 := by
      intro hval
      apply hj
      ext
      exact hval
    exact Nat.pos_of_ne_zero hjval
  omega

/-- Helper for Chap10 Example 10 70 5: the predecessor of a shifted index is the original
presentation index. -/
private theorem polynomialAffineBlowupChartIndexPred_index (i : Fin (n - 1)) :
    polynomialAffineBlowupChartIndexPred n (polynomialAffineBlowupChartIndex n i)
        (polynomialAffineBlowupChartIndex_ne_zero n i) = i := by
  -- The shifted index has value `i + 1`, so its predecessor has value `i`.
  ext
  simp [polynomialAffineBlowupChartIndexPred, polynomialAffineBlowupChartIndex]

/-- Helper for Chap10 Example 10 70 5: the triangular base substitution
`t_0 ↦ y_0`, `t_j ↦ y_0 y_j` for `j ≠ 0`. -/
private noncomputable def polynomialAffineBlowupTriangularBase : P →ₐ[R] P :=
  aeval fun j : Fin n ↦
    if j = 0 then X (0 : Fin n) else X (0 : Fin n) * X j

/-- Helper for Chap10 Example 10 70 5: the triangular base substitution fixes the denominator
coordinate. -/
private theorem polynomialAffineBlowupTriangularBase_apply_zero :
    polynomialAffineBlowupTriangularBase (R := R) n (X (0 : Fin n)) = X (0 : Fin n) := by
  -- This is the zero-coordinate computation for the triangular substitution.
  simp [polynomialAffineBlowupTriangularBase]

/-- Helper for Chap10 Example 10 70 5: the triangular base substitution scales every nonzero
coordinate by the denominator coordinate. -/
private theorem polynomialAffineBlowupTriangularBase_apply_ne_zero
    (j : Fin n) (hj : j ≠ 0) :
    polynomialAffineBlowupTriangularBase (R := R) n (X j) =
      X (0 : Fin n) * X j := by
  -- This is the nonzero-coordinate branch of the triangular substitution.
  simp [polynomialAffineBlowupTriangularBase, hj]

/-- Helper for Chap10 Example 10 70 5: shifted coordinates are scaled by the triangular base
substitution. -/
private theorem polynomialAffineBlowupTriangularBase_apply_index (i : Fin (n - 1)) :
    polynomialAffineBlowupTriangularBase (R := R) n
        (X (polynomialAffineBlowupChartIndex n i)) =
      X (0 : Fin n) * X (polynomialAffineBlowupChartIndex n i) := by
  -- Shifted indices are nonzero, so the nonzero-coordinate computation applies.
  exact polynomialAffineBlowupTriangularBase_apply_ne_zero n
    (polynomialAffineBlowupChartIndex n i)
    (polynomialAffineBlowupChartIndex_ne_zero n i)

/-- Helper for Chap10 Example 10 70 5: eliminate the presentation variables into the triangular
polynomial model. -/
private noncomputable def polynomialAffineBlowupTriangularElim : S →+* P :=
  MvPolynomial.eval₂Hom (polynomialAffineBlowupTriangularBase (R := R) n).toRingHom
    (fun i : Fin (n - 1) ↦ X (polynomialAffineBlowupChartIndex n i))

/-- Helper for Chap10 Example 10 70 5: the triangular quotient section sends `y_0` to `t_0` and
`y_j` to the quotient variable corresponding to `j`. -/
private noncomputable def polynomialAffineBlowupTriangularSection : P →ₐ[R] Q :=
  aeval fun j : Fin n ↦
    if hj : j = 0 then algebraMap P Q (X (0 : Fin n))
    else
      Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n)
        (X (polynomialAffineBlowupChartIndexPred n j hj) : S)

/-- Helper for Chap10 Example 10 70 5: the triangular quotient section sends `y_0` to `t_0`. -/
private theorem polynomialAffineBlowupTriangularSection_apply_zero :
    polynomialAffineBlowupTriangularSection (R := R) n (X (0 : Fin n)) =
      algebraMap P Q (X (0 : Fin n)) := by
  -- This is the zero-coordinate computation for the quotient section.
  simp [polynomialAffineBlowupTriangularSection]

/-- Helper for Chap10 Example 10 70 5: the triangular quotient section sends a shifted coordinate
to the corresponding presentation variable. -/
private theorem polynomialAffineBlowupTriangularSection_apply_index (i : Fin (n - 1)) :
    polynomialAffineBlowupTriangularSection (R := R) n
        (X (polynomialAffineBlowupChartIndex n i)) =
      Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) (X i : S) := by
  -- The predecessor computation removes the index shift in the nonzero branch.
  simp [polynomialAffineBlowupTriangularSection,
    polynomialAffineBlowupChartIndex_ne_zero,
    polynomialAffineBlowupChartIndexPred_index]

/-- Helper for Chap10 Example 10 70 5: the quotient relation rewrites
`t_j` as `t_0 x_j` in the quotient. -/
private theorem polynomialAffineBlowupChartRelation_quotient_eq (i : Fin (n - 1)) :
    algebraMap P Q (X (polynomialAffineBlowupChartIndex n i)) =
      algebraMap P Q (X (0 : Fin n)) *
        Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) (X i : S) := by
  -- The displayed generator of the relation ideal becomes zero in the quotient.
  have hzero :
      Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n)
          (polynomialAffineBlowupChartRelation n i) = (0 : Q) := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hsub :
      algebraMap P Q (X (0 : Fin n)) *
          Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) (X i : S) -
        algebraMap P Q (X (polynomialAffineBlowupChartIndex n i)) = 0 := by
    simpa [polynomialAffineBlowupChartRelation] using hzero
  exact (sub_eq_zero.mp hsub).symm

/-- Helper for Chap10 Example 10 70 5: the quotient section is a left inverse to the triangular
base substitution on base polynomials. -/
private theorem polynomialAffineBlowupTriangularSection_comp_base (p : P) :
    polynomialAffineBlowupTriangularSection (R := R) n
        (polynomialAffineBlowupTriangularBase (R := R) n p) =
      algebraMap P Q p := by
  let lhs : P →+* Q :=
    (polynomialAffineBlowupTriangularSection (R := R) n).toRingHom.comp
      (polynomialAffineBlowupTriangularBase (R := R) n).toRingHom
  let rhs : P →+* Q := algebraMap P Q
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      -- Both maps are `R`-algebra maps on constants.
      calc
        lhs (C r) = algebraMap R Q r := by
          simp [lhs, polynomialAffineBlowupTriangularBase,
            polynomialAffineBlowupTriangularSection]
        _ = rhs (C r) := by
          simpa [rhs] using (IsScalarTower.algebraMap_apply R P Q r)
    · intro j
      by_cases hj : j = 0
      · subst j
        -- The denominator coordinate is fixed by both maps.
        simp [lhs, rhs, polynomialAffineBlowupTriangularBase_apply_zero,
          polynomialAffineBlowupTriangularSection_apply_zero]
      · let i := polynomialAffineBlowupChartIndexPred n j hj
        have hidx : polynomialAffineBlowupChartIndex n i = j :=
          polynomialAffineBlowupChartIndex_pred n j hj
        -- Nonzero coordinates are rewritten using the quotient relation.
        calc
          lhs (X j) =
              polynomialAffineBlowupTriangularSection (R := R) n
                (X (0 : Fin n) * X j) := by
                simp [lhs, polynomialAffineBlowupTriangularBase_apply_ne_zero, hj]
          _ =
              algebraMap P Q (X (0 : Fin n)) *
                Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) (X i : S) := by
                rw [map_mul]
                rw [polynomialAffineBlowupTriangularSection_apply_zero]
                rw [← hidx, polynomialAffineBlowupTriangularSection_apply_index]
          _ = rhs (X j) := by
                rw [← hidx]
                exact (polynomialAffineBlowupChartRelation_quotient_eq n i).symm
  -- Apply the ring-hom equality to the chosen base polynomial.
  exact congrArg (fun φ : P →+* Q ↦ φ p) hhom

/-- Helper for Chap10 Example 10 70 5: the quotient section is a left inverse to triangular
elimination on the full presentation polynomial ring. -/
private theorem polynomialAffineBlowupTriangularSection_comp_elim (f : S) :
    polynomialAffineBlowupTriangularSection (R := R) n
        (polynomialAffineBlowupTriangularElim (R := R) n f) =
      Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) f := by
  let lhs : S →+* Q :=
    (polynomialAffineBlowupTriangularSection (R := R) n).toRingHom.comp
      (polynomialAffineBlowupTriangularElim (R := R) n)
  let rhs : S →+* Q := Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro p
      -- Coefficients are handled by the base-level left-inverse computation.
      calc
        lhs (C p) =
            polynomialAffineBlowupTriangularSection (R := R) n
              (polynomialAffineBlowupTriangularBase (R := R) n p) := by
              simp [lhs, polynomialAffineBlowupTriangularElim]
        _ = algebraMap P Q p := polynomialAffineBlowupTriangularSection_comp_base n p
        _ = rhs (C p) := by
              simpa [rhs, Ideal.Quotient.algebraMap_eq] using
                (IsScalarTower.algebraMap_apply P S Q p).symm
    · intro i
      -- Presentation variables are sent to their matching shifted model coordinates.
      simp [lhs, rhs, polynomialAffineBlowupTriangularElim,
        polynomialAffineBlowupTriangularSection_apply_index]
  -- Apply the ring-hom equality to the chosen presentation polynomial.
  exact congrArg (fun φ : S →+* Q ↦ φ f) hhom

/-- Helper for Chap10 Example 10 70 5: the denominator coordinate is a valid denominator in the
ordinary away localization of the base polynomial ring. -/
private theorem polynomialAffineBlowupBaseDenominator_mem :
    (X (0 : Fin n) : P) ∈ Submonoid.powers (X (0 : Fin n) : P) := by
  -- It is the first power of itself.
  exact ⟨1, by simp⟩

/-- Helper for Chap10 Example 10 70 5: in the ordinary away localization, multiplying by the
denominator cancels the denominator-one fraction. -/
private theorem polynomialAffineBlowupLocalization_denominator_mul_mk_one :
    algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n)) *
        Localization.mk (1 : P)
          ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ =
      (1 : Localization.Away (X (0 : Fin n) : P)) := by
  -- Rewrite to the standard localization constructor and use `x / x = 1`.
  rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
  simpa using
    (Localization.mk_self
      (⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ :
        Submonoid.powers (X (0 : Fin n) : P)))

/-- Helper for Chap10 Example 10 70 5: a denominator-cleared ordinary fraction is the numerator
in the away localization. -/
private theorem polynomialAffineBlowupLocalization_mul_mk_denominator (p : P) :
    algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n)) *
        Localization.mk p ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ =
      algebraMap P (Localization.Away (X (0 : Fin n) : P)) p := by
  -- This is the ordinary localization identity `X_0 * (p / X_0) = p`.
  let denom : Submonoid.powers (X (0 : Fin n) : P) :=
    ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩
  rw [mul_comm]
  change Localization.mk p denom *
      algebraMap P (Localization.Away (X (0 : Fin n) : P)) (denom : P) =
    algebraMap P (Localization.Away (X (0 : Fin n) : P)) p
  rw [Localization.mk_eq_mk'_apply]
  exact @IsLocalization.mk'_spec P _ (Submonoid.powers (X (0 : Fin n) : P))
    (Localization.Away (X (0 : Fin n) : P)) _ _ _ p denom

/-- Helper for Chap10 Example 10 70 5: the product `(X_0 * p) / X_0` is `p` in the ordinary
away localization. -/
private theorem polynomialAffineBlowupLocalization_mul_mk_one_of_mul (p : P) :
    algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n) * p) *
        Localization.mk (1 : P)
          ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ =
      algebraMap P (Localization.Away (X (0 : Fin n) : P)) p := by
  -- Move the numerator factor next to the denominator cancellation.
  rw [map_mul]
  calc
    algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n)) *
          algebraMap P (Localization.Away (X (0 : Fin n) : P)) p *
        Localization.mk (1 : P)
          ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩
        =
      algebraMap P (Localization.Away (X (0 : Fin n) : P)) p *
        (algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n)) *
          Localization.mk (1 : P)
            ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩) := by
        ring
    _ = algebraMap P (Localization.Away (X (0 : Fin n) : P)) p := by
        rw [polynomialAffineBlowupLocalization_denominator_mul_mk_one]
        simp

/-- Helper for Chap10 Example 10 70 5: the triangular map from the polynomial model to the
ordinary away localization sends `y_0` to `t_0` and `y_j` to `t_j / t_0`. -/
private noncomputable def polynomialAffineBlowupTriangularToAway :
    P →ₐ[R] Localization.Away (X (0 : Fin n) : P) :=
  aeval fun j : Fin n ↦
    if j = 0 then algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n))
    else
      Localization.mk (X j : P)
        ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩

/-- Helper for Chap10 Example 10 70 5: the triangular-to-away map sends `y_0` to `t_0`. -/
private theorem polynomialAffineBlowupTriangularToAway_apply_zero :
    polynomialAffineBlowupTriangularToAway (R := R) n (X (0 : Fin n)) =
      algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n)) := by
  -- This is the zero-coordinate computation for the triangular localization map.
  simp [polynomialAffineBlowupTriangularToAway]

/-- Helper for Chap10 Example 10 70 5: the triangular-to-away map sends nonzero model
coordinates to the corresponding ordinary fractions. -/
private theorem polynomialAffineBlowupTriangularToAway_apply_ne_zero
    (j : Fin n) (hj : j ≠ 0) :
    polynomialAffineBlowupTriangularToAway (R := R) n (X j) =
      Localization.mk (X j : P)
        ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
  -- This is the nonzero-coordinate computation for the triangular localization map.
  simp [polynomialAffineBlowupTriangularToAway, hj]

/-- Helper for Chap10 Example 10 70 5: shifted model coordinates map to the displayed ordinary
fractions. -/
private theorem polynomialAffineBlowupTriangularToAway_apply_index (i : Fin (n - 1)) :
    polynomialAffineBlowupTriangularToAway (R := R) n
        (X (polynomialAffineBlowupChartIndex n i)) =
      Localization.mk (X (polynomialAffineBlowupChartIndex n i) : P)
        ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
  -- Shifted indices are nonzero, so the nonzero-coordinate computation applies.
  exact polynomialAffineBlowupTriangularToAway_apply_ne_zero n
    (polynomialAffineBlowupChartIndex n i)
    (polynomialAffineBlowupChartIndex_ne_zero n i)

/-- Helper for Chap10 Example 10 70 5: after triangular substitution, the triangular-to-away map
is the ordinary localization map on base polynomials. -/
private theorem polynomialAffineBlowupTriangularToAway_comp_base (p : P) :
    polynomialAffineBlowupTriangularToAway (R := R) n
        (polynomialAffineBlowupTriangularBase (R := R) n p) =
      algebraMap P (Localization.Away (X (0 : Fin n) : P)) p := by
  let lhs : P →+* Localization.Away (X (0 : Fin n) : P) :=
    (polynomialAffineBlowupTriangularToAway (R := R) n).toRingHom.comp
      (polynomialAffineBlowupTriangularBase (R := R) n).toRingHom
  let rhs : P →+* Localization.Away (X (0 : Fin n) : P) := algebraMap P _
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      -- Both maps agree on constants because all maps are `R`-algebra maps.
      calc
        lhs (C r) = algebraMap R (Localization.Away (X (0 : Fin n) : P)) r := by
          simp [lhs, polynomialAffineBlowupTriangularBase,
            polynomialAffineBlowupTriangularToAway]
        _ = rhs (C r) := by
          simpa [rhs] using
            (IsScalarTower.algebraMap_apply R P
              (Localization.Away (X (0 : Fin n) : P)) r)
    · intro j
      by_cases hj : j = 0
      · subst j
        -- The denominator coordinate maps to itself.
        simp [lhs, rhs, polynomialAffineBlowupTriangularBase_apply_zero,
          polynomialAffineBlowupTriangularToAway_apply_zero]
      · -- Nonzero coordinates are scaled and then the denominator is cancelled.
        calc
          lhs (X j) =
              polynomialAffineBlowupTriangularToAway (R := R) n
                (X (0 : Fin n) * X j) := by
                simp [lhs, polynomialAffineBlowupTriangularBase_apply_ne_zero, hj]
          _ =
              algebraMap P (Localization.Away (X (0 : Fin n) : P)) (X (0 : Fin n)) *
                Localization.mk (X j : P)
                  ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
                rw [map_mul]
                rw [polynomialAffineBlowupTriangularToAway_apply_zero]
                rw [polynomialAffineBlowupTriangularToAway_apply_ne_zero n j hj]
          _ = rhs (X j) := by
                exact polynomialAffineBlowupLocalization_mul_mk_denominator n (X j : P)
  -- Apply the ring-hom equality to the chosen base polynomial.
  exact congrArg (fun φ : P →+* Localization.Away (X (0 : Fin n) : P) ↦ φ p) hhom

/-- Helper for Chap10 Example 10 70 5: the scale-up map on the away localization induced by the
triangular base substitution. -/
private noncomputable def polynomialAffineBlowupTriangularScaleUp :
    Localization.Away (X (0 : Fin n) : P) →+* Localization.Away (X (0 : Fin n) : P) :=
  Localization.awayLift
    ((algebraMap P (Localization.Away (X (0 : Fin n) : P))).comp
      (polynomialAffineBlowupTriangularBase (R := R) n).toRingHom)
    (X (0 : Fin n) : P)
    (by
      -- The triangular base substitution fixes `X_0`, whose image is a unit in the away
      -- localization.
      simpa [polynomialAffineBlowupTriangularBase_apply_zero] using
        (IsLocalization.Away.algebraMap_isUnit (X (0 : Fin n) : P) :
          IsUnit
            (algebraMap P (Localization.Away (X (0 : Fin n) : P))
              (X (0 : Fin n)))))

/-- Helper for Chap10 Example 10 70 5: the scale-up map sends an ordinary denominator-one
fraction to the scaled triangular-base numerator. -/
private theorem polynomialAffineBlowupTriangularScaleUp_mk_one (p : P) :
    polynomialAffineBlowupTriangularScaleUp (R := R) n
        (Localization.mk p
          ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩) =
      algebraMap P (Localization.Away (X (0 : Fin n) : P))
          (polynomialAffineBlowupTriangularBase (R := R) n p) *
        Localization.mk (1 : P)
          ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
  -- Use the explicit computation rule for `Localization.awayLift`.
  have hv :
      ((algebraMap P (Localization.Away (X (0 : Fin n) : P))).comp
          (polynomialAffineBlowupTriangularBase (R := R) n).toRingHom)
          (X (0 : Fin n)) *
        Localization.mk (1 : P)
          ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ = 1 := by
    simpa [polynomialAffineBlowupTriangularBase_apply_zero] using
      polynomialAffineBlowupLocalization_denominator_mul_mk_one (R := R) n
  simpa [polynomialAffineBlowupTriangularScaleUp] using
    Localization.awayLift_mk
      ((algebraMap P (Localization.Away (X (0 : Fin n) : P))).comp
        (polynomialAffineBlowupTriangularBase (R := R) n).toRingHom)
      (X (0 : Fin n) : P) p
      (Localization.mk (1 : P)
        ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩)
      hv 1

/-- Helper for Chap10 Example 10 70 5: scaling up after scaling down is ordinary localization of
the model polynomial ring. -/
private theorem polynomialAffineBlowupTriangularScaleUp_comp_toAway (p : P) :
    polynomialAffineBlowupTriangularScaleUp (R := R) n
        (polynomialAffineBlowupTriangularToAway (R := R) n p) =
      algebraMap P (Localization.Away (X (0 : Fin n) : P)) p := by
  let lhs : P →+* Localization.Away (X (0 : Fin n) : P) :=
    (polynomialAffineBlowupTriangularScaleUp (R := R) n).comp
      (polynomialAffineBlowupTriangularToAway (R := R) n).toRingHom
  let rhs : P →+* Localization.Away (X (0 : Fin n) : P) := algebraMap P _
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      -- Constants are fixed by the triangular base substitution and by the localization lift.
      have htriC :
          polynomialAffineBlowupTriangularToAway (R := R) n (C r : P) =
            algebraMap P (Localization.Away (X (0 : Fin n) : P)) (C r) := by
        calc
          polynomialAffineBlowupTriangularToAway (R := R) n (C r : P) =
              algebraMap R (Localization.Away (X (0 : Fin n) : P)) r := by
              simp [polynomialAffineBlowupTriangularToAway]
          _ = algebraMap P (Localization.Away (X (0 : Fin n) : P)) (C r) := by
              exact IsScalarTower.algebraMap_apply R P
                (Localization.Away (X (0 : Fin n) : P)) r
      calc
        lhs (C r) =
            polynomialAffineBlowupTriangularScaleUp (R := R) n
              (polynomialAffineBlowupTriangularToAway (R := R) n (C r : P)) := by
              rfl
        _ =
            polynomialAffineBlowupTriangularScaleUp (R := R) n
              (algebraMap P (Localization.Away (X (0 : Fin n) : P)) (C r)) := by
              rw [htriC]
        _ =
            ((algebraMap P (Localization.Away (X (0 : Fin n) : P))).comp
              (polynomialAffineBlowupTriangularBase (R := R) n).toRingHom) (C r) := by
              simp [polynomialAffineBlowupTriangularScaleUp]
        _ = rhs (C r) := by
              simp [rhs, polynomialAffineBlowupTriangularBase]
    · intro j
      by_cases hj : j = 0
      · subst j
        -- The denominator coordinate is fixed by scale-down and scale-up.
        simp [lhs, rhs, polynomialAffineBlowupTriangularScaleUp,
          polynomialAffineBlowupTriangularToAway_apply_zero,
          polynomialAffineBlowupTriangularBase_apply_zero]
      · -- For nonzero coordinates, scale-up turns `t_j / t_0` into `y_j`.
        calc
          lhs (X j) =
              polynomialAffineBlowupTriangularScaleUp (R := R) n
                (Localization.mk (X j : P)
                  ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩) := by
                simp [lhs, polynomialAffineBlowupTriangularToAway_apply_ne_zero, hj]
          _ =
              algebraMap P (Localization.Away (X (0 : Fin n) : P))
                  (polynomialAffineBlowupTriangularBase (R := R) n (X j)) *
                Localization.mk (1 : P)
                  ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
                exact polynomialAffineBlowupTriangularScaleUp_mk_one n (X j : P)
          _ =
              algebraMap P (Localization.Away (X (0 : Fin n) : P))
                  (X (0 : Fin n) * X j) *
                Localization.mk (1 : P)
                  ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
                rw [polynomialAffineBlowupTriangularBase_apply_ne_zero n j hj]
          _ = rhs (X j) := by
                exact polynomialAffineBlowupLocalization_mul_mk_one_of_mul n (X j : P)
  -- Apply the ring-hom equality to the chosen model polynomial.
  exact congrArg (fun φ : P →+* Localization.Away (X (0 : Fin n) : P) ↦ φ p) hhom

/-- Helper for Chap10 Example 10 70 5: the ordinary localization map away from `X_0` is
injective on the base polynomial ring. -/
private theorem polynomialAffineBlowupLocalizationAway_algebraMap_injective :
    Function.Injective
      (algebraMap P (Localization.Away (X (0 : Fin n) : P))) := by
  -- Powers of a polynomial variable are nonzerodivisors, so localization at those powers is
  -- faithful.
  apply (IsLocalization.injective (M := Submonoid.powers (X (0 : Fin n) : P))
    (Localization.Away (X (0 : Fin n) : P)))
  intro s hs
  rcases hs with ⟨m, rfl⟩
  exact IsRegular.mem_nonZeroDivisors
    (MvPolynomial.isRegular_X_pow (R := R) (n := (0 : Fin n)) m)

/-- Helper for Chap10 Example 10 70 5: the triangular-to-away map is injective. -/
private theorem polynomialAffineBlowupTriangularToAway_injective :
    Function.Injective (polynomialAffineBlowupTriangularToAway (R := R) n) := by
  intro p q hpq
  -- Compose with scale-up; the composite is the faithful ordinary localization map.
  apply polynomialAffineBlowupLocalizationAway_algebraMap_injective n
  calc
    algebraMap P (Localization.Away (X (0 : Fin n) : P)) p =
        polynomialAffineBlowupTriangularScaleUp (R := R) n
          (polynomialAffineBlowupTriangularToAway (R := R) n p) := by
          exact (polynomialAffineBlowupTriangularScaleUp_comp_toAway n p).symm
    _ =
        polynomialAffineBlowupTriangularScaleUp (R := R) n
          (polynomialAffineBlowupTriangularToAway (R := R) n q) := by
          rw [hpq]
    _ = algebraMap P (Localization.Away (X (0 : Fin n) : P)) q := by
          exact polynomialAffineBlowupTriangularScaleUp_comp_toAway n q

/-- Helper for Chap10 Example 10 70 5: the actual chart evaluation agrees after ordinary
localization with triangular elimination followed by the triangular-to-away map. -/
private theorem polynomialAffineBlowupTriangularComparison (f : S) :
    affineBlowupChartToLocalizationAway Icoord (polynomialAffineBlowupChartDenominator n)
        (polynomialAffineBlowupChartToAffineBlowup n f) =
      polynomialAffineBlowupTriangularToAway (R := R) n
        (polynomialAffineBlowupTriangularElim (R := R) n f) := by
  let lhs : S →+* Localization.Away (X (0 : Fin n) : P) :=
    (affineBlowupChartToLocalizationAway Icoord (polynomialAffineBlowupChartDenominator n)).comp
      (polynomialAffineBlowupChartToAffineBlowup n).toRingHom
  let rhs : S →+* Localization.Away (X (0 : Fin n) : P) :=
    (polynomialAffineBlowupTriangularToAway (R := R) n).toRingHom.comp
      (polynomialAffineBlowupTriangularElim (R := R) n)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro p
      -- Coefficients compare by the chart-to-localization algebra-map formula and the triangular
      -- base comparison.
      have hleft :
          lhs (C p) =
            algebraMap P (Localization.Away (X (0 : Fin n) : P)) p := by
        have heval :
            polynomialAffineBlowupChartToAffineBlowup n (C p : S) =
              algebraMap P Chart p := by
          simp [polynomialAffineBlowupChartToAffineBlowup]
        change
          affineBlowupChartToLocalizationAway Icoord (polynomialAffineBlowupChartDenominator n)
              (polynomialAffineBlowupChartToAffineBlowup n (C p : S)) =
            algebraMap P (Localization.Away (X (0 : Fin n) : P)) p
        rw [heval]
        simpa [polynomialAffineBlowupChartDenominator] using
          affineBlowupChartToLocalizationAway_algebraMap Icoord
            (polynomialAffineBlowupChartDenominator n) p
      have hright :
          rhs (C p) =
            algebraMap P (Localization.Away (X (0 : Fin n) : P)) p := by
        simpa [rhs, polynomialAffineBlowupTriangularElim] using
          polynomialAffineBlowupTriangularToAway_comp_base n p
      exact hleft.trans hright.symm
    · intro i
      -- Presentation variables compare by the basic-fraction localization formula.
      have hbasic :=
        affineBlowupChartToLocalizationAway_basicFraction Icoord
          (polynomialAffineBlowupChartDenominator n)
          (polynomialAffineBlowupChartNumerator n i)
      have heval :
          polynomialAffineBlowupChartToAffineBlowup n (X i : S) =
            polynomialAffineBlowupChartGenerator n i := by
        simp [polynomialAffineBlowupChartToAffineBlowup]
      have hleft :
          lhs (X i) =
            Localization.mk (X (polynomialAffineBlowupChartIndex n i) : P)
              ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
        change
          affineBlowupChartToLocalizationAway Icoord (polynomialAffineBlowupChartDenominator n)
              (polynomialAffineBlowupChartToAffineBlowup n (X i : S)) =
            Localization.mk (X (polynomialAffineBlowupChartIndex n i) : P)
              ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩
        rw [heval]
        simpa [polynomialAffineBlowupChartGenerator,
          polynomialAffineBlowupChartNumerator,
          polynomialAffineBlowupChartDenominator] using hbasic
      have hright :
          rhs (X i) =
            Localization.mk (X (polynomialAffineBlowupChartIndex n i) : P)
              ⟨X (0 : Fin n), polynomialAffineBlowupBaseDenominator_mem n⟩ := by
        simp [rhs, polynomialAffineBlowupTriangularElim,
          polynomialAffineBlowupTriangularToAway_apply_index]
      exact hleft.trans hright.symm
  -- Apply the ring-hom equality to the chosen presentation polynomial.
  exact congrArg (fun φ : S →+* Localization.Away (X (0 : Fin n) : P) ↦ φ f) hhom

/-- Chap10 Example 10 70 5: the quotient presentation map is injective. -/
private theorem polynomialAffineBlowupChartMap_injective :
    Function.Injective chartMap := by
  suffices hker : ∀ q : Q, polynomialAffineBlowupChartMap n q = 0 → q = 0 by
    intro q₁ q₂ hq
    -- Injectivity follows from the kernel-zero criterion applied to the difference.
    apply sub_eq_zero.mp
    apply hker
    simpa [map_sub, hq]
  intro q hq
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  have haway :
      polynomialAffineBlowupTriangularToAway (R := R) n
          (polynomialAffineBlowupTriangularElim (R := R) n f) = 0 := by
    -- The comparison with ordinary localization turns chart-kernel membership into vanishing of
    -- the triangular model after the injective scale-down map.
    rw [← polynomialAffineBlowupTriangularComparison n f]
    simpa [polynomialAffineBlowupChartMap_apply_mk] using
      congrArg
        (affineBlowupChartToLocalizationAway Icoord
          (polynomialAffineBlowupChartDenominator n)) hq
  have helim :
      polynomialAffineBlowupTriangularElim (R := R) n f = 0 :=
    polynomialAffineBlowupTriangularToAway_injective n haway
  -- The quotient section carries triangular elimination back to the original quotient class.
  calc
    Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) f =
        polynomialAffineBlowupTriangularSection (R := R) n
          (polynomialAffineBlowupTriangularElim (R := R) n f) := by
          exact (polynomialAffineBlowupTriangularSection_comp_elim n f).symm
    _ = polynomialAffineBlowupTriangularSection (R := R) n 0 := by
          rw [helim]
    _ = 0 := by
          simp

/-- The canonical presentation map to the affine blowup chart is bijective. -/
private theorem polynomialAffineBlowupChartMap_bijective :
    Function.Bijective chartMap :=
  -- The bijectivity proof is split into the generated-image and saturated-kernel halves.
  ⟨polynomialAffineBlowupChartMap_injective n, polynomialAffineBlowupChartMap_surjective n⟩

local notation "chartMapBijective" => @polynomialAffineBlowupChartMap_bijective R _ n _

/-- Helper for Chap10 Example 10 70 5: for `P = R[t_1, \ldots, t_n]`, `I = (t_1, \ldots, t_n)`, and `a = t_1`, the
quotient `P[x_2, \ldots, x_n] / (t_1 x_2 - t_2, \ldots, t_1 x_n - t_n)` is canonically
isomorphic to the affine blowup chart `P[I/t_1]`. -/
@[stacks 0G8R]
noncomputable def polynomialAffineBlowupChartPresentation :
    (S ⧸
      Ideal.span
        (Set.range fun i : Fin (n - 1) ↦
          C (X (0 : Fin n) : P) * X i - C (X ⟨i.1 + 1, by omega⟩ : P))) ≃ₐ[P]
      affineBlowupChart
        (idealOfVars (Fin n) R)
        (show idealOfVars (Fin n) R from
          ⟨X (0 : Fin n), Ideal.subset_span (Set.mem_range_self (0 : Fin n))⟩) :=
  AlgEquiv.ofBijective chartMap chartMapBijective

local notation "chartPresentation" => @polynomialAffineBlowupChartPresentation R _ n _

/-- The presentation isomorphism sends the class of `x_{i+2}` to the basic fraction
`t_{i+2} / t_1`. -/
theorem polynomialAffineBlowupChartPresentation_apply_variable (i : Fin (n - 1)) :
    chartPresentation
      (Ideal.Quotient.mk
        (Ideal.span
          (Set.range fun j : Fin (n - 1) ↦
            C (X (0 : Fin n) : P) * X j - C (X ⟨j.1 + 1, by omega⟩ : P)))
        (X i : S)) =
        affineBlowupChartBasicFraction
          (idealOfVars (Fin n) R)
          (show idealOfVars (Fin n) R from
            ⟨X (0 : Fin n), Ideal.subset_span (Set.mem_range_self (0 : Fin n))⟩)
          (show idealOfVars (Fin n) R from
            let j : Fin n := ⟨i.1 + 1, by omega⟩
            ⟨X j, Ideal.subset_span (Set.mem_range_self j)⟩) :=
  by
    have h : polynomialAffineBlowupChartMap n
        (Ideal.Quotient.mk (polynomialAffineBlowupChartRelationIdeal n) (X i : S)) =
        polynomialAffineBlowupChartGenerator n i := by
      -- The quotient map is induced by `aeval`, so it sends a variable to its chosen generator.
      simp [polynomialAffineBlowupChartMap, polynomialAffineBlowupChartToAffineBlowup]
    -- Unfold the public spelling of the presentation and the local helper definitions.
    simpa [polynomialAffineBlowupChartPresentation, polynomialAffineBlowupChartRelationIdeal,
      polynomialAffineBlowupChartGenerator, polynomialAffineBlowupChartNumerator,
      polynomialAffineBlowupChartDenominator, polynomialAffineBlowupChartIndex] using h

end
