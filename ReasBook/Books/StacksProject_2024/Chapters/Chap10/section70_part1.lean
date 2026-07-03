import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_70_1 (from Chap10) -/
universe u

noncomputable section

open Polynomial
open HomogeneousLocalization
open scoped DirectSum

section

variable {R : Type u} [CommRing R]

variable (I : Ideal R)

/- Definition 10.70.1: the blowup algebra `Bl_I(R)` is the canonical mathlib Rees algebra
`reesAlgebra I`, viewed as the graded `R`-subalgebra `\bigoplus_{n \ge 0} I^n` inside `R[X]`. -/
recall reesAlgebra

private def reesAlgebraGradeLinear (I : Ideal R) (n : ℕ) : ↥(I ^ n) →ₗ[R] reesAlgebra I where
  toFun r := ⟨monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩
  map_add' r s := by
    apply Subtype.ext
    exact (monomial n).map_add r.1 s.1
  map_smul' c r := by
    apply Subtype.ext
    exact (monomial n).map_smul c r.1

/-- The degree-`n` homogeneous piece `I^n t^n` of the Rees algebra `Bl_I(R)`. -/
def reesAlgebraGrade (n : ℕ) : Submodule R (reesAlgebra I) :=
  LinearMap.range (reesAlgebraGradeLinear I n)

instance instSetLikeGradedMonoidReesAlgebraGrade :
    SetLike.GradedMonoid (reesAlgebraGrade I) where
  one_mem := by
    refine ⟨⟨1, by simp⟩, ?_⟩
    apply Subtype.ext
    simp [reesAlgebraGradeLinear]
  mul_mem {i j} x y hx hy := by
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    refine ⟨⟨x.1 * y.1, by simpa [pow_add] using Ideal.mul_mem_mul x.2 y.2⟩, ?_⟩
    apply Subtype.ext
    simp [reesAlgebraGradeLinear, monomial_mul_monomial]

private theorem reesAlgebraGrade_isInternal :
    DirectSum.IsInternal (reesAlgebraGrade I) := by
  sorry

instance instGradedAlgebraReesAlgebraGrade : GradedAlgebra (reesAlgebraGrade I) :=
  DirectSum.IsInternal.gradedAlgebra (reesAlgebraGrade_isInternal I)

/-- The degree-one homogeneous element `a^(1) = a t` of the Rees algebra `Bl_I(R)`. -/
def reesAlgebraDegreeOne (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.1, by
    exact (reesAlgebra.monomial_mem).2 (by simp [pow_one, a.2])⟩

/-- The degree-one element `a^(1)` lies in the first graded piece of the Rees algebra. -/
theorem reesAlgebraDegreeOne_mem (a : I) :
    reesAlgebraDegreeOne I a ∈ reesAlgebraGrade I 1 := by
  refine ⟨⟨a.1, by simp [pow_one, a.2]⟩, ?_⟩
  apply Subtype.ext
  simp [reesAlgebraDegreeOne, reesAlgebraGradeLinear]

-- Proof sketch: if the coefficients of `x` lie in the powers of `I`, and `f(I) ⊆ J`, then the
-- coefficients of `Polynomial.map f x` lie in the corresponding powers of `J`.
/-- A ring map sending `I` into `J` carries the Rees algebra of `I` into the Rees algebra of `J`.
-/
theorem map_reesAlgebra_mem {I : Ideal R} {S : Type*} [CommRing S] {J : Ideal S} (f : R →+* S)
    (hIJ : I ≤ Ideal.comap f J) (x : reesAlgebra I) :
    Polynomial.mapRingHom f x.1 ∈ reesAlgebra J := sorry

/-- The ring homomorphism on Rees algebras induced by a ring map sending `I` into `J`. -/
def reesAlgebraMap {I : Ideal R} {S : Type*} [CommRing S] {J : Ideal S} (f : R →+* S)
    (hIJ : I ≤ Ideal.comap f J) : reesAlgebra I →+* reesAlgebra J :=
  RingHom.codRestrict
    ((Polynomial.mapRingHom f).comp (reesAlgebra I).toSubring.subtype)
    (reesAlgebra J).toSubring
    (map_reesAlgebra_mem f hIJ)

private noncomputable def reesAlgebraGradeZeroAlgebraMap : R →+* reesAlgebraGrade I 0 where
  toFun r :=
    ⟨algebraMap R (reesAlgebra I) r, by
      refine ⟨⟨r, by simp⟩, ?_⟩
      apply Subtype.ext
      simp [reesAlgebraGradeLinear]⟩
  map_one' := by
    ext
    simp
  map_mul' r s := by
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' r s := by
    ext
    simp

private instance instAlgebraReesAlgebraGradeZero : Algebra R (reesAlgebraGrade I 0) :=
  RingHom.toAlgebra (reesAlgebraGradeZeroAlgebraMap I)

/- Definition 10.70.1: for `a ∈ I`, the source-facing affine blowup algebra `R[I/a]` is modeled
by the owner object `(Bl_I(R))_(a^(1))`, the degree-zero homogeneous localization of the Rees
algebra at the degree-one element `a^(1)`. -/
abbrev affineBlowupChart (a : I) :=
  Away (reesAlgebraGrade I) (reesAlgebraDegreeOne I a)

namespace AffineBlowupChart

scoped syntax:max term:max "[" term:max " / " term:max "]" : term

scoped macro_rules (kind := AffineBlowupChart.«term_[_/_]»)
  | `($R[$I / $a]) => `(@affineBlowupChart $R _ $I $a)

end AffineBlowupChart

open scoped AffineBlowupChart

instance instCommRingAffineBlowupChart (a : I) : CommRing R[I / a] :=
  HomogeneousLocalization.homogeneousLocalizationCommRing

instance instAlgebraAffineBlowupChart (a : I) : Algebra R R[I / a] :=
  RingHom.toAlgebra <|
    show R →+* Away (reesAlgebraGrade I) (reesAlgebraDegreeOne I a) from
      (fromZeroRingHom (reesAlgebraGrade I)
        (Submonoid.powers (reesAlgebraDegreeOne I a))).comp (reesAlgebraGradeZeroAlgebraMap I)

/-- The basic homogeneous fraction `x^(1) / a^(1)` in the affine blowup chart `R[I/a]`. -/
noncomputable def affineBlowupChartBasicFraction (a x : I) : R[I / a] :=
  Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) 1
    (reesAlgebraDegreeOne I x) (reesAlgebraDegreeOne_mem I x)

private noncomputable def reesAlgebraToLocalizationAway (a : I) :
    reesAlgebra I →+* Localization.Away a.1 :=
  (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
    (reesAlgebra I).toSubring.subtype

private theorem reesAlgebraDegreeOne_image_isUnit (a : I) :
    IsUnit (reesAlgebraToLocalizationAway I a (reesAlgebraDegreeOne I a)) := by
  simpa [reesAlgebraToLocalizationAway, reesAlgebraDegreeOne] using
    (IsLocalization.Away.algebraMap_isUnit a.1 :
      IsUnit (algebraMap R (Localization.Away a.1) a.1))

/-- The canonical comparison map from the homogeneous-localization chart `(Bl_I(R))_(a^(1))` to
the ambient localization `R[1/a]`. -/
noncomputable def affineBlowupChartToLocalizationAway (a : I) :
    R[I / a] →+* Localization.Away a.1 :=
  (IsLocalization.Away.lift (reesAlgebraDegreeOne I a)
      (reesAlgebraDegreeOne_image_isUnit I a)).comp
    (algebraMap R[I / a] (Localization.Away (reesAlgebraDegreeOne I a)))

instance instAlgebraLocalizationAwayOfAffineBlowupChart (a : I) :
    Algebra R[I / a] (Localization.Away a.1) :=
  RingHom.toAlgebra (affineBlowupChartToLocalizationAway I a)

@[simp] theorem affineBlowupChartToLocalizationAway_algebraMap (a : I) (r : R) :
    affineBlowupChartToLocalizationAway I a (algebraMap R R[I / a] r) =
      algebraMap R (Localization.Away a.1) r := by
  rw [RingHom.algebraMap_toAlgebra]
  change
    (IsLocalization.Away.lift (reesAlgebraDegreeOne I a)
      (reesAlgebraDegreeOne_image_isUnit I a))
      (algebraMap (reesAlgebra I) (Localization.Away (reesAlgebraDegreeOne I a))
        ((reesAlgebraGradeZeroAlgebraMap I r).1)) =
      algebraMap R (Localization.Away a.1) r
  rw [IsLocalization.Away.lift_eq]
  simp [reesAlgebraToLocalizationAway, reesAlgebraGradeZeroAlgebraMap]

@[simp] theorem affineBlowupChartToLocalizationAway_comp_algebraMap (a : I) :
    (affineBlowupChartToLocalizationAway I a).comp (algebraMap R R[I / a]) =
      algebraMap R (Localization.Away a.1) := by
  ext r
  exact affineBlowupChartToLocalizationAway_algebraMap I a r

end

/-! ### Lemma_10_70_2 (from Chap10) -/
open HomogeneousLocalization
open IsLocalization
open scoped AffineBlowupChart nonZeroDivisors

universe u

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.70.2: the comparison map sends the basic chart fraction `x/a` to the
ordinary localization fraction `x/a` in `R_a`. -/
private theorem affineBlowupChartToLocalizationAway_basicFraction
    (I : Ideal R) (a x : I) :
    affineBlowupChartToLocalizationAway I a (affineBlowupChartBasicFraction I a x) =
      Localization.mk x.1 ⟨a.1, by exact ⟨1, by simp⟩⟩ := by
  let g : reesAlgebra I →+* Localization.Away a.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
      (reesAlgebra I).toSubring.subtype
  have hg : IsUnit (g (reesAlgebraDegreeOne I a)) := by
    simpa [g, reesAlgebraDegreeOne] using
      (IsLocalization.Away.algebraMap_isUnit a.1 :
        IsUnit (algebraMap R (Localization.Away a.1) a.1))
  have hfrac (r : R) :
      algebraMap R (Localization.Away a.1) r * Localization.mk 1 ⟨a.1, by exact ⟨1, by simp⟩⟩ =
        Localization.mk r ⟨a.1, by exact ⟨1, by simp⟩⟩ := by
    -- Rewrite the right-hand fraction into the standard `mk'` form, then use the localization
    -- formula for multiplying by `1 / a`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact (Localization.mk_eq_mk'_apply r ⟨a.1, by exact ⟨1, by simp⟩⟩).symm
  -- Evaluate the homogeneous-localization fraction by the universal property of `R_a`.
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  simp [affineBlowupChartBasicFraction]
  have h := Localization.awayLift_mk g (reesAlgebraDegreeOne I a) (reesAlgebraDegreeOne I x)
      (Localization.mk 1 ⟨a.1, by exact ⟨1, by simp⟩⟩)
      (by
        -- The image of `a^(1)` is the ordinary element `a`, whose chosen inverse is `1 / a`.
        rw [show g (reesAlgebraDegreeOne I a) = algebraMap R (Localization.Away a.1) a.1 by
          simp [g, reesAlgebraDegreeOne]]
        rw [hfrac]
        exact Localization.mk_self ⟨a.1, by exact ⟨1, by simp⟩⟩)
      1
  simpa [g, reesAlgebraDegreeOne, pow_one, hfrac] using h

/-- Helper for Lemma 10.70.2: the power `a^n` is a valid denominator in the away-localization
`R_a`. -/
private theorem affineBlowupChart_parameter_pow_mem (I : Ideal R) (a : I) (n : ℕ) :
    a.1 ^ n ∈ Submonoid.powers a.1 := by
  exact ⟨n, rfl⟩

/-- Helper for Lemma 10.70.2: the element `a` itself is a valid denominator in `R_a`. -/
private theorem affineBlowupChart_parameter_mem (I : Ideal R) (a : I) :
    a.1 ∈ Submonoid.powers a.1 := by
  exact ⟨1, by simp⟩

/-- Helper for Lemma 10.70.2: the monomial with coefficient in `I ^ n` belongs to the degree-`n`
piece of the Rees algebra. -/
private theorem monomial_mem_reesAlgebraGrade
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I n := by
  -- Unpack the graded piece through its range description.
  change (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      LinearMap.range _
  exact ⟨r, rfl⟩

/-- Helper for Lemma 10.70.2: the same monomial numerator also has the degree required by the
chart fraction `x / (a^(1))^n`. -/
private theorem monomial_mem_reesAlgebraGrade_for_chart
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I (n • 1) := by
  -- In the natural-number grading, `n • 1 = n`.
  simpa [nsmul_eq_mul] using monomial_mem_reesAlgebraGrade I n r

/-- Helper for Lemma 10.70.2: after normalizing a chart fraction to a monomial numerator, the
comparison map sends it to the ordinary fraction `r / a^n` in `R_a`. -/
private theorem affineBlowupChartToLocalizationAway_fraction_of_monomial
    (I : Ideal R) (a : I) (n : ℕ) (r : ↥(I ^ n)) :
    affineBlowupChartToLocalizationAway I a
      (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
        (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
        (monomial_mem_reesAlgebraGrade_for_chart I n r)) =
      Localization.mk r.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ := by
  -- Route correction: normalize the chart element first, then compute its image in `R_a`.
  let s : reesAlgebra I := ⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩
  let g : reesAlgebra I →+* Localization.Away a.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
      (reesAlgebra I).toSubring.subtype
  have hfrac₁ (x : R) :
      algebraMap R (Localization.Away a.1) x *
          Localization.mk 1 ⟨a.1, affineBlowupChart_parameter_mem I a⟩ =
        Localization.mk x ⟨a.1, affineBlowupChart_parameter_mem I a⟩ := by
    -- Rewrite the denominator as a standard localization fraction and multiply it out.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact
      (Localization.mk_eq_mk'_apply x ⟨a.1, affineBlowupChart_parameter_mem I a⟩).symm
  have hfrac (x : R) (m : ℕ) :
      algebraMap R (Localization.Away a.1) x *
          Localization.mk 1 ⟨a.1 ^ m, affineBlowupChart_parameter_pow_mem I a m⟩ =
        Localization.mk x ⟨a.1 ^ m, affineBlowupChart_parameter_pow_mem I a m⟩ := by
    -- The same calculation works for every power `a^m`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact
      (Localization.mk_eq_mk'_apply x ⟨a.1 ^ m, affineBlowupChart_parameter_pow_mem I a m⟩).symm
  have h :=
      Localization.awayLift_mk g (reesAlgebraDegreeOne I a) s
        (Localization.mk 1 ⟨a.1, affineBlowupChart_parameter_mem I a⟩)
        (by
          -- The chosen inverse of `a` is the usual fraction `1 / a`.
          rw [show g (reesAlgebraDegreeOne I a) = algebraMap R (Localization.Away a.1) a.1 by
            simp [g, reesAlgebraDegreeOne]]
          rw [hfrac₁]
          exact Localization.mk_self ⟨a.1, affineBlowupChart_parameter_mem I a⟩)
        n
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  have hpow :
      (Localization.mk 1 ⟨a.1, affineBlowupChart_parameter_mem I a⟩ :
          Localization.Away a.1) ^ n =
        Localization.mk 1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ := by
    -- The nth power of `1 / a` is the ordinary fraction `1 / a^n`.
    rw [Localization.mk_pow, one_pow]
    apply congrArg (fun d => Localization.mk 1 d)
    ext
    simp
  rw [hpow] at h
  simpa [g, s, reesAlgebraDegreeOne, hfrac] using h

/-- Helper for Lemma 10.70.2: if a power of `a` kills the coefficient `r`, then the corresponding
normalized chart fraction is already zero in the affine blowup chart. -/
private theorem affineBlowupChart_fraction_eq_zero_of_pow_mul_eq_zero
    (I : Ideal R) (a : I) (n m : ℕ) (r : ↥(I ^ n)) (hzero : a.1 ^ m * r.1 = 0) :
    HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
      (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
      (monomial_mem_reesAlgebraGrade_for_chart I n r) = 0 := by
  -- Compare values inside the ordinary localization of the Rees algebra.
  apply (HomogeneousLocalization.ext_iff_val _ _).2
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨reesAlgebraDegreeOne I a ^ m, by exact ⟨m, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hzero' : r.1 * a.1 ^ m = 0 := by
    simpa [mul_comm] using hzero
  -- Multiplying the numerator by `(a^(1))^m` produces the zero monomial.
  simp [reesAlgebraDegreeOne, Polynomial.monomial_mul_monomial, hzero', mul_comm]

/-- Helper for Lemma 10.70.2: the comparison map from the affine blowup chart to `R_a` is
injective. -/
private theorem affineBlowupChartToLocalizationAway_injective
    (I : Ideal R) (a : I) :
    Function.Injective (affineBlowupChartToLocalizationAway I a) := by
  suffices hker : ∀ z : R[I / a], affineBlowupChartToLocalizationAway I a z = 0 → z = 0 by
    intro z w hzw
    -- Reduce injectivity to the triviality of the kernel.
    apply sub_eq_zero.mp
    apply hker
    simpa [map_sub, hzw]
  intro z hz
  -- Normalize an arbitrary chart element to a monomial numerator.
  obtain ⟨n, s, hs, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesAlgebraGrade I)
    (reesAlgebraDegreeOne_mem I a) z
  have hs' : s ∈ reesAlgebraGrade I n := by
    simpa [nsmul_eq_mul] using hs
  change s ∈ LinearMap.range _ at hs'
  rcases hs' with ⟨r, rfl⟩
  change
    affineBlowupChartToLocalizationAway I a
      (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
        (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
        (monomial_mem_reesAlgebraGrade_for_chart I n r)) = 0 at hz
  rw [affineBlowupChartToLocalizationAway_fraction_of_monomial I a n r,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at hz
  rcases hz with ⟨u, hu⟩
  rcases u.2 with ⟨m, hm⟩
  have hz' : a.1 ^ m * r.1 = 0 := by
    simpa [hm] using hu
  -- The ordinary-localization zero criterion pulls back to the chart.
  simpa using affineBlowupChart_fraction_eq_zero_of_pow_mul_eq_zero I a n m r hz'

/-- Helper for Lemma 10.70.2: inside the affine blowup chart, the basic fraction `x / a`
multiplied by `a` recovers `x`. -/
private theorem affineBlowupChart_basicFraction_mul_chart_parameter
    (I : Ideal R) (a x : I) :
    affineBlowupChartBasicFraction I a x * algebraMap R R[I / a] a.1 =
      algebraMap R R[I / a] x.1 := by
  apply affineBlowupChartToLocalizationAway_injective I a
  -- Compute both sides in `R_a`, where the identity is the ordinary fraction calculation.
  rw [map_mul, affineBlowupChartToLocalizationAway_basicFraction,
    affineBlowupChartToLocalizationAway_algebraMap,
    affineBlowupChartToLocalizationAway_algebraMap, Localization.mk_eq_mk'_apply,
    ← IsLocalization.mk'_one (M := Submonoid.powers a.1) (S := Localization.Away a.1) a.1,
    ← IsLocalization.mk'_mul (M := Submonoid.powers a.1) (S := Localization.Away a.1)]
  simpa using
    (IsLocalization.mk'_mul_cancel_right (M := Submonoid.powers a.1)
      (S := Localization.Away a.1) x.1 ⟨a.1, affineBlowupChart_parameter_mem I a⟩)

/-- Lemma 10.70.2 (1): in the affine blowup chart `(Bl_I(R))_(a^(1))`, the image of `a` is a
nonzerodivisor. -/
theorem affineBlowupChart_isRegular (I : Ideal R) (a : I) :
    IsRegular (algebraMap R R[I / a] a.1) := by
  -- Pull the cancellation of the unit image of `a` in `R_a` back along the injective chart map.
  refine (Commute.isRegular_iff (Commute.all _)).2 ?_
  intro z w hzw
  apply affineBlowupChartToLocalizationAway_injective I a
  have hreg : IsRegular (algebraMap R (Localization.Away a.1) a.1) :=
    (IsLocalization.Away.algebraMap_isUnit a.1).isRegular
  apply hreg.1
  simpa [map_mul] using congrArg (affineBlowupChartToLocalizationAway I a) hzw

/-- Lemma 10.70.2 (2): extending `I` to the affine blowup chart `(Bl_I(R))_(a^(1))` gives the
principal ideal generated by the image of `a`. -/
theorem affineBlowupChart_map_ideal_eq_span_singleton (I : Ideal R) (a : I) :
    Ideal.map (algebraMap R R[I / a]) I =
      Ideal.span {algebraMap R R[I / a] a.1} := by
  apply le_antisymm
  · -- Every generator coming from `I` is a multiple of the image of `a`.
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change algebraMap R R[I / a] x ∈ Ideal.span {algebraMap R R[I / a] a.1}
    rw [Ideal.mem_span_singleton']
    exact ⟨affineBlowupChartBasicFraction I a ⟨x, hx⟩,
      affineBlowupChart_basicFraction_mul_chart_parameter I a ⟨x, hx⟩⟩
  · -- The generator `a` itself already comes from the image of `I`.
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem (algebraMap R R[I / a]) a.2

private theorem affineBlowupChartAwayMap_bijective (I : Ideal R) (a : I) :
    Function.Bijective
      (Localization.awayMapₐ
        (Algebra.ofId R[I / a] (Localization.Away a.1))
        (algebraMap R R[I / a] a.1)) := by
  let f : R[I / a] →+* Localization.Away a.1 := Algebra.ofId R[I / a] (Localization.Away a.1)
  let aA : R[I / a] := algebraMap R R[I / a] a.1
  have hf : f = affineBlowupChartToLocalizationAway I a := rfl
  have hfaA : f aA = algebraMap R (Localization.Away a.1) a.1 := by
    simpa [hf, aA] using affineBlowupChartToLocalizationAway_algebraMap I a a.1
  change Function.Bijective (Localization.awayMap f aA)
  have hinj : Function.Injective (Localization.awayMap f aA) := by
    -- Injectivity uses the already-proved injectivity of the base map.
    apply (Localization.awayMap_injective_iff (f := f) (r := aA)).2
    intro z hz
    rw [hf] at hz
    have hz' : z = 0 := by
      apply affineBlowupChartToLocalizationAway_injective I a
      simpa using hz
    refine ⟨0, ?_⟩
    simpa [hz']
  have hsurj : Function.Surjective (Localization.awayMap f aA) := by
    -- Surjectivity is the usual numerator/denominator normal form in `R_a`.
    apply (Localization.awayMap_surjective_iff (f := f) (r := aA)).2
    intro z
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj a.1 z
    refine ⟨algebraMap R R[I / a] b, m, ?_⟩
    rw [hf, affineBlowupChartToLocalizationAway_algebraMap]
    rw [show affineBlowupChartToLocalizationAway I a aA =
        algebraMap R (Localization.Away a.1) a.1 by
      simpa [aA] using affineBlowupChartToLocalizationAway_algebraMap I a a.1]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hb.symm
  exact ⟨hinj, hsurj⟩

/-- Lemma 10.70.2 (3): localizing the affine blowup chart `(Bl_I(R))_(a^(1))` at the image of `a`
recovers `R_a`; equivalently, `R_a` is the localization of `(Bl_I(R))_(a^(1))` away from the
image of `a`. -/
noncomputable instance affineBlowupChart_isLocalizationAway (I : Ideal R) (a : I) :
    IsLocalization.Away (algebraMap R R[I / a] a.1) (Localization.Away a.1) :=
  by
    let A := R[I / a]
    let S := Localization.Away a.1
    let aA : A := algebraMap R A a.1
    have hmap : (affineBlowupChartToLocalizationAway I a) aA = algebraMap R S a.1 := by
      -- The image of the chart parameter is just the ordinary image of `a` in `R_a`.
      simpa [A, S, aA] using affineBlowupChartToLocalizationAway_algebraMap I a a.1
    have hunit : IsUnit (algebraMap A S aA) := by
      change IsUnit ((affineBlowupChartToLocalizationAway I a) aA)
      rw [hmap]
      exact IsLocalization.Away.algebraMap_isUnit a.1
    have hAwayMap : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A S) aA) := by
      simpa [A, S, aA] using affineBlowupChartAwayMap_bijective I a
    let eAway :
        Localization.Away aA ≃ₐ[A] Localization.Away (algebraMap A S aA) :=
      AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId A S) aA) hAwayMap
    let eUnit : S ≃ₐ[A] Localization.Away (algebraMap A S aA) :=
      (IsLocalization.atUnit S (Localization.Away (algebraMap A S aA))
        (algebraMap A S aA) hunit).restrictScalars A
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers aA)
      (eAway.trans eUnit.symm)

end
