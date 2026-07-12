import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Chap10 Definition 10 70 1: the coefficient monomial of a Rees element again
belongs to the Rees algebra. -/
private theorem reesAlgebraCoeffMonomial_mem (x : reesAlgebra I) (n : ℕ) :
    monomial n (x.1.coeff n) ∈ reesAlgebra I := by
  -- The Rees condition records exactly that the `n`-th coefficient lies in `I ^ n`.
  exact reesAlgebra.monomial_mem.mpr (x.2 n)

/-- Helper for Chap10 Definition 10 70 1: the Rees element represented by the `n`-th
coefficient monomial. -/
private def reesAlgebraCoeffMonomial (x : reesAlgebra I) (n : ℕ) : reesAlgebra I :=
  ⟨monomial n (x.1.coeff n), reesAlgebraCoeffMonomial_mem I x n⟩

/-- Helper for Chap10 Definition 10 70 1: the coefficient monomial lies in its matching
homogeneous Rees grade. -/
private theorem reesAlgebraCoeffMonomial_mem_grade (x : reesAlgebra I) (n : ℕ) :
    reesAlgebraCoeffMonomial I x n ∈ reesAlgebraGrade I n := by
  -- It is the image of the coefficient, viewed as an element of `I ^ n`, under the grade map.
  refine ⟨⟨x.1.coeff n, x.2 n⟩, ?_⟩
  apply Subtype.ext
  simp [reesAlgebraCoeffMonomial, reesAlgebraGradeLinear]

/-- Helper for Chap10 Definition 10 70 1: decompose a Rees polynomial into its coefficient
monomials indexed by the finite polynomial support. -/
private noncomputable def reesAlgebraDecompose (x : reesAlgebra I) :
    ⨁ n, reesAlgebraGrade I n :=
  DirectSum.mk (fun n ↦ reesAlgebraGrade I n) x.1.support
    (fun n ↦ ⟨reesAlgebraCoeffMonomial I x n.1,
      reesAlgebraCoeffMonomial_mem_grade I x n.1⟩)

/-- Helper for Chap10 Definition 10 70 1: the coefficient decomposition has the expected
monomial in every degree. -/
private theorem reesAlgebraDecompose_apply (x : reesAlgebra I) (n : ℕ) :
    (((reesAlgebraDecompose I x n : reesAlgebra I) : R[X])) =
      monomial n (x.1.coeff n) := by
  -- On the support, `DirectSum.mk` returns the stored coefficient monomial.
  by_cases hn : n ∈ x.1.support
  · rw [reesAlgebraDecompose, DirectSum.mk_apply_of_mem hn]
    simp [reesAlgebraCoeffMonomial]
  · -- Off the support, the coefficient is zero, so the missing component is the zero monomial.
    rw [reesAlgebraDecompose, DirectSum.mk_apply_of_notMem hn]
    have hcoeff : x.1.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    simp [hcoeff]

/-- Helper for Chap10 Definition 10 70 1: a homogeneous Rees element is its single coefficient
monomial. -/
private theorem reesAlgebraGrade_eq_monomial_coeff (n : ℕ) (y : reesAlgebraGrade I n) :
    (((y : reesAlgebra I) : R[X])) =
      monomial n ((((y : reesAlgebra I) : R[X])).coeff n) := by
  -- Unpack membership in the range of the grade map and read off the underlying monomial.
  rcases y.2 with ⟨r, hr⟩
  have hpoly : (((y : reesAlgebra I) : R[X])) = monomial n r.1 := by
    exact congrArg Subtype.val hr.symm
  rw [hpoly]
  simp

/-- Helper for Chap10 Definition 10 70 1: a homogeneous component has zero coefficient away from
its degree. -/
private theorem reesAlgebraGrade_coeff_eq_zero_of_ne {m n : ℕ} (hmn : m ≠ n)
    (y : reesAlgebraGrade I m) :
    (((y : reesAlgebra I) : R[X])).coeff n = 0 := by
  -- The monomial normal form makes all off-degree coefficients vanish.
  rw [reesAlgebraGrade_eq_monomial_coeff I m y]
  simp [Polynomial.coeff_monomial, hmn]

/-- Helper for Chap10 Definition 10 70 1: recomposition has degree-`n` coefficient equal to
the degree-`n` component's own coefficient. -/
private theorem reesAlgebraGrade_coeff_coeAddMonoidHom
    (y : ⨁ n, reesAlgebraGrade I n) (n : ℕ) :
    ((((DirectSum.coeAddMonoidHom (reesAlgebraGrade I) y : reesAlgebra I) : R[X])).coeff n) =
      ((((y n : reesAlgebra I) : R[X])).coeff n) := by
  classical
  -- Expand the direct sum as a finite sum over its support and then isolate the `n`-summand.
  calc
    ((((DirectSum.coeAddMonoidHom (reesAlgebraGrade I) y : reesAlgebra I) : R[X])).coeff n)
        =
          ((((DirectSum.coeAddMonoidHom (reesAlgebraGrade I)
              (∑ m ∈ y.support, DirectSum.of (fun k ↦ reesAlgebraGrade I k) m (y m)) :
              reesAlgebra I) : R[X])).coeff n) := by
            rw [DirectSum.sum_support_of y]
    _ = (∑ m ∈ y.support, ((((y m : reesAlgebra I) : R[X])).coeff n)) := by
            simp [map_sum]
    _ = ((((y n : reesAlgebra I) : R[X])).coeff n) := by
            refine Finset.sum_eq_single n ?_ ?_
            · intro m _hm hmn
              exact reesAlgebraGrade_coeff_eq_zero_of_ne I hmn (y m)
            · intro hn
              have hy_zero : y n = 0 := DFinsupp.notMem_support_iff.mp hn
              simp [hy_zero]

/-- Helper for Chap10 Definition 10 70 1: coefficient decomposition is a left inverse to
canonical recomposition. -/
private theorem reesAlgebraDecompose_left_inv :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (reesAlgebraGrade I))
      (reesAlgebraDecompose I) := by
  intro x
  -- Compare Rees elements coefficientwise as polynomials.
  apply Subtype.ext
  ext n
  rw [reesAlgebraGrade_coeff_coeAddMonoidHom I (reesAlgebraDecompose I x) n]
  rw [reesAlgebraDecompose_apply I x n]
  simp

/-- Helper for Chap10 Definition 10 70 1: coefficient decomposition is a right inverse to
canonical recomposition. -/
private theorem reesAlgebraDecompose_right_inv :
    Function.RightInverse (DirectSum.coeAddMonoidHom (reesAlgebraGrade I))
      (reesAlgebraDecompose I) := by
  intro y
  -- Each component is recovered by the same monomial normal form used in the decomposition.
  ext n d
  rw [reesAlgebraDecompose_apply I (DirectSum.coeAddMonoidHom (reesAlgebraGrade I) y) n]
  rw [reesAlgebraGrade_coeff_coeAddMonoidHom I y n]
  rw [reesAlgebraGrade_eq_monomial_coeff I n (y n)]
  simp

private theorem reesAlgebraGrade_isInternal :
    DirectSum.IsInternal (reesAlgebraGrade I) := by
  -- The explicit coefficient decomposition is inverse to the canonical recomposition map.
  exact
    ⟨(reesAlgebraDecompose_right_inv I).injective,
      (reesAlgebraDecompose_left_inv I).surjective⟩

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
    Polynomial.mapRingHom f x.1 ∈ reesAlgebra J := by
  -- Check the Rees condition coefficient by coefficient after applying `f`.
  rw [mem_reesAlgebra_iff]
  intro n
  have hpow : I ^ n ≤ Ideal.comap f (J ^ n) :=
    (Ideal.pow_right_mono hIJ n).trans (J.le_comap_pow f n)
  simpa [Polynomial.coe_mapRingHom, Polynomial.coeff_map] using hpow (x.2 n)

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

/-- Chap10 Definition 10 70 1: for `a ∈ I`, the source-facing affine blowup algebra `R[I/a]` is modeled
by the owner object `(Bl_I(R))_(a^(1))`, the degree-zero homogeneous localization of the Rees
algebra at the degree-one element `a^(1)`. -/
@[stacks 052Q]
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
