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
