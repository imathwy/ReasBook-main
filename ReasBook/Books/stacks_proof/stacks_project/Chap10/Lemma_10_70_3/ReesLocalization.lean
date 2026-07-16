import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_70_1
import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Lemma_10_70_2

open HomogeneousLocalization
open IsLocalization
open Polynomial
open scoped AffineBlowupChart DirectSum TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]

/-- The image of `a ∈ I` in the extended ideal `Ideal.map (algebraMap R S) I`. -/
def mappedIdealElement {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) : Ideal.map (algebraMap R S) I :=
  ⟨algebraMap R S a.1, Ideal.mem_map_of_mem (algebraMap R S) a.2⟩

/-- Helper for Chap10 Lemma 10 70 3: an affine blowup chart after base change carries the induced `R`-algebra structure. -/
private noncomputable instance (priority := 50) affineBlowupAlgebraBaseChangeAlgebra
    {S : Type v} [CommRing S]
    [Algebra R S] (J : Ideal S) (b : J) :
    Algebra R S[J / b] :=
  RingHom.toAlgebra <| (algebraMap S S[J / b]).comp (algebraMap R S)

/-- Helper for Chap10 Lemma 10 70 3: an ideal is contained in the comap of its extension along an algebra map. -/
theorem map_ideal_le_comap {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) :
    I ≤ Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) := by
  intro x hx
  exact Ideal.mem_map_of_mem (algebraMap R S) hx

/-- Helper for Chap10 Lemma 10 70 3: the Rees algebra map induced by base change preserves homogeneous grades. -/
theorem reesAlgebraMap_mem_grade {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R)
    {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ reesAlgebraGrade I n) :
    reesAlgebraMap (algebraMap R S) (map_ideal_le_comap I) x ∈
      reesAlgebraGrade (Ideal.map (algebraMap R S) I) n := by
  -- The source-grade witness already writes `x` as a degree-`n` monomial with coefficient in
  -- `I ^ n`, so we transport that coefficient across `R → S`.
  rcases hx with ⟨y, rfl⟩
  refine ⟨⟨algebraMap R S y.1, ?_⟩, ?_⟩
  · simpa [Ideal.map_pow] using
      (Ideal.mem_map_of_mem (algebraMap R S) y.2 :
        algebraMap R S y.1 ∈ Ideal.map (algebraMap R S) (I ^ n))
  · -- After mapping coefficients, the resulting polynomial is the same degree-`n` monomial.
    apply Subtype.ext
    exact (Polynomial.map_monomial (f := algebraMap R S) (n := n) (a := y.1)).symm

/-- Helper for Lemma 10.70.3: a homogeneous-localization map carries degree-zero fractions `f/1`
to the corresponding degree-zero fractions after applying the graded map on degree zero. -/
theorem homogeneousLocalization_map_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ι → τ) [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) {P : Submonoid A} {Q : Submonoid B} (comap_le : P ≤ Q.comap g)
    (a : 𝒜 0) :
    HomogeneousLocalization.map g comap_le (HomogeneousLocalization.fromZeroRingHom 𝒜 P a) =
      HomogeneousLocalization.fromZeroRingHom ℬ Q (g.gradedAddHom 0 a) := by
  -- Both sides are represented by the same zero-degree numerator and denominator `1`.
  ext
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- Helper for Lemma 10.70.3: `Away.map` sends the degree-zero algebra map to the degree-zero
algebra map after applying the graded homomorphism on coefficients. -/
theorem away_map_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ι → τ) [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (f : A) (a : 𝒜 0) :
    HomogeneousLocalization.Away.map g f
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) a) =
      HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (g f)) (g.gradedAddHom 0 a) := by
  -- Specialize the homogeneous-localization compatibility to the standard away-localization.
  simpa [HomogeneousLocalization.Away.map] using
    homogeneousLocalization_map_fromZeroRingHom 𝒜 ℬ g
      (P := Submonoid.powers f) (Q := Submonoid.powers (g f))
      (by
        intro x hx
        rcases hx with ⟨n, rfl⟩
        exact ⟨n, by simp⟩)
      a

/-- Helper for Chap10 Lemma 10 70 3: the base-change map of Rees algebras as a graded ring homomorphism. -/
noncomputable def reesAlgebraBaseChangeGradedHom {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) :
    reesAlgebraGrade I →+*ᵍ reesAlgebraGrade (Ideal.map (algebraMap R S) I) where
  toRingHom := reesAlgebraMap (algebraMap R S) (map_ideal_le_comap I)
  map_mem := reesAlgebraMap_mem_grade I

/-- Helper for Chap10 Lemma 10 70 3: the base-change graded homomorphism sends the distinguished degree-one element to its image. -/
theorem reesAlgebraBaseChange_degreeOne {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :
    reesAlgebraBaseChangeGradedHom I (reesAlgebraDegreeOne I a) =
      reesAlgebraDegreeOne (Ideal.map (algebraMap R S) I) (mappedIdealElement I a) := by
  -- Both sides are the same degree-one monomial after applying the coefficient map.
  ext
  simp [reesAlgebraBaseChangeGradedHom, reesAlgebraDegreeOne, mappedIdealElement, reesAlgebraMap]

/-- Helper for Lemma 10.70.3: the constant polynomial `r` lies in the degree-zero part of the Rees
algebra. -/
theorem reesAlgebra_zeroDegree_mem (I : Ideal R) (r : R) :
    algebraMap R (reesAlgebra I) r ∈ reesAlgebraGrade I 0 := by
  refine ⟨⟨r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (monomial 0 r : R[X]) = C r
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.3: the constant polynomial `algebraMap R S r` lies in the degree-zero
part of the base-changed Rees algebra. -/
theorem reesAlgebra_baseChange_zeroDegree_mem {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (r : R) :
    algebraMap S (reesAlgebra (Ideal.map (algebraMap R S) I)) (algebraMap R S r) ∈
      reesAlgebraGrade (Ideal.map (algebraMap R S) I) 0 := by
  refine ⟨⟨algebraMap R S r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (monomial 0 (algebraMap R S r) : S[X]) = C (algebraMap R S r)
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.3: the degree-zero Rees coefficient determined by `r`. -/
noncomputable def reesAlgebraZeroDegreeCoeff (I : Ideal R) (r : R) :
    reesAlgebraGrade I 0 :=
  ⟨algebraMap R (reesAlgebra I) r, reesAlgebra_zeroDegree_mem I r⟩

/-- Helper for Lemma 10.70.3: the degree-zero base-changed Rees coefficient determined by
`algebraMap R S r`. -/
noncomputable def reesAlgebraBaseChangeZeroDegreeCoeff {S : Type v} [CommRing S]
    [Algebra R S]
    (I : Ideal R) (r : R) :
    reesAlgebraGrade (Ideal.map (algebraMap R S) I) 0 :=
  ⟨algebraMap S (reesAlgebra (Ideal.map (algebraMap R S) I)) (algebraMap R S r),
    reesAlgebra_baseChange_zeroDegree_mem I r⟩

/-- Helper for Lemma 10.70.3: the base-change graded homomorphism sends the degree-zero Rees
coefficient represented by `r` to the corresponding degree-zero coefficient represented by
`algebraMap R S r`. -/
theorem reesAlgebraBaseChange_zeroDegree_algebraMap {S : Type v} [CommRing S]
    [Algebra R S] (I : Ideal R) (r : R) :
    (reesAlgebraBaseChangeGradedHom I).gradedAddHom 0 (reesAlgebraZeroDegreeCoeff I r) =
      reesAlgebraBaseChangeZeroDegreeCoeff (S := S) I r := by
  -- Both graded degree-zero elements are represented by the same constant polynomial after
  -- applying the coefficient map `R → S`.
  apply Subtype.ext
  ext n
  by_cases hn : n = 0
  · subst hn
    simp [reesAlgebraBaseChangeGradedHom, reesAlgebraZeroDegreeCoeff,
      reesAlgebraBaseChangeZeroDegreeCoeff, reesAlgebraMap]
  · simp [reesAlgebraBaseChangeGradedHom, reesAlgebraZeroDegreeCoeff,
      reesAlgebraBaseChangeZeroDegreeCoeff, reesAlgebraMap]

/-- Helper for Lemma 10.70.3: the base-changed degree-zero Rees coefficients assemble into the
canonical `R`-algebra map on the degree-zero graded piece. -/
noncomputable def reesAlgebraBaseChangeGradeZeroAlgebraMap {S : Type v} [CommRing S]
    [Algebra R S] (I : Ideal R) :
    R →+* reesAlgebraGrade (Ideal.map (algebraMap R S) I) 0 where
  toFun r := reesAlgebraBaseChangeZeroDegreeCoeff (S := S) I r
  map_one' := by
    ext
    simp [reesAlgebraBaseChangeZeroDegreeCoeff]
  map_mul' r s := by
    ext
    simp [reesAlgebraBaseChangeZeroDegreeCoeff]
  map_zero' := by
    ext
    simp [reesAlgebraBaseChangeZeroDegreeCoeff]
  map_add' r s := by
    ext
    simp [reesAlgebraBaseChangeZeroDegreeCoeff]

/-- Helper for Lemma 10.70.3: in any commutative ring, a constant polynomial lies in the
degree-zero piece of the Rees algebra. -/
theorem reesAlgebra_zeroDegree_mem_generic {T : Type w} [CommRing T]
    (J : Ideal T) (t : T) :
    algebraMap T (reesAlgebra J) t ∈ reesAlgebraGrade J 0 := by
  refine ⟨⟨t, by simp⟩, ?_⟩
  apply Subtype.ext
  change (monomial 0 t : T[X]) = C t
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.3: the degree-zero Rees coefficient determined by a scalar in an
arbitrary ambient ring. -/
noncomputable def reesAlgebraZeroDegreeCoeff_generic {T : Type w} [CommRing T]
    (J : Ideal T) (t : T) :
    reesAlgebraGrade J 0 :=
  ⟨algebraMap T (reesAlgebra J) t, reesAlgebra_zeroDegree_mem_generic J t⟩

/-- Helper for Lemma 10.70.3: the specialized and generic target-side degree-zero coefficients
agree after base change. -/
theorem reesAlgebraBaseChangeZeroDegreeCoeff_eq_generic {S : Type v} [CommRing S]
    [Algebra R S] (I : Ideal R) (r : R) :
    reesAlgebraBaseChangeZeroDegreeCoeff (S := S) I r =
      reesAlgebraZeroDegreeCoeff_generic (Ideal.map (algebraMap R S) I) (algebraMap R S r) := by
  -- Both degree-zero coefficients are represented by the same constant polynomial in the target
  -- Rees algebra.
  ext
  simp [reesAlgebraBaseChangeZeroDegreeCoeff, reesAlgebraZeroDegreeCoeff_generic]

/-- Helper for Lemma 10.70.3: the specialized and generic degree-zero Rees coefficients agree. -/
theorem reesAlgebraZeroDegreeCoeff_eq_generic (I : Ideal R) (r : R) :
    reesAlgebraZeroDegreeCoeff I r = reesAlgebraZeroDegreeCoeff_generic I r := by
  ext
  simp [reesAlgebraZeroDegreeCoeff, reesAlgebraZeroDegreeCoeff_generic]

/-- Helper for Lemma 10.70.3: the base-change graded homomorphism also carries the generic
degree-zero Rees coefficient determined by `r` to the corresponding base-changed coefficient. -/
theorem reesAlgebraBaseChange_zeroDegree_algebraMap_generic {S : Type v} [CommRing S]
    [Algebra R S] (I : Ideal R) (r : R) :
    (reesAlgebraBaseChangeGradedHom I).gradedAddHom 0 (reesAlgebraZeroDegreeCoeff_generic I r) =
      reesAlgebraBaseChangeZeroDegreeCoeff (S := S) I r := by
  simpa [reesAlgebraZeroDegreeCoeff_eq_generic I r] using
    reesAlgebraBaseChange_zeroDegree_algebraMap (S := S) I r

/-- Helper for Lemma 10.70.3: the degree-zero Rees coefficients give the canonical algebra map
into the degree-zero graded piece for an arbitrary ideal. -/
noncomputable def reesAlgebraGradeZeroAlgebraMap_generic {T : Type w} [CommRing T]
    (J : Ideal T) :
    T →+* reesAlgebraGrade J 0 where
  toFun t := reesAlgebraZeroDegreeCoeff_generic J t
  map_one' := by
    ext
    simp [reesAlgebraZeroDegreeCoeff_generic]
  map_mul' x y := by
    ext
    simp [reesAlgebraZeroDegreeCoeff_generic]
  map_zero' := by
    ext
    simp [reesAlgebraZeroDegreeCoeff_generic]
  map_add' x y := by
    ext
    simp [reesAlgebraZeroDegreeCoeff_generic]

/-- Helper for Lemma 10.70.3: the canonical algebra map into an affine blowup chart is the
degree-zero `fromZeroRingHom` for that chart. -/
theorem affineBlowupChart_algebraMap_eq_fromZeroRingHom {T : Type w} [CommRing T]
    (J : Ideal T) (b : J) (t : T) :
    algebraMap T T[J / b] t =
      HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade J)
        (Submonoid.powers (reesAlgebraDegreeOne J b))
        (reesAlgebraZeroDegreeCoeff_generic J t) := by
  -- This is the public degree-zero chart formula needed for the target-side rewrite.
  change
    (HomogeneousLocalization.fromZeroRingHom
        (reesAlgebraGrade J)
        (Submonoid.powers (reesAlgebraDegreeOne J b)))
      ((reesAlgebraGradeZeroAlgebraMap_generic J) t) =
    _
  simp [reesAlgebraGradeZeroAlgebraMap_generic]

/-- Helper for Lemma 10.70.3: the degree-zero homogeneous-localization class has ordinary
localization value `a / 1`. -/
theorem homogeneousLocalization_val_fromZeroRingHom
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] (P : Submonoid A) (a : 𝒜 0) :
    HomogeneousLocalization.val (HomogeneousLocalization.fromZeroRingHom 𝒜 P a) =
      Localization.mk a.1 ⟨1, by simp⟩ := by
  -- Unfold the degree-zero constructor once so the value is the ordinary fraction `a / 1`.
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.val_mk]

/-- Helper for Lemma 10.70.3: transporting a ring-hom application along an equality of chart
parameters is the same as transporting the resulting chart element. -/
theorem cast_awayRingHom_apply
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {d : ι} {f g : 𝒜 d} {S : Type*} [CommRing S]
    (h : f = g) (φ : S →+* Away 𝒜 (f : A)) (x : S) :
    cast (congrArg (fun y : 𝒜 d ↦ S →+* Away 𝒜 (y : A)) h) φ x =
      cast (congrArg (fun y : 𝒜 d ↦ Away 𝒜 (y : A)) h) (φ x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.3: transporting an away-chart element along an equality in the graded
piece transports its ordinary localization value along the induced equality of localizations. -/
theorem cast_away_val_subtype
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f g : 𝒜 d} (h : f = g) (x : Away 𝒜 (f : A)) :
    HomogeneousLocalization.val (cast (congrArg (fun y : 𝒜 d ↦ Away 𝒜 (y : A)) h) x) =
      cast (congrArg (fun y : 𝒜 d ↦ Localization.Away (y : A)) h)
        (HomogeneousLocalization.val x) := by
  -- Route correction: move the dependent cast to ordinary localization, where the transport is
  -- definitionally transparent.
  cases h
  rfl

/-- Helper for Chap10 Lemma 10 70 3: transporting a degree-zero homogeneous localization
class across an equality of inverted homogeneous elements replaces the denominator. -/
theorem cast_fromZeroRingHom_powers
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f g : 𝒜 d} (h : f = g) (c : 𝒜 0) :
    cast (congrArg (fun y : 𝒜 d ↦ Away 𝒜 (y : A)) h)
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (f : A)) c) =
      HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (g : A)) c := by
  cases h
  rfl

/-- Helper for Lemma 10.70.3: transporting a standard away-localization fraction along an
equality of inverted elements only changes the recorded denominator witness. -/
theorem cast_localizationAway_mk
    {A : Type*} [CommRing A] {f g r s t : A} (h : f = g) (hst : s = t)
    (hs : s ∈ Submonoid.powers f) (ht : t ∈ Submonoid.powers g) :
    cast (congrArg (fun y ↦ Localization.Away y) h) (Localization.mk r ⟨s, hs⟩) =
      Localization.mk r ⟨t, ht⟩ := by
  -- Once the inverted elements agree, transporting a concrete fraction only changes the
  -- denominator witness term.
  cases h
  cases hst
  rfl

/-- Helper for Lemma 10.70.3: the power `a^n` is an allowed denominator in the ordinary
localization `R_a`. -/
theorem affineBlowupChart_parameter_pow_mem (I : Ideal R) (a : I) (n : ℕ) :
    a.1 ^ n ∈ Submonoid.powers a.1 := by
  exact ⟨n, rfl⟩

/-- Helper for Lemma 10.70.3: the monomial with coefficient in `I ^ n` lies in the degree-`n`
piece of the Rees algebra. -/
theorem monomial_mem_reesAlgebraGrade
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I n := by
  -- Unpack the graded piece through its range description.
  change (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      LinearMap.range _
  exact ⟨r, rfl⟩

/-- Helper for Lemma 10.70.3: the same monomial numerator has the degree required by the chart
fraction with denominator `(a^(1))^n`. -/
theorem monomial_mem_reesAlgebraGrade_for_chart
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I (n • 1) := by
  -- In the natural-number grading, `n • 1 = n`.
  simpa [nsmul_eq_mul] using monomial_mem_reesAlgebraGrade I n r

/-- Helper for Lemma 10.70.3: the normalized monomial fraction `r / a^n` in the affine blowup
chart maps to the ordinary localization fraction `r / a^n` in `R_a`. -/
theorem affineBlowupChartToLocalizationAway_fraction_of_monomial
    (I : Ideal R) (a : I) (n : ℕ) (r : ↥(I ^ n)) :
    affineBlowupChartToLocalizationAway I a
      (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
        (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
        (monomial_mem_reesAlgebraGrade_for_chart I n r)) =
      Localization.mk r.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ := by
  -- Route correction: compute the chart fraction in `R_a` before using it in the tensor proof.
  let s : reesAlgebra I := ⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩
  let g : reesAlgebra I →+* Localization.Away a.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
      (reesAlgebra I).toSubring.subtype
  have hfrac₁ (x : R) :
      algebraMap R (Localization.Away a.1) x *
          Localization.mk 1 ⟨a.1, by exact ⟨1, by simp⟩⟩ =
        Localization.mk x ⟨a.1, by exact ⟨1, by simp⟩⟩ := by
    -- Rewrite the denominator into standard `mk'` form, then multiply by `1 / a`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact
      (Localization.mk_eq_mk'_apply x ⟨a.1, by exact ⟨1, by simp⟩⟩).symm
  have hfrac (x : R) (m : ℕ) :
      algebraMap R (Localization.Away a.1) x *
          Localization.mk 1 ⟨a.1 ^ m, affineBlowupChart_parameter_pow_mem I a m⟩ =
        Localization.mk x ⟨a.1 ^ m, affineBlowupChart_parameter_pow_mem I a m⟩ := by
    -- The same standard calculation works for every power `a^m`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact
      (Localization.mk_eq_mk'_apply x ⟨a.1 ^ m, affineBlowupChart_parameter_pow_mem I a m⟩).symm
  have h :=
      Localization.awayLift_mk g (reesAlgebraDegreeOne I a) s
        (Localization.mk 1 ⟨a.1, by exact ⟨1, by simp⟩⟩)
        (by
          -- The chosen inverse of `a^(1)` is the ordinary fraction `1 / a`.
          rw [show g (reesAlgebraDegreeOne I a) = algebraMap R (Localization.Away a.1) a.1 by
            simp [g, reesAlgebraDegreeOne]]
          rw [hfrac₁]
          exact Localization.mk_self ⟨a.1, by exact ⟨1, by simp⟩⟩)
        n
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  have hpow :
      (Localization.mk 1 ⟨a.1, by exact ⟨1, by simp⟩⟩ :
          Localization.Away a.1) ^ n =
        Localization.mk 1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ := by
    -- The nth power of `1 / a` is the usual fraction `1 / a^n`.
    rw [Localization.mk_pow, one_pow]
    apply congrArg (fun d => Localization.mk 1 d)
    ext
    simp
  rw [hpow] at h
  simpa [g, s, reesAlgebraDegreeOne, hfrac] using h

/-- Helper for Lemma 10.70.3: if a power of `a` kills the coefficient `r`, then the corresponding
normalized chart fraction is already zero in the affine blowup chart. -/
theorem affineBlowupChart_fraction_eq_zero_of_pow_mul_eq_zero
    (I : Ideal R) (a : I) (n m : ℕ) (r : ↥(I ^ n)) (hzero : a.1 ^ m * r.1 = 0) :
    HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
      (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
      (monomial_mem_reesAlgebraGrade_for_chart I n r) = 0 := by
  -- Compare both sides in the ambient localization of the Rees algebra.
  apply (HomogeneousLocalization.ext_iff_val _ _).2
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨reesAlgebraDegreeOne I a ^ m, by exact ⟨m, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hzero' : r.1 * a.1 ^ m = 0 := by
    simpa [mul_comm] using hzero
  -- Multiplying the numerator by `(a^(1))^m` produces the zero monomial.
  simp [reesAlgebraDegreeOne, Polynomial.monomial_mul_monomial, hzero', mul_comm]

/-- Helper for Lemma 10.70.3: the comparison map from the affine blowup chart to the ordinary
localization `R_a` is injective. -/
theorem affineBlowupChartToLocalizationAway_injective
    (I : Ideal R) (a : I) :
    Function.Injective (affineBlowupChartToLocalizationAway I a) := by
  suffices hker : ∀ z : R[I / a], affineBlowupChartToLocalizationAway I a z = 0 → z = 0 by
    intro z w hzw
    -- Reduce injectivity to the triviality of the kernel.
    apply sub_eq_zero.mp
    apply hker
    simp [map_sub, hzw]
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

/-- Helper for Lemma 10.70.3: the ordinary localization `R_a` is the localization of the chart
`R[I/a]` at powers of the distinguished chart parameter. -/
theorem affineBlowupChartToLocalizationAway_isLocalizationAway
    (I : Ideal R) (a : I) :
    IsLocalization.Away (algebraMap R R[I / a] a.1) (Localization.Away a.1) := by
  -- Reuse the localization witness already proved in Lemma 10.70.2.
  simpa using (affineBlowupChart_isLocalizationAway I a)

/-- Helper for Lemma 10.70.3: the normalized degree-`n` chart fraction is cleared by the nth power
of the chart parameter. -/
theorem affineBlowupChart_fraction_mul_parameter_pow
    (I : Ideal R) (a : I) (n : ℕ) (r : ↥(I ^ n)) :
    let frac :=
      HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
        (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
        (monomial_mem_reesAlgebraGrade_for_chart I n r)
    frac * (algebraMap R R[I / a] a.1) ^ n = algebraMap R R[I / a] r.1 := by
  let frac :=
    HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
      (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
      (monomial_mem_reesAlgebraGrade_for_chart I n r)
  -- Compute both sides in `R_a`, where the denominator-clearing identity is standard.
  apply affineBlowupChartToLocalizationAway_injective I a
  have ha_map :
      affineBlowupChartToLocalizationAway I a ((algebraMap R R[I / a] a.1) ^ n) =
        algebraMap R (Localization.Away a.1) (a.1 ^ n) := by
    calc
      affineBlowupChartToLocalizationAway I a ((algebraMap R R[I / a] a.1) ^ n) =
          (affineBlowupChartToLocalizationAway I a (algebraMap R R[I / a] a.1)) ^ n := by
            rw [map_pow]
      _ = (algebraMap R (Localization.Away a.1) a.1) ^ n := by
            exact congrArg (fun z : Localization.Away a.1 ↦ z ^ n)
              (affineBlowupChartToLocalizationAway_algebraMap I a a.1)
      _ = algebraMap R (Localization.Away a.1) (a.1 ^ n) := by
            rw [← map_pow]
  have hr_map :
      affineBlowupChartToLocalizationAway I a (algebraMap R R[I / a] r.1) =
        algebraMap R (Localization.Away a.1) r.1 := by
    exact affineBlowupChartToLocalizationAway_algebraMap I a r.1
  rw [map_mul, affineBlowupChartToLocalizationAway_fraction_of_monomial, ha_map, hr_map,
    Localization.mk_eq_mk'_apply,
    ← IsLocalization.mk'_one (M := Submonoid.powers a.1) (S := Localization.Away a.1) (a.1 ^ n),
    ← IsLocalization.mk'_mul (M := Submonoid.powers a.1) (S := Localization.Away a.1)]
  simpa using
    (IsLocalization.mk'_mul_cancel_right (M := Submonoid.powers a.1)
      (S := Localization.Away a.1) r.1
      ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩)

/-- Helper for Lemma 10.70.3: the comparison map sends `x / a` to the ordinary localization
fraction `x / a`. -/
theorem affineBlowupChartToLocalizationAway_basicFraction
    (I : Ideal R) (a x : I) :
    affineBlowupChartToLocalizationAway I a (affineBlowupChartBasicFraction I a x) =
      Localization.mk x.1 ⟨a.1, by exact ⟨1, by simp⟩⟩ := by
  let g : reesAlgebra I →+* Localization.Away a.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
      (reesAlgebra I).toSubring.subtype
  have hfrac (r : R) :
      algebraMap R (Localization.Away a.1) r *
          Localization.mk 1 ⟨a.1, by exact ⟨1, by simp⟩⟩ =
        Localization.mk r ⟨a.1, by exact ⟨1, by simp⟩⟩ := by
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact (Localization.mk_eq_mk'_apply r ⟨a.1, by exact ⟨1, by simp⟩⟩).symm
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply]
  simp [affineBlowupChartBasicFraction]
  have h :=
    Localization.awayLift_mk g (reesAlgebraDegreeOne I a) (reesAlgebraDegreeOne I x)
      (Localization.mk 1 ⟨a.1, by exact ⟨1, by simp⟩⟩)
      (by
        rw [show g (reesAlgebraDegreeOne I a) = algebraMap R (Localization.Away a.1) a.1 by
          simp [g, reesAlgebraDegreeOne]]
        rw [hfrac]
        exact Localization.mk_self ⟨a.1, by exact ⟨1, by simp⟩⟩)
      1
  simpa [g, reesAlgebraDegreeOne, pow_one, hfrac] using h

/-- Helper for Lemma 10.70.3: a basic chart fraction is cleared by the chart parameter. -/
theorem affineBlowupChart_basicFraction_mul_parameter
    (I : Ideal R) (a x : I) :
    affineBlowupChartBasicFraction I a x * algebraMap R R[I / a] a.1 =
      algebraMap R R[I / a] x.1 := by
  apply affineBlowupChartToLocalizationAway_injective I a
  rw [map_mul, affineBlowupChartToLocalizationAway_basicFraction,
    affineBlowupChartToLocalizationAway_algebraMap,
    affineBlowupChartToLocalizationAway_algebraMap, Localization.mk_eq_mk'_apply,
    ← IsLocalization.mk'_one (M := Submonoid.powers a.1) (S := Localization.Away a.1) a.1,
    ← IsLocalization.mk'_mul (M := Submonoid.powers a.1) (S := Localization.Away a.1)]
  simpa using
    (IsLocalization.mk'_mul_cancel_right (M := Submonoid.powers a.1)
      (S := Localization.Away a.1) x.1
      ⟨a.1, by exact ⟨1, by simp⟩⟩)

/-- Helper for Lemma 10.70.3: the normalized degree-`n` chart fraction with numerator in `I ^ n`.
-/
noncomputable def affineBlowupChartPowerFraction
    (I : Ideal R) (a : I) (n : ℕ) (r : ↥(I ^ n)) :
    R[I / a] :=
  HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
    (monomial_mem_reesAlgebraGrade_for_chart I n r)

/- The direct chart map is the canonical bridge from the source-facing blowup chart `R[I/a]` to
the base-changed chart `S[IS/b]`; the tensor-product comparison map below is derived from it. -/

end
