import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_70_3 (from Chap10) -/
open HomogeneousLocalization
open IsLocalization
open Polynomial
open scoped AffineBlowupChart DirectSum TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling pass for Lemma 10.70.3.

Primary domain: commutative algebra of affine blowup charts under flat base change.

Sampled owner declarations:
* `affineBlowupChart` from `Definition_10_70_1.lean`;
* `affineBlowupChartScaledMap_surjective_and_ker_eq_f_power_torsion` from
  `Lemma_10_70_8.lean`;
* `Ideal.primaryComponent_mem` and `Submodule.mem_torsionBySet_iff` from mathlib's torsion API.

Owner abstraction: the affine blowup chart `R[I/a]`, with the canonical base-change map
`tensorToAffineBlowupAlgebra : S ⊗[R] R[I/a] → S[IS/b]`.
Primitive data here are the induced ideal `Ideal.map (algebraMap R S) I`, the distinguished image
`mappedIdealElement I a`, and the comparison map on blowup charts. The primary-component equality
is derived API; the source-facing statement is the torsion description of the kernel.

Source/core/bridge triage:
* source-facing: the surjective base-change map with kernel given by powers of the distinguished
  tensor image of `a`;
* core/canonical: the same kernel as a primary component;
* bridge/view: `tensorToAffineBlowupAlgebra`.
-/

/-- The image of `a ∈ I` in the extended ideal `Ideal.map (algebraMap R S) I`. -/
def mappedIdealElement {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) : Ideal.map (algebraMap R S) I :=
  ⟨algebraMap R S a.1, Ideal.mem_map_of_mem (algebraMap R S) a.2⟩

private noncomputable instance affineBlowupAlgebraBaseChangeAlgebra {S : Type v} [CommRing S]
    [Algebra R S] (J : Ideal S) (b : J) :
    Algebra R S[J / b] :=
  RingHom.toAlgebra <| (algebraMap S S[J / b]).comp (algebraMap R S)

private theorem map_ideal_le_comap {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) :
    I ≤ Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) := by
  intro x hx
  exact Ideal.mem_map_of_mem (algebraMap R S) hx

private theorem reesAlgebraMap_mem_grade {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R)
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
private theorem homogeneousLocalization_map_fromZeroRingHom
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
private theorem away_map_fromZeroRingHom
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

private noncomputable def reesAlgebraBaseChangeGradedHom {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) :
    reesAlgebraGrade I →+*ᵍ reesAlgebraGrade (Ideal.map (algebraMap R S) I) where
  toRingHom := reesAlgebraMap (algebraMap R S) (map_ideal_le_comap I)
  map_mem := reesAlgebraMap_mem_grade I

private theorem reesAlgebraBaseChange_degreeOne {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :
    reesAlgebraBaseChangeGradedHom I (reesAlgebraDegreeOne I a) =
      reesAlgebraDegreeOne (Ideal.map (algebraMap R S) I) (mappedIdealElement I a) := by
  -- Both sides are the same degree-one monomial after applying the coefficient map.
  ext
  simp [reesAlgebraBaseChangeGradedHom, reesAlgebraDegreeOne, mappedIdealElement, reesAlgebraMap]

/-- Helper for Lemma 10.70.3: the constant polynomial `r` lies in the degree-zero part of the Rees
algebra. -/
private theorem reesAlgebra_zeroDegree_mem (I : Ideal R) (r : R) :
    algebraMap R (reesAlgebra I) r ∈ reesAlgebraGrade I 0 := by
  refine ⟨⟨r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (monomial 0 r : R[X]) = C r
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.3: the constant polynomial `algebraMap R S r` lies in the degree-zero
part of the base-changed Rees algebra. -/
private theorem reesAlgebra_baseChange_zeroDegree_mem {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (r : R) :
    algebraMap S (reesAlgebra (Ideal.map (algebraMap R S) I)) (algebraMap R S r) ∈
      reesAlgebraGrade (Ideal.map (algebraMap R S) I) 0 := by
  refine ⟨⟨algebraMap R S r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (monomial 0 (algebraMap R S r) : S[X]) = C (algebraMap R S r)
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.3: the degree-zero Rees coefficient determined by `r`. -/
private noncomputable def reesAlgebraZeroDegreeCoeff (I : Ideal R) (r : R) :
    reesAlgebraGrade I 0 :=
  ⟨algebraMap R (reesAlgebra I) r, reesAlgebra_zeroDegree_mem I r⟩

/-- Helper for Lemma 10.70.3: the degree-zero base-changed Rees coefficient determined by
`algebraMap R S r`. -/
private noncomputable def reesAlgebraBaseChangeZeroDegreeCoeff {S : Type v} [CommRing S]
    [Algebra R S]
    (I : Ideal R) (r : R) :
    reesAlgebraGrade (Ideal.map (algebraMap R S) I) 0 :=
  ⟨algebraMap S (reesAlgebra (Ideal.map (algebraMap R S) I)) (algebraMap R S r),
    reesAlgebra_baseChange_zeroDegree_mem I r⟩

/-- Helper for Lemma 10.70.3: the base-change graded homomorphism sends the degree-zero Rees
coefficient represented by `r` to the corresponding degree-zero coefficient represented by
`algebraMap R S r`. -/
private theorem reesAlgebraBaseChange_zeroDegree_algebraMap {S : Type v} [CommRing S]
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
private noncomputable def reesAlgebraBaseChangeGradeZeroAlgebraMap {S : Type v} [CommRing S]
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
private theorem reesAlgebra_zeroDegree_mem_generic {T : Type w} [CommRing T]
    (J : Ideal T) (t : T) :
    algebraMap T (reesAlgebra J) t ∈ reesAlgebraGrade J 0 := by
  refine ⟨⟨t, by simp⟩, ?_⟩
  apply Subtype.ext
  change (monomial 0 t : T[X]) = C t
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.3: the degree-zero Rees coefficient determined by a scalar in an
arbitrary ambient ring. -/
private noncomputable def reesAlgebraZeroDegreeCoeff_generic {T : Type w} [CommRing T]
    (J : Ideal T) (t : T) :
    reesAlgebraGrade J 0 :=
  ⟨algebraMap T (reesAlgebra J) t, reesAlgebra_zeroDegree_mem_generic J t⟩

/-- Helper for Lemma 10.70.3: the degree-zero Rees coefficients give the canonical algebra map
into the degree-zero graded piece for an arbitrary ideal. -/
private noncomputable def reesAlgebraGradeZeroAlgebraMap_generic {T : Type w} [CommRing T]
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
private theorem affineBlowupChart_algebraMap_eq_fromZeroRingHom {T : Type w} [CommRing T]
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
  rfl

/-- Helper for Lemma 10.70.3: the power `a^n` is an allowed denominator in the ordinary
localization `R_a`. -/
private theorem affineBlowupChart_parameter_pow_mem (I : Ideal R) (a : I) (n : ℕ) :
    a.1 ^ n ∈ Submonoid.powers a.1 := by
  exact ⟨n, rfl⟩

/-- Helper for Lemma 10.70.3: the monomial with coefficient in `I ^ n` lies in the degree-`n`
piece of the Rees algebra. -/
private theorem monomial_mem_reesAlgebraGrade
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I n := by
  -- Unpack the graded piece through its range description.
  change (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      LinearMap.range _
  exact ⟨r, rfl⟩

/-- Helper for Lemma 10.70.3: the same monomial numerator has the degree required by the chart
fraction with denominator `(a^(1))^n`. -/
private theorem monomial_mem_reesAlgebraGrade_for_chart
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I (n • 1) := by
  -- In the natural-number grading, `n • 1 = n`.
  simpa [nsmul_eq_mul] using monomial_mem_reesAlgebraGrade I n r

/-- Helper for Lemma 10.70.3: the normalized monomial fraction `r / a^n` in the affine blowup
chart maps to the ordinary localization fraction `r / a^n` in `R_a`. -/
private theorem affineBlowupChartToLocalizationAway_fraction_of_monomial
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
private theorem affineBlowupChart_fraction_eq_zero_of_pow_mul_eq_zero
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
private theorem affineBlowupChartToLocalizationAway_injective
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

/-- Helper for Lemma 10.70.3: the normalized degree-`n` chart fraction is cleared by the nth power
of the chart parameter. -/
private theorem affineBlowupChart_fraction_mul_parameter_pow
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

/-- Helper for Lemma 10.70.3: the normalized degree-`n` chart fraction with numerator in `I ^ n`.
-/
private noncomputable def affineBlowupChartPowerFraction
    (I : Ideal R) (a : I) (n : ℕ) (r : ↥(I ^ n)) :
    R[I / a] :=
  HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
    (monomial_mem_reesAlgebraGrade_for_chart I n r)

/- The direct chart map is the canonical bridge from the source-facing blowup chart `R[I/a]` to
the base-changed chart `S[IS/b]`; the tensor-product comparison map below is derived from it. -/
set_option maxHeartbeats 400000 in
/-- Helper for Lemma 10.70.3: the underlying ring homomorphism of the base-change chart map. -/
private noncomputable def affineBlowupChartBaseChangeMap_toRingHom {S : Type v} [CommRing S]
    [Algebra R S] (I : Ideal R) (a : I) :
    R[I / a] →+*
      affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  exact Eq.mp
    (congrArg
      (fun x ↦ R[I / a] →+* Away (reesAlgebraGrade J) x)
      (by simpa [J, b] using reesAlgebraBaseChange_degreeOne I a))
    (HomogeneousLocalization.Away.map (reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a))

/-- Helper for Lemma 10.70.3: transporting an ordinary function along a codomain equality commutes
with evaluating the transported function at a point. -/
private theorem cast_apply_of_codomain_eq
    {α : Sort u} {β γ : Sort w} (h : β = γ) (g : α → β) (x : α) :
    Eq.mp (congrArg (fun T ↦ α → T) h) g x = cast h (g x) := by
  -- This isolates the pointwise transport before any localization-specific rewriting.
  cases h
  rfl

/-- Helper for Lemma 10.70.3: the target chart’s `R`-algebra map is the composite of the scalar
extension map `R → S` with the target chart’s canonical `S`-algebra map. -/
private theorem affineBlowupChartBaseChange_target_algebraMap_eq
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (r : R) :
    algebraMap R
        (affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a)) r =
      algebraMap S
        (affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a))
        (algebraMap R S r) := by
  -- The auxiliary `R`-algebra structure on the target chart is defined by this composite.
  rfl

set_option maxHeartbeats 40000000 in
/-- The canonical affine-blowup-chart map induced by a base change `R → S`. -/
noncomputable def affineBlowupChartBaseChangeMap {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    R[I / a] →ₐ[R] S[J / b] := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  letI : Algebra R S[J / b] :=
    affineBlowupAlgebraBaseChangeAlgebra J b
  exact
    { toRingHom := affineBlowupChartBaseChangeMap_toRingHom (S := S) I a
      commutes' := by
        intro r
        let hdeg :
            Away (reesAlgebraGrade J)
                ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)) =
              affineBlowupChart J b := by
          simpa [affineBlowupChart, J, b] using
            congrArg (fun x ↦ Away (reesAlgebraGrade J) x)
              (reesAlgebraBaseChange_degreeOne (S := S) I a)
        have hsource :
            algebraMap R R[I / a] r =
              HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade I)
                (Submonoid.powers (reesAlgebraDegreeOne I a))
                (reesAlgebraZeroDegreeCoeff I r) := by
          -- Rewrite the source scalar as the canonical degree-zero class in the source chart.
          simpa [reesAlgebraZeroDegreeCoeff, reesAlgebraZeroDegreeCoeff_generic] using
            affineBlowupChart_algebraMap_eq_fromZeroRingHom I a r
        have hcast :
            affineBlowupChartBaseChangeMap_toRingHom (S := S) I a
                (HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade I)
                  (Submonoid.powers (reesAlgebraDegreeOne I a))
                  (reesAlgebraZeroDegreeCoeff I r)) =
              cast hdeg
                (HomogeneousLocalization.Away.map (reesAlgebraBaseChangeGradedHom I)
                  (reesAlgebraDegreeOne I a)
                  (HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade I)
                    (Submonoid.powers (reesAlgebraDegreeOne I a))
                    (reesAlgebraZeroDegreeCoeff I r))) := by
          -- Isolate the codomain transport so the graded-map computation happens before the cast.
          simpa [affineBlowupChartBaseChangeMap_toRingHom, J, b, hdeg] using
            (cast_apply_of_codomain_eq
              (h := hdeg)
              (g := HomogeneousLocalization.Away.map (reesAlgebraBaseChangeGradedHom I)
                (reesAlgebraDegreeOne I a))
              (x := HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade I)
                (Submonoid.powers (reesAlgebraDegreeOne I a))
                (reesAlgebraZeroDegreeCoeff I r)))
        have hraw :
            HomogeneousLocalization.Away.map (reesAlgebraBaseChangeGradedHom I)
                (reesAlgebraDegreeOne I a)
                (HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade I)
                  (Submonoid.powers (reesAlgebraDegreeOne I a))
                  (reesAlgebraZeroDegreeCoeff I r)) =
              HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade J)
                (Submonoid.powers ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)))
                ((reesAlgebraBaseChangeGradedHom I).gradedAddHom 0
                  (reesAlgebraZeroDegreeCoeff I r)) := by
          -- The raw away-map sends a degree-zero scalar class to the corresponding target scalar
          -- class.
          simpa using
            (away_map_fromZeroRingHom (reesAlgebraGrade I) (reesAlgebraGrade J)
              (reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)
              (reesAlgebraZeroDegreeCoeff I r))
        have htarget :
            HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade J)
                (Submonoid.powers (reesAlgebraDegreeOne J b))
                (reesAlgebraBaseChangeZeroDegreeCoeff (S := S) I r) =
              algebraMap R (affineBlowupChart J b) r := by
          -- Convert the target degree-zero class back to the canonical `R`-algebra scalar.
          calc
            HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade J)
                (Submonoid.powers (reesAlgebraDegreeOne J b))
                (reesAlgebraBaseChangeZeroDegreeCoeff (S := S) I r) =
              algebraMap S (affineBlowupChart J b) (algebraMap R S r) := by
                simpa [reesAlgebraBaseChangeZeroDegreeCoeff,
                  reesAlgebraZeroDegreeCoeff_generic] using
                  (affineBlowupChart_algebraMap_eq_fromZeroRingHom J b
                    (algebraMap R S r)).symm
            _ = algebraMap R (affineBlowupChart J b) r := by
                symm
                exact affineBlowupChartBaseChange_target_algebraMap_eq (S := S) I a r
        -- Route correction: compute the graded-map image on the raw degree-zero class first, then
        -- eliminate the codomain cast only at the end.
        rw [hsource, hcast, hraw, reesAlgebraBaseChange_zeroDegree_algebraMap]
        simpa [hdeg] using htarget }

noncomputable instance instAlgebraAffineBlowupChartBaseChange {S : Type v} [CommRing S]
    [Algebra R S]
    (I : Ideal R) (a : I) :
    Algebra R[I / a] (affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a)) :=
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  RingHom.toAlgebra (show R[I / a] →+* S[J / b] from (affineBlowupChartBaseChangeMap I a).toRingHom)

/-- The canonical base-change map
`S ⊗[R] R[I/a] → S[J/b]`, where `J = Ideal.map (algebraMap R S) I` and `b ∈ J` is the image of
`a`. -/
noncomputable def tensorToAffineBlowupAlgebra
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    S ⊗[R] R[I / a] →ₐ[S] S[J / b] :=
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  letI : Algebra S S := Algebra.id S
  letI : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S S[J / b] := inferInstance
  letI : SMul S S[J / b] := (inferInstance : Algebra S S[J / b]).toSMul
  letI : Algebra R S[J / b] := affineBlowupAlgebraBaseChangeAlgebra J b
  letI : IsScalarTower R S S[J / b] :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change ((algebraMap S S[J / b]).comp (algebraMap R S)) x =
        (algebraMap S S[J / b]) ((algebraMap R S) x)
      rfl
  let f : S →ₐ[S] S[J / b] := Algebra.ofId S S[J / b]
  let g : R[I / a] →ₐ[R] S[J / b] := affineBlowupChartBaseChangeMap I a
  (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) :
    S ⊗[R] R[I / a] →ₐ[S] S[J / b])

/-- Helper for Lemma 10.70.3: the base-change tensor map sends the distinguished source parameter
to the distinguished chart parameter in the target. -/
private theorem tensorToAffineBlowupAlgebra_parameter_image
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    (tensorToAffineBlowupAlgebra S I a) (algebraMap R (S ⊗[R] R[I / a]) a.1) =
      algebraMap S S[J / b] b.1 := by
  intro J b
  -- View the source parameter as an `S`-algebra scalar inside the tensor product, then use the
  -- `S`-algebra compatibility of the tensor lift.
  simpa [J, b, mappedIdealElement, Algebra.TensorProduct.algebraMap_apply] using
    (AlgHom.commutes (tensorToAffineBlowupAlgebra S I a) (algebraMap R S a.1))

/-- Helper for Lemma 10.70.3: the base-changed chart map sends a source basic fraction to the
corresponding target basic fraction. -/
private theorem affineBlowupChartBaseChangeMap_basicFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a x : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    affineBlowupChartBaseChangeMap_toRingHom (S := S) I a (affineBlowupChartBasicFraction I a x) =
      affineBlowupChartBasicFraction J b (mappedIdealElement I x) := by
  intro J b
  let hdeg :
      Away (reesAlgebraGrade J)
          ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)) =
        affineBlowupChart J b := by
    simpa [affineBlowupChart, J, b] using
      congrArg (fun y ↦ Away (reesAlgebraGrade J) y)
        (reesAlgebraBaseChange_degreeOne (S := S) I a)
  -- The base-change chart map is the homogeneous-localization map induced by the Rees algebra
  -- coefficient map, so it preserves normalized degree-one fractions.
  change cast hdeg
      (HomogeneousLocalization.Away.map (reesAlgebraBaseChangeGradedHom I)
        (reesAlgebraDegreeOne I a) (affineBlowupChartBasicFraction I a x)) =
    affineBlowupChartBasicFraction J b (mappedIdealElement I x)
  simp [affineBlowupChartBasicFraction, J, b, mappedIdealElement, hdeg]

/-- Helper for Lemma 10.70.3: the base-changed chart map preserves normalized degree-`n`
fractions. -/
private theorem affineBlowupChartBaseChangeMap_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    let xJ : ↥(J ^ n) :=
      ⟨algebraMap R S x.1, by
        simpa [J, Ideal.map_pow] using
          (Ideal.mem_map_of_mem (algebraMap R S) x.2 :
            algebraMap R S x.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
    affineBlowupChartBaseChangeMap_toRingHom (S := S) I a
        (affineBlowupChartPowerFraction I a n x) =
      affineBlowupChartPowerFraction J b n xJ := by
  intro J b xJ
  let hdeg :
      Away (reesAlgebraGrade J)
          ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)) =
        affineBlowupChart J b := by
    simpa [affineBlowupChart, J, b] using
      congrArg (fun y ↦ Away (reesAlgebraGrade J) y)
        (reesAlgebraBaseChange_degreeOne (S := S) I a)
  -- The homogeneous-localization map acts coefficientwise on the normalized monomial fraction.
  change cast hdeg
      (HomogeneousLocalization.Away.map (reesAlgebraBaseChangeGradedHom I)
        (reesAlgebraDegreeOne I a) (affineBlowupChartPowerFraction I a n x)) =
    affineBlowupChartPowerFraction J b n xJ
  simp [affineBlowupChartPowerFraction, J, b, mappedIdealElement, hdeg]

/-- Helper for Lemma 10.70.3: on a pure tensor `s ⊗ x/a`, the tensor comparison map multiplies
the target basic fraction by the scalar `s`. -/
private theorem tensorToAffineBlowupAlgebra_tmul_basicFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a x : I) (s : S) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    tensorToAffineBlowupAlgebra S I a (s ⊗ₜ[R] affineBlowupChartBasicFraction I a x) =
      algebraMap S S[J / b] s * affineBlowupChartBasicFraction J b (mappedIdealElement I x) := by
  intro J b
  -- Evaluate the tensor lift on a pure tensor, then rewrite the chart component via the previous
  -- basic-fraction transport lemma.
  simp [tensorToAffineBlowupAlgebra, Algebra.TensorProduct.lift_tmul,
    affineBlowupChartBaseChangeMap_basicFraction, J, b]

/-- Helper for Lemma 10.70.3: on a pure tensor `s ⊗ x/a^n`, the tensor comparison map multiplies
the target normalized degree-`n` fraction by the scalar `s`. -/
private theorem tensorToAffineBlowupAlgebra_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    let xJ : ↥(J ^ n) :=
      ⟨algebraMap R S x.1, by
        simpa [J, Ideal.map_pow] using
          (Ideal.mem_map_of_mem (algebraMap R S) x.2 :
            algebraMap R S x.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
    tensorToAffineBlowupAlgebra S I a (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) =
      algebraMap S S[J / b] s * affineBlowupChartPowerFraction J b n xJ := by
  intro J b xJ
  -- Evaluate the tensor lift on a pure tensor, then rewrite the chart component by the degree-`n`
  -- transport lemma.
  simp [tensorToAffineBlowupAlgebra, Algebra.TensorProduct.lift_tmul,
    affineBlowupChartBaseChangeMap_powerFraction, J, b]

/-- Helper for Lemma 10.70.3: every element of the extended ideal `IS` comes from a tensor in
`S ⊗[R] I` under the multiplication map. -/
private theorem mappedIdealElement_exists_tensorLift
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R)
    (x : Ideal.map (algebraMap R S) I) :
    ∃ t : S ⊗[R] I,
      (Algebra.TensorProduct.rid R R S).toLinearMap
          ((LinearMap.lTensor S (Submodule.subtype (I.restrictScalars R))) t) = x.1 := by
  let μ : S ⊗[R] I →ₗ[R] S :=
    (Algebra.TensorProduct.rid R R S).toLinearMap.comp
      (LinearMap.lTensor S (Submodule.subtype (I.restrictScalars R)))
  have hrid_surj :
      Function.Surjective
        ((Algebra.TensorProduct.rid R R S).toAlgHom : S ⊗[R] R →ₐ[R] S) :=
    (Algebra.TensorProduct.rid R R S).surjective
  have hrid_comp :
      ((Algebra.TensorProduct.rid R R S).toAlgHom).comp
          (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) =
        algebraMap R S := by
    ext r
    simp
  have hxmap :
      x.1 ∈ Ideal.map ((Algebra.TensorProduct.rid R R S).toAlgHom)
        (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) I) := by
    simpa [Ideal.map_map, hrid_comp] using x.2
  rcases (Ideal.mem_map_iff_of_surjective
      ((Algebra.TensorProduct.rid R R S).toAlgHom) hrid_surj).1 hxmap with
    ⟨y, hy, hyx⟩
  change y ∈
      ((Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R) I).restrictScalars R :
        Submodule R (S ⊗[R] R)) at hy
  rw [Ideal.map_includeRight_eq (R := R) (A := S) (B := R) I] at hy
  rcases hy with ⟨t, rfl⟩
  refine ⟨t, ?_⟩
  simpa [μ, TensorProduct.lmul'_toLinearMap] using hyx

/-- Helper for Lemma 10.70.3: every target basic fraction `x / b` comes from the tensor
comparison map. -/
private theorem affineBlowupChart_target_basicFraction_surjective
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    ∀ x : J, ∃ z : S ⊗[R] R[I / a],
      tensorToAffineBlowupAlgebra S I a z = affineBlowupChartBasicFraction J b x := by
  intro J b x
  rcases mappedIdealElement_exists_tensorLift S I x with ⟨t, ht⟩
  let A := S ⊗[R] R[I / a]
  let B := S[J / b]
  let φ := tensorToAffineBlowupAlgebra S I a
  let bB : B := algebraMap S B b.1
  have hcleared :
      ∃ z : A, φ z * bB = algebraMap S B x.1 := by
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · refine ⟨0, by simp [bB]⟩
    · intro s y
      refine ⟨s ⊗ₜ[R] affineBlowupChartBasicFraction I a y, ?_⟩
      have hbasic :
          affineBlowupChartBasicFraction J b (mappedIdealElement I y) * bB =
            algebraMap S B (algebraMap R S y.1) := by
        have hyJ : algebraMap R S y.1 ∈ J := by
          simpa [J, mappedIdealElement] using (mappedIdealElement I y).2
        -- Clear the denominator in the target chart using the degree-one fraction formula.
        simpa [B, bB, affineBlowupChartBasicFraction, pow_one, mappedIdealElement] using
          (affineBlowupChart_fraction_mul_parameter_pow (R := S) J b 1
            (r := ⟨algebraMap R S y.1, by simpa [pow_one] using hyJ⟩))
      calc
        φ (s ⊗ₜ[R] affineBlowupChartBasicFraction I a y) * bB =
            (algebraMap S B s * affineBlowupChartBasicFraction J b (mappedIdealElement I y)) * bB := by
              rw [tensorToAffineBlowupAlgebra_tmul_basicFraction]
        _ = algebraMap S B s * (affineBlowupChartBasicFraction J b (mappedIdealElement I y) * bB) := by
              ring
        _ = algebraMap S B s * algebraMap S B (algebraMap R S y.1) := by rw [hbasic]
        _ = algebraMap S B ((Algebra.TensorProduct.rid R R S).toLinearMap
              ((LinearMap.lTensor S (Submodule.subtype (I.restrictScalars R))) (s ⊗ₜ[R] y))) := by
              simp [LinearMap.lTensor_tmul, Algebra.TensorProduct.rid_tmul, Algebra.smul_def,
                mul_comm, mul_left_comm, mul_assoc]
    · intro t₁ t₂ h₁ h₂
      rcases h₁ with ⟨z₁, hz₁⟩
      rcases h₂ with ⟨z₂, hz₂⟩
      refine ⟨z₁ + z₂, ?_⟩
      simp [φ, bB, left_distrib, right_distrib, hz₁, hz₂]
  rcases hcleared with ⟨z, hz⟩
  have hbasic :
      affineBlowupChartBasicFraction J b x * bB = algebraMap S B x.1 := by
    -- The target basic fraction is characterized by the same cleared-denominator identity.
    simpa [B, bB, affineBlowupChartBasicFraction, pow_one] using
      (affineBlowupChart_fraction_mul_parameter_pow (R := S) J b 1
        (r := ⟨x.1, by simpa [pow_one] using x.2⟩))
  have hreg : IsRegular bB := by
    simpa [B, bB] using (affineBlowupChart_isRegular (R := S) J b)
  refine ⟨z, ?_⟩
  apply (hreg.1)
  calc
    bB * φ z = φ z * bB := by ring
    _ = algebraMap S B x.1 := hz
    _ = affineBlowupChartBasicFraction J b x * bB := hbasic.symm
    _ = bB * affineBlowupChartBasicFraction J b x := by ring

/-- Helper for Lemma 10.70.3: every normalized target fraction `y / b^n` with `y ∈ J ^ n` comes
from the tensor comparison map. -/
private theorem affineBlowupChart_target_powerFraction_surjective
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    ∀ x : J ^ n, ∃ z : S ⊗[R] R[I / a],
      tensorToAffineBlowupAlgebra S I a z = affineBlowupChartPowerFraction J b n x := by
  intro J b x
  rcases mappedIdealElement_exists_tensorLift S (I ^ n) x with ⟨t, ht⟩
  let A := S ⊗[R] R[I / a]
  let B := S[J / b]
  let φ := tensorToAffineBlowupAlgebra S I a
  let bB : B := algebraMap S B b.1
  have hcleared :
      ∃ z : A, φ z * bB ^ n = algebraMap S B x.1 := by
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · refine ⟨0, by simp⟩
    · intro s y
      let yJ : ↥(J ^ n) :=
        ⟨algebraMap R S y.1, by
          simpa [J, Ideal.map_pow] using
            (Ideal.mem_map_of_mem (algebraMap R S) y.2 :
              algebraMap R S y.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
      refine ⟨s ⊗ₜ[R] affineBlowupChartPowerFraction I a n y, ?_⟩
      have hbasic :
          affineBlowupChartPowerFraction J b n yJ * bB ^ n =
            algebraMap S B (algebraMap R S y.1) := by
        -- Clear the denominator in the target chart using the degree-`n` fraction formula.
        simpa [B, bB, affineBlowupChartPowerFraction, yJ] using
          (affineBlowupChart_fraction_mul_parameter_pow (R := S) J b n yJ)
      calc
        φ (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n y) * bB ^ n =
            (algebraMap S B s * affineBlowupChartPowerFraction J b n yJ) * bB ^ n := by
              rw [tensorToAffineBlowupAlgebra_tmul_powerFraction]
        _ = algebraMap S B s * (affineBlowupChartPowerFraction J b n yJ * bB ^ n) := by
              ring
        _ = algebraMap S B s * algebraMap S B (algebraMap R S y.1) := by rw [hbasic]
        _ = algebraMap S B ((Algebra.TensorProduct.rid R R S).toLinearMap
              ((LinearMap.lTensor S (Submodule.subtype ((I ^ n).restrictScalars R)))
                (s ⊗ₜ[R] y))) := by
              simp [LinearMap.lTensor_tmul, Algebra.TensorProduct.rid_tmul, Algebra.smul_def,
                mul_comm, mul_left_comm, mul_assoc]
    · intro t₁ t₂ h₁ h₂
      rcases h₁ with ⟨z₁, hz₁⟩
      rcases h₂ with ⟨z₂, hz₂⟩
      refine ⟨z₁ + z₂, ?_⟩
      simp [φ, bB, left_distrib, right_distrib, hz₁, hz₂]
  rcases hcleared with ⟨z, hz⟩
  have hbasic :
      affineBlowupChartPowerFraction J b n x * bB ^ n = algebraMap S B x.1 := by
    -- The target normalized fraction is characterized by the same cleared-denominator identity.
    simpa [B, bB, affineBlowupChartPowerFraction] using
      (affineBlowupChart_fraction_mul_parameter_pow (R := S) J b n x)
  have hreg : IsRegular bB := by
    simpa [B, bB] using (affineBlowupChart_isRegular (R := S) J b)
  refine ⟨z, ?_⟩
  apply (hreg.pow n).1
  calc
    bB ^ n * φ z = φ z * bB ^ n := by ring
    _ = algebraMap S B x.1 := by simpa [ht] using hz
    _ = affineBlowupChartPowerFraction J b n x * bB ^ n := hbasic.symm
    _ = bB ^ n * affineBlowupChartPowerFraction J b n x := by ring

/-- Helper for Lemma 10.70.3: every source element annihilated by a power of the distinguished
tensor parameter already lies in the kernel of the base-change map. -/
private theorem exists_pow_mul_eq_zero_mem_ker_tensorToAffineBlowupAlgebra
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    (∃ n : ℕ, (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x = 0) →
      x ∈ RingHom.ker (tensorToAffineBlowupAlgebra S I a).toRingHom := by
  intro hx
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  let φ := tensorToAffineBlowupAlgebra S I a
  have hreg : IsRegular (algebraMap S S[J / b] b.1) := by
    simpa using (affineBlowupChart_isRegular (R := S) J b)
  have haS_pow (n : ℕ) :
      (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n =
        ((algebraMap R S a.1) ^ n) ⊗ₜ[R] (1 : R[I / a]) := by
    induction n with
    | zero =>
        rw [pow_zero, Algebra.TensorProduct.one_def]
        simp
    | succ n ih =>
        rw [pow_succ, ih, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
        simp [pow_succ]
  rcases hx with ⟨n, hn⟩
  rw [RingHom.mem_ker]
  have hparamPow_tmul :
      φ (((algebraMap R S a.1) ^ n) ⊗ₜ[R] (1 : R[I / a])) =
        (algebraMap S S[J / b] b.1) ^ n := by
    -- First identify the image of the parameter, then raise that identity to the nth power.
    calc
      φ (((algebraMap R S a.1) ^ n) ⊗ₜ[R] (1 : R[I / a])) =
          φ ((((algebraMap R S a.1) ⊗ₜ[R] (1 : R[I / a])) : S ⊗[R] R[I / a]) ^ n) := by
            simp [Algebra.TensorProduct.tmul_pow]
      _ = (φ (((algebraMap R S a.1) ⊗ₜ[R] (1 : R[I / a])))) ^ n := by
            rw [map_pow]
      _ = (algebraMap S S[J / b] b.1) ^ n := by
            exact congrArg (fun z : S[J / b] ↦ z ^ n)
              (tensorToAffineBlowupAlgebra_parameter_image (S := S) I a)
  have hparamPow :
      φ ((algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n) =
        (algebraMap S S[J / b] b.1) ^ n := by
    simpa [haS_pow n] using hparamPow_tmul
  apply (hreg.pow n).1
  -- Mapping the annihilating relation across `φ` turns `aS` into the target parameter `b`.
  have hmapped :
      (algebraMap S S[J / b] b.1) ^ n * φ x =
        φ ((algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x) := by
    rw [← hparamPow, ← map_mul]
  calc
    (algebraMap S S[J / b] b.1) ^ n * φ x =
        φ ((algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x) := hmapped
    _ = φ 0 := by simpa [haS_pow n] using congrArg φ hn
    _ = (algebraMap S S[J / b] b.1) ^ n * 0 := by simp

/-- Helper for Lemma 10.70.3: tensoring the source chart-to-away map on the right gives the
explicit localization map from `S ⊗[R] R[I/a]` to `S ⊗[R] R_a`. -/
private noncomputable def tensorAffineBlowupSourceToLocalizationTensor
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    S ⊗[R] R[I / a] →+* S ⊗[R] Localization.Away a.1 :=
  (Algebra.TensorProduct.map (AlgHom.id R S)
      { toRingHom := affineBlowupChartToLocalizationAway I a
        commutes' := affineBlowupChartToLocalizationAway_algebraMap (I := I) a }).toRingHom

/-- Helper for Lemma 10.70.3: on normalized pure tensors, the tensor-localization map acts only on
the chart factor. -/
private theorem tensorAffineBlowupSourceToLocalizationTensor_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    tensorAffineBlowupSourceToLocalizationTensor S I a
        (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) =
      s ⊗ₜ[R] Localization.mk x.1
        ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ := by
  -- The tensor map is coefficientwise on pure tensors, so only the chart factor needs the
  -- monomial-fraction calculation.
  simp [tensorAffineBlowupSourceToLocalizationTensor,
    affineBlowupChartToLocalizationAway_fraction_of_monomial, affineBlowupChartPowerFraction,
    Algebra.TensorProduct.map_tmul]

/-- Helper for Lemma 10.70.3: composing the tensor-localization map with the standard
tensor/localization equivalence gives the ordinary away-localization map from the source tensor
product to `S_b`. -/
private noncomputable def tensorAffineBlowupSourceToAway
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    S ⊗[R] R[I / a] →+* Localization.Away (algebraMap R S a.1) :=
  (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1)).toRingHom.comp
    (tensorAffineBlowupSourceToLocalizationTensor S I a)

/-- Helper for Lemma 10.70.3: on normalized pure tensors, the ordinary away-localization map from
the source tensor product has the expected textbook formula `s ⊗ x/a^n ↦ s · x/b^n`. -/
private theorem tensorAffineBlowupSourceToAway_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    tensorAffineBlowupSourceToAway S I a
        (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
  let e : S ⊗[R] Localization.Away a.1 ≃ₐ[S] Localization.Away (algebraMap R S a.1) :=
    IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1)
  -- Route correction: evaluate the tensor/localization equivalence on `s ⊗ 1` and `1 ⊗ x/a^n`
  -- separately, then multiply the two standard formulas.
  rw [tensorAffineBlowupSourceToAway, RingHom.comp_apply,
    tensorAffineBlowupSourceToLocalizationTensor_tmul_powerFraction]
  have hs :
      e (s ⊗ₜ[R] (1 : Localization.Away a.1)) =
        algebraMap S (Localization.Away (algebraMap R S a.1)) s := by
    exact Localization.tensorLeftAlgEquiv_apply_tmul_one
      (M := Submonoid.powers a.1) (S := S) (x := s)
  have hxloc :
      e (1 ⊗ₜ[R] (Localization.mk x.1
          ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ : Localization.Away a.1)) =
        IsLocalization.Away.map (Localization.Away a.1)
          (Localization.Away (algebraMap R S a.1)) (algebraMap R S) a.1
          (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) := by
    exact Localization.tensorLeftAlgEquiv_apply_one_tmul
      (M := Submonoid.powers a.1) (S := S)
      (x := (Localization.mk x.1
        ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ : Localization.Away a.1))
  have hmk :
      IsLocalization.Away.map (Localization.Away a.1)
          (Localization.Away (algebraMap R S a.1)) (algebraMap R S) a.1
          (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) =
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
    rw [IsLocalization.Away.map, Localization.mk_eq_mk'_apply, IsLocalization.map_mk']
    apply congrArg (fun d =>
      IsLocalization.mk' (Localization.Away (algebraMap R S a.1)) (algebraMap R S x.1) d)
    ext
    simp [map_pow]
  calc
    e (s ⊗ₜ[R] Localization.mk x.1
        ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) =
      e ((s ⊗ₜ[R] (1 : Localization.Away a.1)) *
        (1 ⊗ₜ[R] Localization.mk x.1
          ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩)) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
    _ =
      e (s ⊗ₜ[R] (1 : Localization.Away a.1)) *
        e (1 ⊗ₜ[R] Localization.mk x.1
          ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) := by
            rw [map_mul]
    _ =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        IsLocalization.Away.map (Localization.Away a.1)
          (Localization.Away (algebraMap R S a.1)) (algebraMap R S) a.1
          (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) := by
            rw [hs, hxloc]
    _ =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
            rw [hmk]

/-- Helper for Lemma 10.70.3: after composing with the ordinary away-localization of the target
chart, the base-change map agrees with the ordinary away-localization map on a normalized pure
tensor. -/
private theorem tensorToAffineBlowupAlgebra_comp_to_away_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    affineBlowupChartToLocalizationAway J b
        (tensorToAffineBlowupAlgebra S I a (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x)) =
      tensorAffineBlowupSourceToAway S I a
        (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) := by
  intro J b
  let xJ : ↥(J ^ n) :=
    ⟨algebraMap R S x.1, by
      simpa [J, Ideal.map_pow] using
        (Ideal.mem_map_of_mem (algebraMap R S) x.2 :
          algebraMap R S x.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
  -- Evaluate the target chart map first, then rewrite the target fraction in the ordinary
  -- localization with the monomial-fraction formula.
  rw [tensorToAffineBlowupAlgebra_tmul_powerFraction]
  rw [map_mul]
  have hs :
      affineBlowupChartToLocalizationAway J b (algebraMap S S[J / b] s) =
        algebraMap S (Localization.Away (algebraMap R S a.1)) s := by
    simpa [J, b, mappedIdealElement] using
      (affineBlowupChartToLocalizationAway_algebraMap J b s)
  rw [hs, affineBlowupChartToLocalizationAway_fraction_of_monomial]
  simpa [xJ] using
    (tensorAffineBlowupSourceToAway_tmul_powerFraction (S := S) I a n x s).symm

/-- Helper for Lemma 10.70.3: after composing with ordinary away-localization, the target chart
map agrees with the source tensor-localization map on all source elements. -/
private theorem tensorToAffineBlowupAlgebra_comp_to_away
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    ∀ z : S ⊗[R] R[I / a],
      affineBlowupChartToLocalizationAway J b (tensorToAffineBlowupAlgebra S I a z) =
        tensorAffineBlowupSourceToAway S I a z := by
  intro J b z
  -- Normalize the chart factor to monomial fractions, then use tensor induction.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensorAffineBlowupSourceToAway]
  · intro s y
    obtain ⟨n, t, ht, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesAlgebraGrade I)
      (reesAlgebraDegreeOne_mem I a) y
    have ht' : t ∈ reesAlgebraGrade I n := by
      simpa [nsmul_eq_mul] using ht
    change t ∈ LinearMap.range _ at ht'
    rcases ht' with ⟨x, rfl⟩
    simpa [affineBlowupChartPowerFraction] using
      tensorToAffineBlowupAlgebra_comp_to_away_tmul_powerFraction (S := S) I a n x s
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂, tensorAffineBlowupSourceToAway]

/-- Helper for Lemma 10.70.3: tensoring the chart localization witness on the right gives the
canonical localization of `R[I/a] ⊗[R] S` at the image of powers of the chart parameter. -/
private theorem tensorAffineBlowupSource_right_isLocalization
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    IsLocalization
      (Algebra.algebraMapSubmonoid (R[I / a] ⊗[R] S)
        (Submonoid.powers (algebraMap R R[I / a] a.1)))
      (Localization.Away a.1 ⊗[R] S) := by
  let Q := R[I / a]
  letI : IsLocalization.Away (algebraMap R Q a.1) (Localization.Away a.1) :=
    inferInstance
  letI : Algebra S (Q ⊗[R] S) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := Q) (B := S)
  letI : Algebra S (Localization.Away a.1 ⊗[R] S) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := Localization.Away a.1) (B := S)
  letI : Algebra (Q ⊗[R] S) (Localization.Away a.1 ⊗[R] S) :=
    (tensor_right_map (R := R) (S := Localization.Away a.1) (Q := Q) (T := S)).toAlgebra
  have hQtower :
      (algebraMap (Q ⊗[R] S) (Localization.Away a.1 ⊗[R] S)).comp
          (algebraMap Q (Q ⊗[R] S)) =
        algebraMap Q (Localization.Away a.1 ⊗[R] S) := by
    exact tensor_right_map_q_tower (R := R) (S := Localization.Away a.1) (Q := Q) (T := S)
  letI : IsScalarTower Q (Q ⊗[R] S) (Localization.Away a.1 ⊗[R] S) :=
    IsScalarTower.of_algebraMap_eq' hQtower
  have hcompat :
      (algebraMap (Q ⊗[R] S) (Localization.Away a.1 ⊗[R] S)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    exact tensor_right_map_includeRight_comp
      (R := R) (S := Localization.Away a.1) (Q := Q) (T := S)
  -- Tensor the chart-localization witness on the right, then expose the same denominator submonoid
  -- on `R[I / a] ⊗[R] S`.
  simpa [Q] using
    (isLocalization_tensor_right_of_isLocalization
      (R := R) (S := Localization.Away a.1) (Q := Q)
      (M := Submonoid.powers (algebraMap R Q a.1)) (T := S) hcompat :
      IsLocalization
        (Algebra.algebraMapSubmonoid (Q ⊗[R] S)
          (Submonoid.powers (algebraMap R Q a.1)))
        (Localization.Away a.1 ⊗[R] S))

/-- Helper for Lemma 10.70.3: after commuting tensor factors, the source tensor-localization map
is the canonical right-tensor map induced by `R[I/a] → R_a`. -/
private theorem tensorAffineBlowupSourceToLocalizationTensor_comm
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    (Algebra.TensorProduct.comm R S (Localization.Away a.1))
      (tensorAffineBlowupSourceToLocalizationTensor S I a x) =
      tensor_right_map (R := R) (S := Localization.Away a.1) (Q := R[I / a]) (T := S)
        ((Algebra.TensorProduct.comm R S R[I / a]) x) := by
  -- Commute both tensor products and compare the two maps on simple tensors.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [tensorAffineBlowupSourceToLocalizationTensor]
  · intro s y
    simp [tensorAffineBlowupSourceToLocalizationTensor, tensor_right_map_tmul]
  · intro x₁ x₂ hx₁ hx₂
    simp [hx₁, hx₂]

/-- Helper for Lemma 10.70.3: vanishing of the ordinary away-localization map on the source tensor
product is equivalent, after commuting tensor factors, to vanishing of the canonical
right-tensor localization map. -/
private theorem tensorAffineBlowupSourceToAway_eq_zero_iff_tensor_right_map_eq_zero
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    tensorAffineBlowupSourceToAway S I a x = 0 ↔
      tensor_right_map (R := R) (S := Localization.Away a.1) (Q := R[I / a]) (T := S)
        ((Algebra.TensorProduct.comm R S R[I / a]) x) = 0 := by
  let commQa : S ⊗[R] Localization.Away a.1 ≃ₐ[R] Localization.Away a.1 ⊗[R] S :=
    Algebra.TensorProduct.comm R S (Localization.Away a.1)
  constructor
  · intro hχ
    have hχ0 : tensorAffineBlowupSourceToLocalizationTensor S I a x = 0 := by
      -- First remove the tensor/localization equivalence from the ordinary away-localization map.
      apply (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1)).injective
      simpa [tensorAffineBlowupSourceToAway] using hχ
    have hcomm :
        commQa (tensorAffineBlowupSourceToLocalizationTensor S I a x) = 0 := by
      -- Then commute tensor factors so the right-oriented localization owner can read the
      -- vanishing statement.
      simpa [commQa] using congrArg commQa hχ0
    simpa [commQa, tensorAffineBlowupSourceToLocalizationTensor_comm] using hcomm
  · intro hright
    have hcomm :
        commQa (tensorAffineBlowupSourceToLocalizationTensor S I a x) = 0 := by
      -- Rewrite the right-tensor vanishing back to the commuted source localization map.
      simpa [commQa, tensorAffineBlowupSourceToLocalizationTensor_comm] using hright
    have hχ0 : tensorAffineBlowupSourceToLocalizationTensor S I a x = 0 := by
      -- Undo the tensor commutation before reintroducing the away-localization equivalence.
      apply commQa.injective
      simpa [commQa] using hcomm
    simpa [tensorAffineBlowupSourceToAway] using
      congrArg (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1)) hχ0

/-- Helper for Lemma 10.70.3: if the source tensor element vanishes in the ordinary away
localization, then some power of the tensor image of `a` already annihilates it. -/
private theorem exists_pow_mul_eq_zero_of_tensorAffineBlowupSourceToAway_eq_zero
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a])
    (hχ : tensorAffineBlowupSourceToAway S I a x = 0) :
    ∃ n : ℕ, (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x = 0 := by
  let Q := R[I / a]
  let commQ : S ⊗[R] Q ≃ₐ[R] Q ⊗[R] S := Algebra.TensorProduct.comm R S Q
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid (Q ⊗[R] S)
          (Submonoid.powers (algebraMap R Q a.1)))
        (Localization.Away a.1 ⊗[R] S) :=
    tensorAffineBlowupSource_right_isLocalization (S := S) I a
  have hright :
      tensor_right_map (R := R) (S := Localization.Away a.1) (Q := Q) (T := S)
          (commQ x) = 0 := by
    -- Route correction: package the tensor-commutation transport once, then run the localization
    -- zero criterion only on the canonical right-oriented owner.
    exact
      (tensorAffineBlowupSourceToAway_eq_zero_iff_tensor_right_map_eq_zero
        (S := S) I a x).1 hχ
  obtain ⟨m, hm⟩ :=
    (IsLocalization.map_eq_zero_iff
      (M := Algebra.algebraMapSubmonoid (Q ⊗[R] S)
        (Submonoid.powers (algebraMap R Q a.1)))
      (S := Localization.Away a.1 ⊗[R] S)
      (commQ x)).mp hright
  rcases m with ⟨m, hm_mem⟩
  rcases
      (show ∃ u : Submonoid.powers (algebraMap R Q a.1),
          algebraMap Q (Q ⊗[R] S) u = m by
        simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map] using hm_mem) with
    ⟨u, rfl⟩
  rcases u.2 with ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  have hpow :
      algebraMap Q (Q ⊗[R] S) ((algebraMap R Q a.1) ^ n) =
        (algebraMap R (Q ⊗[R] S) a.1) ^ n := by
    rw [map_pow, IsScalarTower.algebraMap_apply R Q (Q ⊗[R] S)]
  have hright_pow :
      (algebraMap R (Q ⊗[R] S) a.1) ^ n * commQ x = 0 := by
    simpa [hpow] using hm
  -- Commute back to the original tensor order to recover the torsion relation on `x`.
  have hleft_pow := congrArg commQ.symm hright_pow
  simpa [commQ, map_mul, map_pow] using hleft_pow

-- Proof sketch: the canonical map `S ⊗[R] R[I/a] → S[IS/b]` sends `s ⊗ x / a^n` to the
-- corresponding fraction in `S[IS/b]`, which gives surjectivity by writing elements of `J^n` as
-- sums of tensors from `I^n`. Its kernel is exactly the `b`-power torsion, because localizing away
-- from `b` kills precisely the elements annihilated by some power of `b`.
/-- Membership in the kernel of the base-change map is exactly torsion by a power of the
distinguished tensor image of `a`. -/
theorem mem_ker_tensorToAffineBlowupAlgebra_iff_exists_pow_mul_eq_zero
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    x ∈ RingHom.ker (tensorToAffineBlowupAlgebra S I a).toRingHom ↔
      ∃ n : ℕ, (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x = 0 := by
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    have hχ :
        tensorAffineBlowupSourceToAway S I a x = 0 := by
      -- Route correction: the source-faithful step is now reduced to the ordinary
      -- away-localization comparison map `χ`.
      rw [← tensorToAffineBlowupAlgebra_comp_to_away (S := S) I a x, hx]
      simp
    -- Read vanishing in the ordinary away-localization as annihilation by a power of `a`.
    exact exists_pow_mul_eq_zero_of_tensorAffineBlowupSourceToAway_eq_zero S I a x hχ
  · -- The reverse implication is the easy regularity half of the source argument.
    exact exists_pow_mul_eq_zero_mem_ker_tensorToAffineBlowupAlgebra S I a x

/-- Lemma 10.70.3 (Stacks tag `0BIP`): the canonical base-change map
`S ⊗[R] R[I/a] → S[IS/b]` is surjective, and its kernel consists exactly of the elements
annihilated by some power of the image of `a` in the tensor product. -/
theorem affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let A := S ⊗[R] R[I / a]
    let φ := tensorToAffineBlowupAlgebra S I a
    let aS : A := algebraMap R A a.1
    Function.Surjective φ ∧
      ∀ x : A, x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, aS ^ n * x = 0 := by
  let A := S ⊗[R] R[I / a]
  let φ := tensorToAffineBlowupAlgebra S I a
  let aS : A := algebraMap R A a.1
  change Function.Surjective φ ∧
    ∀ x : A, x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, aS ^ n * x = 0
  refine ⟨?_, ?_⟩
  · -- Normalize a target element to `y / b^n`, then lift the numerator `y ∈ J ^ n` through the
    -- tensor presentation of `J ^ n`.
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    intro z
    obtain ⟨n, s, hs, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesAlgebraGrade J)
      (reesAlgebraDegreeOne_mem J b) z
    have hs' : s ∈ reesAlgebraGrade J n := by
      simpa [nsmul_eq_mul] using hs
    change s ∈ LinearMap.range _ at hs'
    rcases hs' with ⟨x, rfl⟩
    -- Normalize the target fraction to a monomial numerator, then lift that numerator through
    -- the tensor presentation of `J ^ n`.
    simpa [φ, J, b, affineBlowupChartPowerFraction] using
      affineBlowupChart_target_powerFraction_surjective (S := S) I a n x
  · intro x
    exact mem_ker_tensorToAffineBlowupAlgebra_iff_exists_pow_mul_eq_zero S I a x

/-- Canonical reformulation of Lemma 10.70.3: the kernel of the base-change map is the primary
component of the principal ideal generated by the distinguished tensor image of `a`. -/
theorem affineBlowupChart_baseChange_surjective_and_ker_eq_primaryComponent
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let A := S ⊗[R] R[I / a]
    let φ := tensorToAffineBlowupAlgebra S I a
    let aS : A := algebraMap R A a.1
    Function.Surjective φ ∧
      RingHom.ker φ.toRingHom = (Ideal.span ({aS} : Set A)).primaryComponent A := by
  let A := S ⊗[R] R[I / a]
  let φ := tensorToAffineBlowupAlgebra S I a
  let aT : A := (algebraMap R S a.1) ⊗ₜ[R] (1 : R[I / a])
  have hbase := affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion S I a
  have h :
      Function.Surjective φ ∧
        RingHom.ker φ.toRingHom = (Ideal.span ({aT} : Set A)).primaryComponent A := by
    have haTpow (n : ℕ) : aT ^ n = ((algebraMap R S a.1) ^ n) ⊗ₜ[R] (1 : R[I / a]) := by
      induction n with
      | zero =>
          rw [pow_zero, Algebra.TensorProduct.one_def]
          simp
      | succ n ih =>
          rw [pow_succ, ih, show aT = (algebraMap R S a.1) ⊗ₜ[R] (1 : R[I / a]) by rfl,
            Algebra.TensorProduct.tmul_mul_tmul]
          simp [pow_succ]
    refine ⟨hbase.1, ?_⟩
    ext x
    rw [Ideal.primaryComponent_mem]
    constructor
    · intro hx
      rcases (hbase.2 x).mp hx with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hx' : x ∈ Submodule.torsionBy A A (aT ^ n) := by
        simpa [Submodule.mem_torsionBy_iff, smul_eq_mul, haTpow n] using hn
      simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx'
    · rintro ⟨n, hx⟩
      have hx' : x ∈ Submodule.torsionBy A A (aT ^ n) := by
        simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx
      refine (hbase.2 x).mpr ⟨n, ?_⟩
      simpa [Submodule.mem_torsionBy_iff, smul_eq_mul, haTpow n] using hx'
  simpa [aT, Algebra.TensorProduct.algebraMap_apply] using h

end

/-! ### Example_10_70_4 (from Chap10) -/
universe u

open MvPolynomial

section

variable (R : Type u) [CommRing R]
variable (n : ℕ)

local notation "P" => MvPolynomial (Fin n) R
local notation "S" => MvPolynomial (Fin n) P

local notation "Icoord" => idealOfVars (Fin n) R

/-- The relation `t_i T_j - t_j T_i` in `P[T_1, ..., T_n]`. -/
noncomputable def polynomialBlowupPresentationRelation (i j : Fin n) : S :=
  MvPolynomial.C (X i : P) * X j - MvPolynomial.C (X j : P) * X i

/-- The ideal generated by the relations `t_i T_j - t_j T_i`. -/
noncomputable def polynomialBlowupRelationIdeal : Ideal S :=
  Ideal.span (Set.range fun ij : Fin n × Fin n ↦
    polynomialBlowupPresentationRelation R n ij.1 ij.2)

local notation "J" => polynomialBlowupRelationIdeal R n

local notation "Q" => S ⧸ J

/-- The canonical `P`-algebra map sending `T_i` to the degree-one Rees generator `t_i^(1)`. -/
private noncomputable def presentationToRees : S →ₐ[P] reesAlgebra Icoord :=
  aeval fun i ↦ reesAlgebraDegreeOne Icoord
    ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩

/-- Each defining relation of the presentation maps to zero in the Rees algebra. -/
-- Proof sketch: evaluating sends both terms to the same degree-two monomial in `reesAlgebra Icoord`,
-- namely the monomial with coefficient `X i * X j`.
private theorem relation_toRees_eq_zero (i j : Fin n) :
    presentationToRees R n (polynomialBlowupPresentationRelation R n i j) = 0 := sorry

/-- Every element of the relation ideal maps to zero under the canonical map to the Rees algebra. -/
-- Proof sketch: the relation ideal is spanned by the generators `t_i T_j - t_j T_i`, and the
-- previous theorem kills each generator, so the whole span maps to zero.
private theorem relations_toRees_eq_zero (f : S) (hf : f ∈ J) :
    presentationToRees R n f = 0 := sorry

/-- The quotient map from the presentation ring to the blowup algebra. -/
private noncomputable def presentationMap : Q →ₐ[P] reesAlgebra Icoord :=
  Ideal.Quotient.liftₐ J (presentationToRees R n) (relations_toRees_eq_zero R n)

/-- The canonical presentation map from the quotient ring to the Rees algebra is bijective. -/
-- Proof sketch: surjectivity follows from `adjoin_monomial_eq_reesAlgebra`, since the target is
-- generated by the degree-one classes `t_i^(1)`. Injectivity is exactly the monomial-relations
-- argument for the graded pieces `Icoord ^ e` described in the example.
private theorem presentationMap_bijective : Function.Bijective (presentationMap R n) :=
  sorry

/-- Example 10.70.4: for `P = R[t_1, ..., t_n]` and `I = (t_1, ..., t_n)`, the canonical
`P`-algebra map
`P[T_1, ..., T_n] / (t_i T_j - t_j T_i) \to \mathrm{Bl}_I(P) = reesAlgebra I`
sending `T_i` to the degree-one Rees generator `t_i^(1)` is an isomorphism. -/
noncomputable def polynomialBlowupPresentation :
    (S ⧸ polynomialBlowupRelationIdeal R n) ≃ₐ[P] reesAlgebra Icoord :=
  AlgEquiv.ofBijective (presentationMap R n) (presentationMap_bijective R n)

/-- The presentation isomorphism sends the class of `T_i` to the generator `t_i^(1)`. -/
-- Proof sketch: `polynomialBlowupPresentation` is induced from `MvPolynomial.aeval`, so on the
-- quotient class of the variable `T_i` it agrees with the chosen image used to define the map.
theorem polynomialBlowupPresentation_apply_variable (i : Fin n) :
    polynomialBlowupPresentation R n
        (Ideal.Quotient.mk (polynomialBlowupRelationIdeal R n) (X i : S)) =
      reesAlgebraDegreeOne Icoord ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩ := sorry

end

/-! ### Example_10_70_5 (from Chap10) -/
universe u

open MvPolynomial

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
  sorry

/-- Every element of the relation ideal maps to zero in the affine blowup chart. -/
private theorem polynomialAffineBlowupChartRelationIdeal_map_eq_zero
    (f : S) (hf : f ∈ polynomialAffineBlowupChartRelationIdeal n) :
    polynomialAffineBlowupChartToAffineBlowup n f = (0 : Chart) := sorry

/-- The quotient presentation map from `P[x_2, \ldots, x_n]/(t_1 x_j - t_j)` to `P[I/t_1]`. -/
private noncomputable def polynomialAffineBlowupChartMap :
    Q →ₐ[P] Chart :=
  Ideal.Quotient.liftₐ (polynomialAffineBlowupChartRelationIdeal n)
    (polynomialAffineBlowupChartToAffineBlowup n)
    (polynomialAffineBlowupChartRelationIdeal_map_eq_zero n)

local notation "chartMap" => @polynomialAffineBlowupChartMap R _ n _

/-- The canonical presentation map to the affine blowup chart is bijective. -/
private theorem polynomialAffineBlowupChartMap_bijective :
    Function.Bijective chartMap := sorry

local notation "chartMapBijective" => @polynomialAffineBlowupChartMap_bijective R _ n _

/-- Example 10.70.5: for `P = R[t_1, \ldots, t_n]`, `I = (t_1, \ldots, t_n)`, and `a = t_1`, the
quotient `P[x_2, \ldots, x_n] / (t_1 x_2 - t_2, \ldots, t_1 x_n - t_n)` is canonically
isomorphic to the affine blowup chart `P[I/t_1]`. -/
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
  sorry

end
