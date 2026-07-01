import stacks_project.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

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
