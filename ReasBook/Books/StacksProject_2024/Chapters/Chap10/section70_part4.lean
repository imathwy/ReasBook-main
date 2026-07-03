import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_70_11 (from Chap10) -/
universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.70.11: if `a ∈ I` and `a` is contained in no minimal prime of `R`, then the induced
map `Spec(R[I/a]) → Spec(R)` has dense image. -/
-- Proof sketch: the owner abstraction for density is `DenseRange (comap f)`, equivalently the
-- condition that every minimal prime lies in the image. If `a ∉ p` for a minimal prime `p`, then
-- `p` lies in the image of `Spec(R_a) → Spec(R)` because that image is the basic open `D(a)`.
-- Composing with the canonical comparison map `R[I/a] → R_a` lifts this image point to
-- `Spec(R[I/a])`, so every minimal prime of `R` lies in the image of `Spec(R[I/a]) → Spec(R)`.
theorem denseRange_comap_affineBlowupChart_of_not_mem_minimalPrimes
    (I : Ideal R) (a : I) (hmin : ∀ p ∈ minimalPrimes R, (a : R) ∉ p) :
    DenseRange (comap (algebraMap R (affineBlowupChart I a))) := by
  rw [denseRange_comap_iff_minimalPrimes]
  intro p hp
  let p' : PrimeSpectrum R := ⟨p, Ideal.minimalPrimes_isPrime hp⟩
  have hp_range : p' ∈ Set.range (comap (algebraMap R (Localization.Away (a : R)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (a : R)) (a : R)]
    exact (PrimeSpectrum.mem_basicOpen (a : R) p').2 (hmin p hp)
  rcases hp_range with ⟨q, hq⟩
  refine ⟨PrimeSpectrum.comap (affineBlowupChartToLocalizationAway I a) q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply,
    affineBlowupChartToLocalizationAway_comp_algebraMap]
  exact hq

end

/-! ### Lemma_10_70_12 (from Chap10) -/
universe u v

open IsLocalRing Localization
open HomogeneousLocalization

/-
Domain-style sampling pass for Lemma 10.70.12.

Primary domain: affine blowup charts inside valuation subrings of a fraction field.

Sampled owner declarations:
* `affineBlowupChart` and `affineBlowupChartToLocalizationAway` from
  `Definition_10_70_1.lean`;
* `affineBlowupChart_isLocalizationAway` from `Lemma_10_70_2.lean`;
* `LocalSubring.range` / `ValuationSubring.toLocalSubring` from
  `Definition_10_50_1.lean`.

Owner abstraction: the source-facing object is the chart `affineBlowupChart I a`; its canonical
map into the fraction field is the owner declaration `algebraMap (affineBlowupChart I a) K`,
obtained from the existing localization and domain owners. The induced subring of `K` is derived
owner data, so this file uses `RingHom.range` directly instead of keeping a parallel wrapper map.

Layering:
* source-facing: `IsAffineBlowupApproximation` and the directed union theorem;
* core/canonical: `ValuationSubring K`, `LocalSubring.range`, `algebraMap`, and `RingHom.range`;
* bridge/view: `affineBlowupChartToLocalizationAway`.
-/

section

variable {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable instance instAlgebraAffineBlowupChartFractionField
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    Algebra (affineBlowupChart I a) K :=
  RingHom.toAlgebra <|
    (Localization.mapToFractionRing K (Submonoid.powers (a : R))
      (Localization.Away (a : R)) (powers_le_nonZeroDivisors_of_noZeroDivisors a.2)).toRingHom.comp
      (affineBlowupChartToLocalizationAway I a)

/-- Helper for Lemma 10.70.12: the distinguished generator belongs to its own powers submonoid. -/
private theorem self_mem_powers (r : R) : r ∈ Submonoid.powers r :=
  by
    refine ⟨1, ?_⟩
    simp

/-- Helper for Lemma 10.70.12: the element `r` packaged as an element of `Submonoid.powers r`. -/
private def selfPower (r : R) : Submonoid.powers r :=
  ⟨r, self_mem_powers r⟩

/-- Helper for Lemma 10.70.12: the comparison map sends the basic chart fraction `x / a` to the
ordinary localization fraction `x / a`. -/
private theorem affineBlowupChartToLocalizationAway_basicFraction
    (I : Ideal R) (a x : I) :
    affineBlowupChartToLocalizationAway I a (affineBlowupChartBasicFraction I a x) =
      Localization.mk x.1 (selfPower a.1) := by
  let g : reesAlgebra I →+* Localization.Away a.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
      (reesAlgebra I).toSubring.subtype
  have hfrac (r : R) :
      algebraMap R (Localization.Away a.1) r * Localization.mk 1 (selfPower a.1) =
        Localization.mk r (selfPower a.1) := by
    -- Rewrite the right-hand fraction into the standard `mk'` form, then use the localization
    -- formula for multiplying by `1 / a`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact (Localization.mk_eq_mk'_apply r (selfPower a.1)).symm
  -- Evaluate the homogeneous-localization fraction by the universal property of `R_a`.
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  simp [affineBlowupChartBasicFraction]
  have ha_unit :
      g (reesAlgebraDegreeOne I a) * Localization.mk 1 (selfPower a.1) = 1 := by
    -- The image of `a^(1)` is the ordinary element `a`, whose chosen inverse is `1 / a`.
    rw [show g (reesAlgebraDegreeOne I a) = algebraMap R (Localization.Away a.1) a.1 by
      simp [g, reesAlgebraDegreeOne]]
    rw [hfrac]
    exact Localization.mk_self (selfPower a.1)
  have h :=
      Localization.awayLift_mk g (reesAlgebraDegreeOne I a) (reesAlgebraDegreeOne I x)
        (Localization.mk 1 (selfPower a.1))
        ha_unit
        1
  simpa [g, reesAlgebraDegreeOne, pow_one, hfrac] using h

/-- The basic fraction `x / a` with `x ∈ I` lies in the canonical image of the affine blowup chart
`R[I/a]` in the ambient fraction field. -/
private theorem algebraMap_affineBlowupChartBasicFraction
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) (x : I) :
    algebraMap (affineBlowupChart I a) K (affineBlowupChartBasicFraction I a x) =
      algebraMap R K (x : R) / algebraMap R K (a : R) := by
  -- Rewrite the chart fraction through the canonical localization-away comparison map.
  change
    Localization.mapToFractionRing K (Submonoid.powers (a : R))
        (Localization.Away (a : R))
        (powers_le_nonZeroDivisors_of_noZeroDivisors a.2)
        (affineBlowupChartToLocalizationAway I a (affineBlowupChartBasicFraction I a x)) =
      algebraMap R K (x : R) / algebraMap R K (a : R)
  rw [affineBlowupChartToLocalizationAway_basicFraction]
  rw [Localization.mapToFractionRing_apply, Localization.mk_eq_mk'_apply, IsLocalization.lift_mk']
  rw [div_eq_mul_inv]
  congr 1
  simpa using congrArg Inv.inv <|
    IsUnit.coe_liftRight
      ((algebraMap R K : R →* K).restrict (Submonoid.powers (a : R)))
      (Localization.map_isUnit_of_le K (Submonoid.powers (a : R))
        (powers_le_nonZeroDivisors_of_noZeroDivisors a.2))
      (selfPower (a : R))

/-- The basic fraction `x / a` with `x ∈ I` lies in the canonical image of the affine blowup chart
`R[I/a]` in the ambient fraction field. -/
theorem mem_affineBlowupChartSubring_basicFraction
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) (x : I) :
    algebraMap R K (x : R) / algebraMap R K (a : R) ∈
      (algebraMap (affineBlowupChart I a) K).range := by
  -- Package the explicit image formula as membership in the image subring.
  refine ⟨affineBlowupChartBasicFraction I a x, ?_⟩
  simpa using (algebraMap_affineBlowupChartBasicFraction (R := R) (K := K) I a x).symm

end

section

variable {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [IsLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Helper for Lemma 10.70.12: if a subring of the fraction field contains the image of `R` and
the displayed basic generator fractions of a tuple-generated chart, then it contains the whole
chart image. -/
private theorem affineBlowupChart_range_le_of_tuple_generators
    {r : ℕ} (f : Fin (r + 1) → R) (hf0 : f 0 ≠ 0) (B : Subring K)
    (hR : (algebraMap R K).range ≤ B)
    (hgen : ∀ i : Fin r, algebraMap R K (f i.succ) / algebraMap R K (f 0) ∈ B) :
    let I : Ideal R := Ideal.span (Set.range f)
    let a : { a : I // (a : R) ≠ 0 } := ⟨tupleSpanFirst f, hf0⟩
    (algebraMap (affineBlowupChart I a) K).range ≤ B := by
  classical
  let ιB : R →+* B := (algebraMap R K).codRestrict B hR
  let coord : Fin r → B := fun i ↦
    ⟨algebraMap R K (f i.succ) / algebraMap R K (f 0), hgen i⟩
  let evalB : MvPolynomial (Fin r) R →+* B := MvPolynomial.eval₂Hom ιB coord
  have hf0K : algebraMap R K (f 0) ≠ 0 := map_ne_zero hf0
  have hrel :
      ∀ i : Fin r, evalB (affineBlowupTuplePresentationRelation f i) = 0 := by
    intro i
    apply Subtype.ext
    -- Each defining relation vanishes because the chosen coordinate is exactly `fᵢ₊₁ / f₀`.
    change
      algebraMap R K (f 0) *
          (algebraMap R K (f i.succ) / algebraMap R K (f 0)) -
        algebraMap R K (f i.succ) = 0
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hf0K, mul_one, sub_self]
  have hker :
      affineBlowupTuplePresentationRelationIdeal f ≤ RingHom.ker evalB := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hrel i
  let evalQ : affineBlowupTuplePresentationQuotient f →+* B :=
    Ideal.Quotient.lift _ evalB fun φ hφ => show evalB φ = 0 from hker hφ
  have hcomp :
      B.subtype.comp evalQ =
        ((algebraMap (affineBlowupChart (Ideal.span (Set.range f)) ⟨tupleSpanFirst f, hf0⟩) K).comp
          (affineBlowupTuplePresentationMap f).toRingHom) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r0
      simp [evalQ, evalB, ιB]
    · intro i
      -- Compare the quotient generator with the corresponding basic fraction in the chart.
      simp [evalQ, evalB, coord, affineBlowupTuplePresentationMap,
        affineBlowupTuplePresentationToBlowup, affineBlowupTuplePresentationGenerator,
        algebraMap_affineBlowupChartBasicFraction]
  intro y hy
  rcases hy with ⟨z, rfl⟩
  obtain ⟨q, rfl⟩ :=
    (affineBlowupTuplePresentationMap_surjective_and_ker_eq_a_power_torsion f).1 z
  refine ⟨evalQ q, ?_⟩
  exact RingHom.congr_fun hcomp q

/-- Helper for Lemma 10.70.12: a generating tuple for an ideal `I` with first entry `a`
immediately yields range containment for the original chart `R[I/a]`. -/
private theorem affineBlowupChart_range_le_of_generating_tuple
    {r : ℕ} {I : Ideal R} {a : { a : I // (a : R) ≠ 0 }}
    (f : Fin (r + 1) → R) (hf0 : f 0 = a.1) (hspan : Ideal.span (Set.range f) = I)
    (B : Subring K) (hR : (algebraMap R K).range ≤ B)
    (hgen : ∀ i : Fin r, algebraMap R K (f i.succ) / algebraMap R K (f 0) ∈ B) :
    (algebraMap (affineBlowupChart I a) K).range ≤ B := by
  classical
  -- Route correction: rewrite once from the original chart to the tuple-generated presentation,
  -- then reuse the established tuple-range lemma instead of transporting by repeated `convert`.
  subst hspan
  have hf0' : f 0 ≠ 0 := by
    simpa [hf0] using a.2
  have haeq : (⟨tupleSpanFirst f, hf0'⟩ : { x : Ideal.span (Set.range f) // (x : R) ≠ 0 }) = a := by
    -- The chosen denominator is exactly the first tuple entry after identifying the spanning ideal.
    apply Subtype.ext
    exact hf0
  -- Apply the tuple-generated chart lemma and then rewrite back to the original denominator `a`.
  simpa [haeq] using
    (affineBlowupChart_range_le_of_tuple_generators (R := R) (K := K) f hf0' B hR hgen)

/-- Helper for Lemma 10.70.12: a finitely generated ideal together with a chosen element admits a
finite tuple of generators whose first entry is that chosen element. -/
private theorem exists_tuple_generating_ideal_with_first
    (I : Ideal R) (hI : I.FG) (a : I) :
    ∃ r : ℕ, ∃ f : Fin (r + 1) → R, f 0 = a.1 ∧ Ideal.span (Set.range f) = I := by
  classical
  let s : Finset R := (Submodule.FG.finite_generators hI).toFinset
  have hs_generators : (s : Set R) = I.generators := by
    exact (Submodule.FG.finite_generators hI).coe_toFinset
  let tail : Fin s.card → R := fun i ↦ ((Finset.equivFin s i : s) : R)
  let f : Fin (s.card + 1) → R := Fin.cons a.1 tail
  refine ⟨s.card, f, rfl, ?_⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    rcases hx with ⟨i, rfl⟩
    refine Fin.cases ?_ ?_ i
    · exact a.2
    · intro j
      have hj : tail j ∈ I.generators := by
        have : tail j ∈ (s : Set R) := by
          exact (Finset.equivFin s j).2
        rwa [hs_generators] at this
      exact Submodule.FG.generators_mem (p := I) hj
  · rw [← I.span_generators]
    apply Ideal.span_le
    intro x hx
    have hx' : x ∈ (s : Set R) := by
      rwa [hs_generators] at hx
    refine Ideal.subset_span ?_
    refine ⟨((Finset.equivFin s).symm ⟨x, hx'⟩).succ, ?_⟩
    simp [f, tail]

/-- Helper for Lemma 10.70.12: the product ideal `I * J` admits a finite tuple of generators
whose first entry is the distinguished product `a * b`. -/
private theorem exists_tuple_generating_mul_ideal_with_first_mul
    {I J : Ideal R} (hI : I.FG) (hJ : J.FG) (a : I) (b : J) :
    ∃ r : ℕ, ∃ f : Fin (r + 1) → R, f 0 = a.1 * b.1 ∧ Ideal.span (Set.range f) = I * J := by
  -- The source route uses the actual product ideal `I * J`, so first package its finite generation.
  have hIJ : (I * J).FG := hI.mul hJ
  let ab : I * J := ⟨a.1 * b.1, Ideal.mul_mem_mul a.2 b.2⟩
  -- Then reuse the general finite-generator tuple construction with the chosen first entry.
  exact exists_tuple_generating_ideal_with_first (R := R) (I * J) hIJ ab

/-- Helper for Lemma 10.70.12: scaling numerator and denominator by the same nonzero element does
not change the represented fraction in the fraction field. -/
private theorem generator_fraction_eq_scaled_basicFraction
    (x a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    algebraMap R K x / algebraMap R K a =
      algebraMap R K (b * x) / algebraMap R K (b * a) := by
  have haK : algebraMap R K a ≠ 0 := map_ne_zero ha
  have hbaK : algebraMap R K (b * a) ≠ 0 := by
    simpa [map_mul] using mul_ne_zero (map_ne_zero hb) haK
  apply (div_eq_div_iff haK hbaK).2
  rw [map_mul, map_mul, map_mul, map_mul]
  ring

/-- Helper for Lemma 10.70.12: once a subring contains the basic pairwise product fractions
coming from two generating tuples, span induction upgrades this to every denominator-`fI 0 * fJ 0`
fraction with numerator in the span of those pairwise products. -/
private theorem fraction_mem_of_mem_span_pairwise_products
    {rI rJ : ℕ} (fI : Fin (rI + 1) → R) (fJ : Fin (rJ + 1) → R)
    (hfI0 : fI 0 ≠ 0) (hfJ0 : fJ 0 ≠ 0)
    (B : Subring K) (hR : (algebraMap R K).range ≤ B)
    (hpair :
      ∀ i : Fin (rI + 1), ∀ j : Fin (rJ + 1),
        algebraMap R K (fI i * fJ j) / algebraMap R K (fI 0 * fJ 0) ∈ B)
    {x : R} (hx : x ∈ Ideal.span (Set.range fI * Set.range fJ)) :
    algebraMap R K x / algebraMap R K (fI 0 * fJ 0) ∈ B := by
  have hdenK : algebraMap R K (fI 0 * fJ 0) ≠ 0 := by
    simpa [map_mul] using mul_ne_zero (map_ne_zero hfI0) (map_ne_zero hfJ0)
  -- Induct over the `R`-linear span of pairwise products, matching the source proof's
  -- linear-combination argument inside the ambient field.
  refine Submodule.span_induction (p := fun y _ ↦
      algebraMap R K y / algebraMap R K (fI 0 * fJ 0) ∈ B) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨u, hu, v, hv, rfl⟩
    rcases hu with ⟨i, rfl⟩
    rcases hv with ⟨j, rfl⟩
    exact hpair i j
  · -- The zero numerator gives the zero fraction.
    simpa using B.zero_mem
  · intro y z hy hz hy_mem hz_mem
    -- Equal denominators let us add fractions termwise.
    simpa [map_add, add_div] using B.add_mem hy_mem hz_mem
  · intro r y hy hy_mem
    have hr : algebraMap R K r ∈ B := hR ⟨r, rfl⟩
    -- Scalar multiplication on the ideal side becomes multiplication by an image of `R`.
    simpa [smul_eq_mul, map_mul, mul_div_assoc] using B.mul_mem hr hy_mem

/-- Helper for Lemma 10.70.12: the dominating map `R → A` obtained by codomain-restricting the
ambient fraction-field map. -/
private noncomputable def algebraMapToValuationSubring
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) :
    R →+* A :=
  (algebraMap R K).codRestrict A.toSubring
    (fun r => hA.1 (show algebraMap R K r ∈ (LocalSubring.range (algebraMap R K)).toSubring
      from ⟨r, rfl⟩))

/-- Helper for Lemma 10.70.12: the codomain-restricted map `R → A` is local because `A`
dominates the image of `R` in the fraction field. -/
private theorem isLocalHom_algebraMapToValuationSubring
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) :
    IsLocalHom (algebraMapToValuationSubring (R := R) (K := K) A hA) := by
  have hcomp :
      IsLocalHom
        ((Subring.inclusion hA.1).comp ((algebraMap R K).rangeRestrict)) := by
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _
      hA.2 (.of_surjective _ (algebraMap R K).rangeRestrict_surjective)
  simpa [algebraMapToValuationSubring] using hcomp

/-- Helper for Lemma 10.70.12: once the canonical image of the chart lies in the dominating
valuation subring, the closed fiber over `maximalIdeal R` is nontrivial. -/
theorem affineBlowupChartFiber_nontrivial_of_range_le_valuation
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    {I : Ideal R} {a : { a : I // (a : R) ≠ 0 }}
    (hC : (algebraMap (affineBlowupChart I a) K).range ≤ A.toSubring) :
    Nontrivial ((maximalIdeal R).Fiber (affineBlowupChart I a)) := by
  let f : R →+* A := algebraMapToValuationSubring (R := R) (K := K) A hA
  let g : affineBlowupChart I a →+* A :=
    (algebraMap (affineBlowupChart I a) K).codRestrict A.toSubring
      (fun z => hC
        (show algebraMap (affineBlowupChart I a) K z ∈
            (algebraMap (affineBlowupChart I a) K).range from ⟨z, rfl⟩))
  have hf : IsLocalHom f := isLocalHom_algebraMapToValuationSubring (R := R) (K := K) A hA
  have hcomp :
      g.comp (algebraMap R (affineBlowupChart I a)) = f := by
    ext r
    change
      Localization.mapToFractionRing K (Submonoid.powers (a : R))
          (Localization.Away (a : R))
          (powers_le_nonZeroDivisors_of_noZeroDivisors a.2)
          (affineBlowupChartToLocalizationAway I a ((algebraMap R (affineBlowupChart I a)) r)) =
        algebraMap R K r
    rw [affineBlowupChartToLocalizationAway_algebraMap, Localization.mapToFractionRing_apply]
    simp
  let pA : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  let pR : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
  have hmem :
      pR ∈ Set.range (PrimeSpectrum.comap (algebraMap R (affineBlowupChart I a))) := by
    refine ⟨PrimeSpectrum.comap g pA, ?_⟩
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hcomp]
    -- Use the local-hom computation directly, avoiding a transient local instance declaration.
    exact @IsLocalRing.maximalIdeal_comap _ _ _ _ f hf
  -- Convert the closed-point image criterion into nontriviality of the fiber ring.
  simpa using
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap
      (S := affineBlowupChart I a) pR).2 hmem

/-- An affine blowup chart `R[I/a]` approximates `A` if its center lies in the maximal ideal, the
center ideal is finitely generated, the fiber over the maximal ideal is nontrivial, and the
canonical image of the chart in the fraction field is contained in `A`. -/
def IsAffineBlowupApproximation
    (A : ValuationSubring K) (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) : Prop :=
  I ≤ maximalIdeal R ∧
    I.FG ∧
    Nontrivial ((maximalIdeal R).Fiber (affineBlowupChart I a)) ∧
    (algebraMap (affineBlowupChart I a) K).range ≤ A.toSubring

/-- Helper for Lemma 10.70.12: the product-stage ideal used for the common upper bound of two
affine blowup approximations. -/
private abbrev productApproximationIdeal (I J : Ideal R) : Ideal R :=
  I * J

/-- Helper for Lemma 10.70.12: the distinguished product denominator `ab` in the product ideal
`IJ`. -/
private def productApproximationDenominator
    {I J : Ideal R} (a : { a : I // (a : R) ≠ 0 }) (b : { b : J // (b : R) ≠ 0 }) :
    { c : productApproximationIdeal I J // (c : R) ≠ 0 } :=
  ⟨⟨a.1 * b.1, Ideal.mul_mem_mul a.1.property b.1.property⟩, mul_ne_zero a.2 b.2⟩

/-- Helper for Lemma 10.70.12: if `R[I/a]` and `R[J/b]` both approximate the dominating
valuation ring `A`, then the product chart `R[IJ/ab]` is still contained in `A`. -/
private theorem product_chart_range_le_of_approximations
    (A : ValuationSubring K) {I J : Ideal R}
    {a : { a : I // (a : R) ≠ 0 }} {b : { b : J // (b : R) ≠ 0 }}
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    (hI : IsAffineBlowupApproximation A I a) (hJ : IsAffineBlowupApproximation A J b) :
    let L : Ideal R := productApproximationIdeal I J
    let c : { c : L // (c : R) ≠ 0 } := productApproximationDenominator a b
    (algebraMap (affineBlowupChart L c) K).range ≤ A.toSubring := by
  classical
  let L : Ideal R := productApproximationIdeal I J
  let c : { c : L // (c : R) ≠ 0 } := productApproximationDenominator a b
  obtain ⟨rI, fI, hfI0, hspanI⟩ := exists_tuple_generating_ideal_with_first (R := R) I hI.2.1 a
  obtain ⟨rJ, fJ, hfJ0, hspanJ⟩ := exists_tuple_generating_ideal_with_first (R := R) J hJ.2.1 b
  obtain ⟨rL, fL, hfL0, hspanL⟩ :=
    exists_tuple_generating_mul_ideal_with_first_mul (R := R) (I := I) (J := J)
      hI.2.1 hJ.2.1 a b
  have hprod_span : L = Ideal.span (Set.range fI * Set.range fJ) := by
    -- Route correction: keep the source product ideal `I * J` visible as the span of pairwise
    -- products of chosen generators before transporting to an arbitrary tuple of `L`.
    dsimp [L]
    rw [← hspanI, ← hspanJ, Ideal.span_mul_span]
  have hpair :
      ∀ i : Fin (rI + 1), ∀ j : Fin (rJ + 1),
        algebraMap R K (fI i * fJ j) / algebraMap R K (fI 0 * fJ 0) ∈ A.toSubring := by
    intro i j
    have hfi_mem : fI i ∈ I := by
      rw [← hspanI]
      exact Ideal.subset_span ⟨i, rfl⟩
    have hfj_mem : fJ j ∈ J := by
      rw [← hspanJ]
      exact Ideal.subset_span ⟨j, rfl⟩
    let xi : I := ⟨fI i, hfi_mem⟩
    let xj : J := ⟨fJ j, hfj_mem⟩
    have hxi :
        algebraMap R K (fI i) / algebraMap R K (fI 0) ∈ A.toSubring := by
      simpa [hfI0] using
        hI.2.2.2 (mem_affineBlowupChartSubring_basicFraction (R := R) (K := K) I a xi)
    have hxj :
        algebraMap R K (fJ j) / algebraMap R K (fJ 0) ∈ A.toSubring := by
      simpa [hfJ0] using
        hJ.2.2.2 (mem_affineBlowupChartSubring_basicFraction (R := R) (K := K) J b xj)
    -- Pairwise generators of `IJ` map to products of the corresponding `I/a` and `J/b`
    -- fractions, exactly as in the source proof.
    simpa [map_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hfI0, hfJ0] using
      A.toSubring.mul_mem hxi hxj
  have hgenL :
      ∀ i : Fin rL, algebraMap R K (fL i.succ) / algebraMap R K (fL 0) ∈ A.toSubring := by
    intro i
    have hmemL : fL i.succ ∈ L := by
      rw [← hspanL]
      exact Ideal.subset_span ⟨i.succ, rfl⟩
    have hmemSpan : fL i.succ ∈ Ideal.span (Set.range fI * Set.range fJ) := by
      simpa [hprod_span] using hmemL
    -- First place the chosen `L`-generator in the span of pairwise products, then invoke the
    -- span-closure lemma to recover its denominator-`ab` fraction in `A`.
    simpa [hfL0, hfI0, hfJ0, mul_comm, mul_left_comm, mul_assoc] using
      (fraction_mem_of_mem_span_pairwise_products (R := R) (K := K)
        fI fJ hfI0 hfJ0 A.toSubring hA.1 hpair hmemSpan)
  -- The arbitrary generating tuple of `L` now closes because each of its generator fractions is
  -- already known to lie in `A`.
  simpa [L, c] using
    (affineBlowupChart_range_le_of_generating_tuple (R := R) (K := K)
      (I := L) (a := c) fL hfL0 hspanL A.toSubring hA.1 hgenL)

/-- Helper for Lemma 10.70.12: the two source inclusions
`R[I/a] ≤ R[IJ/ab]` and `R[J/b] ≤ R[IJ/ab]` are obtained by scaling generators by the other
denominator, exactly as in the source proof. -/
private theorem factor_chart_range_le_product_chart
    {I J : Ideal R}
    {a : { a : I // (a : R) ≠ 0 }} {b : { b : J // (b : R) ≠ 0 }}
    (hI : I.FG) (hJ : J.FG) :
    let L : Ideal R := productApproximationIdeal I J
    let c : { c : L // (c : R) ≠ 0 } := productApproximationDenominator a b
    let C : Subring K := (algebraMap (affineBlowupChart L c) K).range
    (algebraMap (affineBlowupChart I a) K).range ≤ C ∧
      (algebraMap (affineBlowupChart J b) K).range ≤ C := by
  classical
  let L : Ideal R := productApproximationIdeal I J
  let c : { c : L // (c : R) ≠ 0 } := productApproximationDenominator a b
  let C : Subring K := (algebraMap (affineBlowupChart L c) K).range
  have hR : (algebraMap R K).range ≤ C := by
    intro z hz
    rcases hz with ⟨r, rfl⟩
    refine ⟨algebraMap R (affineBlowupChart L c) r, ?_⟩
    simp [C]
  obtain ⟨rI, fI, hfI0, hspanI⟩ := exists_tuple_generating_ideal_with_first (R := R) I hI a
  obtain ⟨rJ, fJ, hfJ0, hspanJ⟩ := exists_tuple_generating_ideal_with_first (R := R) J hJ b
  have hgenI :
      ∀ i : Fin rI, algebraMap R K (fI i.succ) / algebraMap R K (fI 0) ∈ C := by
    intro i
    have hfi : fI i.succ ∈ I := by
      rw [← hspanI]
      exact Ideal.subset_span ⟨i.succ, rfl⟩
    have hfI0_ne : fI 0 ≠ 0 := by
      simpa [hfI0] using a.2
    have hxi_mem : fI i.succ * b.1 ∈ L := by
      simpa [L, mul_comm] using Ideal.mul_mem_mul hfi b.1.property
    let xi : L := ⟨fI i.succ * b.1, hxi_mem⟩
    have hscaled :
        algebraMap R K (fI i.succ) / algebraMap R K (fI 0) =
          algebraMap R K (b.1 * fI i.succ) / algebraMap R K (b.1 * fI 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (generator_fraction_eq_scaled_basicFraction (R := R) (K := K)
          (fI i.succ) (fI 0) b.1 hfI0_ne b.2)
    -- The scaled numerator is a generator of the product chart, so its fraction lies in the range.
    rw [hscaled]
    simpa [C, c, hfI0, mul_comm, mul_left_comm, mul_assoc] using
      (mem_affineBlowupChartSubring_basicFraction (R := R) (K := K) L c xi)
  have hgenJ :
      ∀ i : Fin rJ, algebraMap R K (fJ i.succ) / algebraMap R K (fJ 0) ∈ C := by
    intro i
    have hfj : fJ i.succ ∈ J := by
      rw [← hspanJ]
      exact Ideal.subset_span ⟨i.succ, rfl⟩
    have hfJ0_ne : fJ 0 ≠ 0 := by
      simpa [hfJ0] using b.2
    have hxj_mem : a.1 * fJ i.succ ∈ L := by
      simpa [L, mul_left_comm, mul_comm] using Ideal.mul_mem_mul a.1.property hfj
    let xj : L := ⟨a.1 * fJ i.succ, hxj_mem⟩
    have hscaled :
        algebraMap R K (fJ i.succ) / algebraMap R K (fJ 0) =
          algebraMap R K (a.1 * fJ i.succ) / algebraMap R K (a.1 * fJ 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (generator_fraction_eq_scaled_basicFraction (R := R) (K := K)
          (fJ i.succ) (fJ 0) a.1 hfJ0_ne a.2)
    -- The same scaling argument gives the symmetric inclusion for `R[J/b]`.
    rw [hscaled]
    simpa [C, c, hfJ0, mul_comm, mul_left_comm, mul_assoc] using
      (mem_affineBlowupChartSubring_basicFraction (R := R) (K := K) L c xj)
  refine ⟨?_, ?_⟩
  · -- Repackage the generator-level containments into the whole-chart inclusion for `R[I/a]`.
    exact affineBlowupChart_range_le_of_generating_tuple
      (R := R) (K := K) fI hfI0 hspanI C hR hgenI
  · -- Repackage the symmetric generator-level containments into the whole-chart inclusion for `R[J/b]`.
    exact affineBlowupChart_range_le_of_generating_tuple
      (R := R) (K := K) fJ hfJ0 hspanJ C hR hgenJ

/-- The affine blowup charts `R[I/a]` contained in a valuation subring form a directed family
under inclusion of their canonical images in the fraction field. -/
-- Proof sketch: if `R[I/a]` and `R[J/b]` lie in `A`, then both are contained in the product stage
-- `R[IJ/ab]`, which still has center inside `maximalIdeal R`, remains finitely generated, and
-- still has nontrivial fiber over `maximalIdeal R`. Hence any two stages admit a common upper
-- bound in the same family.
theorem affineBlowupApproximations_directed
    (A : ValuationSubring K) {I J : Ideal R}
    {a : { a : I // (a : R) ≠ 0 }} {b : { b : J // (b : R) ≠ 0 }}
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    (hI : IsAffineBlowupApproximation A I a) (hJ : IsAffineBlowupApproximation A J b) :
    ∃ (L : Ideal R) (c : { c : L // (c : R) ≠ 0 }),
      let C : Subring K := (algebraMap (affineBlowupChart L c) K).range
      IsAffineBlowupApproximation A L c ∧
        (algebraMap (affineBlowupChart I a) K).range ≤ C ∧
        (algebraMap (affineBlowupChart J b) K).range ≤ C := by
  -- Route correction: the tuple-transport part is now isolated in
  -- `affineBlowupChart_range_le_of_generating_tuple`, so the remaining source-style work is the
  -- actual product stage `R[IJ/ab]`.
  let L : Ideal R := productApproximationIdeal I J
  let c : { c : L // (c : R) ≠ 0 } := productApproximationDenominator a b
  let C : Subring K := (algebraMap (affineBlowupChart L c) K).range
  have hfactor :
      (algebraMap (affineBlowupChart I a) K).range ≤ C ∧
        (algebraMap (affineBlowupChart J b) K).range ≤ C := by
    -- The easy source inclusions are already reduced to scaling basic fractions by the other denominator.
    simpa [L, c, C] using
      (factor_chart_range_le_product_chart (R := R) (K := K) (I := I) (J := J)
        (a := a) (b := b) hI.2.1 hJ.2.1)
  have hL_le_m :
      L ≤ maximalIdeal R := by
    -- The product center stays inside the maximal ideal because `I * J ≤ I ≤ maximalIdeal R`.
    intro x hx
    exact hI.1 (Ideal.mul_le_right hx)
  have hL_fg : L.FG := hI.2.1.mul hJ.2.1
  have hproduct_range :
      C ≤ A.toSubring := by
    -- The remaining source step is now isolated as the product-chart containment theorem.
    simpa [L, c, C] using
      (product_chart_range_le_of_approximations (R := R) (K := K) A hA hI hJ)
  have hfiber :
      Nontrivial ((maximalIdeal R).Fiber (affineBlowupChart L c)) := by
    -- The product chart inherits nontrivial fiber from the ambient domination hypothesis.
    exact affineBlowupChartFiber_nontrivial_of_range_le_valuation
      (R := R) (K := K) A hA hproduct_range
  refine ⟨L, c, ?_⟩
  dsimp [C]
  exact ⟨⟨hL_le_m, ⟨hL_fg, ⟨hfiber, hproduct_range⟩⟩⟩, ⟨hfactor.1, hfactor.2⟩⟩

/-- Helper for Lemma 10.70.12: every element of the dominating valuation subring lies in one
two-generator affine blowup chart with center inside the maximal ideal. -/
private theorem element_mem_some_affineBlowupApproximation
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    (hm : maximalIdeal R ≠ ⊥)
    {x : K} (hx : x ∈ A.toSubring) :
    ∃ (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }),
      IsAffineBlowupApproximation A I a ∧
        x ∈ (algebraMap (affineBlowupChart I a) K).range := by
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective R x
  obtain ⟨m0, hm0_mem, hm0_ne⟩ := (maximalIdeal R).ne_bot_iff.mp hm
  let t : Fin 2 → R := Fin.cons (g * m0) fun _ ↦ f * m0
  let I : Ideal R := Ideal.span (Set.range t)
  have ht0 : t 0 = g * m0 := rfl
  have ht1 : t 1 = f * m0 := by
    simp [t]
  have ht0_ne : t 0 ≠ 0 := by
    rw [ht0]
    exact mul_ne_zero (nonZeroDivisors.ne_zero hg) hm0_ne
  let a : { a : I // (a : R) ≠ 0 } := ⟨tupleSpanFirst t, ht0_ne⟩
  have hI_le_m : I ≤ maximalIdeal R := by
    -- Both chosen generators are multiples of the same maximal-ideal element `m0`.
    rw [I, Ideal.span_le]
    intro y hy
    rcases hy with ⟨i, rfl⟩
    fin_cases i
    · simpa [ht0] using (maximalIdeal R).mul_mem_left g hm0_mem
    · simpa [ht1] using (maximalIdeal R).mul_mem_left f hm0_mem
  have hI_fg : I.FG := by
    -- The center ideal is generated by two explicit elements.
    simpa [I] using (Submodule.fg_span (Set.finite_range t))
  have hgen :
      ∀ i : Fin 1, algebraMap R K (t i.succ) / algebraMap R K (t 0) ∈ A.toSubring := by
    intro i
    fin_cases i
    have hscaled :
        algebraMap R K f / algebraMap R K g =
          algebraMap R K (m0 * f) / algebraMap R K (m0 * g) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (generator_fraction_eq_scaled_basicFraction (R := R) (K := K)
          f g m0 (nonZeroDivisors.ne_zero hg) hm0_ne)
    -- The unique nontrivial generator fraction is exactly the chosen element of `A`.
    simpa [ht0, ht1, hscaled, mul_comm, mul_left_comm, mul_assoc] using hx
  have hchart_le_A :
      (algebraMap (affineBlowupChart I a) K).range ≤ A.toSubring := by
    -- Repackage the two-generator chart through the generating-tuple containment lemma.
    exact affineBlowupChart_range_le_of_generating_tuple
      (R := R) (K := K) (I := I) (a := a) t rfl rfl A.toSubring hA.1 hgen
  have hfiber :
      Nontrivial ((maximalIdeal R).Fiber (affineBlowupChart I a)) := by
    -- The constructed chart still has nontrivial closed fiber because it lies in `A`.
    exact affineBlowupChartFiber_nontrivial_of_range_le_valuation
      (R := R) (K := K) A hA hchart_le_A
  have hx_range :
      algebraMap R K f / algebraMap R K g ∈
        (algebraMap (affineBlowupChart I a) K).range := by
    let xf : I := ⟨t 1, Ideal.subset_span ⟨1, rfl⟩⟩
    have hscaled :
        algebraMap R K f / algebraMap R K g =
          algebraMap R K (m0 * f) / algebraMap R K (m0 * g) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (generator_fraction_eq_scaled_basicFraction (R := R) (K := K)
          f g m0 (nonZeroDivisors.ne_zero hg) hm0_ne)
    -- The represented element is the basic fraction of the second generator over the first.
    rw [hscaled]
    simpa [I, a, t, ht0, ht1, mul_comm, mul_left_comm, mul_assoc] using
      (mem_affineBlowupChartSubring_basicFraction (R := R) (K := K) I a xf)
  exact ⟨I, a, ⟨hI_le_m, ⟨hI_fg, ⟨hfiber, hchart_le_A⟩⟩⟩, hx_range⟩

/-- Lemma 10.70.12: if a valuation subring `A` of the fraction field `K` dominates the local
domain `R`, then `A` is the directed union of the affine blowup charts `R[I/a]` contained in
`A`, where `a ∈ I` is nonzero, `I ⊆ maximalIdeal R` is finitely generated, and the fiber over
`maximalIdeal R` is nontrivial. -/
-- Proof sketch: for a finite subset of `A`, choose a common nonzero denominator `a ∈ R` and let
-- `I` be the finitely generated ideal generated by the corresponding numerators together with `a`.
-- Then that finite subset lies in the chart `R[I/a]` inside `A`. This shows every element of `A`
-- belongs to some such stage, while the previous directedness statement identifies the supremum
-- with the directed colimit.
theorem valuationSubring_eq_iSup_affineBlowupApproximations
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring)
    (hm : maximalIdeal R ≠ ⊥) :
    A.toSubring =
      ⨆ (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }),
        ⨆ (_ : IsAffineBlowupApproximation A I a),
          (algebraMap (affineBlowupChart I a) K).range := by
  apply le_antisymm
  · intro x hx
    rcases
        element_mem_some_affineBlowupApproximation (R := R) (K := K) A hA hm hx with
      ⟨I, a, hIa, hxI⟩
    exact le_iSup_of_le I <| le_iSup_of_le a <| le_iSup_of_le hIa hxI
  · refine iSup_le fun I => iSup_le fun a => iSup_le fun hIa => ?_
    exact hIa.2.2.2

end
