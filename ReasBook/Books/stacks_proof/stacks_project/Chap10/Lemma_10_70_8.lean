import stacks_proof.stacks_project.Chap10.Lemma_10_70_8.Index
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open HomogeneousLocalization
open IsLocalization
open Polynomial
open scoped DirectSum

/-
Domain-style sampling pass for Lemma 10.70.8.

Primary domain: commutative algebra of Rees algebras and affine blowup charts.

Sampled owner declarations:
* `affineBlowupChart`, `reesAlgebraGrade`, and `reesAlgebraDegreeOne` from
  `Definition_10_70_1.lean`;
* `HomogeneousLocalization.Away.map` from mathlib's homogeneous-localization API;
* `Ideal.primaryComponent_mem` from mathlib's primary-component API.

Owner abstraction: `affineBlowupChart I a`, built from the graded owner `reesAlgebraGrade I`.
Primitive data here are the scaled ideal `Ideal.span ({f} : Set R) * I`, the distinguished
element `fa ∈ (f)I`, and the induced graded map on Rees algebras.

Source/core/bridge triage:
* source-facing: the kernel description by `f`-power torsion;
* core/canonical: the same kernel as a primary component;
* bridge/view: the scaled chart map itself.
-/

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.70.8: transporting a raw `Away` ring homomorphism along an equality of
the underlying inverted elements commutes with evaluation. -/
private theorem cast_awayRingHom_apply_base
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {f g : A} {S : Type*} [CommRing S]
    (h : f = g) (φ : S →+* Away 𝒜 f) (x : S) :
    cast (congrArg (fun y : A ↦ S →+* Away 𝒜 y) h) φ x =
      cast (congrArg (fun y : A ↦ Away 𝒜 y) h) (φ x) := by
  -- The assertion is just transport functoriality once the parameter equality is reduced.
  cases h
  rfl

/-- Helper for Lemma 10.70.8: casts along two proofs of the same type equality agree. -/
private theorem cast_eq_of_proof_irrel {α β : Sort u} (h₁ h₂ : α = β) (x : α) :
    cast h₁ x = cast h₂ x := by
  -- Equality proofs live in a proposition, so dependent casts cannot see which proof was used.
  cases h₁
  cases h₂
  rfl

/-- Helper for Lemma 10.70.8: the ordinary-localization value of a degree-zero homogeneous
fraction is the fraction with denominator `1`. -/
private theorem homogeneousLocalization_val_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] (P : Submonoid A) (a : 𝒜 0) :
    HomogeneousLocalization.val (HomogeneousLocalization.fromZeroRingHom 𝒜 P a) =
      Localization.mk a.1 ⟨1, Submonoid.one_mem P⟩ := by
  -- Expand the degree-zero constructor and read its value in the ordinary localization.
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.val_mk]



/-- Helper for Lemma 10.70.8: applying the transported scaled chart map is the same as applying
the raw `Away.map` and transporting the resulting codomain element. -/
private theorem affineBlowupChartScaledMap_toRingHom_apply
    (I : Ideal R) (a : I) (f : R) (x : affineBlowupChart I a) :
    affineBlowupChartScaledMap_toRingHom I a f x =
      cast (scaled_chart_codomain_eq I a f)
        ((HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)) x) := by
  -- First compute evaluation for the exact equality proof used in the definition.
  let φ := HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
  have happly := cast_awayRingHom_apply_base (reesAlgebraGrade (scaledIdeal I f))
    (scaled_degreeOne I a f) φ x
  unfold affineBlowupChartScaledMap_toRingHom
  calc
    (cast (congrArg
        (fun x_1 ↦ affineBlowupChart I a →+* Away (reesAlgebraGrade (scaledIdeal I f)) x_1)
        (scaled_degreeOne I a f))
      (HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a))) x =
        cast (congrArg
          (fun y : reesAlgebra (scaledIdeal I f) ↦
            Away (reesAlgebraGrade (scaledIdeal I f)) y)
          (scaled_degreeOne I a f)) (φ x) := by
          simpa [φ] using happly
    _ = cast (scaled_chart_codomain_eq I a f) (φ x) := by
          exact cast_eq_of_proof_irrel _ _ (φ x)
    _ = cast (scaled_chart_codomain_eq I a f)
        ((HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)) x) := by
          rfl

/-- Helper for Lemma 10.70.8: transporting the raw degree-zero scalar class preserves its
ordinary-localization value. -/
private theorem scaledChartRawZeroDegreeClass_val_transport
    (I : Ideal R) (a : I) (f r : R) :
    HomogeneousLocalization.val
        (cast (scaled_chart_codomain_eq I a f) (scaledChartRawZeroDegreeClass I a f r)) =
      HomogeneousLocalization.val (algebraMap R (scaledChartTarget I a f) r) := by
  -- Push the chart transport to the ordinary localization and keep the proof-term change separate.
  let 𝒜 := reesAlgebraGrade (scaledIdeal I f)
  let b : reesAlgebra (scaledIdeal I f) :=
    (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
  let c : reesAlgebra (scaledIdeal I f) :=
    reesAlgebraDegreeOne (scaledIdeal I f) (scaledElement I a f)
  let e : b = c := scaled_degreeOne I a f
  let x : Away 𝒜 b := scaledChartRawZeroDegreeClass I a f r
  have hcastElem :
      cast (scaled_chart_codomain_eq I a f) x =
        cast (congrArg (fun y : reesAlgebra (scaledIdeal I f) ↦ Away 𝒜 y) e) x := by
    exact cast_eq_of_proof_irrel _ _ x
  have hcastVal := cast_away_val 𝒜 e x
  rw [hcastElem, hcastVal]
  -- Both sides are now ordinary localization fractions with denominator `1`.
  have hsource : HomogeneousLocalization.val x =
      Localization.mk (scaledReesAlgebraZeroDegreeCoeff I f r : reesAlgebra (scaledIdeal I f))
        ⟨1, Submonoid.one_mem (Submonoid.powers b)⟩ := by
    simpa [x, 𝒜, b, scaledChartRawZeroDegreeClass] using
      (homogeneousLocalization_val_fromZeroRingHom 𝒜 (Submonoid.powers b)
        (scaledReesAlgebraZeroDegreeCoeff I f r))
  rw [hsource]
  have hloc :
      cast (congrArg (fun y : reesAlgebra (scaledIdeal I f) ↦ Localization.Away y) e)
        (Localization.mk (scaledReesAlgebraZeroDegreeCoeff I f r : reesAlgebra (scaledIdeal I f))
          ⟨1, Submonoid.one_mem (Submonoid.powers b)⟩) =
        Localization.mk (scaledReesAlgebraZeroDegreeCoeff I f r : reesAlgebra (scaledIdeal I f))
          ⟨1, Submonoid.one_mem (Submonoid.powers c)⟩ := by
    exact cast_localizationAway_mk e rfl _ _
  rw [hloc]
  -- The target algebra map is the same degree-zero homogeneous fraction.
  simpa [scaledChartTarget, scaledIdeal, scaledElement, RingHom.algebraMap_toAlgebra,
    instAlgebraAffineBlowupChart, scaledReesAlgebraZeroDegreeCoeff]
    using (homogeneousLocalization_val_fromZeroRingHom 𝒜 (Submonoid.powers c)
      (scaledReesAlgebraZeroDegreeCoeff I f r)).symm

/-- Helper for Lemma 10.70.8: transporting the raw degree-zero scalar class gives the ordinary
scalar class in the standard scaled chart. -/
private theorem scaledChartRawZeroDegreeClass_cast
    (I : Ideal R) (a : I) (f r : R) :
    cast (scaled_chart_codomain_eq I a f) (scaledChartRawZeroDegreeClass I a f r) =
      algebraMap R (scaledChartTarget I a f) r := by
  -- Lift the ordinary-localization identity back to the homogeneous localization.
  exact (HomogeneousLocalization.ext_iff_val _ _).2
    (scaledChartRawZeroDegreeClass_val_transport I a f r)

/-- Helper for Lemma 10.70.8: the scaled chart map is compatible with the `R`-algebra structures
because the graded map is the identity on degree zero. -/
private theorem affineBlowupChartScaledMap_commutes
    (I : Ideal R) (a : I) (f r : R) :
    affineBlowupChartScaledMap_toRingHom I a f (algebraMap R (affineBlowupChart I a) r) =
      algebraMap R
        (affineBlowupChart (Ideal.span ({f} : Set R) * I)
          ⟨f * a.1, Ideal.mul_mem_mul (Ideal.subset_span (by simp)) a.2⟩) r :=
  by
    -- Compute the scalar image in the raw chart first, then transport it to the standard codomain.
    rw [affineBlowupChartScaledMap_toRingHom_apply]
    have hraw :
        cast (scaled_chart_codomain_eq I a f)
            ((HomogeneousLocalization.Away.map (scaledGradedHom I f)
              (reesAlgebraDegreeOne I a)) (algebraMap R (affineBlowupChart I a) r)) =
          cast (scaled_chart_codomain_eq I a f) (scaledChartRawZeroDegreeClass I a f r) := by
      exact congrArg (cast (scaled_chart_codomain_eq I a f))
        (affineBlowupChartScaledMap_raw_commutes I a f r)
    rw [scaledChartRawZeroDegreeClass_cast I a f r] at hraw
    exact hraw

/-- Helper for Lemma 10.70.8: the power `(a^(1))^n` is a valid denominator in the source affine
blowup chart. -/
private theorem affineBlowupChart_parameter_pow_mem (I : Ideal R) (a : I) (n : ℕ) :
    a.1 ^ n ∈ Submonoid.powers a.1 := by
  exact ⟨n, rfl⟩

/-- Helper for Lemma 10.70.8: a monomial with coefficient in `I ^ n` represents a degree-`n`
homogeneous element of the Rees algebra. -/
private theorem monomial_mem_reesAlgebraGrade
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I n := by
  -- Unpack the graded piece through the defining range map.
  change (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      LinearMap.range _
  exact ⟨r, rfl⟩

/-- Helper for Lemma 10.70.8: the same monomial numerator has the degree required by the chart
fraction with denominator `(a^(1))^n`. -/
private theorem monomial_mem_reesAlgebraGrade_for_chart
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      reesAlgebraGrade I (n • 1) := by
  -- In the natural-number grading, `n • 1 = n`.
  simpa [nsmul_eq_mul] using monomial_mem_reesAlgebraGrade I n r

/-- Helper for Lemma 10.70.8: the raw mapped monomial class in the scaled chart before
transport. -/
private noncomputable def scaledChartRawMappedMonomial
    (I : Ideal R) (a : I) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    scaledChartRaw I a f :=
  HomogeneousLocalization.Away.mk
    (reesAlgebraGrade (scaledIdeal I f))
    ((scaledGradedHom I f).map_mem (reesAlgebraDegreeOne_mem I a))
    n
    ((scaledGradedHom I f)
      (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I))
    ((scaledGradedHom I f).map_mem (monomial_mem_reesAlgebraGrade_for_chart I n r))

/-- Helper for Lemma 10.70.8: the target normalized monomial class in the scaled chart. -/
private noncomputable def scaledChartTargetMonomial
    (I : Ideal R) (a : I) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    scaledChartTarget I a f :=
  let num : reesAlgebra (scaledIdeal I f) :=
    ⟨Polynomial.monomial n (f ^ n * r.1),
      (reesAlgebra.monomial_mem).2
        ((mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩)⟩
  HomogeneousLocalization.Away.mk
    (reesAlgebraGrade (scaledIdeal I f))
    (reesAlgebraDegreeOne_mem (scaledIdeal I f) (scaledElement I a f))
    n
    num
    (monomial_mem_reesAlgebraGrade_for_chart
      (scaledIdeal I f) n
      ⟨f ^ n * r.1, (mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩⟩)

/-- Helper for Lemma 10.70.8: transporting the raw mapped monomial fraction gives the standard
target monomial fraction. -/
private theorem scaledChartRawMappedMonomial_val_transport
    (I : Ideal R) (a : I) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    HomogeneousLocalization.val
        (cast (scaled_chart_codomain_eq I a f) (scaledChartRawMappedMonomial I a f n r)) =
      HomogeneousLocalization.val (scaledChartTargetMonomial I a f n r) := by
  -- As in the scalar case, reduce the chart transport to a transport of ordinary localizations.
  let 𝒜 := reesAlgebraGrade (scaledIdeal I f)
  let b : reesAlgebra (scaledIdeal I f) :=
    (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
  let c : reesAlgebra (scaledIdeal I f) :=
    reesAlgebraDegreeOne (scaledIdeal I f) (scaledElement I a f)
  let e : b = c := scaled_degreeOne I a f
  let rawNum : reesAlgebra (scaledIdeal I f) :=
    (scaledGradedHom I f)
      (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
  let targetNum : reesAlgebra (scaledIdeal I f) :=
    ⟨Polynomial.monomial n (f ^ n * r.1),
      (reesAlgebra.monomial_mem).2
        ((mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩)⟩
  let x : Away 𝒜 b := scaledChartRawMappedMonomial I a f n r
  have hcastElem :
      cast (scaled_chart_codomain_eq I a f) x =
        cast (congrArg (fun y : reesAlgebra (scaledIdeal I f) ↦ Away 𝒜 y) e) x := by
    exact cast_eq_of_proof_irrel _ _ x
  have hcastVal := cast_away_val 𝒜 e x
  rw [hcastElem, hcastVal]
  -- The raw value is the ordinary fraction with numerator obtained by the scaled Rees map.
  have hsource : HomogeneousLocalization.val x =
      Localization.mk rawNum ⟨b ^ n, by exact ⟨n, rfl⟩⟩ := by
    simpa [x, rawNum, 𝒜, b, scaledChartRawMappedMonomial] using
      (HomogeneousLocalization.Away.val_mk (reesAlgebraGrade (scaledIdeal I f)) n
        ((scaledGradedHom I f).map_mem (reesAlgebraDegreeOne_mem I a))
        ((scaledGradedHom I f)
          (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I))
        ((scaledGradedHom I f).map_mem (monomial_mem_reesAlgebraGrade_for_chart I n r)))
  rw [hsource]
  have hloc :
      cast (congrArg (fun y : reesAlgebra (scaledIdeal I f) ↦ Localization.Away y) e)
        (Localization.mk rawNum ⟨b ^ n, by exact ⟨n, rfl⟩⟩) =
        Localization.mk rawNum ⟨c ^ n, by exact ⟨n, rfl⟩⟩ := by
    exact cast_localizationAway_mk e
      (congrArg (fun z : reesAlgebra (scaledIdeal I f) ↦ z ^ n) e) _ _
  rw [hloc]
  -- Replace the mapped numerator by its explicit normalized monomial.
  have hnum : rawNum = targetNum := by
    simpa [rawNum, targetNum] using scaledReesAlgebraRingHom_monomial I f n r
  rw [hnum]
  -- The target monomial class has exactly the same ordinary-localization value.
  simpa [targetNum, c, 𝒜, scaledChartTargetMonomial] using
    (HomogeneousLocalization.Away.val_mk (reesAlgebraGrade (scaledIdeal I f)) n
      (reesAlgebraDegreeOne_mem (scaledIdeal I f) (scaledElement I a f))
      (⟨Polynomial.monomial n (f ^ n * r.1),
        (reesAlgebra.monomial_mem).2
          ((mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩)⟩ : reesAlgebra (scaledIdeal I f))
      (monomial_mem_reesAlgebraGrade_for_chart
        (scaledIdeal I f) n
        ⟨f ^ n * r.1, (mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩⟩)).symm

/-- Helper for Lemma 10.70.8: transporting the raw mapped monomial fraction gives the standard
target monomial fraction. -/
private theorem scaledChartRawMappedMonomial_cast
    (I : Ideal R) (a : I) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    cast (scaled_chart_codomain_eq I a f) (scaledChartRawMappedMonomial I a f n r) =
      scaledChartTargetMonomial I a f n r := by
  -- Lift the ordinary-localization computation back to the homogeneous localization.
  exact (HomogeneousLocalization.ext_iff_val _ _).2
    (scaledChartRawMappedMonomial_val_transport I a f n r)

/-- Helper for Lemma 10.70.8: before transporting the codomain, the raw scaled chart map is
surjective on normalized monomial fractions. -/
private theorem affineBlowupChartScaledMap_raw_surjective
    (I : Ideal R) (a : I) (f : R) :
    let Araw :=
      Away (reesAlgebraGrade (scaledIdeal I f))
        ((scaledGradedHom I f) (reesAlgebraDegreeOne I a))
    let ψ : affineBlowupChart I a →+* Araw :=
      HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
    Function.Surjective ψ := by
  intro Araw ψ z
  obtain ⟨n, s, hs, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (reesAlgebraGrade (scaledIdeal I f))
    (show (scaledGradedHom I f (reesAlgebraDegreeOne I a)) ∈ reesAlgebraGrade (scaledIdeal I f) 1 by
      simpa using (scaledGradedHom I f).map_mem (reesAlgebraDegreeOne_mem I a))
    z
  have hs' : s ∈ reesAlgebraGrade (scaledIdeal I f) n := by
    simpa [nsmul_eq_mul] using hs
  change s ∈ LinearMap.range _ at hs'
  rcases hs' with ⟨r, rfl⟩
  rcases (mem_scaledIdeal_pow_iff_exists I f n r.1).1 r.2 with ⟨y, hy⟩
  have hr :
      r = ⟨f ^ n * y.1, (mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨y, rfl⟩⟩ := by
    apply Subtype.ext
    exact hy.symm
  subst hr
  refine ⟨HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
      (⟨Polynomial.monomial n y.1, (reesAlgebra.monomial_mem).2 y.2⟩ : reesAlgebra I)
      (monomial_mem_reesAlgebraGrade_for_chart I n y), ?_⟩
  -- The image of the chosen preimage is the required target fraction `f^n y / (a^(1))^n`.
  simpa [ψ, scaledGradedHom, scaledReesAlgebraRingHom_monomial] using
    (HomogeneousLocalization.Away.map_mk (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
      (reesAlgebraDegreeOne_mem I a) n
      (⟨Polynomial.monomial n y.1, (reesAlgebra.monomial_mem).2 y.2⟩ : reesAlgebra I)
      (monomial_mem_reesAlgebraGrade_for_chart I n y))

/-- Lemma 10.70.8 (Stacks tag `0BBI`): the scaled affine blowup chart map
`R[I/a] → R[fI/(fa)]` sending `x / a^n` to `f^n x / (fa)^n`. -/
@[stacks 0BBI]
noncomputable def affineBlowupChartScaledMap
    (I : Ideal R) (a : I) (f : R) :
    affineBlowupChart I a →ₐ[R]
      affineBlowupChart (Ideal.span ({f} : Set R) * I)
        ⟨f * a.1, Ideal.mul_mem_mul (Ideal.subset_span (by simp)) a.2⟩ where
  toRingHom := affineBlowupChartScaledMap_toRingHom I a f
  commutes' := affineBlowupChartScaledMap_commutes I a f

/-- Helper for Lemma 10.70.8: the element `a` itself is a valid denominator in the ordinary
localization `R_a`. -/
private theorem affineBlowupChart_parameter_mem (I : Ideal R) (a : I) :
    a.1 ∈ Submonoid.powers a.1 := by
  exact ⟨1, by simp⟩

/-- Helper for Lemma 10.70.8: after normalizing a chart fraction to a monomial numerator, the
comparison map sends it to the ordinary fraction `r / a^n` in `R_a`. -/
private theorem affineBlowupChartToLocalizationAway_fraction_of_monomial
    (J : Ideal R) (b : J) (n : ℕ) (r : ↥(J ^ n)) :
    affineBlowupChartToLocalizationAway J b
      (HomogeneousLocalization.Away.mk (reesAlgebraGrade J) (reesAlgebraDegreeOne_mem J b) n
        (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra J)
        (monomial_mem_reesAlgebraGrade_for_chart J n r)) =
      Localization.mk r.1 ⟨b.1 ^ n, affineBlowupChart_parameter_pow_mem J b n⟩ := by
  -- Route correction: compute the normalized fraction in the ordinary localization first.
  let s : reesAlgebra J := ⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩
  let g : reesAlgebra J →+* Localization.Away b.1 :=
    (Polynomial.eval₂RingHom (algebraMap R (Localization.Away b.1)) 1).comp
      (reesAlgebra J).toSubring.subtype
  have hfrac₁ (x : R) :
      algebraMap R (Localization.Away b.1) x *
          Localization.mk 1 ⟨b.1, affineBlowupChart_parameter_mem J b⟩ =
        Localization.mk x ⟨b.1, affineBlowupChart_parameter_mem J b⟩ := by
    -- Rewrite `x / b` into standard localization form and multiply by the chosen inverse of `b`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact
      (Localization.mk_eq_mk'_apply x ⟨b.1, affineBlowupChart_parameter_mem J b⟩).symm
  have hfrac (x : R) (m : ℕ) :
      algebraMap R (Localization.Away b.1) x *
          Localization.mk 1 ⟨b.1 ^ m, affineBlowupChart_parameter_pow_mem J b m⟩ =
        Localization.mk x ⟨b.1 ^ m, affineBlowupChart_parameter_pow_mem J b m⟩ := by
    -- The same standard calculation works for every power `b^m`.
    rw [← Algebra.smul_def, Localization.mk_eq_mk'_apply, IsLocalization.smul_mk'_one]
    exact
      (Localization.mk_eq_mk'_apply x ⟨b.1 ^ m, affineBlowupChart_parameter_pow_mem J b m⟩).symm
  have h :=
      Localization.awayLift_mk g (reesAlgebraDegreeOne J b) s
        (Localization.mk 1 ⟨b.1, affineBlowupChart_parameter_mem J b⟩)
        (by
          -- The chosen inverse of `b^(1)` is the ordinary fraction `1 / b`.
          rw [show g (reesAlgebraDegreeOne J b) = algebraMap R (Localization.Away b.1) b.1 by
            simp [g, reesAlgebraDegreeOne]]
          rw [hfrac₁]
          exact Localization.mk_self ⟨b.1, affineBlowupChart_parameter_mem J b⟩)
        n
  rw [affineBlowupChartToLocalizationAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  have hpow :
      (Localization.mk 1 ⟨b.1, affineBlowupChart_parameter_mem J b⟩ :
          Localization.Away b.1) ^ n =
        Localization.mk 1 ⟨b.1 ^ n, affineBlowupChart_parameter_pow_mem J b n⟩ := by
    -- The nth power of `1 / b` is the usual fraction `1 / b^n`.
    rw [Localization.mk_pow, one_pow]
    apply congrArg (fun d => Localization.mk 1 d)
    ext
    simp
  rw [hpow] at h
  simpa [g, s, reesAlgebraDegreeOne, hfrac] using h

/-- Helper for Lemma 10.70.8: the comparison map from the affine blowup chart to the ordinary
localization `R_b` detects zero. -/
private theorem affineBlowupChartToLocalizationAway_eq_zero_iff
    (J : Ideal R) (b : J) (x : affineBlowupChart J b) :
    affineBlowupChartToLocalizationAway J b x = 0 ↔ x = 0 := by
  let A := affineBlowupChart J b
  let bA : A := algebraMap R A b.1
  have hb : Submonoid.powers bA ≤ nonZeroDivisors A := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact ((affineBlowupChart_isRegular J b).pow n).mem_nonZeroDivisors
  -- The chart-to-localization map is the algebra map for the away-localization instance.
  simpa [A, RingHom.algebraMap_toAlgebra] using
    (IsLocalization.to_map_eq_zero_iff (M := Submonoid.powers bA)
      (S := Localization.Away b.1) hb (x := x))

/-- Helper for Lemma 10.70.8: the comparison map to the ordinary localization detects equality of
chart elements, not just vanishing. -/
private theorem affineBlowupChart_eq_of_toLocalizationAway_eq
    (J : Ideal R) (b : J) {x y : affineBlowupChart J b}
    (hxy : affineBlowupChartToLocalizationAway J b x =
      affineBlowupChartToLocalizationAway J b y) :
    x = y := by
  -- Reduce equality to the zero-detection statement for the difference.
  apply sub_eq_zero.mp
  apply (affineBlowupChartToLocalizationAway_eq_zero_iff J b (x - y)).mp
  simpa [map_sub, hxy]

/-- Helper for Lemma 10.70.8: the ordinary map `R_a → R_{fa}` sends the normalized fraction
`r / a^n` to `f^n r / (fa)^n`. -/
private theorem away_map_fraction_of_monomial
    (I : Ideal R) (a : I) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    let ψ : Localization.Away a.1 →+* Localization.Away (f * a.1) := by
      letI : IsLocalization.Away (a.1 * f) (Localization.Away (f * a.1)) := by
        simpa [mul_comm] using
          (inferInstance : IsLocalization.Away (f * a.1) (Localization.Away (f * a.1)))
      exact IsLocalization.Away.awayToAwayRight a.1 f
    ψ (Localization.mk r.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) =
      Localization.mk (f ^ n * r.1) ⟨(f * a.1) ^ n, by exact ⟨n, rfl⟩⟩ :=
  by
    let T := Localization.Away (f * a.1)
    let fa : Submonoid.powers (f * a.1) := ⟨f * a.1, by exact ⟨1, by simp⟩⟩
    let fan : Submonoid.powers (f * a.1) := ⟨(f * a.1) ^ n, by exact ⟨n, by simp⟩⟩
    letI : IsLocalization.Away (a.1 * f) T := by
      simpa [mul_comm] using
        (inferInstance : IsLocalization.Away (f * a.1) (Localization.Away (f * a.1)))
    let ψ : Localization.Away a.1 →+* T := IsLocalization.Away.awayToAwayRight a.1 f
    let v : T := Localization.mk f fa
    have hv : algebraMap R T a.1 * v = 1 := by
      -- The chosen inverse of `a` in `R_(fa)` is the ordinary fraction `f / (fa)`.
      calc
        algebraMap R T a.1 * v =
            Localization.mk (a.1 * f) fa := by
              rw [show v = IsLocalization.mk' T f fa by
                rw [← Localization.mk_eq_mk'_apply]]
              rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
              rw [← Localization.mk_eq_mk'_apply]
        _ = Localization.mk (f * a.1) fa := by
              simp [mul_comm]
        _ = 1 := Localization.mk_self fa
    let ψ' : Localization.Away a.1 →+* T :=
      Localization.awayLift (algebraMap R T) a.1
        (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)
    have hψ : ψ = ψ' := by
      -- Both maps agree on `R`, so the localization universal property identifies them.
      apply IsLocalization.ringHom_ext (Submonoid.powers a.1)
      ext x
      simp only [RingHom.comp_apply]
      simpa [ψ', Localization.awayLift] using
        (IsLocalization.Away.awayToAwayRight_eq
          (S := Localization.Away a.1) (P := T) (x := a.1) (y := f) x)
    have hvpow :
        v ^ n = Localization.mk (f ^ n) fan := by
      -- Raising `f / (fa)` to the nth power gives the expected normalized denominator.
      rw [show v = Localization.mk f fa by rfl, Localization.mk_pow]
      have hfa_pow : fa ^ n = fan := by
        ext
        simp [fa, fan]
      exact congrArg (fun d : Submonoid.powers (f * a.1) ↦ Localization.mk (f ^ n) d) hfa_pow
    change ψ (Localization.mk r.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) = _
    rw [hψ]
    calc
      ψ' (Localization.mk r.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) =
          algebraMap R T r.1 * v ^ n := by
            simpa [ψ', v] using
              (Localization.awayLift_mk (algebraMap R T) a.1 r.1 v hv n)
      _ = algebraMap R T r.1 *
          Localization.mk (f ^ n) fan := by
            rw [hvpow]
      _ = Localization.mk (r.1 * f ^ n) fan := by
            rw [show Localization.mk (f ^ n) fan =
                IsLocalization.mk' T (f ^ n) fan by
                  rw [← Localization.mk_eq_mk'_apply]]
            rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
            rw [← Localization.mk_eq_mk'_apply]
      _ = Localization.mk (f ^ n * r.1) fan := by
            simp [mul_comm]

/-- Helper for Lemma 10.70.8: after identifying both charts with ordinary localizations, the
scaled chart map agrees with the ordinary map `R_a → R_{fa}`. -/
private theorem affineBlowupChartScaledMap_fraction_of_monomial
    (I : Ideal R) (a : I) (f : R) (n : ℕ) (r : ↥(I ^ n)) :
    affineBlowupChartScaledMap I a f
      (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
        (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
        (monomial_mem_reesAlgebraGrade_for_chart I n r)) =
      HomogeneousLocalization.Away.mk
        (reesAlgebraGrade (scaledIdeal I f))
        (reesAlgebraDegreeOne_mem (scaledIdeal I f) (scaledElement I a f))
        n
        (⟨Polynomial.monomial n (f ^ n * r.1),
          (reesAlgebra.monomial_mem).2
            ((mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩)⟩ :
          reesAlgebra (scaledIdeal I f))
        (monomial_mem_reesAlgebraGrade_for_chart
          (scaledIdeal I f) n
          ⟨f ^ n * r.1, (mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩⟩) :=
  by
    change affineBlowupChartScaledMap_toRingHom I a f
        (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
          (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
          (monomial_mem_reesAlgebraGrade_for_chart I n r)) =
      scaledChartTargetMonomial I a f n r
    rw [affineBlowupChartScaledMap_toRingHom_apply, HomogeneousLocalization.Away.map_mk]
    -- The raw `Away.map` image is exactly the transported monomial class.
    simpa [scaledChartRawMappedMonomial] using scaledChartRawMappedMonomial_cast I a f n r

/-- Helper for Lemma 10.70.8: after identifying both charts with ordinary localizations, the
scaled chart map agrees with the ordinary map `R_a → R_{fa}`. -/
private theorem affineBlowupChartScaledMap_comp_toLocalizationAway
    (I : Ideal R) (a : I) (f : R) (x : affineBlowupChart I a) :
    let ψ : Localization.Away a.1 →+* Localization.Away (f * a.1) := by
      letI : IsLocalization.Away (a.1 * f) (Localization.Away (f * a.1)) := by
        simpa [mul_comm] using
          (inferInstance : IsLocalization.Away (f * a.1) (Localization.Away (f * a.1)))
      exact IsLocalization.Away.awayToAwayRight a.1 f
    affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
        (affineBlowupChartScaledMap I a f x) =
      ψ (affineBlowupChartToLocalizationAway I a x) :=
  by
    let ψ : Localization.Away a.1 →+* Localization.Away (f * a.1) := by
      letI : IsLocalization.Away (a.1 * f) (Localization.Away (f * a.1)) := by
        simpa [mul_comm] using
          (inferInstance : IsLocalization.Away (f * a.1) (Localization.Away (f * a.1)))
      exact IsLocalization.Away.awayToAwayRight a.1 f
    obtain ⟨n, s, hs, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) x
    have hs' : s ∈ reesAlgebraGrade I n := by
      simpa [nsmul_eq_mul] using hs
    change s ∈ LinearMap.range _ at hs'
    rcases hs' with ⟨r, rfl⟩
    -- Normalize both sides to the same explicit ordinary fraction `f^n r / (fa)^n`.
    change affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
        ((affineBlowupChartScaledMap I a f)
          (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
            (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
            (monomial_mem_reesAlgebraGrade_for_chart I n r))) =
      ψ
        (affineBlowupChartToLocalizationAway I a
          (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
            (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
            (monomial_mem_reesAlgebraGrade_for_chart I n r)))
    calc
      affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
          ((affineBlowupChartScaledMap I a f)
            (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
              (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
              (monomial_mem_reesAlgebraGrade_for_chart I n r))) =
          Localization.mk (f ^ n * r.1)
            ⟨(scaledElement I a f).1 ^ n,
              affineBlowupChart_parameter_pow_mem (scaledIdeal I f) (scaledElement I a f) n⟩ := by
            rw [affineBlowupChartScaledMap_fraction_of_monomial]
            simpa [scaledIdeal, scaledElement] using
              (affineBlowupChartToLocalizationAway_fraction_of_monomial
                (scaledIdeal I f) (scaledElement I a f) n
                ⟨f ^ n * r.1, (mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨r, rfl⟩⟩)
      _ = ψ
          (affineBlowupChartToLocalizationAway I a
            (HomogeneousLocalization.Away.mk (reesAlgebraGrade I) (reesAlgebraDegreeOne_mem I a) n
              (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
              (monomial_mem_reesAlgebraGrade_for_chart I n r))) := by
            rw [affineBlowupChartToLocalizationAway_fraction_of_monomial]
            simpa [ψ, scaledElement] using (away_map_fraction_of_monomial I a f n r).symm

/-- Helper for Lemma 10.70.8: the scaled chart map is surjective because the raw normalized
monomial-fraction map is surjective, and the only remaining step is the codomain transport coming
from `scaled_degreeOne`. -/
private theorem affineBlowupChartScaledMap_surjective
    (I : Ideal R) (a : I) (f : R) :
    Function.Surjective (affineBlowupChartScaledMap I a f) :=
  by
    intro z
    -- Reuse the already proved raw surjectivity and then transport the codomain back to the
    -- standard scaled chart.
    let zraw : scaledChartRaw I a f := cast (scaled_chart_codomain_eq I a f).symm z
    rcases affineBlowupChartScaledMap_raw_surjective I a f zraw with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change affineBlowupChartScaledMap_toRingHom I a f x = z
    rw [affineBlowupChartScaledMap_toRingHom_apply]
    simpa [zraw] using congrArg
      (cast (scaled_chart_codomain_eq I a f)) hx

/-- Helper for Lemma 10.70.8: the canonical ordinary localization map `R_a → R_{fa}` has the
textbook zero criterion. -/
private theorem awayToAwayRight_eq_zero_iff_exists_pow_mul_eq_zero
    (I : Ideal R) (a : I) (f : R) (z : Localization.Away a.1) :
    let ψ : Localization.Away a.1 →+* Localization.Away (f * a.1) := by
      letI : IsLocalization.Away (a.1 * f) (Localization.Away (f * a.1)) := by
        simpa [mul_comm] using
          (inferInstance : IsLocalization.Away (f * a.1) (Localization.Away (f * a.1)))
      exact IsLocalization.Away.awayToAwayRight a.1 f
    ψ z = 0 ↔ ∃ n : ℕ, (algebraMap R (Localization.Away a.1) f) ^ n * z = 0 :=
  by
    let T := Localization.Away (f * a.1)
    letI : IsLocalization.Away (a.1 * f) T := by
      simpa [mul_comm] using
        (inferInstance : IsLocalization.Away (f * a.1) (Localization.Away (f * a.1)))
    let ψ : Localization.Away a.1 →+* T := IsLocalization.Away.awayToAwayRight a.1 f
    constructor
    · intro hz
      obtain ⟨k, d, hk⟩ := IsLocalization.Away.surj a.1 z
      have hk' : ψ z * (algebraMap R T a.1) ^ k = algebraMap R T d := by
        -- Clearing the source `a`-denominator survives after mapping to `R_(fa)`.
        have hkmap := congrArg ψ hk
        rw [map_mul, map_pow,
          IsLocalization.Away.awayToAwayRight_eq
            (S := Localization.Away a.1) (P := T) (x := a.1) (y := f) a.1,
          IsLocalization.Away.awayToAwayRight_eq
            (S := Localization.Away a.1) (P := T) (x := a.1) (y := f) d] at hkmap
        exact hkmap
      rw [hz, zero_mul] at hk'
      have hk'' : algebraMap R T d = 0 := by
        simpa using hk'.symm
      rcases (IsLocalization.map_eq_zero_iff
          (M := Submonoid.powers (f * a.1))
          (S := T) d).mp hk'' with ⟨m, hm⟩
      rcases m.2 with ⟨n, hn⟩
      have hm' : (f * a.1) ^ n * d = 0 := by
        simpa [hn] using hm
      have hsource :
          algebraMap R (Localization.Away a.1) ((f * a.1) ^ n * d) = 0 := by
        simpa using congrArg (algebraMap R (Localization.Away a.1)) hm'
      have hmul :
          ((algebraMap R (Localization.Away a.1) f) ^ n * z) *
              (algebraMap R (Localization.Away a.1) a.1) ^ (n + k) = 0 := by
        -- Rewrite the cleared-denominator relation in `R_a` and collect the powers of `a`.
        calc
          ((algebraMap R (Localization.Away a.1) f) ^ n * z) *
              (algebraMap R (Localization.Away a.1) a.1) ^ (n + k)
              = algebraMap R (Localization.Away a.1) ((f * a.1) ^ n * d) := by
                  rw [pow_add]
                  calc
                    ((algebraMap R (Localization.Away a.1) f) ^ n * z) *
                        ((algebraMap R (Localization.Away a.1) a.1) ^ n *
                          (algebraMap R (Localization.Away a.1) a.1) ^ k)
                        =
                      (algebraMap R (Localization.Away a.1) f) ^ n *
                        (z * (algebraMap R (Localization.Away a.1) a.1) ^ k) *
                        (algebraMap R (Localization.Away a.1) a.1) ^ n := by
                          simp [mul_assoc, mul_left_comm, mul_comm]
                    _ =
                      (algebraMap R (Localization.Away a.1) f) ^ n *
                        algebraMap R (Localization.Away a.1) d *
                        (algebraMap R (Localization.Away a.1) a.1) ^ n := by
                          rw [hk]
                    _ = algebraMap R (Localization.Away a.1) ((f * a.1) ^ n * d) := by
                          simpa [map_mul, map_pow, mul_assoc, mul_left_comm, mul_comm, ← mul_pow]
          _ = 0 := hsource
      have haunit :
          IsUnit ((algebraMap R (Localization.Away a.1) a.1) ^ (n + k)) :=
        (IsLocalization.Away.algebraMap_isUnit a.1).pow (n + k)
      have hmul' :
          (algebraMap R (Localization.Away a.1) a.1) ^ (n + k) *
              ((algebraMap R (Localization.Away a.1) f) ^ n * z) = 0 := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      exact ⟨n, (haunit.mul_right_eq_zero.mp hmul')⟩
    · rintro ⟨n, hn⟩
      have hmap :
          (algebraMap R T f) ^ n * ψ z = 0 := by
        -- Mapping the annihilating relation carries `f` to the same scalar in `R_(fa)`.
        have hnmap := congrArg ψ hn
        rw [map_mul, map_pow,
          IsLocalization.Away.awayToAwayRight_eq
            (S := Localization.Away a.1) (P := T) (x := a.1) (y := f) f] at hnmap
        simpa using hnmap
      have hfunit : IsUnit ((algebraMap R T f) ^ n) := by
        exact (IsLocalization.Away.isUnit_of_dvd (S := T) (x := f * a.1)
          (dvd_mul_right f a.1)).pow n
      exact hfunit.mul_right_eq_zero.mp (by simpa [mul_comm] using hmap)

/-- Membership in the kernel of the scaled chart map is exactly `f`-power torsion. -/
theorem mem_ker_affineBlowupChartScaledMap_iff_exists_pow_mul_eq_zero
    (I : Ideal R) (a : I) (f : R) (x : affineBlowupChart I a) :
    x ∈ RingHom.ker (affineBlowupChartScaledMap I a f).toRingHom ↔
      ∃ n : ℕ, (algebraMap R (affineBlowupChart I a) f) ^ n * x = 0 :=
  by
    constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      let ψ : Localization.Away a.1 →+* Localization.Away (f * a.1) := by
        letI : IsLocalization.Away (a.1 * f) (Localization.Away (f * a.1)) := by
          simpa [mul_comm] using
            (inferInstance : IsLocalization.Away (f * a.1) (Localization.Away (f * a.1)))
        exact IsLocalization.Away.awayToAwayRight a.1 f
      have hloc :
          ψ (affineBlowupChartToLocalizationAway I a x) = 0 := by
        -- Push the kernel equation through the comparison square into ordinary localizations.
        have hcomp := affineBlowupChartScaledMap_comp_toLocalizationAway I a f x
        dsimp at hcomp
        change
          affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
            ((affineBlowupChartScaledMap I a f).toRingHom x) =
              ψ ((affineBlowupChartToLocalizationAway I a) x) at hcomp
        rw [hx] at hcomp
        calc
          ψ ((affineBlowupChartToLocalizationAway I a) x) =
              affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f) 0 := by
                exact hcomp.symm
          _ = 0 := by simp
      rcases (awayToAwayRight_eq_zero_iff_exists_pow_mul_eq_zero I a f
          (affineBlowupChartToLocalizationAway I a x)).mp hloc with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      apply (affineBlowupChartToLocalizationAway_eq_zero_iff I a _).mp
      -- Pull the vanishing relation back from `R_a` to the source chart.
      simpa [map_mul, map_pow] using hn
    · rintro ⟨n, hn⟩
      rw [RingHom.mem_ker]
      let A :=
        affineBlowupChart (Ideal.span ({f} : Set R) * I)
          ⟨f * a.1, Ideal.mul_mem_mul (Ideal.subset_span (by simp)) a.2⟩
      have hmap :
          (algebraMap R A f) ^ n *
              affineBlowupChartScaledMap I a f x = 0 := by
        -- Mapping the annihilating relation carries `f` to the same scalar in the target chart.
        simpa [A] using congrArg (affineBlowupChartScaledMap I a f) hn
      have hfa :
          (algebraMap R A (f * a.1)) ^ n *
              affineBlowupChartScaledMap I a f x = 0 := by
        -- Multiply by the image of `a^n` so the regular target parameter `(fa)` appears.
        calc
          (algebraMap R A (f * a.1)) ^ n *
              affineBlowupChartScaledMap I a f x =
              ((algebraMap R A f) * algebraMap R A a.1) ^ n *
                affineBlowupChartScaledMap I a f x := by
                  rw [map_mul]
          _ =
              ((algebraMap R A f) ^ n * (algebraMap R A a.1) ^ n) *
                affineBlowupChartScaledMap I a f x := by
                  rw [mul_pow]
          _ =
              (algebraMap R A a.1) ^ n *
                ((algebraMap R A f) ^ n *
                  affineBlowupChartScaledMap I a f x) := by
                  ac_rfl
          _ = 0 := by
                  rw [hmap, mul_zero]
      have hregular : IsRegular (algebraMap R A (f * a.1)) := by
        convert (affineBlowupChart_isRegular (scaledIdeal I f) (scaledElement I a f)) using 1
      exact (hregular.pow n).1 (by simpa using hfa)

/-- Chap10 Lemma 10 70 8 (Stacks tag `0BBI`): the scaled map `R[I/a] → R[fI/(fa)]`
is surjective, and its kernel consists exactly of the elements annihilated by some power of the
image of `f`. -/
@[stacks 0BBI]
theorem affineBlowupChartScaledMap_surjective_and_ker_eq_f_power_torsion
    (I : Ideal R) (a : I) (f : R) :
    let A := affineBlowupChart I a
    let φ := affineBlowupChartScaledMap I a f
    let fA : A := algebraMap R A f
    Function.Surjective φ ∧
      ∀ x : A, x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, fA ^ n * x = 0 :=
  by
    refine ⟨affineBlowupChartScaledMap_surjective I a f, ?_⟩
    intro x
    exact mem_ker_affineBlowupChartScaledMap_iff_exists_pow_mul_eq_zero I a f x

/-- Canonical reformulation of Lemma 10.70.8: the kernel of the scaled map is the primary
component of the principal ideal generated by the image of `f`. -/
theorem affineBlowupChartScaledMap_surjective_and_ker_eq_primaryComponent
    (I : Ideal R) (a : I) (f : R) :
    let A := affineBlowupChart I a
    let φ := affineBlowupChartScaledMap I a f
    let fA : A := algebraMap R A f
    Function.Surjective φ ∧
      RingHom.ker φ.toRingHom = (Ideal.span ({fA} : Set A)).primaryComponent A := by
  refine ⟨(affineBlowupChartScaledMap_surjective_and_ker_eq_f_power_torsion I a f).1, ?_⟩
  · ext x
    rw [Ideal.primaryComponent_mem]
    constructor
    · intro hx
      rcases
        (affineBlowupChartScaledMap_surjective_and_ker_eq_f_power_torsion I a f).2 x |>.mp hx with
          ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [Submodule.mem_torsionBySet_iff]
      intro y
      rcases y with ⟨y, hy⟩
      rw [Ideal.span_singleton_pow] at hy
      change y ∈ Ideal.span ({(algebraMap R (affineBlowupChart I a) f) ^ n} :
        Set (affineBlowupChart I a)) at hy
      rw [Ideal.mem_span_singleton'] at hy
      rcases hy with ⟨c, rfl⟩
      simp [smul_eq_mul, mul_assoc, hn]
    · rintro ⟨n, hx⟩
      refine
        (affineBlowupChartScaledMap_surjective_and_ker_eq_f_power_torsion I a f).2 x |>.mpr
          ⟨n, ?_⟩
      rw [Submodule.mem_torsionBySet_iff] at hx
      simpa [smul_eq_mul, Ideal.span_singleton_pow] using
        hx ⟨(algebraMap R (affineBlowupChart I a) f) ^ n, by
          rw [Ideal.span_singleton_pow]
          exact Ideal.subset_span (by simp)⟩

end
