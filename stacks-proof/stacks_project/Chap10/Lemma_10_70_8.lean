import stacks_project.Chap10.Definition_10_70_1
import stacks_project.Chap10.Lemma_10_70_2

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

private def scaledIdeal (I : Ideal R) (f : R) : Ideal R :=
  Ideal.span ({f} : Set R) * I

private def scaledElement (I : Ideal R) (a : I) (f : R) : scaledIdeal I f :=
  ⟨f * a.1, Ideal.mul_mem_mul (Ideal.subset_span (by simp)) a.2⟩

/-- Helper for Lemma 10.70.8: an element of the `n`th power of the scaled ideal is exactly a
multiple of `f ^ n` by an element of `I ^ n`. -/
private theorem mem_scaledIdeal_pow_iff_exists
    (I : Ideal R) (f : R) (n : ℕ) (x : R) :
    x ∈ scaledIdeal I f ^ n ↔ ∃ y : ↥(I ^ n), f ^ n * y.1 = x := by
  rw [scaledIdeal, mul_pow, Ideal.span_singleton_pow]
  simpa [mul_comm] using
    (Submodule.mem_span_singleton_mul (R := R) (P := (I ^ n : Submodule R R))
      (x := x) (y := f ^ n))

/-- Helper for Lemma 10.70.8: evaluating at `C f * X` multiplies the `n`th coefficient by
`f ^ n`. -/
private theorem eval2_C_mul_X_coeff
    (f : R) (p : R[X]) (n : ℕ) :
    (Polynomial.eval₂ C (C f * X) p).coeff n = p.coeff n * f ^ n := by
  -- Polynomial induction reduces the claim to a single monomial calculation.
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq, add_mul]
  | monomial m a =>
      rw [Polynomial.eval₂_monomial, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
      by_cases hmn : n = m
      · subst hmn
        simp
      · have hmn' : m ≠ n := by
          exact fun h => hmn h.symm
        simp [hmn, hmn']

/-- Helper for Lemma 10.70.8: evaluating a Rees-algebra polynomial at `fX` stays inside the Rees
algebra of the scaled ideal. -/
private theorem scaledReesAlgebra_mem
    (I : Ideal R) (f : R) (x : reesAlgebra I) :
    eval₂RingHom C (C f * X) x.1 ∈
      reesAlgebra (scaledIdeal I f) := by
  -- Check the Rees-algebra condition coefficientwise after evaluation at `fX`.
  rw [mem_reesAlgebra_iff (I := scaledIdeal I f)]
  intro n
  have hxcoeff : x.1.coeff n ∈ I ^ n := (mem_reesAlgebra_iff (I := I) x.1).1 x.2 n
  change (Polynomial.eval₂ C (C f * X) x.1).coeff n ∈ scaledIdeal I f ^ n
  rw [eval2_C_mul_X_coeff]
  exact (mem_scaledIdeal_pow_iff_exists I f n _).2
    ⟨⟨x.1.coeff n, hxcoeff⟩, by simp [mul_comm]⟩

/-- Helper for Lemma 10.70.8: the codomain proof for the scaled Rees-algebra ring homomorphism. -/
private theorem scaledReesAlgebraRingHom_mem
    (I : Ideal R) (f : R) (x : (reesAlgebra I).toSubring) :
    ((Polynomial.eval₂RingHom C (C f * X)).comp (reesAlgebra I).toSubring.subtype) x ∈
      (reesAlgebra (scaledIdeal I f)).toSubring := by
  change Polynomial.eval₂RingHom C (C f * X) x.1 ∈ reesAlgebra (scaledIdeal I f)
  exact scaledReesAlgebra_mem I f ⟨x.1, x.2⟩

private noncomputable def scaledReesAlgebraRingHom
    (I : Ideal R) (f : R) :
    reesAlgebra I →+* reesAlgebra (scaledIdeal I f) :=
  RingHom.codRestrict
    ((Polynomial.eval₂RingHom C (C f * X)).comp (reesAlgebra I).toSubring.subtype)
    (reesAlgebra (scaledIdeal I f)).toSubring
    (scaledReesAlgebraRingHom_mem I f)

/-- Helper for Lemma 10.70.8: the scaled Rees-algebra map sends a degree-`n` monomial to the
degree-`n` monomial with coefficient multiplied by `f ^ n`. -/
private theorem scaledReesAlgebraRingHom_monomial
    (I : Ideal R) (f : R) (n : ℕ) (y : ↥(I ^ n)) :
    scaledReesAlgebraRingHom I f
      (⟨Polynomial.monomial n y.1, (reesAlgebra.monomial_mem).2 y.2⟩ : reesAlgebra I) =
        ⟨Polynomial.monomial n (f ^ n * y.1),
          (reesAlgebra.monomial_mem).2 ((mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨y, rfl⟩)⟩ := by
  apply Subtype.ext
  change Polynomial.eval₂ C (C f * X) (Polynomial.monomial n y.1) = _
  rw [Polynomial.eval₂_monomial, mul_pow, ← Polynomial.C_pow]
  calc
    C y.1 * (C (f ^ n) * X ^ n) = (C y.1 * C (f ^ n)) * X ^ n := by rw [mul_assoc]
    _ = C (y.1 * f ^ n) * X ^ n := by rw [← Polynomial.C_mul]
    _ = Polynomial.monomial n (y.1 * f ^ n) := by rw [Polynomial.C_mul_X_pow_eq_monomial]
    _ = Polynomial.monomial n (f ^ n * y.1) := by simp [mul_comm]

private theorem scaledReesAlgebra_mem_grade
    (I : Ideal R) (f : R) {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ reesAlgebraGrade I n) :
    scaledReesAlgebraRingHom I f x ∈ reesAlgebraGrade (scaledIdeal I f) n := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨⟨f ^ n * y.1, (mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨y, rfl⟩⟩, ?_⟩
  simpa using (scaledReesAlgebraRingHom_monomial I f n y).symm

private noncomputable def scaledGradedHom
    (I : Ideal R) (f : R) :
    reesAlgebraGrade I →+*ᵍ reesAlgebraGrade (scaledIdeal I f) where
  toRingHom := scaledReesAlgebraRingHom I f
  map_mem := scaledReesAlgebra_mem_grade I f

private theorem scaled_degreeOne
    (I : Ideal R) (a : I) (f : R) :
    scaledGradedHom I f (reesAlgebraDegreeOne I a) =
      reesAlgebraDegreeOne (scaledIdeal I f) (scaledElement I a f) := by
  apply Subtype.ext
  simpa [scaledGradedHom, scaledElement, reesAlgebraDegreeOne, pow_one, mul_comm,
    mul_left_comm, mul_assoc] using
    congrArg Subtype.val
      (scaledReesAlgebraRingHom_monomial I f 1 ⟨a.1, by simpa using a.2⟩)

/-- Helper for Lemma 10.70.8: the constant polynomial `r` lies in the degree-zero part of the
Rees algebra. -/
private theorem reesAlgebra_zeroDegree_mem (I : Ideal R) (r : R) :
    algebraMap R (reesAlgebra I) r ∈ reesAlgebraGrade I 0 := by
  refine ⟨⟨r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (Polynomial.monomial 0 r : R[X]) = C r
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.8: the constant polynomial `r` also lies in the degree-zero part of
the scaled Rees algebra. -/
private theorem scaledReesAlgebra_zeroDegree_mem (I : Ideal R) (f r : R) :
    algebraMap R (reesAlgebra (scaledIdeal I f)) r ∈ reesAlgebraGrade (scaledIdeal I f) 0 := by
  refine ⟨⟨r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (Polynomial.monomial 0 r : R[X]) = C r
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.8: the degree-zero Rees coefficient determined by `r`. -/
private noncomputable def reesAlgebraZeroDegreeCoeff (I : Ideal R) (r : R) :
    reesAlgebraGrade I 0 :=
  ⟨algebraMap R (reesAlgebra I) r, reesAlgebra_zeroDegree_mem I r⟩

/-- Helper for Lemma 10.70.8: the degree-zero coefficient determined by `r` in the scaled Rees
algebra. -/
private noncomputable def scaledReesAlgebraZeroDegreeCoeff
    (I : Ideal R) (f r : R) :
    reesAlgebraGrade (scaledIdeal I f) 0 :=
  ⟨algebraMap R (reesAlgebra (scaledIdeal I f)) r, scaledReesAlgebra_zeroDegree_mem I f r⟩

/-- Helper for Lemma 10.70.8: the canonical ring map from `R` into the degree-zero part of the
scaled Rees algebra. -/
private noncomputable def scaledReesAlgebraGradeZeroAlgebraMap
    (I : Ideal R) (f : R) :
    R →+* reesAlgebraGrade (scaledIdeal I f) 0 where
  toFun r := scaledReesAlgebraZeroDegreeCoeff I f r
  map_one' := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]
  map_mul' r s := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]
  map_zero' := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]
  map_add' r s := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]

/-- Helper for Lemma 10.70.8: the scaled graded map is the identity on degree-zero coefficients
coming from the base ring. -/
private theorem scaledReesAlgebra_zeroDegree_algebraMap
    (I : Ideal R) (f r : R) :
    (scaledGradedHom I f).gradedAddHom 0 (reesAlgebraZeroDegreeCoeff I r) =
      scaledReesAlgebraZeroDegreeCoeff I f r := by
  -- Both degree-zero elements are represented by the same constant polynomial `C r`.
  apply Subtype.ext
  ext n
  by_cases hn : n = 0
  · subst hn
    simp [scaledGradedHom, scaledReesAlgebraRingHom, reesAlgebraZeroDegreeCoeff,
      scaledReesAlgebraZeroDegreeCoeff]
  · simp [scaledGradedHom, scaledReesAlgebraRingHom, reesAlgebraZeroDegreeCoeff,
      scaledReesAlgebraZeroDegreeCoeff]

/-- Helper for Lemma 10.70.8: a homogeneous-localization map sends a degree-zero fraction `r / 1`
to the corresponding degree-zero fraction after applying the graded map on degree zero. -/
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
  ext
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- Helper for Lemma 10.70.8: `Away.map` preserves the degree-zero algebra map. -/
private theorem away_map_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ι → τ) [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (f : A) (a : 𝒜 0) :
    HomogeneousLocalization.Away.map g f
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) a) =
      HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (g f))
        (g.gradedAddHom 0 a) := by
  simpa [HomogeneousLocalization.Away.map] using
    homogeneousLocalization_map_fromZeroRingHom 𝒜 ℬ g
      (P := Submonoid.powers f) (Q := Submonoid.powers (g f))
      (by
        intro x hx
        rcases hx with ⟨n, rfl⟩
        exact ⟨n, by simp⟩)
      a

/-- Helper for Lemma 10.70.8: transporting a function along a codomain equality commutes with
evaluation at a point. -/
private theorem cast_fun_apply
    {α : Type u} {β γ : Type v} (h : β = γ) (f : α → β) (x : α) :
    cast (congrArg (fun t ↦ α → t) h) f x = cast h (f x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: transporting a homogeneous-localization ring homomorphism along an
equality of the inverted degree-one parameter commutes with evaluation. -/
private theorem cast_awayRingHom_apply
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {d : ι} {f g : 𝒜 d} {S : Type*} [CommRing S]
    (h : f = g) (φ : S →+* Away 𝒜 (f : A)) (x : S) :
    cast (congrArg (fun y : 𝒜 d ↦ S →+* Away 𝒜 (y : A)) h) φ x =
      cast (congrArg (fun y : 𝒜 d ↦ Away 𝒜 (y : A)) h) (φ x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: transporting a function along a domain equality commutes with
evaluation after transporting the input. -/
private theorem cast_fun_dom_apply
    {α β : Type u} {γ : Type v} (h : α = β) (f : β → γ) (x : α) :
    cast (congrArg (fun t ↦ t → γ) h.symm) f x = f (cast h x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: transporting an away-chart element along an equality of chart
parameters transports its ordinary localization value along the induced equality of localizations.
-/
private theorem cast_away_val
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {f g : A} (h : f = g) (x : Away 𝒜 f) :
    HomogeneousLocalization.val (cast (congrArg (fun y ↦ Away 𝒜 y) h) x) =
      cast (congrArg (fun y ↦ Localization.Away y) h) (HomogeneousLocalization.val x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: the same transport formula for `Away` values when the chart
parameter equality comes from equality inside a graded piece. -/
private theorem cast_away_val_subtype
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f g : 𝒜 d} (h : f = g) (x : Away 𝒜 (f : A)) :
    HomogeneousLocalization.val (cast (congrArg (fun y : 𝒜 d ↦ Away 𝒜 (y : A)) h) x) =
      cast (congrArg (fun y : 𝒜 d ↦ Localization.Away (y : A)) h)
        (HomogeneousLocalization.val x) := by
  simpa using cast_away_val 𝒜 (congrArg Subtype.val h) x

/-- Helper for Lemma 10.70.8: transporting a standard away-localization fraction along an
equality of inverted elements only changes the recorded denominator data. -/
private theorem cast_localizationAway_mk
    {A : Type*} [CommRing A] {f g r s t : A} (h : f = g) (hst : s = t)
    (hs : s ∈ Submonoid.powers f) (ht : t ∈ Submonoid.powers g) :
    cast (congrArg (fun y ↦ Localization.Away y) h) (Localization.mk r ⟨s, hs⟩) =
      Localization.mk r ⟨t, ht⟩ := by
  cases h
  cases hst
  rfl

/-- Helper for Lemma 10.70.8: the raw codomain of the scaled chart map agrees with the standard
scaled affine blowup chart after rewriting the degree-one parameter. -/
private theorem scaled_chart_codomain_eq
    (I : Ideal R) (a : I) (f : R) :
    Away (reesAlgebraGrade (scaledIdeal I f))
      ((scaledGradedHom I f) (reesAlgebraDegreeOne I a)) =
      affineBlowupChart (scaledIdeal I f) (scaledElement I a f) := by
  simpa [affineBlowupChart] using
    congrArg
      (fun y ↦ Away (reesAlgebraGrade (scaledIdeal I f)) y)
      (scaled_degreeOne I a f)

/-- Helper for Lemma 10.70.8: the raw codomain of the scaled chart map before transport. -/
private abbrev scaledChartRaw
    (I : Ideal R) (a : I) (f : R) :=
  Away (reesAlgebraGrade (scaledIdeal I f))
    ((scaledGradedHom I f) (reesAlgebraDegreeOne I a))

/-- Helper for Lemma 10.70.8: the target scaled affine blowup chart. -/
private abbrev scaledChartTarget
    (I : Ideal R) (a : I) (f : R) :=
  affineBlowupChart (scaledIdeal I f) (scaledElement I a f)

/-- Helper for Lemma 10.70.8: the raw degree-zero class in the scaled chart before transport. -/
private noncomputable def scaledChartRawZeroDegreeClass
    (I : Ideal R) (a : I) (f r : R) :
    scaledChartRaw I a f :=
  HomogeneousLocalization.fromZeroRingHom
    (reesAlgebraGrade (scaledIdeal I f))
    (Submonoid.powers ((scaledGradedHom I f) (reesAlgebraDegreeOne I a)))
    (scaledReesAlgebraZeroDegreeCoeff I f r)

/-- Helper for Lemma 10.70.8: the raw scaled-chart codomain carries the canonical homogeneous
localization ring structure. -/
private noncomputable instance scaledAffineBlowupChartRawCommRing
    (I : Ideal R) (a : I) (f : R) :
    CommRing (scaledChartRaw I a f) :=
  HomogeneousLocalization.homogeneousLocalizationCommRing

/-- Helper for Lemma 10.70.8: the raw scaled chart compares to the ordinary localization
`R_(fa)` by transporting the standard target-chart comparison map back along
`scaled_chart_codomain_eq`. -/
private noncomputable def scaledChartRawToLocalizationAway
    (I : Ideal R) (a : I) (f : R) :
    scaledChartRaw I a f → Localization.Away (f * a.1) :=
  fun y ↦ affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
    (cast (scaled_chart_codomain_eq I a f) y)

/-- Helper for Lemma 10.70.8: evaluating the transported raw comparison map is the same as first
transporting the raw chart element into the standard scaled chart. -/
private theorem scaledChartRawToLocalizationAway_cast
    (I : Ideal R) (a : I) (f : R) (y : scaledChartRaw I a f) :
    scaledChartRawToLocalizationAway I a f y =
      affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
        (cast (scaled_chart_codomain_eq I a f) y) := by
  rfl

/-- Helper for Lemma 10.70.8: the underlying ring homomorphism of the scaled chart map. -/
private noncomputable def affineBlowupChartScaledMap_toRingHom
    (I : Ideal R) (a : I) (f : R) :
    affineBlowupChart I a →+*
      affineBlowupChart (Ideal.span ({f} : Set R) * I)
        ⟨f * a.1, Ideal.mul_mem_mul (Ideal.subset_span (by simp)) a.2⟩ :=
  Eq.mp
    (congrArg
      (fun x ↦ affineBlowupChart I a →+* Away (reesAlgebraGrade (scaledIdeal I f)) x)
      (scaled_degreeOne I a f))
    (HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a))

/-- Helper for Lemma 10.70.8: before transporting the codomain along `scaled_degreeOne`, the raw
homogeneous-localization map already commutes with the base-ring algebra map. -/
private theorem affineBlowupChartScaledMap_raw_commutes
    (I : Ideal R) (a : I) (f r : R) :
    let Araw :=
      Away (reesAlgebraGrade (scaledIdeal I f))
        ((scaledGradedHom I f) (reesAlgebraDegreeOne I a))
    let ψ : affineBlowupChart I a →+* Araw :=
      HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
    ψ (algebraMap R (affineBlowupChart I a) r) =
      HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade (scaledIdeal I f))
        (Submonoid.powers ((scaledGradedHom I f) (reesAlgebraDegreeOne I a)))
        (scaledReesAlgebraZeroDegreeCoeff I f r) := by
  let Araw :=
    Away (reesAlgebraGrade (scaledIdeal I f))
      ((scaledGradedHom I f) (reesAlgebraDegreeOne I a))
  letI : CommRing Araw := HomogeneousLocalization.homogeneousLocalizationCommRing
  let ψ : affineBlowupChart I a →+* Araw :=
    HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
  -- Compute the raw `Away.map` on the degree-zero class `r / 1` before introducing any casts.
  simpa [Araw, ψ, RingHom.algebraMap_toAlgebra,
    scaledReesAlgebra_zeroDegree_algebraMap I f r] using
    (away_map_fromZeroRingHom (𝒜 := reesAlgebraGrade I)
      (ℬ := reesAlgebraGrade (scaledIdeal I f)) (scaledGradedHom I f)
      (reesAlgebraDegreeOne I a) (reesAlgebraZeroDegreeCoeff I r))

/-- Helper for Lemma 10.70.8: applying the transported scaled chart map is the same as applying
the raw `Away.map` and transporting the resulting codomain element. -/
private theorem affineBlowupChartScaledMap_toRingHom_apply
    (I : Ideal R) (a : I) (f : R) (x : affineBlowupChart I a) :
    affineBlowupChartScaledMap_toRingHom I a f x =
      cast (scaled_chart_codomain_eq I a f)
        ((HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)) x) := by
  -- TODO: prove this by specializing `cast_awayRingHom_apply` after freezing the exact
  -- `Eq.mp` proof used in `affineBlowupChartScaledMap_toRingHom`; the remaining blocker is
  -- aligning that proof with `scaled_chart_codomain_eq` without triggering `whnf` timeout.
  sorry

/-- Helper for Lemma 10.70.8: transporting the raw degree-zero scalar class preserves its
ordinary-localization value. -/
private theorem scaledChartRawZeroDegreeClass_val_transport
    (I : Ideal R) (a : I) (f r : R) :
    HomogeneousLocalization.val
        (cast (scaled_chart_codomain_eq I a f) (scaledChartRawZeroDegreeClass I a f r)) =
      HomogeneousLocalization.val (algebraMap R (scaledChartTarget I a f) r) := by
  -- TODO: push the chart cast to `Localization.Away` via `cast_away_val_subtype`, then identify
  -- the resulting degree-zero fraction with the target `algebraMap`; the blocker is expressing
  -- the localization-side cast with the exact proof term Lean expects.
  sorry

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
  -- TODO: first transport the raw class to `Localization.Away` with `cast_away_val_subtype`,
  -- then rewrite the numerator by `scaledReesAlgebraRingHom_monomial`; the remaining blocker is
  -- the proof-term alignment for the denominator cast after transport.
  sorry

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

/-- Lemma 10.70.8 (Stacks tag `0BBI`): the scaled map `R[I/a] → R[fI/(fa)]` is surjective, and
its kernel consists exactly of the elements annihilated by some power of the image of `f`. -/
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
