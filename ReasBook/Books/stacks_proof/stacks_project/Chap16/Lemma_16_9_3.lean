import Mathlib
import stacks_proof.stacks_project.Chap16.Lemma_16_2_8
import stacks_proof.stacks_project.Chap16.Lemma_16_3_7
import stacks_proof.stacks_project.Chap16.Lemma_16_3_4
import stacks_proof.stacks_project.Chap16.Lemma_16_6_1
import stacks_proof.stacks_project.Chap16.Lemma_16_9_2
import stacks_proof.stacks_project.Chap16.Situation_16_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

open PrimeSpectrum
open IsLocalization
open scoped SingularIdealNotation

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]

section Prime

variable (q : PrimeSpectrum Λ)

/- Domain-style sampling:
- primary domain: localized commutative algebra and finite-presentation resolution data;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `resolvableAtPrime_iff`,
  `Localization.AtPrime`,
  `PrimeSpectrum.asIdeal`;
- best owner abstraction: the localized source condition in Lemma `16.9.3` is the existing owner
  `ResolvableAtPrime`, specialized to `R_𝔭 → A_𝔭 → Λ_𝔮 ⊃ 𝔮Λ_𝔮`, with the prime carried
  canonically by `q : PrimeSpectrum Λ`;
- primitive vs. derived: the primitive data are the localized rings and the prime-spectrum point
  `q`; the localized target prime `𝔮Λ_𝔮` and all algebra structures are derived from that owner
  object rather than reconstructed through a theorem-local `let` block.

Source/core/bridge triage:
- `source-facing`: the localized resolution hypothesis in the Stacks statement;
- `core/canonical`: `ResolvableAtPrime` on the localized rings;
- `bridge/view`: the local notation identifying the localized base ring, algebra, target ring, and
  target prime ideal from `q : PrimeSpectrum Λ`.
-/

local notation "Rₚ" => Localization.AtPrime (q.asIdeal.under R)
local notation "Sₚ" => Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R))
local notation "Aₚ" => Localization Sₚ
local notation "Λ_𝔮" => Localization.AtPrime q.asIdeal
local notation "𝔮Λ_𝔮" => Ideal.map (algebraMap Λ Λ_𝔮) q.asIdeal

private theorem localizedTargetSubmonoid_le :
    Algebra.algebraMapSubmonoid Λ (Ideal.primeCompl (q.asIdeal.under R)) ≤ q.asIdeal.primeCompl := by
  rintro _ ⟨r, hr, rfl⟩
  simpa [Ideal.primeCompl, Ideal.mem_comap] using hr

private theorem localizedSubmonoid_le :
    Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R)) ≤
      Submonoid.comap (algebraMap A Λ) q.asIdeal.primeCompl := by
  intro a ha
  exact localizedTargetSubmonoid_le q <|
    (Algebra.algebraMapSubmonoid_le_comap (Ideal.primeCompl (q.asIdeal.under R))
      (IsScalarTower.toAlgHom R A Λ)) ha

noncomputable instance : Algebra Aₚ Λ_𝔮 := by
  have hSubmonoid : Sₚ ≤ Submonoid.comap (algebraMap A Λ) q.asIdeal.primeCompl :=
    localizedSubmonoid_le q
  exact
    RingHom.toAlgebra <| IsLocalization.map Λ_𝔮 (algebraMap A Λ) hSubmonoid

instance : IsScalarTower Rₚ Aₚ Λ_𝔮 := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (Ideal.primeCompl (q.asIdeal.under R)) x
  have hSubmonoid : Sₚ ≤ Submonoid.comap (algebraMap A Λ) q.asIdeal.primeCompl :=
    localizedSubmonoid_le q
  have hsA : algebraMap R A ↑s ∈ Sₚ := by
    exact ⟨↑s, s.2, rfl⟩
  have hsΛ : algebraMap R Λ ↑s ∈ q.asIdeal.primeCompl := by
    change ↑s ∉ q.asIdeal.under R
    exact s.2
  change algebraMap Rₚ Λ_𝔮 (IsLocalization.mk' Rₚ r s) =
    algebraMap Aₚ Λ_𝔮 (algebraMap Rₚ Aₚ (IsLocalization.mk' Rₚ r s))
  have hAp :
      algebraMap Rₚ Aₚ (IsLocalization.mk' Rₚ r s) =
        IsLocalization.mk' Aₚ (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩ :=
    by simpa using IsLocalization.algebraMap_mk' A Rₚ Aₚ r s
  have hRq :
      algebraMap Rₚ Λ_𝔮 (IsLocalization.mk' Rₚ r s) =
        IsLocalization.mk' Λ_𝔮 (algebraMap R Λ r) ⟨algebraMap R Λ ↑s, hsΛ⟩ := by
    refine (Localization.localRingHom_mk' (q.asIdeal.under R) q.asIdeal (algebraMap R Λ) rfl r s)
      |>.trans ?_
    congr 1
  rw [hAp, hRq]
  have hMap :
      algebraMap Aₚ Λ_𝔮 (IsLocalization.mk' Aₚ (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩) =
        IsLocalization.mk' Λ_𝔮 (algebraMap R Λ r) ⟨algebraMap R Λ ↑s, hsΛ⟩ := by
    change
      IsLocalization.map Λ_𝔮 (algebraMap A Λ) hSubmonoid
          (IsLocalization.mk' Aₚ (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩) =
        _
    simpa [IsScalarTower.algebraMap_eq R A Λ] using
      IsLocalization.map_mk' hSubmonoid
        (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩
  simp [hMap]

variable [FinitePresentation R A]

/-- Helper for Lemma 16.9.3: in the local ring `Λ_𝔮`, any ideal that is not contained in the
maximal ideal is already the unit ideal. -/
private theorem ideal_eq_top_of_not_le_localizedPrime
    (I : Ideal Λ_𝔮) (hI : ¬ I ≤ 𝔮Λ_𝔮) : I = ⊤ := by
  -- In a local ring, every proper ideal is contained in the maximal ideal.
  by_contra hne
  exact hI (IsLocalRing.le_maximalIdeal (J := I) hne)

/-- Helper for Lemma 16.9.3: a local resolution over `Λ_𝔮` first yields a smooth
factorization of `A_𝔭 → Λ_𝔮`. -/
private theorem exists_localSmoothFactorization_of_resolvableAtPrimeAtLocalPrime
    [FinitePresentation Rₚ Aₚ] (hresolve : ResolvableAtPrime Rₚ Aₚ Λ_𝔮 𝔮Λ_𝔮) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra Rₚ B) (_ : Smooth Rₚ B)
      (f : Aₚ →ₐ[Rₚ] B) (g : B →ₐ[Rₚ] Λ_𝔮),
      g.comp f = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮 := by
  -- Unpack the local resolution witness so the target singular ideal can be smoothed out.
  obtain ⟨B', hB'CommRing, hB'Alg, hB'fp, f', g', hcomp', -, hg'notle⟩ :=
    (resolvableAtPrime_iff (R := Rₚ) (A := Aₚ) (Λ := Λ_𝔮) 𝔮Λ_𝔮).1 hresolve
  letI : CommRing B' := hB'CommRing
  letI : Algebra Rₚ B' := hB'Alg
  letI : FinitePresentation Rₚ B' := hB'fp
  have hsingTop : g'.singularIdealIn Rₚ = ⊤ := by
    -- The target ring is local, so noncontainment in the maximal ideal forces the unit ideal.
    exact ideal_eq_top_of_not_le_localizedPrime (q := q) (I := g'.singularIdealIn Rₚ) hg'notle
  have hmapTop : Ideal.map g' (H[B'⁄Rₚ]) = ⊤ := by
    -- Rewrite the target singular ideal back to the mapped source singular ideal.
    rw [RingHom.singularIdealIn] at hsingTop
    exact Ideal.radical_eq_top.mp hsingTop
  obtain ⟨C, hCCommRing, hCAlg, hCSmooth, i, g, hg⟩ :=
    exists_smooth_factorization_of_singularIdeal_map_eq_top
      (R := Rₚ) (A := B') (Λ := Λ_𝔮) g' hmapTop
  letI : CommRing C := hCCommRing
  letI : Algebra Rₚ C := hCAlg
  refine ⟨C, inferInstance, inferInstance, hCSmooth, i.comp f', g, ?_⟩
  -- Compose the refined smooth factorization with the original factorization from `Aₚ`.
  rw [AlgHom.comp_assoc, hg, hcomp']

/-- Helper for Lemma 16.9.3: a finite family of elements of `Λ_𝔮` admits one common denominator
outside `𝔮`. -/
private theorem exists_commonDenominator_of_fintype_atPrimeFamily
    {ι : Type*} [Fintype ι] (x : ι → Λ_𝔮) :
    ∃ λ₀ : q.asIdeal.primeCompl, ∃ num : ι → Λ,
      ∀ i, algebraMap Λ Λ_𝔮 (num i) = algebraMap Λ Λ_𝔮 (λ₀ : Λ) * x i := by
  classical
  let frac : ι → Λ × q.asIdeal.primeCompl := fun i ↦
    Classical.choose (IsLocalization.surj q.asIdeal.primeCompl (x i))
  have hfrac :
      ∀ i, x i * algebraMap Λ Λ_𝔮 ((frac i).2 : Λ) = algebraMap Λ Λ_𝔮 ((frac i).1) := by
    intro i
    exact Classical.choose_spec (IsLocalization.surj q.asIdeal.primeCompl (x i))
  let λ₀ : q.asIdeal.primeCompl := ∏ i, (frac i).2
  refine ⟨λ₀, fun i ↦ (frac i).1 * ↑((Finset.univ.erase i).prod fun j ↦ (frac j).2), ?_⟩
  intro i
  -- Multiply the individual denominator identity by the complementary product.
  calc
    algebraMap Λ Λ_𝔮 ((frac i).1 * ↑((Finset.univ.erase i).prod fun j ↦ (frac j).2)) =
        algebraMap Λ Λ_𝔮 ((frac i).1) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap Λ Λ_𝔮 ((frac j).2 : Λ)) := by
            simp [map_prod]
    _ = (x i * algebraMap Λ Λ_𝔮 ((frac i).2 : Λ)) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap Λ Λ_𝔮 ((frac j).2 : Λ)) := by
            rw [← hfrac i]
    _ = x i * algebraMap Λ Λ_𝔮 (λ₀ : Λ) := by
          rw [mul_assoc]
          congr 1
          calc
            algebraMap Λ Λ_𝔮 ((frac i).2 : Λ) *
                ((Finset.univ.erase i).prod fun j ↦ algebraMap Λ Λ_𝔮 ((frac j).2 : Λ)) =
              ∏ j, algebraMap Λ Λ_𝔮 ((frac j).2 : Λ) := by
                exact
                  Finset.mul_prod_erase Finset.univ
                    (fun j ↦ algebraMap Λ Λ_𝔮 ((frac j).2 : Λ)) (by simp)
            _ = algebraMap Λ Λ_𝔮 (λ₀ : Λ) := by
                  simp [λ₀, map_prod]
    _ = algebraMap Λ Λ_𝔮 (λ₀ : Λ) * x i := by
          rw [mul_comm]

/-- Helper for Lemma 16.9.3: if a finite family of target elements dies in `Λ_𝔮`, then one
element outside `𝔮` annihilates the whole family already in `Λ`. -/
private theorem exists_commonTargetAnnihilator_of_fintype_atPrimeZeroFamily
    {ι : Type*} [Fintype ι] (x : ι → Λ)
    (hx : ∀ i, algebraMap Λ Λ_𝔮 (x i) = 0) :
    ∃ μ : q.asIdeal.primeCompl, ∀ i, (μ : Λ) * x i = 0 := by
  classical
  have hkillWitness : ∀ i, ∃ s : q.asIdeal.primeCompl, (s : Λ) * x i = 0 := by
    intro i
    -- Vanishing in the localization means one denominator outside `𝔮` already kills the element.
    simpa [mul_comm] using
      (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl Λ_𝔮 (x i)).1 (hx i)
  choose s hs using hkillWitness
  let μ : q.asIdeal.primeCompl := ∏ i, s i
  refine ⟨μ, ?_⟩
  intro i
  have hμ :
      (μ : Λ) = (s i : Λ) * ((Finset.univ.erase i).prod fun j ↦ (s j : Λ)) := by
    simp [μ, Finset.mul_prod_erase, Finset.mem_univ]
  -- Multiply the single annihilator by the complementary finite product to use one common factor.
  calc
    (μ : Λ) * x i =
        ((s i : Λ) * ((Finset.univ.erase i).prod fun j ↦ (s j : Λ))) * x i := by
          rw [hμ]
    _ = ((Finset.univ.erase i).prod fun j ↦ (s j : Λ)) * ((s i : Λ) * x i) := by
          ac_rfl
    _ = 0 := by
          rw [hs i, mul_zero]

/-- Helper for Lemma 16.9.3: after the local smoothing step, one may refine further to a local
standard-smooth factorization over `R_𝔭`. -/
private theorem exists_localStandardSmoothFactorization_of_resolvableAtPrimeAtLocalPrime
    [FinitePresentation Rₚ Aₚ] (hresolve : ResolvableAtPrime Rₚ Aₚ Λ_𝔮 𝔮Λ_𝔮) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra Rₚ C) (_ : IsStandardSmooth Rₚ C)
      (f : Aₚ →ₐ[Rₚ] C) (g : C →ₐ[Rₚ] Λ_𝔮),
      g.comp f = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮 := by
  -- First extract the verified smooth local factorization over `Rₚ`.
  obtain ⟨B', hB'CommRing, hB'Alg, hB'Smooth, f', g', hcomp'⟩ :=
    exists_localSmoothFactorization_of_resolvableAtPrimeAtLocalPrime
      (R := R) (A := A) (Λ := Λ) (q := q) hresolve
  letI : CommRing B' := hB'CommRing
  letI : Algebra Rₚ B' := hB'Alg
  letI : Smooth Rₚ B' := hB'Smooth
  -- Then replace the smooth local algebra by a standard-smooth retract over `Rₚ`.
  obtain ⟨C, hCCommRing, hCAlg, hCBAlg, hTower, hCBSmooth, r, hstdC⟩ :=
    exists_smooth_retraction_standardSmooth_of_smooth (R := Rₚ) (A := B')
  letI : CommRing C := hCCommRing
  letI : Algebra Rₚ C := hCAlg
  letI : Algebra B' C := hCBAlg
  letI : IsScalarTower Rₚ B' C := hTower
  letI : Smooth B' C := hCBSmooth
  let i : B' →ₐ[Rₚ] C := IsScalarTower.toAlgHom Rₚ B' C
  let r' : C →ₐ[Rₚ] B' := AlgHom.restrictScalars Rₚ r
  have hri : r'.comp i = AlgHom.id Rₚ B' := by
    -- The retraction is `B'`-linear, so it is the identity on the image of `B'`.
    ext x
    simp [i, r']
  refine ⟨C, inferInstance, inferInstance, hstdC, i.comp f', g'.comp r', ?_⟩
  -- Compose the refined factorization through the retraction identity.
  ext x
  simp [i, r', hri, hcomp']

/-- Helper for Lemma 16.9.3: a finite family in an at-prime scalar localization shares one
common denominator from the source prime complement. -/
private theorem exists_commonDenominator_of_fintype_scalarAtPrimeFamily
    {T : Type*} [CommRing T] [Algebra R T]
    {Tₚ : Type*} [CommRing Tₚ] [Algebra R Tₚ] [Algebra T Tₚ] [IsScalarTower R T Tₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid T (Ideal.primeCompl (q.asIdeal.under R))) Tₚ]
    {ι : Type*} [Fintype ι] (x : ι → Tₚ) :
    ∃ s : Ideal.primeCompl (q.asIdeal.under R), ∃ num : ι → T,
      ∀ i, algebraMap T Tₚ (num i) = algebraMap R Tₚ (s : R) * x i := by
  classical
  let frac : ι → T × Algebra.algebraMapSubmonoid T (Ideal.primeCompl (q.asIdeal.under R)) :=
    fun i ↦
      Classical.choose (IsLocalization.surj
        (Algebra.algebraMapSubmonoid T (Ideal.primeCompl (q.asIdeal.under R))) (x i))
  have hfracMem :
      ∀ i, ((frac i).2 : T) ∈
        Algebra.algebraMapSubmonoid T (Ideal.primeCompl (q.asIdeal.under R)) :=
    fun i ↦ (frac i).2.2
  let den : ι → Ideal.primeCompl (q.asIdeal.under R) := fun i ↦
    ⟨Classical.choose ((Submonoid.mem_map).1 (hfracMem i)),
      (Classical.choose_spec ((Submonoid.mem_map).1 (hfracMem i))).1⟩
  have hden : ∀ i, algebraMap R T (den i : R) = ((frac i).2 : T) := fun i ↦
    (Classical.choose_spec ((Submonoid.mem_map).1 (hfracMem i))).2
  let s : Ideal.primeCompl (q.asIdeal.under R) := ∏ i, den i
  refine ⟨s, fun i ↦
    (frac i).1 * algebraMap R T (((Finset.univ.erase i).prod fun j ↦ (den j : R))), ?_⟩
  intro i
  -- First rewrite the chosen local denominator as the image of an element outside `q ∩ R`.
  have hfrac :
      x i * algebraMap T Tₚ ((frac i).2 : T) = algebraMap T Tₚ ((frac i).1) :=
    Classical.choose_spec (IsLocalization.surj
      (Algebra.algebraMapSubmonoid T (Ideal.primeCompl (q.asIdeal.under R))) (x i))
  have hdenMap :
      algebraMap T Tₚ ((frac i).2 : T) = algebraMap R Tₚ (den i : R) := by
    rw [← hden i]
    simp [IsScalarTower.algebraMap_eq R T Tₚ]
  have hprod :
      algebraMap T Tₚ ((frac i).2 : T) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₚ (den j : R)) =
        algebraMap R Tₚ (s : R) := by
    calc
      algebraMap T Tₚ ((frac i).2 : T) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₚ (den j : R))
          = algebraMap R Tₚ (den i : R) *
              ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₚ (den j : R)) := by
              rw [hdenMap]
      _ = ∏ j, algebraMap R Tₚ (den j : R) := by
            exact
              Finset.mul_prod_erase Finset.univ
                (fun j ↦ algebraMap R Tₚ (den j : R)) (by simp)
      _ = algebraMap R Tₚ (s : R) := by
            simp [s, map_prod]
  -- Then multiply the individual denominator identity by the complementary product.
  calc
    algebraMap T Tₚ
        ((frac i).1 * algebraMap R T (((Finset.univ.erase i).prod fun j ↦ (den j : R)))) =
        algebraMap T Tₚ ((frac i).1) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₚ (den j : R)) := by
            simp [map_prod, IsScalarTower.algebraMap_eq R T Tₚ]
    _ = (x i * algebraMap T Tₚ ((frac i).2 : T)) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₚ (den j : R)) := by
            rw [← hfrac]
    _ = x i * algebraMap R Tₚ (s : R) := by
          rw [mul_assoc, hprod]
    _ = algebraMap R Tₚ (s : R) * x i := by
          rw [mul_comm]

/-- Helper for Lemma 16.9.3: a local standard-smooth chart can be normalized so that the first
distinguished variables are the frozen generators of `A`. -/
private theorem exists_normalizedAtPrimeSubmersivePresentation
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ] [IsStandardSmooth Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) :
    ∃ (c m : ℕ) (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
      (h : Presentation.ofFinitePresentationVars R A ≤ c),
      Q.map = Sum.inl ∧
        ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
          Q.val (.inl (Fin.castLE h i)) =
            fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)) := by
  -- Freeze the generator family coming from the chosen finite presentation of `A`.
  simpa using
    (IsStandardSmooth.exists_submersivePresentation_with_prescribed_family
      (R := Rₚ) (A := Cₚ)
      (β := fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i))))

/-- Helper for Lemma 16.9.3: a finite family of localized polynomial relations over `R_𝔭`
admits one common denominator outside `q ∩ R`. -/
private theorem exists_commonDenominator_of_fintype_atPrimePolynomialFamily
    {σ ι : Type*} [Fintype ι] (u : ι → MvPolynomial σ Rₚ) :
    ∃ s : Ideal.primeCompl (q.asIdeal.under R), ∃ uLift : ι → MvPolynomial σ R,
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (uLift i) =
        algebraMap R (MvPolynomial σ Rₚ) (s : R) * u i := by
  -- View `MvPolynomial σ Rₚ` as the scalar localization of `MvPolynomial σ R`.
  simpa using
    (exists_commonDenominator_of_fintype_scalarAtPrimeFamily
      (R := R) (q := q) (T := MvPolynomial σ R) (Tₚ := MvPolynomial σ Rₚ) u)

/-- Helper for Lemma 16.9.3: only the extra normalized chart coordinates need a common
denominator in `Λ_𝔮`; the frozen source-generator block stays literal in `Λ`. -/
private theorem exists_commonDenominator_of_extraChartFamily
    {m : ℕ} (x : Fin m → Λ_𝔮) :
    ∃ λ₀ : q.asIdeal.primeCompl, ∃ num : Fin m → Λ,
      ∀ i, algebraMap Λ Λ_𝔮 (num i) = algebraMap Λ Λ_𝔮 (λ₀ : Λ) * x i := by
  -- Restrict the generic finite-family denominator package to the genuinely extra chart block.
  simpa using
    (exists_commonDenominator_of_fintype_atPrimeFamily
      (R := R) (A := A) (Λ := Λ) (q := q) x)

/-- Helper for Lemma 16.9.3: the distinguished tail of the normalized `.inl` chart block also
admits one common denominator outside `𝔮`. -/
private theorem exists_commonDenominator_of_distinguishedTailChartFamily
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c) :
    ∃ λ₁ : q.asIdeal.primeCompl,
      ∃ tailLift : Fin (c - Presentation.ofFinitePresentationVars R A) → Λ,
        ∀ i,
          algebraMap Λ Λ_𝔮 (tailLift i) =
            algebraMap Λ Λ_𝔮 (λ₁ : Λ) *
              gₚ (Q.val (.inl (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i))) := by
  let tailValue : Fin (c - Presentation.ofFinitePresentationVars R A) → Λ_𝔮 :=
    fun i ↦ gₚ (Q.val (.inl (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i)))
  obtain ⟨λ₁, tailLift, hTailLift⟩ :=
    exists_commonDenominator_of_fintype_atPrimeFamily
      (R := R) (A := A) (Λ := Λ) (q := q) tailValue
  refine ⟨λ₁, tailLift, ?_⟩
  intro i
  -- The generic denominator package now specializes to the distinguished tail coordinates.
  simpa [tailValue] using hTailLift i

/-- Helper for Lemma 16.9.3: the cleared global chart quotient cut out only by the lifted local
relations. -/
private noncomputable abbrev clearedChartQuotient {c m : ℕ}
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) : Type u :=
  MvPolynomial (Fin c ⊕ Fin m) R ⧸ Ideal.span (Set.range relationLift)

/-- Helper for Lemma 16.9.3: the naive presentation of the cleared global chart quotient, using
the first `c` variables as the distinguished Jacobian block. -/
private noncomputable def clearedChartPresentation {c m : ℕ}
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) :
    PreSubmersivePresentation R
      (clearedChartQuotient (R := R) relationLift)
      (Fin c ⊕ Fin m) (Fin c) :=
  PreSubmersivePresentation.naive Sum.inl Sum.inl_injective
    (Function.surjInv Ideal.Quotient.mk_surjective)
    (Function.surjInv_eq Ideal.Quotient.mk_surjective)

/-- Helper for Lemma 16.9.3: localizing the cleared chart quotient away from its Jacobian class is
standard smooth over `R`. -/
private theorem standardSmoothAway_of_clearedChartPresentation
    {c m : ℕ} (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) :
    IsStandardSmooth R
      (Localization.Away
        (clearedChartPresentation (R := R) relationLift).jacobian) := by
  classical
  let P := clearedChartPresentation (R := R) relationLift
  -- Localizing away from the Jacobian adjoins exactly the inverse variable of the source proof.
  let Q :
      SubmersivePresentation
        (clearedChartQuotient (R := R) relationLift)
        (Localization.Away P.jacobian) Unit Unit :=
    SubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian
  let PQ :
      SubmersivePresentation R (Localization.Away P.jacobian)
        (Sum Unit (Fin c ⊕ Fin m)) (Sum Unit (Fin c)) :=
    { toPreSubmersivePresentation :=
        PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P
      jacobian_isUnit := by
        -- The old Jacobian becomes a unit after adjoining its inverse.
        have hP :
            IsUnit
              (algebraMap (clearedChartQuotient (R := R) relationLift)
                (Localization.Away P.jacobian) P.jacobian) :=
          IsLocalization.map_units _ (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
        have hQ : IsUnit (hP.unit • Q.jacobian) :=
          Q.jacobian_isUnit.smul hP.unit
        show IsUnit
          (PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P).jacobian
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
        convert hQ using 1
        exact Algebra.smul_def P.jacobian Q.jacobian }
  -- The composed submersive presentation is the canonical standard-smooth chart over `R`.
  simpa [P] using PQ.isStandardSmooth

/-- Helper for Lemma 16.9.3: once an ideal of an `R`-algebra dies after localizing away from
`g`, the away localization identifies with the away localization of the quotient by that ideal. -/
private noncomputable theorem localizationAway_quotient_algEquiv_of_map_eq_bot
    {B : Type*} [CommRing B] [Algebra R B] (I : Ideal B) (g : B)
    (hbot : Ideal.map (algebraMap B (Localization.Away g)) I = ⊥) :
    Localization.Away g ≃ₐ[R] Localization.Away (Ideal.Quotient.mk I g) := by
  classical
  let eQuot := Classical.choice <|
    Ideal.quotient_localizationAway_algEquiv (R := B) (I := I) (g := g)
  let eBot :
      Localization.Away g ≃ₐ[B]
        ((Localization.Away g) ⧸ Ideal.map (algebraMap B (Localization.Away g)) I) := by
    -- Once the extended ideal is zero, quotienting by it is the identity quotient.
    exact hbot ▸ (AlgEquiv.quotientBot B (Localization.Away g)).symm
  let eBotR :
      Localization.Away g ≃ₐ[R]
        ((Localization.Away g) ⧸ Ideal.map (algebraMap B (Localization.Away g)) I) :=
    AlgEquiv.restrictScalars R eBot
  let eQuotR :
      ((Localization.Away g) ⧸ Ideal.map (algebraMap B (Localization.Away g)) I) ≃ₐ[R]
        Localization.Away (Ideal.Quotient.mk I g) :=
    AlgEquiv.restrictScalars R eQuot
  -- Compose the quotient-by-`⊥` collapse with the canonical quotient/localization comparison.
  exact eBotR.trans eQuotR

/-- Helper for Lemma 16.9.3: an elementary-standard element always belongs to the singular ideal.
-/
private theorem mem_singularIdeal_of_isElementaryStandard
    {C : Type*} [CommRing C] [Algebra R C] [FinitePresentation R C] {c : C}
    (hc : IsElementaryStandard R c) :
    c ∈ H[C⁄R] := by
  -- Rewrite the singular ideal through the elementary-standard description and insert `c`.
  rw [singularIdeal_eq_radical_span_elementaryStandard]
  exact Ideal.subset_radical (Ideal.subset_span hc)

/-- Helper for Lemma 16.9.3: applying an `Rₚ`-algebra map after evaluating a polynomial in a
submersive presentation agrees with evaluating directly in the target. -/
private theorem map_submersivePresentation_aeval
    {C : Type*} [CommRing C] [Algebra Rₚ C]
    {σ τ : Type*} (Q : SubmersivePresentation Rₚ C σ τ) (g : C →ₐ[Rₚ] Λ_𝔮) :
    ∀ p : MvPolynomial σ Rₚ,
      MvPolynomial.aeval (fun i ↦ g (Q.val i)) p = g (MvPolynomial.aeval Q.val p) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      -- Constants are preserved because `g` is an `Rₚ`-algebra map.
      simpa using g.commutes a
  | add p q hp hq =>
      -- Addition commutes with both evaluation and the target algebra map.
      simpa [map_add] using congrArg₂ (fun x y ↦ x + y) hp hq
  | mul_X p i hp =>
      -- Multiplication by a variable evaluates at the chosen chart value `g (Q.val i)`.
      simpa [MvPolynomial.aeval_def, map_mul] using
        congrArg (fun x ↦ x * g (Q.val i)) hp

/-- Helper for Lemma 16.9.3: any substitution on the presentation generators that matches a fixed
`R`-algebra map kills every defining relation. -/
private theorem relation_aeval_eq_zero_of_generator_image
    {S : Type*} [CommRing S] [Algebra R S] {n m : ℕ}
    (P : Presentation R A (Fin n) (Fin m))
    (f : A →ₐ[R] S) (φ : Fin n → S)
    (hφ : ∀ i : Fin n, f (P.val i) = φ i) :
    ∀ j : Fin m, MvPolynomial.aeval φ (P.relation j) = 0 := by
  have hEval :
      ∀ p : P.Ring, f (algebraMap P.Ring A p) = MvPolynomial.aeval φ p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        -- Constants commute with every `R`-algebra map.
        simpa [P.algebraMap_apply, MvPolynomial.aeval_def] using f.commutes a
    | add p q hp hq =>
        -- Both sides preserve addition termwise.
        simpa [P.algebraMap_apply, map_add] using congrArg₂ (fun x y ↦ x + y) hp hq
    | mul_X p i hp =>
        -- Multiplication by a generator uses the prescribed image `φ i`.
        calc
          f (algebraMap P.Ring A (p * X i)) =
              f (algebraMap P.Ring A p) * f (P.val i) := by
                simp [P.algebraMap_apply, map_mul]
          _ = MvPolynomial.aeval φ p * φ i := by rw [hp, hφ i]
          _ = MvPolynomial.aeval φ (p * X i) := by
                simp [MvPolynomial.aeval_def, map_mul]
  intro j
  have hrelZero : algebraMap P.Ring A (P.relation j) = 0 := by
    -- The defining relations lie in the presentation kernel.
    simpa [P.algebraMap_apply, RingHom.mem_ker] using P.relation_mem_ker j
  -- Evaluate the relation through the fixed map and rewrite with the kernel identity.
  calc
    MvPolynomial.aeval φ (P.relation j) = f (algebraMap P.Ring A (P.relation j)) := by
      symm
      exact hEval (P.relation j)
    _ = 0 := by simp [hrelZero]

/-- Helper for Lemma 16.9.3: in the normalized local chart, the renamed defining relations of the
fixed presentation of `A` already vanish in `Cₚ` before any target-side localization step. -/
private theorem renamedSourcePresentationRelation_aeval_eq_zero_in_chart
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval Q.val
          (MvPolynomial.map (algebraMap R Rₚ)
            (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j))) = 0 := by
  intro j
  let P_A :
      Presentation R A
        (Fin (Presentation.ofFinitePresentationVars R A))
        (Fin (Presentation.ofFinitePresentationRels R A)) :=
    Presentation.ofFinitePresentation R A
  -- First move the renamed source relation back to the frozen source block of the chart.
  rw [MvPolynomial.map_rename, MvPolynomial.aeval_rename]
  -- Then apply the generic presentation relation vanishing lemma to the composed map `A → Cₚ`.
  exact
    relation_aeval_eq_zero_of_generator_image
      (R := R) (A := A) (Λ := Cₚ) P_A
      ((AlgHom.restrictScalars R fₚ).comp (algebraMap A Aₚ))
      (fun i ↦ Q.val (.inl (Fin.castLE hQ i)))
      (fun i ↦ by
        simpa [P_A] using (hQval i).symm)
      j

/-- Helper for Lemma 16.9.3: after passing only to the normalized local chart over `Rₚ`, each
renamed source relation already belongs to the span of the chart relations. -/
private theorem renamedSourcePresentationRelation_mem_localizedChartRelationSpan
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.map (algebraMap R Rₚ)
          (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            Sum.inl (Fin.castLE hQ i))
            ((Presentation.ofFinitePresentation R A).relation j)) ∈
        Ideal.span (Set.range Q.relation) := by
  intro j
  -- Rewrite kernel membership through the presentation kernel of the normalized chart.
  rw [← Q.toPreSubmersivePresentation.toPresentation.span_range_relation_eq_ker, RingHom.mem_ker]
  simpa using
    renamedSourcePresentationRelation_aeval_eq_zero_in_chart
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ Q hQ hQval j

/-- Helper for Lemma 16.9.3: after clearing coefficients, the lifted local chart relations already
vanish in `Λ_𝔮` when evaluated at the normalized chart values. -/
private theorem relationLift_aeval_eq_zero_in_localizedTarget
    {Cₚ : Type*} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    ∀ i : Fin c, MvPolynomial.aeval (fun j ↦ gₚ (Q.val j)) (relationLift i) = 0 := by
  intro i
  have hQrel :
      MvPolynomial.aeval (fun j ↦ gₚ (Q.val j)) (Q.relation i) = 0 := by
    -- First collapse evaluation through the target map and use that each presentation relation
    -- already lies in the kernel of the chart quotient map.
    calc
      MvPolynomial.aeval (fun j ↦ gₚ (Q.val j)) (Q.relation i) =
          gₚ (MvPolynomial.aeval Q.val (Q.relation i)) := by
            simpa using
              map_submersivePresentation_aeval
                (R := R) (A := A) (Λ := Λ) (q := q) Q gₚ (Q.relation i)
      _ = 0 := by
            have hker : MvPolynomial.aeval Q.val (Q.relation i) = 0 := by
              simpa [Q.algebraMap_apply, RingHom.mem_ker] using Q.relation_mem_ker i
            simp [hker]
  have hlocal :
      MvPolynomial.aeval (fun j ↦ gₚ (Q.val j))
          (MvPolynomial.map (algebraMap R Rₚ) (relationLift i)) = 0 := by
    -- Rewrite the localized lift by the cleared relation package and use the vanishing of
    -- `Q.relation i` under the normalized target values.
    calc
      MvPolynomial.aeval (fun j ↦ gₚ (Q.val j))
          (MvPolynomial.map (algebraMap R Rₚ) (relationLift i)) =
        MvPolynomial.aeval (fun j ↦ gₚ (Q.val j))
          (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) := by
            rw [hRelationLift i]
      _ = algebraMap R Λ_𝔮 (sRelation : R) *
            MvPolynomial.aeval (fun j ↦ gₚ (Q.val j)) (Q.relation i) := by
            simp [MvPolynomial.aeval_def, map_mul]
      _ = 0 := by simp [hQrel]
  -- Finally forget the intermediate coefficient localization on the cleared relation lift.
  exact
    (MvPolynomial.aeval_map_algebraMap
      (R := R) (A := Rₚ) (B := Λ_𝔮) (x := fun j ↦ gₚ (Q.val j)) (relationLift i)).symm.trans
      hlocal

/-- Helper for Lemma 16.9.3: the cleared local chart ideal is killed by evaluation in `Λ_𝔮` at
the normalized chart values. -/
private theorem clearedChartRelationIdeal_le_ker_localizedTargetEval
    {Cₚ : Type*} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    Ideal.span (Set.range relationLift) ≤
      RingHom.ker
        ((MvPolynomial.aeval (fun j ↦ gₚ (Q.val j)) :
          MvPolynomial (Fin c ⊕ Fin m) R →ₐ[R] Λ_𝔮).toRingHom) := by
  -- The span is generated by the finitely many cleared relations, and each generator vanishes.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  simpa [RingHom.mem_ker] using
    relationLift_aeval_eq_zero_in_localizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) gₚ Q sRelation relationLift hRelationLift i

/-- Helper for Lemma 16.9.3: every element of the cleared local chart ideal evaluates to zero in
`Λ_𝔮` at the normalized chart values. -/
private theorem clearedChartRelationIdeal_eval_eq_zero_localizedTarget
    {Cₚ : Type*} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i)
    {p : MvPolynomial (Fin c ⊕ Fin m) R}
    (hp : p ∈ Ideal.span (Set.range relationLift)) :
    MvPolynomial.aeval (fun j ↦ gₚ (Q.val j)) p = 0 := by
  -- Convert ideal membership in the kernel back to the required vanishing equality.
  simpa [RingHom.mem_ker] using
    (clearedChartRelationIdeal_le_ker_localizedTargetEval
      (R := R) (A := A) (Λ := Λ) (q := q) gₚ Q sRelation relationLift hRelationLift hp)

/-- Helper for Lemma 16.9.3: the cleared chart quotient still has a canonical map to the localized
target `Λ_𝔮` through the normalized chart values. -/
private noncomputable def clearedChartQuotientToLocalizedTarget
    {Cₚ : Type*} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    clearedChartQuotient (R := R) relationLift →ₐ[R] Λ_𝔮 :=
  Ideal.Quotient.liftₐ (R₁ := R) (I := Ideal.span (Set.range relationLift))
    (MvPolynomial.aeval (fun j ↦ gₚ (Q.val j)))
    ((clearedChartRelationIdeal_eval_eq_zero_localizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) gₚ Q sRelation relationLift hRelationLift))

/-- Helper for Lemma 16.9.3: on the frozen presentation generators of `A`, the normalized local
chart values agree with the localized target map coming from `A → Aₚ → Cₚ → Λ_𝔮`. -/
private theorem normalizedChartValue_eq_localizedTarget_of_sourceGenerator
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    (hfactor : gₚ.comp fₚ = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
      gₚ (Q.val (.inl (Fin.castLE hQ i))) =
        algebraMap Aₚ Λ_𝔮 (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)) := by
  intro i
  -- First rewrite the normalized chart value through the frozen source generator.
  rw [hQval i]
  -- Then collapse the composed factorization `Aₚ → Cₚ → Λ_𝔮` back to the canonical map.
  exact congrArg
    (fun h : Aₚ →ₐ[Rₚ] Λ_𝔮 =>
      h (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)))
    hfactor

/-- Helper for Lemma 16.9.3: the frozen defining relations of the fixed presentation of `A`
already vanish in `Λ_𝔮` when evaluated at the normalized local chart values. -/
private theorem sourcePresentationRelation_aeval_eq_zero_in_localizedTarget
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    (hfactor : gₚ.comp fₚ = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval
          (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            gₚ (Q.val (.inl (Fin.castLE hQ i))))
          ((Presentation.ofFinitePresentation R A).relation j) = 0 := by
  intro j
  let P_A :
      Presentation R A
        (Fin (Presentation.ofFinitePresentationVars R A))
        (Fin (Presentation.ofFinitePresentationRels R A)) :=
    Presentation.ofFinitePresentation R A
  have hvals :
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        gₚ (Q.val (.inl (Fin.castLE hQ i)))) =
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        algebraMap Aₚ Λ_𝔮 (algebraMap A Aₚ (P_A.val i))) := by
    -- The normalized chart carries the frozen source generators exactly as the local
    -- factorization `Aₚ → Cₚ → Λ_𝔮`.
    funext i
    simpa [P_A] using
      normalizedChartValue_eq_localizedTarget_of_sourceGenerator
        (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQval i
  -- Rewrite the evaluation through the canonical localized image of the presentation variables.
  rw [hvals]
  calc
    MvPolynomial.aeval
        (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
          algebraMap Aₚ Λ_𝔮 (algebraMap A Aₚ (P_A.val i)))
        (P_A.relation j)
        =
      algebraMap Aₚ Λ_𝔮
        (MvPolynomial.aeval (fun i ↦ algebraMap A Aₚ (P_A.val i)) (P_A.relation j)) := by
          symm
          simpa [P_A, IsScalarTower.algebraMap_eq R A Aₚ] using
            (MvPolynomial.aeval_map_algebraMap
              (R := R) (A := Aₚ) (B := Λ_𝔮)
              (x := fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
                algebraMap A Aₚ (P_A.val i))
              (P_A.relation j))
    _ = 0 := by
          -- The fixed presentation relations are already in the kernel of the presentation map.
          have hker :
              MvPolynomial.aeval (fun i ↦ algebraMap A Aₚ (P_A.val i)) (P_A.relation j) = 0 := by
            simpa [P_A.algebraMap_apply, RingHom.mem_ker] using P_A.relation_mem_ker j
          simp [hker]

/-- Helper for Lemma 16.9.3: after renaming the frozen presentation relations of `A` into the
full normalized chart variable set, they still vanish in `Λ_𝔮`. -/
private theorem renamedSourcePresentationRelation_aeval_eq_zero_in_localizedTarget
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    (hfactor : gₚ.comp fₚ = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval (fun i : Fin c ⊕ Fin m ↦ gₚ (Q.val i))
          (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            Sum.inl (Fin.castLE hQ i))
            ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
  intro j
  -- Evaluating a renamed source relation on the big chart is the same as evaluating the original
  -- relation on the frozen source coordinates.
  rw [MvPolynomial.aeval_rename]
  exact
    sourcePresentationRelation_aeval_eq_zero_in_localizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQval j

/-- Helper for Lemma 16.9.3: once the frozen source-generator block is kept literal in `Λ`, the
defining relations of the fixed finite presentation of `A` already vanish there. -/
private theorem sourcePresentationRelation_aeval_eq_zero_in_target
    {c m : ℕ} (λDesc : Fin c ⊕ Fin m → Λ)
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hFrozen :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        λDesc (.inl (Fin.castLE hQ i)) =
          algebraMap A Λ ((Presentation.ofFinitePresentation R A).val i)) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval
          (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            λDesc (.inl (Fin.castLE hQ i)))
          ((Presentation.ofFinitePresentation R A).relation j) = 0 := by
  intro j
  let P_A :
      Presentation R A
        (Fin (Presentation.ofFinitePresentationVars R A))
        (Fin (Presentation.ofFinitePresentationRels R A)) :=
    Presentation.ofFinitePresentation R A
  have hvals :
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        λDesc (.inl (Fin.castLE hQ i))) =
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        algebraMap A Λ (P_A.val i)) := by
    -- The frozen coordinates are exactly the images of the fixed presentation generators of `A`.
    funext i
    simpa [P_A] using hFrozen i
  -- Rewrite the evaluation through the canonical presentation variables of `A`.
  rw [hvals]
  calc
    MvPolynomial.aeval
        (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
          algebraMap A Λ (P_A.val i))
        (P_A.relation j) =
      algebraMap A Λ
        (MvPolynomial.aeval (fun i ↦ P_A.val i) (P_A.relation j)) := by
          symm
          simpa [P_A] using
            (MvPolynomial.aeval_map_algebraMap
              (R := R) (A := A) (B := Λ)
              (x := fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦ P_A.val i)
              (P_A.relation j))
    _ = 0 := by
          -- The defining relations lie in the kernel of the chosen presentation map.
          have hker :
              MvPolynomial.aeval (fun i ↦ P_A.val i) (P_A.relation j) = 0 := by
            simpa [P_A.algebraMap_apply, RingHom.mem_ker] using P_A.relation_mem_ker j
          simp [hker]

/-- Helper for Lemma 16.9.3: after renaming the frozen source relations into the enlarged global
chart, they still vanish in `Λ` as soon as the frozen block matches the actual images from `A`. -/
private theorem renamedSourcePresentationRelation_aeval_eq_zero_in_target
    {c m : ℕ} (λDesc : Fin c ⊕ Fin m → Λ)
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hFrozen :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        λDesc (.inl (Fin.castLE hQ i)) =
          algebraMap A Λ ((Presentation.ofFinitePresentation R A).val i)) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval λDesc
          (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            Sum.inl (Fin.castLE hQ i))
            ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
  intro j
  -- Evaluating the renamed relation on the big chart reduces to the literal frozen block.
  rw [MvPolynomial.aeval_rename]
  exact
    sourcePresentationRelation_aeval_eq_zero_in_target
      (R := R) (A := A) (Λ := Λ) λDesc hQ hFrozen j

/-- Helper for Lemma 16.9.3: after cutting out the cleared chart relations, the frozen source
relations of the fixed presentation of `A` generate a canonical second quotient ideal. -/
private noncomputable def sourceRelationIdealInClearedChart
    {c m : ℕ} (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) :
    Ideal (clearedChartQuotient (R := R) relationLift) :=
  Ideal.span (Set.range fun j : Fin (Presentation.ofFinitePresentationRels R A) ↦
    Ideal.Quotient.mk (Ideal.span (Set.range relationLift))
      (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        Sum.inl (Fin.castLE hQ i))
        ((Presentation.ofFinitePresentation R A).relation j)))

/-- Helper for Lemma 16.9.3: the canonical map from the cleared chart quotient to `Λ_𝔮` kills the
frozen source relations as well, so it descends through the second quotient. -/
private theorem sourceRelationIdealInClearedChart_le_ker_localizedTarget
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    (hfactor : gₚ.comp fₚ = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift ≤
      RingHom.ker
        ((clearedChartQuotientToLocalizedTarget
          (R := R) (A := A) (Λ := Λ) (q := q) gₚ Q sRelation relationLift hRelationLift).toRingHom) := by
  -- The second quotient is generated by renamed source relations, and each such generator already
  -- vanishes under the localized target evaluation on the normalized chart.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  rw [RingHom.mem_ker]
  -- Expand the descended map once, then reuse the frozen-source vanishing lemma.
  rw [clearedChartQuotientToLocalizedTarget, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simpa using
    renamedSourcePresentationRelation_aeval_eq_zero_in_localizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQval j

/-- Helper for Lemma 16.9.3: the localized target map from the cleared chart quotient descends
through the additional quotient by the frozen source relations of `A`. -/
private noncomputable def descendedChartQuotientToLocalizedTarget
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    (hfactor : gₚ.comp fₚ = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    (clearedChartQuotient (R := R) relationLift ⧸
      sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift) →ₐ[R] Λ_𝔮 :=
  Ideal.Quotient.liftₐ
    (R₁ := R)
    (I := sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift)
    (clearedChartQuotientToLocalizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) gₚ Q sRelation relationLift hRelationLift)
    (fun x hx ↦
      RingHom.mem_ker.mp <|
        sourceRelationIdealInClearedChart_le_ker_localizedTarget
          (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQval
          sRelation relationLift hRelationLift hx)

/-- Helper for Lemma 16.9.3: after multiplying by the common relation denominator `sRelation`,
each renamed frozen source relation lands in the localized ideal generated by the mapped cleared
chart relations. -/
private theorem sourceRelation_mul_mem_mappedClearedChartSpan
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) *
          MvPolynomial.map (algebraMap R Rₚ)
            (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j)) ∈
        Ideal.span (Set.range (fun i : Fin c ↦
          MvPolynomial.map (algebraMap R Rₚ) (relationLift i))) := by
  intro j
  obtain ⟨coeff, hcoeff⟩ :=
    Ideal.mem_span_range_iff_exists_fun.mp
      (renamedSourcePresentationRelation_mem_localizedChartRelationSpan
        (R := R) (A := A) (Λ := Λ) (q := q) fₚ Q hQ hQval j)
  refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨coeff, ?_⟩
  -- Proof comment: the cleared relation generators are exactly `sRelation • Q.relation i`,
  -- so the original coefficient witness can be reused after factoring out the common scalar.
  calc
    ∑ i : Fin c,
        coeff i *
          MvPolynomial.map (algebraMap R Rₚ) (relationLift i)
      =
        ∑ i : Fin c,
          coeff i *
            (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) *
              Q.relation i) := by
          simp [hRelationLift]
    _ =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) *
          ∑ i : Fin c, coeff i * Q.relation i := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) *
          MvPolynomial.map (algebraMap R Rₚ)
            (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j)) := by
          rw [hcoeff]

/-- Helper for Lemma 16.9.3: one base-ring denominator clears all renamed frozen source
relations into the ideal generated by the cleared chart relations over `R`. -/
private theorem exists_sourceRelationClearer_in_clearedChart
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    ∃ sSource : Ideal.primeCompl (q.asIdeal.under R),
      ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sSource : R) *
            MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j) ∈
          Ideal.span (Set.range relationLift) := by
  classical
  let sourceRelationRenamed :
      Fin (Presentation.ofFinitePresentationRels R A) →
        MvPolynomial (Fin c ⊕ Fin m) R := fun j ↦
      MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        Sum.inl (Fin.castLE hQ i))
        ((Presentation.ofFinitePresentation R A).relation j)
  choose coeff hcoeff using fun j :
      Fin (Presentation.ofFinitePresentationRels R A) ↦
    Ideal.mem_span_range_iff_exists_fun.mp
      (sourceRelation_mul_mem_mappedClearedChartSpan
        (R := R) (A := A) (Λ := Λ) (q := q) fₚ Q hQ hQval
        sRelation relationLift hRelationLift j)
  let coeffFamily :
      Fin (Presentation.ofFinitePresentationRels R A) × Fin c →
        MvPolynomial (Fin c ⊕ Fin m) Rₚ := fun ji ↦ coeff ji.1 ji.2
  obtain ⟨sCoeff, coeffLiftFamily, hcoeffLiftFamily⟩ :=
    exists_commonDenominator_of_fintype_atPrimePolynomialFamily
      (R := R) (A := A) (Λ := Λ) (q := q) (u := coeffFamily)
  let coeffLift :
      Fin (Presentation.ofFinitePresentationRels R A) → Fin c →
        MvPolynomial (Fin c ⊕ Fin m) R := fun j i ↦ coeffLiftFamily ⟨j, i⟩
  have hcoeffLift :
      ∀ j i,
        MvPolynomial.map (algebraMap R Rₚ) (coeffLift j i) =
          algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sCoeff : R) * coeff j i := by
    intro j i
    simpa [coeffLift, coeffFamily] using hcoeffLiftFamily ⟨j, i⟩
  let residual :
      Fin (Presentation.ofFinitePresentationRels R A) →
        MvPolynomial (Fin c ⊕ Fin m) R := fun j ↦
      algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) ((sCoeff : R) * (sRelation : R)) *
          sourceRelationRenamed j -
        ∑ i : Fin c, coeffLift j i * relationLift i
  have hresidualMapZero :
      ∀ j,
        MvPolynomial.map (algebraMap R Rₚ) (residual j) = 0 := by
    intro j
    -- Proof comment: clear the coefficient family first, then compare with the localized ideal
    -- expression already known for the renamed source relation.
    calc
      MvPolynomial.map (algebraMap R Rₚ) (residual j)
        =
          algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sCoeff : R) *
              (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) *
                MvPolynomial.map (algebraMap R Rₚ) (sourceRelationRenamed j)) -
            algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sCoeff : R) *
              ∑ i : Fin c,
                coeff j i *
                  MvPolynomial.map (algebraMap R Rₚ) (relationLift i) := by
            simp [residual, sourceRelationRenamed, coeffLift, hcoeffLift,
              map_sum, map_mul, Finset.mul_sum, sub_eq_add_neg, mul_assoc, mul_left_comm,
              mul_comm, add_comm, add_left_comm, add_assoc]
      _ = 0 := by
            rw [hcoeff j]
            ring
  choose residualDen hresidualSingle using fun j :
      Fin (Presentation.ofFinitePresentationRels R A) ↦ by
    obtain ⟨u, hu⟩ :=
      (IsLocalization.map_eq_zero_iff
        (Algebra.algebraMapSubmonoid
          (MvPolynomial (Fin c ⊕ Fin m) R) (Ideal.primeCompl (q.asIdeal.under R)))
        (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (residual j)).mp (hresidualMapZero j)
    let s : Ideal.primeCompl (q.asIdeal.under R) :=
      ⟨Classical.choose ((Submonoid.mem_map).1 u.2),
        (Classical.choose_spec ((Submonoid.mem_map).1 u.2)).1⟩
    have hs :
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (s : R) =
          ((u : Algebra.algebraMapSubmonoid
            (MvPolynomial (Fin c ⊕ Fin m) R) (Ideal.primeCompl (q.asIdeal.under R))) :
            MvPolynomial (Fin c ⊕ Fin m) R) := by
      exact (Classical.choose_spec ((Submonoid.mem_map).1 u.2)).2
    refine ⟨s, ?_⟩
    -- Proof comment: every localization annihilator for a residual identity comes from a base-ring
    -- denominator because the scalar localization is built from `R`.
    simpa [hs] using hu
  let sEq : Ideal.primeCompl (q.asIdeal.under R) :=
    ∏ j : Fin (Presentation.ofFinitePresentationRels R A), residualDen j
  have hresidualClear :
      ∀ j,
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sEq : R) * residual j = 0 := by
    intro j
    have hsingle := hresidualSingle j
    -- Proof comment: multiply the one-relation annihilator by the complementary finite product
    -- to obtain a single denominator valid for every renamed source relation at once.
    calc
      algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sEq : R) * residual j
        =
          ((Finset.univ.erase j).prod
              fun k : Fin (Presentation.ofFinitePresentationRels R A) ↦
                algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (residualDen k : R)) *
            (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (residualDen j : R) *
              residual j) := by
            calc
              algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sEq : R) * residual j
                =
                  (∏ k : Fin (Presentation.ofFinitePresentationRels R A),
                      algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R)
                        (residualDen k : R)) * residual j := by
                    simp [sEq, map_prod]
              _ =
                  (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (residualDen j : R) *
                      (∏ k in Finset.univ.erase j,
                        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R)
                          (residualDen k : R))) * residual j := by
                    congr 1
                    symm
                    exact
                      Finset.mul_prod_erase Finset.univ
                        (fun k : Fin (Presentation.ofFinitePresentationRels R A) ↦
                          algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R)
                            (residualDen k : R)) (by simp)
              _ =
                  ((Finset.univ.erase j).prod
                      fun k : Fin (Presentation.ofFinitePresentationRels R A) ↦
                        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R)
                          (residualDen k : R)) *
                    (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (residualDen j : R) *
                      residual j) := by
                    ring
      _ = 0 := by simp [hsingle]
  let sSource : Ideal.primeCompl (q.asIdeal.under R) := sEq * sCoeff * sRelation
  refine ⟨sSource, ?_⟩
  intro j
  refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨
    fun i : Fin c ↦ algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sEq : R) * coeffLift j i,
    ?_⟩
  -- Proof comment: expand the uniformly cleared residual identity and move the finite sum to the
  -- other side; this produces the desired `R`-linear combination of the cleared chart relations.
  have hclear := hresidualClear j
  have hrewrite :
      algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sSource : R) *
          sourceRelationRenamed j =
        ∑ i : Fin c,
          (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sEq : R) * coeffLift j i) *
            relationLift i := by
    have hclear' :
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sEq : R) * residual j =
          algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sSource : R) *
              sourceRelationRenamed j -
            ∑ i : Fin c,
              (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sEq : R) * coeffLift j i) *
                relationLift i := by
      simp [residual, sSource, sourceRelationRenamed, Finset.mul_sum, sub_eq_add_neg,
        mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc]
    rw [hclear'] at hclear
  exact sub_eq_zero.mp hclear
  simpa [sourceRelationRenamed] using hrewrite

/-- Helper for Lemma 16.9.3: after localizing the cleared chart quotient away from the source
relation clearer, the extra quotient by the frozen source relations disappears. -/
private theorem sourceRelationIdeal_map_eq_bot_awaySourceClearer
    {c m : ℕ} (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (sSource : Ideal.primeCompl (q.asIdeal.under R))
    (hsSource :
      ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sSource : R) *
            MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j) ∈
          Ideal.span (Set.range relationLift)) :
    Ideal.map
        (algebraMap (clearedChartQuotient (R := R) relationLift)
          (Localization.Away
            (algebraMap R (clearedChartQuotient (R := R) relationLift) (sSource : R))))
        (sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift) = ⊥ := by
  let B := clearedChartQuotient (R := R) relationLift
  let locMap :
      B →ₐ[R] Localization.Away (algebraMap R B (sSource : R)) :=
    algebraMap B (Localization.Away (algebraMap R B (sSource : R)))
  apply bot_unique
  rw [Ideal.map_le_iff_le_comap]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  rw [Ideal.mem_comap, Submodule.mem_bot]
  have hclear :
      algebraMap R B (sSource : R) *
          Ideal.Quotient.mk (Ideal.span (Set.range relationLift))
            (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
    -- The chosen source-clearer annihilates every renamed source relation in the cleared quotient.
    calc
      algebraMap R B (sSource : R) *
          Ideal.Quotient.mk (Ideal.span (Set.range relationLift))
            (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j)) =
        Ideal.Quotient.mk (Ideal.span (Set.range relationLift))
          (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sSource : R) *
            MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j)) := by
            simp [B, map_mul]
      _ = 0 := by
            simpa [B, Ideal.Quotient.eq_zero_iff_mem] using hsSource j
  have hunit :
      IsUnit (locMap (algebraMap R B (sSource : R))) := by
    -- The source-clearer is inverted by the away localization built from it.
    exact
      IsLocalization.map_units _
        (⟨algebraMap R B (sSource : R), 1, by simp⟩ :
          Submonoid.powers (algebraMap R B (sSource : R)))
  have hmul :
      locMap (algebraMap R B (sSource : R)) *
          locMap
            (Ideal.Quotient.mk (Ideal.span (Set.range relationLift))
              (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
                Sum.inl (Fin.castLE hQ i))
                ((Presentation.ofFinitePresentation R A).relation j))) = 0 := by
    -- Apply the localization map to the annihilation identity in the cleared quotient.
    simpa [locMap, map_mul] using congrArg locMap hclear
  rcases hunit with ⟨u, hu⟩
  have hmulUnit :
      (u : Localization.Away (algebraMap R B (sSource : R))) *
          locMap
            (Ideal.Quotient.mk (Ideal.span (Set.range relationLift))
              (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
                Sum.inl (Fin.castLE hQ i))
                ((Presentation.ofFinitePresentation R A).relation j))) = 0 := by
    simpa [hu] using hmul
  have hcancel := congrArg
      (fun z : Localization.Away (algebraMap R B (sSource : R)) ↦ (↑u⁻¹) * z) hmulUnit
  -- Cancel the now-invertible source-clearer by multiplying with the explicit inverse unit.
  simpa [mul_assoc] using hcancel

/-- Helper for Lemma 16.9.3: localizing away from the source-clearer identifies the cleared chart
quotient with the corresponding away localization of its descended quotient by the frozen source
relations. -/
private noncomputable theorem localizationAway_sourceClearerQuotient_algEquiv
    {c m : ℕ} (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (sSource : Ideal.primeCompl (q.asIdeal.under R))
    (hsSource :
      ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) R) (sSource : R) *
            MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j) ∈
          Ideal.span (Set.range relationLift)) :
    Localization.Away
        (algebraMap R (clearedChartQuotient (R := R) relationLift) (sSource : R)) ≃ₐ[R]
      Localization.Away
        (Ideal.Quotient.mk
          (sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift)
          (algebraMap R (clearedChartQuotient (R := R) relationLift) (sSource : R))) := by
  -- The away localization only remembers the quotient once the extra source ideal has vanished.
  exact
    localizationAway_quotient_algEquiv_of_map_eq_bot
      (R := R)
      (B := clearedChartQuotient (R := R) relationLift)
      (I := sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift)
      (g := algebraMap R (clearedChartQuotient (R := R) relationLift) (sSource : R))
      (sourceRelationIdeal_map_eq_bot_awaySourceClearer
        (R := R) (A := A) (Λ := Λ) (q := q) hQ relationLift sSource hsSource)

/-- Helper for Lemma 16.9.3: the Jacobian unit on the normalized local chart admits one target
denominator outside `𝔮` that clears its inverse back in `Λ`. -/
private theorem exists_targetDenominator_mul_jacobian_eq
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ]
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮) :
    ∃ μ : q.asIdeal.primeCompl, ∃ η : Λ,
      algebraMap Λ Λ_𝔮 η * gₚ Q.jacobian = algebraMap Λ Λ_𝔮 (μ : Λ) := by
  -- First rewrite the Jacobian image as a unit in the localized target.
  obtain ⟨u, hu⟩ : ∃ u : Units Λ_𝔮, (u : Λ_𝔮) = gₚ Q.jacobian := by
    rcases (Q.jacobian_isUnit.map gₚ) with ⟨u, hu⟩
    exact ⟨u, hu⟩
  obtain ⟨μ, num, hnum⟩ :=
    exists_commonDenominator_of_fintype_atPrimeFamily
      (R := R) (A := A) (Λ := Λ) (q := q)
      (ι := Unit) (fun _ : Unit ↦ (↑u⁻¹ : Λ_𝔮))
  refine ⟨μ, num (), ?_⟩
  -- Then multiply the cleared inverse relation by the Jacobian itself.
  calc
    algebraMap Λ Λ_𝔮 (num ()) * gₚ Q.jacobian =
        (algebraMap Λ Λ_𝔮 (μ : Λ) * (↑u⁻¹ : Λ_𝔮)) * gₚ Q.jacobian := by
          rw [hnum ()]
    _ = (algebraMap Λ Λ_𝔮 (μ : Λ) * (↑u⁻¹ : Λ_𝔮)) * ↑u := by rw [← hu]
    _ = algebraMap Λ Λ_𝔮 (μ : Λ) := by
          simp [mul_assoc]

/-- Helper for Lemma 16.9.3: after fixing a normalized standard-smooth local chart and the two
finite denominator packages for its coordinates and defining relations, the only remaining task is
the source-faithful homogenized descent back to `R`. -/
private theorem exists_descendedFactorization_of_normalizedAtPrimeChartData
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ] [IsStandardSmooth Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    (hfactor : gₚ.comp fₚ = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮)
    {c m : ℕ} (Q : SubmersivePresentation Rₚ Cₚ (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQmap : Q.map = Sum.inl)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          fₚ (algebraMap A Aₚ ((Presentation.ofFinitePresentation R A).val i)))
    (λ₀ : q.asIdeal.primeCompl) (extraChartLift : Fin m → Λ)
    (hExtraChartLift :
      ∀ i, algebraMap Λ Λ_𝔮 (extraChartLift i) =
        algebraMap Λ Λ_𝔮 (λ₀ : Λ) * gₚ (Q.val (.inr i)))
    (sRelation : Ideal.primeCompl (q.asIdeal.under R))
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₚ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₚ) (sRelation : R) * Q.relation i) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra R C) (_ : FinitePresentation R C)
      (f : A →ₐ[R] C) (g : C →ₐ[R] Λ) (b : C),
      g.comp f = IsScalarTower.toAlgHom R A Λ ∧
        g b ∉ q.asIdeal ∧
        IsStandardSmooth R (Localization.Away b) := by
  -- Route correction: the local standard-smooth reduction is finished. The remaining blocker is
  -- exactly the textbook homogenized descent that turns the normalized chart data into a global
  -- quotient receiving both `A → C` and `C → Λ`. The frozen `A`-block is now kept literal, and
  -- only the genuinely extra chart coordinates are rescaled by the common denominator `λ₀`.
  have hRenamedSourceEvalTarget :
      ∀ λDesc : Fin c ⊕ Fin m → Λ,
        (∀ i : Fin (Presentation.ofFinitePresentationVars R A),
          λDesc (.inl (Fin.castLE hQ i)) =
            algebraMap A Λ ((Presentation.ofFinitePresentation R A).val i)) →
        ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
          MvPolynomial.aeval λDesc
              (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
                Sum.inl (Fin.castLE hQ i))
                ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
    intro λDesc hFrozen j
    -- The global frozen source relations now already vanish in `Λ` before any localization step.
    exact
      renamedSourcePresentationRelation_aeval_eq_zero_in_target
        (R := R) (A := A) (Λ := Λ) λDesc hQ hFrozen j
  let _ := hfactor
  let _ := hQmap
  let _ := hQval
  let _ := hExtraChartLift
  let _ := hRelationLift
  let _ := extraChartLift
  let _ := relationLift
  let _ := λ₀
  let _ := sRelation
  let _ :=
    clearedChartQuotientToLocalizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) gₚ Q sRelation relationLift hRelationLift
  let _ :=
    renamedSourcePresentationRelation_aeval_eq_zero_in_localizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQval
  let _ :=
    sourceRelationIdealInClearedChart_le_ker_localizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQval
      sRelation relationLift hRelationLift
  let _ :=
    descendedChartQuotientToLocalizedTarget
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQval
      sRelation relationLift hRelationLift
  obtain ⟨sSource, hsSource⟩ :=
    exists_sourceRelationClearer_in_clearedChart
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ Q hQ hQval
      sRelation relationLift hRelationLift
  obtain ⟨λTailInl, tailChartLift, hTailChartLift⟩ :=
    exists_commonDenominator_of_distinguishedTailChartFamily
      (R := R) (A := A) (Λ := Λ) (q := q) gₚ Q hQ
  let λTail : q.asIdeal.primeCompl := λTailInl * λ₀
  let λDesc : Fin c ⊕ Fin m → Λ := fun i ↦
    match i with
    | .inl j =>
        if hj : j.1 < Presentation.ofFinitePresentationVars R A then
          algebraMap A Λ
            ((Presentation.ofFinitePresentation R A).val
              ⟨j.1, hj⟩)
        else
          (λ₀ : Λ) *
            tailChartLift
              ⟨j.1 - Presentation.ofFinitePresentationVars R A,
                by
                  omega⟩
    | .inr j => (λTailInl : Λ) * extraChartLift j
  have hλDescFrozen :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        λDesc (.inl (Fin.castLE hQ i)) =
          algebraMap A Λ ((Presentation.ofFinitePresentation R A).val i) := by
    intro i
    -- The frozen source block remains literal in the descended global chart assignment.
    simp [λDesc, Fin.val_castLE, i.isLt]
  have hλDescTail :
      ∀ i : Fin (c - Presentation.ofFinitePresentationVars R A),
        algebraMap Λ Λ_𝔮 (λDesc (.inl (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i))) =
          algebraMap Λ Λ_𝔮 (λTail : Λ) *
            gₚ (Q.val (.inl (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i))) := by
    intro i
    -- Both distinguished tail coordinates and free coordinates now share the same denominator.
    have hi :
        ¬ (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i).1 <
          Presentation.ofFinitePresentationVars R A := by
      exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
    calc
      algebraMap Λ Λ_𝔮 (λDesc (.inl (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i))) =
          algebraMap Λ Λ_𝔮 (λ₀ : Λ) *
            algebraMap Λ Λ_𝔮 (tailChartLift i) := by
              simp [λDesc, hi, map_mul]
      _ =
          algebraMap Λ Λ_𝔮 (λ₀ : Λ) *
            (algebraMap Λ Λ_𝔮 (λTailInl : Λ) *
              gₚ (Q.val (.inl (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i)))) := by
              rw [hTailChartLift i]
      _ =
          algebraMap Λ Λ_𝔮 (λTail : Λ) *
            gₚ (Q.val (.inl (Fin.natAdd (Presentation.ofFinitePresentationVars R A) i))) := by
              simp [λTail, mul_assoc, mul_left_comm, mul_comm]
  have hλDescExtra :
      ∀ i : Fin m,
        algebraMap Λ Λ_𝔮 (λDesc (.inr i)) =
          algebraMap Λ Λ_𝔮 (λTail : Λ) * gₚ (Q.val (.inr i)) := by
    intro i
    -- The original `.inr` denominator package is rescaled by the new tail denominator.
    calc
      algebraMap Λ Λ_𝔮 (λDesc (.inr i)) =
          algebraMap Λ Λ_𝔮 (λTailInl : Λ) *
            algebraMap Λ Λ_𝔮 (extraChartLift i) := by
              simp [λDesc, map_mul]
      _ =
          algebraMap Λ Λ_𝔮 (λTailInl : Λ) *
            (algebraMap Λ Λ_𝔮 (λ₀ : Λ) * gₚ (Q.val (.inr i))) := by
              rw [hExtraChartLift i]
      _ = algebraMap Λ Λ_𝔮 (λTail : Λ) * gₚ (Q.val (.inr i)) := by
            simp [λTail, mul_assoc, mul_left_comm, mul_comm]
  let _ := hRenamedSourceEvalTarget
  let _ := sSource
  let _ := hsSource
  let _ := λTailInl
  let _ := tailChartLift
  let _ := hTailChartLift
  let _ := λTail
  let _ := λDesc
  let _ := hλDescFrozen
  let _ := hλDescTail
  let _ := hλDescExtra
  let _ :=
    sourceRelationIdeal_map_eq_bot_awaySourceClearer
      (R := R) (A := A) (Λ := Λ) (q := q) hQ relationLift sSource hsSource
  let _ :=
    localizationAway_sourceClearerQuotient_algEquiv
      (R := R) (A := A) (Λ := Λ) (q := q) hQ relationLift sSource hsSource
  obtain ⟨μJac, jacNum, hJacNum⟩ :=
    exists_targetDenominator_mul_jacobian_eq
      (R := R) (A := A) (Λ := Λ) (q := q) Q gₚ
  -- The frozen source relations now already vanish on the normalized local chart, and the cleared
  -- local chart quotient and its second quotient by the raw source relations both map
  -- canonically to `Λ_𝔮`, the global frozen source relations also vanish in `Λ` on any enlarged
  -- chart that keeps the frozen block literal, `sSource` clears those source relations back
  -- to an honest `R`-ideal, and that second quotient already dies after localizing away from the
  -- source-clearer itself. The remaining blocker is therefore only the target-side globalization:
  -- combine `hExtraChartLift` with the literal frozen source block to define the homogenized
  -- global chart map to `Λ`, clear one target denominator `μ ∉ 𝔮` so the descended localized
  -- target map comes from a map to `Λ`, use the already-cleared Jacobian denominator package
  -- `hJacNum`, and then transport standard smoothness from the cleared
  -- chart basic open across the final away-localization comparison.
  let _ := μJac
  let _ := jacNum
  let _ := hJacNum
  -- TODO: the non-frozen distinguished tail is now bundled together with the old `.inr` block in
  -- the single descended assignment `λDesc`, and `hλDescTail`/`hλDescExtra` show that every
  -- non-frozen coordinate has the same localized denominator `λTail`. The generic finite-family
  -- annihilator step is now isolated by
  -- `exists_commonTargetAnnihilator_of_fintype_atPrimeZeroFamily`, so the remaining blocker is
  -- only to compute a partial homogenization formula for the target-side chart relations and then
  -- transport standard smoothness across the resulting away-localization comparison.
  sorry

/-- Helper for Lemma 16.9.3: the remaining denominator-clearing descent should output a global
finitely presented factorization together with a standard-smooth basic open whose image avoids
`𝔮`. -/
private theorem exists_factorization_with_standardSmoothAway_not_mem_prime_of_localStandardSmoothFactorizationAtPrime
    [FinitePresentation Rₚ Aₚ]
    {Cₚ : Type (max u v w)} [CommRing Cₚ] [Algebra Rₚ Cₚ] [IsStandardSmooth Rₚ Cₚ]
    (fₚ : Aₚ →ₐ[Rₚ] Cₚ) (gₚ : Cₚ →ₐ[Rₚ] Λ_𝔮)
    (hfactor : gₚ.comp fₚ = IsScalarTower.toAlgHom Rₚ Aₚ Λ_𝔮) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra R C) (_ : FinitePresentation R C)
      (f : A →ₐ[R] C) (g : C →ₐ[R] Λ) (b : C),
      g.comp f = IsScalarTower.toAlgHom R A Λ ∧
        g b ∉ q.asIdeal ∧
        IsStandardSmooth R (Localization.Away b) := by
  -- Route correction: normalize the local standard-smooth chart first, then isolate the explicit
  -- finite denominator-clearing/global-quotient descent as the only remaining step.
  obtain ⟨c, m, Q, hQ, hQmap, hQval⟩ :=
    exists_normalizedAtPrimeSubmersivePresentation
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ
  let extraChartValue : Fin m → Λ_𝔮 := fun i ↦ gₚ (Q.val (.inr i))
  obtain ⟨λ₀, extraChartLift, hExtraChartLift⟩ :=
    exists_commonDenominator_of_extraChartFamily
      (R := R) (A := A) (Λ := Λ) (q := q) extraChartValue
  obtain ⟨sRelation, relationLift, hRelationLift⟩ :=
    exists_commonDenominator_of_fintype_atPrimePolynomialFamily
      (R := R) (A := A) (Λ := Λ) (q := q) (u := Q.relation)
  -- The local chart normalization and denominator packages are complete, so only the explicit
  -- homogenized descent helper remains.
  exact
    exists_descendedFactorization_of_normalizedAtPrimeChartData
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hfactor Q hQ hQmap hQval
      λ₀ extraChartLift hExtraChartLift sRelation relationLift hRelationLift

/-- Helper for Lemma 16.9.3: a source singular element whose image avoids `𝔮` witnesses the
required target noncontainment. -/
private theorem singularIdeal_not_le_of_mem_sourceSingularIdeal_not_mem_prime
    {C : Type*} [CommRing C] [Algebra R C] [Algebra C Λ] [IsScalarTower R C Λ]
    (g : C →ₐ[R] Λ) {c : C} (hc : c ∈ H[C⁄R]) (hcg : g c ∉ q.asIdeal) :
    ¬ g.singularIdealIn R ≤ q.asIdeal := by
  -- The image of any source singular element lies in the target singular ideal by definition.
  intro hle
  have hmem : g c ∈ g.singularIdealIn R := by
    rw [RingHom.singularIdealIn]
    exact Ideal.subset_radical (Ideal.mem_map_of_mem g hc)
  exact hcg (hle hmem)

-- Proof sketch: start from the local resolution at `Λ_𝔮`, replace it by a standard smooth
-- factorization over `R_𝔭` using Lemmas `16.2.8`, `16.3.4`, and `16.3.6`, then clear
-- denominators in the resulting standard smooth presentation and homogenize the defining
-- equations. The resulting finitely presented global algebra still maps to `Λ`, and the chosen
-- Jacobian determinant stays away from `𝔮`, so the image of `H_{C/R}` is not contained in `𝔮`.
/-- Lemma 16.9.3: if `𝔮` is a minimal prime over `𝔥_A` and the localized map
`R_𝔭 → A_𝔭 → Λ_𝔮 ⊃ 𝔮 Λ_𝔮`, with `𝔭 = R ∩ 𝔮`, admits a resolution and `R` is Noetherian while `A`
is finitely presented over `R`, then `A → Λ` factors through a finitely presented `R`-algebra `C`
whose singular ideal image in `Λ` is not contained in `𝔮`. -/
@[stacks 07F9]
theorem exists_factorization_with_singularIdeal_not_le_of_localResolutionAtMinimalPrime
    [IsNoetherianRing R] [FinitePresentation R A] (q : PrimeSpectrum Λ)
    (hq : q.asIdeal ∈ (h(A⁄R, Λ)).minimalPrimes) (hresolve : ResolvableAtPrime Rₚ Aₚ Λ_𝔮 𝔮Λ_𝔮) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra R C) (_ : FinitePresentation R C)
      (f : A →ₐ[R] C) (g : C →ₐ[R] Λ),
      g.comp f = IsScalarTower.toAlgHom R A Λ ∧
        ¬ g.singularIdealIn R ≤ q.asIdeal := by
  -- Route correction: first refine the verified smooth local factorization to a standard-smooth
  -- chart, then isolate the only unresolved step as the denominator-clearing descent back to `R`.
  obtain ⟨Cₚ, hCₚCommRing, hCₚAlg, hCₚStd, fₚ, gₚ, hcompₚ⟩ :=
    exists_localStandardSmoothFactorization_of_resolvableAtPrimeAtLocalPrime
      (R := R) (A := A) (Λ := Λ) (q := q) hresolve
  letI : CommRing Cₚ := hCₚCommRing
  letI : Algebra Rₚ Cₚ := hCₚAlg
  letI : IsStandardSmooth Rₚ Cₚ := hCₚStd
  let _ := hq
  obtain ⟨C, hCCommRing, hCAlg, hCfp, f, g, b, hcomp, hgb, hSmoothAway⟩ :=
    exists_factorization_with_standardSmoothAway_not_mem_prime_of_localStandardSmoothFactorizationAtPrime
      (R := R) (A := A) (Λ := Λ) (q := q) fₚ gₚ hcompₚ
  letI : CommRing C := hCCommRing
  letI : Algebra R C := hCAlg
  letI : FinitePresentation R C := hCfp
  letI : Algebra C Λ := g.toAlgebra
  letI : IsScalarTower R C Λ := IsScalarTower.of_algHom g
  obtain ⟨e0, he0⟩ :=
    standardSmoothAway_eventually_elementaryStandard_pow (R := R) (A := C) (a := b) hSmoothAway
  have hpowNotMem : g (b ^ (e0 + 1)) ∉ q.asIdeal := by
    -- Powers of an element outside the prime still map outside that prime.
    intro hbpow
    apply hgb
    exact q.isPrime.mem_of_pow_mem _ (by simpa [map_pow] using hbpow)
  have hcSing : b ^ (e0 + 1) ∈ H[C⁄R] := by
    -- The chosen power is elementary standard on the descended standard-smooth basic open.
    exact
      mem_singularIdeal_of_isElementaryStandard (R := R) (C := C)
        (he0 (e0 + 1) (Nat.le_succ e0))
  refine ⟨C, inferInstance, inferInstance, inferInstance, f, g, hcomp, ?_⟩
  -- A source singular element mapping outside `q` gives the required noncontainment.
  exact
    singularIdeal_not_le_of_mem_sourceSingularIdeal_not_mem_prime
      (R := R) (Λ := Λ) (q := q) g hcSing hpowNotMem

end Prime

end

end Algebra
