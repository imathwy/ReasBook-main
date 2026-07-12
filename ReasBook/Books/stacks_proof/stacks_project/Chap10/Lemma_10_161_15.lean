import Mathlib
import StacksProject_2024.Chap10.Lemma_10_25_3
import StacksProject_2024.Chap10.Lemma_10_37_17
import StacksProject_2024.Chap10.Lemma_10_161_3
import StacksProject_2024.Chap10.Lemma_10_161_4
import StacksProject_2024.Chap10.Lemma_10_161_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Helper for Lemma 10.161.15: if finitely many elements generate the normalization as an
`R`-module and a single element `f` clears their denominators, then the away map to the localized
normalization is surjective. -/
lemma awayMap_surjective_of_denominator_clearing
    {n : ℕ} (f : R) (s : Fin n → integralClosure R (FractionRing R))
    (hs : Submodule.span R (Set.range s) = ⊤) (a : Fin n → R)
    (ha : ∀ i,
      algebraMap R (FractionRing R) (a i) =
        algebraMap R (FractionRing R) f * (s i : FractionRing R)) :
    Function.Surjective
      (Localization.awayMap
        (algebraMap R (integralClosure R (FractionRing R))) f) := by
  -- Proof comment: every element of the normalization is an `R`-linear combination of the chosen
  -- generators, and multiplying once by `f` replaces each generator by an element from `R`.
  rw [Localization.awayMap_surjective_iff]
  intro x
  have hx_span : x ∈ Submodule.span R (Set.range s) := by
    simpa [hs] using
      (show x ∈ (⊤ : Submodule R (integralClosure R (FractionRing R))) by trivial)
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (R := R) (v := s) (x := x)).mp hx_span
  refine ⟨∑ i, c i * a i, 1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  -- Proof comment: after rewriting `x` as a finite linear combination, the denominator-clearing
  -- identities for the generators turn the right-hand side into `f * x`.
  calc
    algebraMap R (FractionRing R) (∑ i, c i * a i)
        = ∑ i, algebraMap R (FractionRing R) (c i * a i) := by
            simp
    _ = ∑ i, algebraMap R (FractionRing R) (c i) *
          (algebraMap R (FractionRing R) f * (s i : FractionRing R)) := by
            simp [ha]
    _ = algebraMap R (FractionRing R) f * ∑ i, algebraMap R (FractionRing R) (c i) * (s i :
          FractionRing R) := by
            calc
              ∑ i, algebraMap R (FractionRing R) (c i) *
                    (algebraMap R (FractionRing R) f * (s i : FractionRing R))
                  = ∑ i, algebraMap R (FractionRing R) f *
                      (algebraMap R (FractionRing R) (c i) * (s i : FractionRing R)) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
              _ = algebraMap R (FractionRing R) f * ∑ i,
                    algebraMap R (FractionRing R) (c i) * (s i : FractionRing R) := by
                        rw [Finset.mul_sum]
    _ = algebraMap R (FractionRing R) f * (x : FractionRing R) := by
            have hc' :
                ∑ i, algebraMap R (FractionRing R) (c i) * (s i : FractionRing R) =
                  (x : FractionRing R) := by
              simpa [Algebra.smul_def] using
                congrArg (fun z : integralClosure R (FractionRing R) => (z : FractionRing R)) hc
            rw [hc']

/-- Helper for Lemma 10.161.15: package a bijective away map as the explicit ring equivalence
used in the source argument `R_f = S_f`. -/
noncomputable def awayMapRingEquivOfBijective
    {S : Type*} [CommRing S] [Algebra R S] (f : R)
    (hbij : Function.Bijective (Localization.awayMap (algebraMap R S) f)) :
    Localization.Away f ≃+* Localization.Away (algebraMap R S f) :=
  RingEquiv.ofBijective (Localization.awayMap (algebraMap R S) f) hbij

/-- Helper for Lemma 10.161.15: once the source equality `R_f = S_f` is packaged as an explicit
equivalence, normality transports back across that equivalence. -/
lemma isNormalRing_of_bijective_awayMap
    {S : Type*} [CommRing S] [Algebra R S] {f : R}
    (hbij : Function.Bijective (Localization.awayMap (algebraMap R S) f))
    [IsNormalRing (Localization.Away (algebraMap R S f))] :
    IsNormalRing (Localization.Away f) := by
  let e : Localization.Away f ≃+* Localization.Away (algebraMap R S f) :=
    awayMapRingEquivOfBijective (R := R) (S := S) f hbij
  -- Proof comment: this isolates the earlier elaboration hotspot to a single named equivalence,
  -- so the final transport of normality is just `isNormalRing_of_equiv`.
  exact isNormalRing_of_equiv e.symm

/-- Helper for Lemma 10.161.15: finite normalization generators admit one common nonzero
denominator in the fraction field. -/
lemma exists_generating_family_with_common_denominator_of_finite_normalization
    (hfinite : Module.Finite R (integralClosure R (FractionRing R))) :
    ∃ n : ℕ, ∃ s : Fin n → integralClosure R (FractionRing R), ∃ f : R, ∃ a : Fin n → R,
      f ≠ 0 ∧ Submodule.span R (Set.range s) = ⊤ ∧
        (∀ i,
          algebraMap R (FractionRing R) (a i) =
            algebraMap R (FractionRing R) f * (s i : FractionRing R)) := by
  classical
  letI : Module.Finite R (integralClosure R (FractionRing R)) := hfinite
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R)
    (M := integralClosure R (FractionRing R))
  let coords : Fin n → FractionRing R := fun i ↦ (s i : FractionRing R)
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors R) coords
  have hf : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hnum_exists :
      ∀ i, ∃ r : R,
        algebraMap R (FractionRing R) r =
          algebraMap R (FractionRing R) (b : R) * (s i : FractionRing R) := by
    intro i
    -- Proof comment: `IsInteger` is exactly membership in the image of `R → Frac(R)`.
    simpa [coords, IsLocalization.IsInteger, RingHom.mem_range, Algebra.smul_def] using hb i
  choose a ha using hnum_exists
  refine ⟨n, s, (b : R), a, hf, hs, ?_⟩
  intro i
  exact ha i

/-- Helper for Lemma 10.161.15: the common-denominator package makes the away map from `R_f` to
the localized normalization bijective. -/
lemma bijective_awayMap_of_generating_family_with_common_denominator
    {n : ℕ} (f : R) (s : Fin n → integralClosure R (FractionRing R))
    (hs : Submodule.span R (Set.range s) = ⊤) (a : Fin n → R)
    (ha : ∀ i,
      algebraMap R (FractionRing R) (a i) =
        algebraMap R (FractionRing R) f * (s i : FractionRing R)) :
    Function.Bijective
      (Localization.awayMap
        (algebraMap R (integralClosure R (FractionRing R))) f) := by
  refine ⟨?_, awayMap_surjective_of_denominator_clearing
    (R := R) (f := f) (s := s) hs a ha⟩
  -- Proof comment: injectivity reduces to injectivity of `R → Frac(R)`, so exponent `0`
  -- already clears every kernel element of the away map.
  rw [Localization.awayMap_injective_iff]
  intro r hr
  have hr_frac : algebraMap R (FractionRing R) r = 0 := by
    simpa using
      congrArg (fun z : integralClosure R (FractionRing R) => (z : FractionRing R)) hr
  have hr_zero : r = 0 := (IsFractionRing.injective R (FractionRing R)) <| by
    simpa using hr_frac
  refine ⟨0, ?_⟩
  simpa [hr_zero]

/- 
Domain triage:
* primary domain: commutative algebra of the `N-1` property, localization of normalization, and
  descent from maximal-local data;
* sampled owner/bridge declarations:
  - `IsN1Ring`, the source-facing owner from `Definition_10_161_1`;
  - `isN1Ring_of_isLocalization`, the localization-stability bridge from `Lemma_10_161_3`;
  - `IsLocalization.integralClosure`, the canonical localization bridge for normalization;
  - `RingHom.finite_ofLocalizationSpan`, the canonical finite-descent owner for integral maps.
* best owner abstraction: the main owner throughout is `IsN1Ring R`; the normal-away statement in
  clause `(1)` remains source-facing via `IsNormalRing (Localization.Away f)`, while clause `(3)`
  is the reverse implication combining that source-facing witness with maximal-local `N-1` data.

Layer triage:
* `source-facing`: the three numbered clauses of Lemma `10.161.15`;
* `core/canonical`: `IsN1Ring`, `IsNormalRing`, `Localization.Away`, `Localization.AtPrime`, and
  the normalization map `R → integralClosure R (FractionRing R)`;
* `bridge/view`: specialization of localization stability to maximal ideals and identification of
  localized normalization via `IsLocalization.integralClosure`.
-/

-- Proof sketch: identify the integral closure of `R` in `FractionRing R` as a finite `R`-module,
-- choose finitely many generators, and clear denominators to find a nonzero `f` such that the
-- localization away from `f` identifies with the integral closure and is therefore normal.
/-- Lemma 10.161.15 (1): if a domain `R` is `N-1`, then there exists a nonzero
element `f : R` such that `R_f` is normal. -/
@[stacks 0333]
theorem exists_isNormalRing_localizationAway_of_isN1Ring
    (hR : IsN1Ring R) :
    ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f) := by
  letI : IsN1Ring R := hR
  obtain ⟨n, s, f, a, hf, hs, ha⟩ :=
    exists_generating_family_with_common_denominator_of_finite_normalization
      (R := R) (hfinite := inferInstance)
  have hbij :
      Function.Bijective
        (Localization.awayMap
          (algebraMap R (integralClosure R (FractionRing R))) f) :=
    bijective_awayMap_of_generating_family_with_common_denominator
      (R := R) (f := f) (s := s) hs a ha
  have hf_normalization :
      algebraMap R (integralClosure R (FractionRing R)) f ≠ 0 := by
    intro hf_zero
    apply hf
    apply (IsFractionRing.injective R (FractionRing R))
    simpa using
      congrArg (fun z : integralClosure R (FractionRing R) => (z : FractionRing R)) hf_zero
  have hpow_le :
      Submonoid.powers (algebraMap R (integralClosure R (FractionRing R)) f) ≤
        nonZeroDivisors (integralClosure R (FractionRing R)) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf_normalization
  letI : IsFractionRing (integralClosure R (FractionRing R)) (FractionRing R) :=
    integralClosure.isFractionRing_of_finite_extension
      (A := R) (K := FractionRing R) (L := FractionRing R)
  letI : IsIntegrallyClosed (integralClosure R (FractionRing R)) := by
    exact (isIntegrallyClosed_iff_isIntegrallyClosedIn
      (R := integralClosure R (FractionRing R)) (K := FractionRing R)).2 inferInstance
  letI : IsNormalRing (Localization.Away
      (algebraMap R (integralClosure R (FractionRing R)) f)) := by
    letI : IsDomain (Localization.Away
        (algebraMap R (integralClosure R (FractionRing R)) f)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors
        (Localization.Away (algebraMap R (integralClosure R (FractionRing R)) f)) hpow_le
    letI : IsIntegrallyClosed (Localization.Away
        (algebraMap R (integralClosure R (FractionRing R)) f)) :=
      isIntegrallyClosed_of_isLocalization
        (R := integralClosure R (FractionRing R))
        (S := Localization.Away
          (algebraMap R (integralClosure R (FractionRing R)) f))
        (M := Submonoid.powers (algebraMap R (integralClosure R (FractionRing R)) f))
        hpow_le
    -- Proof comment: the normalization is normal, and normality survives the principal
    -- localization used in the source argument `R_f = S_f`.
    infer_instance
  refine ⟨f, hf, ?_⟩
  -- Proof comment: the source equality `R_f = S_f` is now the bijective away map, so normality
  -- transports back to `R_f`.
  exact isNormalRing_of_bijective_awayMap
    (R := R) (S := integralClosure R (FractionRing R)) hbij

-- Proof sketch: apply localization stability of `N-1` from `Lemma 10.161.3` to the localization
-- of `R` at the complement of each maximal ideal.
/-- Lemma 10.161.15 (2): if a domain `R` is `N-1`, then every localization `R_𝔪` at a
maximal ideal is `N-1`. -/
@[stacks 0333]
theorem isN1Ring_localizationAtMaximal_of_isN1Ring
    (hR : IsN1Ring R) (m : MaximalSpectrum R) :
    IsN1Ring (Localization.AtPrime m.asIdeal) := by
  letI : IsN1Ring R := hR
  exact isN1Ring_of_isLocalization m.asIdeal.primeCompl

section

variable [IsNoetherianRing R]

/-- Helper for Lemma 10.161.15: a Noetherian normal domain is `N-1`. -/
lemma isN1Ring_of_isNormalRing_noetherian :
    [IsNormalRing R] →
    IsN1Ring R := by
  intro
  -- Proof comment: an integrally closed domain identifies with its normalization in the fraction
  -- field, so finite generation is transported across that canonical equivalence.
  let e : integralClosure R (FractionRing R) ≃ₐ[R] R :=
    (Subalgebra.equivOfEq _ _
      (IsIntegrallyClosed.integralClosure_eq_bot (R := R) (K := FractionRing R))).trans
        (Algebra.botEquivOfInjective (R := R) (A := FractionRing R)
          (IsFractionRing.injective R (FractionRing R)))
  exact IsN1Ring.mk <| Module.Finite.equiv e.toLinearEquiv.symm

/-- Helper for Lemma 10.161.15: a Noetherian normal principal localization is `N-1`. -/
lemma isN1Ring_localizationAway_of_normalAway
    {f : R} [IsDomain (Localization.Away f)] [IsNoetherianRing (Localization.Away f)]
    (hAway : IsNormalRing (Localization.Away f)) :
    IsN1Ring (Localization.Away f) := by
  letI : IsNormalRing (Localization.Away f) := hAway
  exact isN1Ring_of_isNormalRing_noetherian (R := Localization.Away f)

/-- Helper for Lemma 10.161.15: a normal principal localization has finite normalization. -/
lemma integralClosure_finite_localizationAway_of_normalAway
    {f : R} [IsDomain (Localization.Away f)] [IsNoetherianRing (Localization.Away f)]
    (hAway : IsNormalRing (Localization.Away f)) :
    Module.Finite (Localization.Away f)
      (integralClosure (Localization.Away f) (FractionRing (Localization.Away f))) := by
  letI : IsN1Ring (Localization.Away f) :=
    isN1Ring_localizationAway_of_normalAway (R := R) hAway
  -- Proof comment: once the principal localization is `N-1`, its defining finite-normalization
  -- statement is exactly the target.
  exact IsN1Ring.integralClosure_finite (R := Localization.Away f)

/-- Helper for Lemma 10.161.15: from witnesses near every maximal ideal containing `f`, one
extracts a finite principal-open cover containing `D(f)`. -/
lemma exists_finite_basicOpen_cover_of_maximal_witness
    (f : R) (P : R → Prop)
    (hwitness : ∀ m : MaximalSpectrum R, f ∈ m.asIdeal → ∃ g : R, g ∉ m.asIdeal ∧ P g) :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧ f ∈ s ∧
      ∀ g ∈ s, g = f ∨ P g := by
  classical
  let t : Set R := insert f {g : R | P g}
  have hspan : Ideal.span t = ⊤ := by
    -- Proof comment: a maximal ideal containing the span would contain `f` and therefore also its
    -- designated witness `g ∉ m`, which is impossible.
    by_contra hspan
    obtain ⟨I, hImax, hle⟩ := Ideal.exists_le_maximal (Ideal.span t) hspan
    let m : MaximalSpectrum R := ⟨I, hImax⟩
    have hfmem : f ∈ m.asIdeal := hle <| Ideal.subset_span <| by simp [t]
    obtain ⟨g, hgnot, hgP⟩ := hwitness m hfmem
    have hgmem : g ∈ m.asIdeal := hle <| Ideal.subset_span <| by simp [t, hgP]
    exact hgnot hgmem
  obtain ⟨u, hu_subset, hu_top⟩ := (Ideal.span_eq_top_iff_finite t).mp hspan
  let s : Finset R := insert f u
  refine ⟨s, ?_, by simp [s], ?_⟩
  · -- Proof comment: adding `f` to the finite subset does not shrink the span.
    apply top_unique
    rw [← hu_top]
    exact Ideal.span_mono <| by
      intro x hx
      simp [s, hx]
  · -- Proof comment: every chosen generator is either the original `f` or comes from the
    -- witness predicate `P`.
    intro g hg
    rcases Finset.mem_insert.mp (by simpa [s] using hg) with rfl | hg'
    · exact Or.inl rfl
    · simpa [t] using hu_subset hg'

/-- Helper for Lemma 10.161.15: a finite subalgebra of the fraction field of a normal domain is
already the base ring. -/
lemma eq_bot_of_finite_subalgebra_of_isNormalRing_commonFractionField
    {S K : Type*} [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    (B : Subalgebra S K) (hfinite : Module.Finite S B)
    [IsNormalRing S] :
    B = ⊥ := by
  letI : IsIntegrallyClosed S := inferInstance
  letI : Algebra.IsIntegral S B := Algebra.IsIntegral.of_finite S B
  apply le_antisymm ?_ bot_le
  intro x hx
  let xB : B := ⟨x, hx⟩
  have hx_integral : IsIntegral S ((xB : B) : K) := by
    exact (show IsIntegral S xB from Algebra.IsIntegral.isIntegral xB).map
      (Algebra.ofId B K)
  have hx_mem_closure : x ∈ integralClosure S K := hx_integral
  -- Proof comment: once the ambient base ring is normal, every integral element in the common
  -- fraction field already comes from the base ring, so the finite subalgebra collapses to `⊥`.
  simpa [IsIntegrallyClosed.integralClosure_eq_bot (R := S) (K := K)] using hx_mem_closure

/-- Helper for Lemma 10.161.15: a finite subalgebra of the fraction field of a normal domain is
already the base ring. -/
lemma eq_bot_of_finite_subalgebra_of_isNormalRing
    (A : Subalgebra R (FractionRing R)) (hfinite : Module.Finite R A)
    [IsNormalRing R] :
    A = ⊥ := by
  exact eq_bot_of_finite_subalgebra_of_isNormalRing_commonFractionField
    (S := R) (K := FractionRing R) A hfinite

/-- Helper for Lemma 10.161.15: for a finite intermediate ring `A ⊆ Frac(R)`, `badImage A` is the
image in `Spec(R)` of the non-normal locus of `A`. -/
def badImage (A : Subalgebra R (FractionRing R)) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.comap (algebraMap R A) '' (PrimeSpectrum.normalLocus A)ᶜ

/-- Helper for Lemma 10.161.15: once the normal locus of a finite intermediate ring is open, its
image in `Spec(R)` is closed because integral finite maps are closed on spectra. -/
lemma isClosed_badImage_of_isOpen_normalLocus
    (A : Subalgebra R (FractionRing R)) (hfinite : Module.Finite R A)
    (hopen : IsOpen (PrimeSpectrum.normalLocus A)) :
    IsClosed (badImage (R := R) A) := by
  letI : Module.Finite R A := hfinite
  letI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  have hInt : (algebraMap R A).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  -- Proof comment: the complement of the normal locus is closed in `Spec(A)`, and the integral
  -- spectrum map `Spec(A) → Spec(R)` sends closed sets to closed sets.
  simpa [badImage] using
    (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R A) hInt)
      ((PrimeSpectrum.normalLocus A)ᶜ) hopen.isClosed_compl

/-- Helper for Lemma 10.161.15: localizing a finite intermediate ring away from `f` remains a
finite algebra over the principal localization `R_f`. -/
private noncomputable instance localizationAwayImageAlgebra
    {A : Type*} [CommRing A] [Algebra R A] (f : R) :
    Algebra (Localization.Away f) (Localization.Away (algebraMap R A f)) := by
  simpa [Algebra.ofId_apply] using
    (Localization.awayMapₐ (Algebra.ofId R A) f).toAlgebra

/-- Helper for Lemma 10.161.15: the localized intermediate ring lies in a scalar tower over the
principal localization `R_f`. -/
private noncomputable instance localizationAwayImageIsScalarTower
    {A : Type*} [CommRing A] [Algebra R A] (f : R) :
    IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R A f)) := by
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  simpa [localizationAwayImageAlgebra] using
    ((Localization.awayMapₐ (Algebra.ofId R A) f).commutes r).symm

/-- Helper for Lemma 10.161.15: localizing a finite intermediate ring away from `f` remains a
finite algebra over the principal localization `R_f`. -/
lemma moduleFinite_localizationAway_of_finite_intermediate
    {A : Type*} [CommRing A] [Algebra R A] {f : R}
    (hfinite : Module.Finite R A) :
    Module.Finite (Localization.Away f) (Localization.Away (algebraMap R A f)) := by
  letI : Module.Finite R A := hfinite
  letI :
      IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))
        (Localization.Away (algebraMap R A f)) := by
    infer_instance
  -- Proof comment: finite generation descends through localization along the same multiplicative
  -- set used in the source argument.
  exact Module.Finite.of_isLocalization R A (Submonoid.powers f)

/-- Helper for Lemma 10.161.15: a nonzero element of `R` stays nonzero in any intermediate
subalgebra of `Frac(R)`. -/
lemma algebraMap_subalgebra_ne_zero_of_ne_zero
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0) :
    algebraMap R A f ≠ 0 := by
  intro hfA
  apply hf
  exact (IsFractionRing.injective R (FractionRing R)) <| by
    simpa using congrArg (fun z : A => (z : FractionRing R)) hfA

/-- Helper for Lemma 10.161.15: localizing a finite intermediate ring away from the image of a
nonzero element still gives a domain. -/
lemma isDomain_localizationAway_of_finite_intermediate
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0) :
    IsDomain (Localization.Away (algebraMap R A f)) := by
  have hfA : algebraMap R A f ≠ 0 :=
    algebraMap_subalgebra_ne_zero_of_ne_zero (R := R) A hf
  have hpowA : Submonoid.powers (algebraMap R A f) ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hfA
  -- Proof comment: the intermediate ring is already a domain inside `Frac(R)`, so inverting a
  -- nonzero element preserves the domain property.
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (Localization.Away (algebraMap R A f)) hpowA

/-- Helper for Lemma 10.161.15: every element of the principal-open denominator submonoid becomes
a unit in the common fraction field. -/
lemma away_image_submonoid_le_units_fractionRing
    {f : R} (hf : f ≠ 0) :
    Algebra.algebraMapSubmonoid (FractionRing R) (Submonoid.powers f) ≤
      IsUnit.submonoid (FractionRing R) := by
  let hpow : Submonoid.powers f ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf
  -- Proof comment: every power of `f` is a nonzerodivisor in the domain `R`, hence its image in
  -- `Frac(R)` is invertible.
  rintro _ ⟨x, hx, rfl⟩
  exact IsLocalization.map_units (FractionRing R) ⟨x, hpow hx⟩

/-- Helper for Lemma 10.161.15: the localized inclusion of a finite intermediate ring into the
common fraction field, viewed as a plain localized ring homomorphism. -/
noncomputable def localized_intermediate_to_fractionRing_over_away
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0) :
    Localization.Away (algebraMap R A f) →+* FractionRing R :=
  letI :
      IsLocalization (Algebra.algebraMapSubmonoid (FractionRing R) (Submonoid.powers f))
        (FractionRing R) :=
    IsLocalization.self (away_image_submonoid_le_units_fractionRing (R := R) hf)
  IsLocalization.map (FractionRing R) (A.val : A →+* FractionRing R)
    (Algebra.algebraMapSubmonoid_le_comap (Submonoid.powers f) A.val)

/-- Helper for Lemma 10.161.15: the common fraction field is the localization of an intermediate
ring away from the image of the chosen nonzero denominator. -/
lemma localized_intermediate_fractionRing_isLocalization
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0) :
    IsLocalization ((Submonoid.powers (algebraMap R A f)).map (A.val : A →+* FractionRing R))
      (FractionRing R) := by
  -- Proof comment: the image of the powers of `f` in the intermediate ring maps to the same
  -- powers inside the common fraction field, where those powers are already units.
  simpa [Submonoid.map_powers] using
    (IsLocalization.self (away_image_submonoid_le_units_fractionRing (R := R) hf) :
      IsLocalization (Algebra.algebraMapSubmonoid (FractionRing R) (Submonoid.powers f))
        (FractionRing R))

/-- Helper for Lemma 10.161.15: the localized inclusion agrees with the original inclusion on the
intermediate ring `A`. -/
@[simp] lemma localized_intermediate_to_fractionRing_over_away_algebraMap
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0) (a : A) :
    localized_intermediate_to_fractionRing_over_away (R := R) A hf (algebraMap A _ a) =
      algebraMap A (FractionRing R) a := by
  -- Proof comment: `IsLocalization.mapₐ` is characterized by its action on elements of the source
  -- ring before localization.
  letI :
      IsLocalization (Algebra.algebraMapSubmonoid (FractionRing R) (Submonoid.powers f))
        (FractionRing R) :=
    IsLocalization.self (away_image_submonoid_le_units_fractionRing (R := R) hf)
  exact IsLocalization.map_eq (Q := FractionRing R)
    (g := (A.val : A →+* FractionRing R))
    (hy := Algebra.algebraMapSubmonoid_le_comap (Submonoid.powers f) A.val) a

/-- Helper for Lemma 10.161.15: the localized inclusion commutes with scalars from `R_f`. -/
lemma localized_intermediate_to_fractionRing_over_away_comp_algebraMap
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0)
    [Algebra (Localization.Away f) (FractionRing R)]
    [IsScalarTower R (Localization.Away f) (FractionRing R)] :
    (localized_intermediate_to_fractionRing_over_away (R := R) A hf).comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f))) =
      algebraMap (Localization.Away f) (FractionRing R) := by
  -- Proof comment: this is the first remaining transport blocker. The intended proof is by
  -- localization extensionality on `R_f`, reducing to the already-proved formula on elements of
  -- `A` coming from `R`.
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  -- Proof comment: after restricting to `R`, both maps are the canonical scalar map into the
  -- common fraction field, and the localized inclusion formula on `A` closes the check.
  have hleft :
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f)))
          ((algebraMap R (Localization.Away f)) r) =
        algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r) := by
    calc
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f)))
          ((algebraMap R (Localization.Away f)) r)
        = algebraMap R (Localization.Away (algebraMap R A f)) r := by
            exact (IsScalarTower.algebraMap_apply R (Localization.Away f)
              (Localization.Away (algebraMap R A f)) r).symm
      _ = algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r) := by
            exact (IsScalarTower.algebraMap_apply R A
              (Localization.Away (algebraMap R A f)) r).symm
  have hright :
      (algebraMap (Localization.Away f) (FractionRing R))
          ((algebraMap R (Localization.Away f)) r) =
        algebraMap A (FractionRing R) (algebraMap R A r) := by
    calc
      (algebraMap (Localization.Away f) (FractionRing R))
          ((algebraMap R (Localization.Away f)) r)
        = algebraMap R (FractionRing R) r := by
            exact (IsScalarTower.algebraMap_apply R (Localization.Away f) (FractionRing R) r).symm
      _ = algebraMap A (FractionRing R) (algebraMap R A r) := by
            exact (IsScalarTower.algebraMap_apply R A (FractionRing R) r).symm
  calc
    (localized_intermediate_to_fractionRing_over_away (R := R) A hf)
        ((algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f)))
          ((algebraMap R (Localization.Away f)) r))
      = (localized_intermediate_to_fractionRing_over_away (R := R) A hf)
          (algebraMap A (Localization.Away (algebraMap R A f)) (algebraMap R A r)) := by
            rw [hleft]
    _ = algebraMap A (FractionRing R) (algebraMap R A r) := by
          rw [localized_intermediate_to_fractionRing_over_away_algebraMap]
    _ = (algebraMap (Localization.Away f) (FractionRing R))
          ((algebraMap R (Localization.Away f)) r) := by
          rw [hright]

/-- Helper for Lemma 10.161.15: the localized inclusion of an intermediate ring into the common
fraction field is injective. -/
lemma localized_intermediate_to_fractionRing_over_away_injective
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0) :
    Function.Injective (localized_intermediate_to_fractionRing_over_away (R := R) A hf) := by
  letI :
      IsLocalization ((Submonoid.powers (algebraMap R A f)).map (A.val : A →+* FractionRing R))
        (FractionRing R) :=
    localized_intermediate_fractionRing_isLocalization (R := R) A hf
  -- Proof comment: the localized map is the away map of the injective inclusion `A ↪ Frac(R)`,
  -- so localization injectivity reduces to injectivity of that inclusion.
  simpa [localized_intermediate_to_fractionRing_over_away] using
    (IsLocalization.map_injective_of_injective
      (Submonoid.powers (algebraMap R A f))
      (Localization.Away (algebraMap R A f))
      (FractionRing R)
      (show Function.Injective (A.val : A →+* FractionRing R) from Subtype.val_injective))

/-- Helper for Lemma 10.161.15: the localized inclusion commutes with scalars from the principal
localization `R_f`. -/
lemma localized_intermediate_to_fractionRing_over_away_commutes
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0)
    [Algebra (Localization.Away f) (FractionRing R)]
    [IsScalarTower R (Localization.Away f) (FractionRing R)] :
    ∀ c : Localization.Away f,
      localized_intermediate_to_fractionRing_over_away (R := R) A hf
          (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f)) c) =
        algebraMap (Localization.Away f) (FractionRing R) c := by
  intro c
  -- Proof comment: the earlier compatibility lemma is already an equality of ring homomorphisms,
  -- so applying it to the scalar `c` gives the required commutation formula.
  simpa using
    DFunLike.congr_fun
      (localized_intermediate_to_fractionRing_over_away_comp_algebraMap
        (R := R) A hf) c

/-- Helper for Lemma 10.161.15: bundle the localized inclusion into the common fraction field as
an explicit `R_f`-algebra map. -/
noncomputable def localized_intermediate_to_fractionRing_over_away_algHom
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0)
    [Algebra (Localization.Away f) (FractionRing R)]
    [IsScalarTower R (Localization.Away f) (FractionRing R)] :
    Localization.Away (algebraMap R A f) →ₐ[Localization.Away f] FractionRing R :=
  { localized_intermediate_to_fractionRing_over_away (R := R) A hf with
    commutes' := localized_intermediate_to_fractionRing_over_away_commutes (R := R) A hf }

/-- Helper for Lemma 10.161.15: the localized intermediate ring is canonically equivalent to the
range of its inclusion into the common fraction field over `R_f`. -/
noncomputable def localized_intermediate_range_equiv_over_away
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0)
    [Algebra (Localization.Away f) (FractionRing R)]
    [IsScalarTower R (Localization.Away f) (FractionRing R)] :
    Localization.Away (algebraMap R A f) ≃ₐ[Localization.Away f]
      (localized_intermediate_to_fractionRing_over_away_algHom (R := R) A hf).range := by
  let φ := localized_intermediate_to_fractionRing_over_away_algHom (R := R) A hf
  -- Proof comment: the localized inclusion is injective and its range-restriction is always
  -- surjective, so `AlgEquiv.ofBijective` packages the source-faithful identification with the
  -- image inside the common fraction field.
  refine AlgEquiv.ofBijective φ.rangeRestrict ?_
  refine ⟨?_, AlgHom.rangeRestrict_surjective φ⟩
  intro x y hxy
  exact localized_intermediate_to_fractionRing_over_away_injective (R := R) A hf
    (congrArg Subtype.val hxy)

/-- Helper for Lemma 10.161.15: the localized inclusion into the common fraction field has range
finite over the principal localization `R_f`. -/
lemma localized_intermediate_range_finite_over_away
    (A : Subalgebra R (FractionRing R)) {f : R} (hf : f ≠ 0)
    [Algebra (Localization.Away f) (FractionRing R)]
    [IsScalarTower R (Localization.Away f) (FractionRing R)]
    (hfinite : Module.Finite R A) :
    Module.Finite (Localization.Away f)
      (localized_intermediate_to_fractionRing_over_away_algHom (R := R) A hf).range := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R A f)) :=
    localizationAwayImageAlgebra (R := R) (A := A) f
  letI : Module (Localization.Away f) (Localization.Away (algebraMap R A f)) :=
    (localizationAwayImageAlgebra (R := R) (A := A) f).toModule
  letI : Module.Finite (Localization.Away f) (Localization.Away (algebraMap R A f)) :=
    moduleFinite_localizationAway_of_finite_intermediate (R := R) (A := A) (f := f) hfinite
  let e := localized_intermediate_range_equiv_over_away (R := R) A hf
  -- Proof comment: the source is already finite after localizing away from `f`, and the new
  -- equivalence transports that finite generation directly to the range.
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 10.161.15: once `R_f` is normal, every finite intermediate ring becomes
normal after localizing away from the image of `f`. -/
lemma isNormalRing_localizationAway_of_finite_intermediate
    {f : R} (hf : f ≠ 0) (hAway : IsNormalRing (Localization.Away f))
    (A : Subalgebra R (FractionRing R)) (hfinite : Module.Finite R A) :
    IsNormalRing (Localization.Away (algebraMap R A f)) := by
  -- Proof comment: with the localized range package available, the remaining source-faithful
  -- closing step is to collapse that finite range inside the common fraction field of `R_f`,
  -- identify it with the bottom subalgebra, and transport normality back across the resulting
  -- equivalence.
  letI : IsDomain (Localization.Away (algebraMap R A f)) :=
    isDomain_localizationAway_of_finite_intermediate (R := R) A hf
  let hpow : Submonoid.powers f ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf
  letI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f) hpow
  letI : Algebra (Localization.Away f) (FractionRing R) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away f) (FractionRing R) (Submonoid.powers f) (nonZeroDivisors R) hpow
  letI : IsScalarTower R (Localization.Away f) (FractionRing R) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away f) (FractionRing R) (Submonoid.powers f) (nonZeroDivisors R) hpow
  letI : IsFractionRing (Localization.Away f) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers f) (Localization.Away f) (FractionRing R)
  letI : IsNormalRing (Localization.Away f) := hAway
  let φ := localized_intermediate_to_fractionRing_over_away_algHom (R := R) A hf
  have hφinj : Function.Injective φ :=
    localized_intermediate_to_fractionRing_over_away_injective (R := R) A hf
  have hφfinite : Module.Finite (Localization.Away f) φ.range :=
    localized_intermediate_range_finite_over_away (R := R) A hf hfinite
  have hbot : φ.range = ⊥ := by
    exact eq_bot_of_finite_subalgebra_of_isNormalRing_commonFractionField
      (S := Localization.Away f) (K := FractionRing R) φ.range hφfinite
  let eRange :
      Localization.Away (algebraMap R A f) ≃ₐ[Localization.Away f] φ.range :=
    localized_intermediate_range_equiv_over_away (R := R) A hf
  let e :
      Localization.Away (algebraMap R A f) ≃ₐ[Localization.Away f] Localization.Away f :=
    eRange.trans <|
      (Subalgebra.equivOfEq _ _ hbot).trans <|
        Algebra.botEquivOfInjective (R := Localization.Away f) (A := FractionRing R)
          (IsFractionRing.injective (Localization.Away f) (FractionRing R))
  exact isNormalRing_of_equiv e.symm.toRingEquiv

/-- Helper for Lemma 10.161.15: the fixed normal-away witness on `R` should make the bad image of
every finite intermediate ring closed. -/
lemma isClosed_badImage_of_finite_intermediate
    (hnormalAway : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f))
    (A : Subalgebra R (FractionRing R)) (hfinite : Module.Finite R A) :
    IsClosed (badImage (R := R) A) := by
  rcases hnormalAway with ⟨f, hf, hAway⟩
  have hfA : algebraMap R A f ≠ 0 := by
    intro hfA
    apply hf
    exact (IsFractionRing.injective R (FractionRing R)) <| by
      simpa using congrArg (fun z : A => (z : FractionRing R)) hfA
  have hopen : IsOpen (PrimeSpectrum.normalLocus A) := by
    letI : Module.Finite R A := hfinite
    letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
    -- Proof comment: after transporting the source witness `R_f` normal to the finite
    -- intermediate ring `A`, Lemma `10.161.14` makes the normal locus of `A` open.
    apply isOpen_normal_locus_of_exists_isNormalRing_localizationAway
    refine ⟨algebraMap R A f, hfA, ?_⟩
    exact isNormalRing_localizationAway_of_finite_intermediate
      (R := R) hf hAway A hfinite
  -- Proof comment: the bad image is the image of the closed non-normal locus under an integral
  -- finite map, hence closed.
  exact isClosed_badImage_of_isOpen_normalLocus (R := R) A hfinite hopen

/-- Helper for Lemma 10.161.15: an `N-1` domain has finite normalization in any chosen model of
its fraction field. -/
lemma moduleFinite_integralClosure_of_isN1Ring_of_isFractionRing
    {S : Type*} [CommRing S] [IsDomain S] [IsN1Ring S]
    {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] :
    Module.Finite S (integralClosure S L) := by
  letI : Module.Finite S (integralClosure S (FractionRing S)) :=
    IsN1Ring.integralClosure_finite (R := S)
  exact Module.Finite.equiv (FractionRing.algEquiv S L).mapIntegralClosure.toLinearEquiv

/-- Helper for Lemma 10.161.15: the maximal-local `N-1` hypothesis makes the local normalization
finite even after transporting the common fraction field back to `FractionRing R`. -/
lemma moduleFinite_local_normalization_common_fraction_field
    (m : MaximalSpectrum R) (hm : IsN1Ring (Localization.AtPrime m.asIdeal)) :
    Module.Finite (Localization.AtPrime m.asIdeal)
      (integralClosure (Localization.AtPrime m.asIdeal) (FractionRing R)) := by
  letI : IsN1Ring (Localization.AtPrime m.asIdeal) := hm
  letI : Algebra (Localization.AtPrime m.asIdeal) (FractionRing R) := by
    infer_instance
  letI : IsFractionRing (Localization.AtPrime m.asIdeal) (FractionRing R) := by
    infer_instance
  -- Proof comment: the local `N-1` witness already gives finite normalization over the standard
  -- local fraction field, and the common-field equivalence transports that finiteness unchanged.
  exact moduleFinite_integralClosure_of_isN1Ring_of_isFractionRing
    (S := Localization.AtPrime m.asIdeal) (L := FractionRing R)

/-- Helper for Lemma 10.161.15: an element integral over `R` in the common fraction field remains
integral over the maximal localization `R_𝔪`. -/
lemma map_integralClosure_to_local_normalization_mem
    (m : MaximalSpectrum R) (x : integralClosure R (FractionRing R)) :
    (x : FractionRing R) ∈ integralClosure (Localization.AtPrime m.asIdeal) (FractionRing R) := by
  -- Proof comment: integrality ascends along the scalar tower `R → R_𝔪 → Frac(R)`.
  change IsIntegral (Localization.AtPrime m.asIdeal) (x : FractionRing R)
  exact x.2.tower_top

/-- Helper for Lemma 10.161.15: the identity on the common fraction field restricts to the
canonical map from the global normalization to the maximal-local normalization. -/
noncomputable def integralClosure_to_local_normalization
    (m : MaximalSpectrum R) :
    integralClosure R (FractionRing R) →ₐ[R]
      (integralClosure (Localization.AtPrime m.asIdeal) (FractionRing R)).restrictScalars R :=
  let hle :
      integralClosure R (FractionRing R) ≤
        (integralClosure (Localization.AtPrime m.asIdeal) (FractionRing R)).restrictScalars R := by
    intro x hx
    exact map_integralClosure_to_local_normalization_mem (R := R) m ⟨x, hx⟩
  Subalgebra.inclusion hle

/-- Helper for Lemma 10.161.15: adjoining finitely many elements of the global normalization inside
the common fraction field produces a finite intermediate ring. -/
lemma moduleFinite_adjoin_of_integralClosure_family
    {n : ℕ} (y : Fin n → integralClosure R (FractionRing R)) :
    Module.Finite R
      (Algebra.adjoin R (Set.range fun i ↦ ((y i : integralClosure R (FractionRing R)) :
        FractionRing R))) := by
  let s : Set (FractionRing R) :=
    Set.range fun i ↦ ((y i : integralClosure R (FractionRing R)) : FractionRing R)
  have hsfinite : s.Finite := Set.finite_range _
  have hsintegral : ∀ z ∈ s, IsIntegral R z := by
    rintro _ ⟨i, rfl⟩
    exact (y i).2
  -- Proof comment: the adjoined generators already lie in the integral closure, so the standard
  -- finite-adjoin theorem closes the finiteness step.
  simpa [s] using
    Algebra.finite_adjoin_of_finite_of_isIntegral (R := R) hsfinite hsintegral

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- Helper for Lemma 10.161.15: if the localization of a finite intermediate ring at the
complement of a maximal ideal is integrally closed, then that maximal ideal does not lie in the
bad image. -/
lemma not_mem_badImage_of_isIntegrallyClosed_localization_at_maximal_complement
    (A : Subalgebra R (FractionRing R)) (m : MaximalSpectrum R)
    [IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl))] :
    m.toPrimeSpectrum ∉ badImage (R := R) A := by
  let M : Submonoid A := Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl
  let Am : Type u := Localization M
  have hM_nonZero : M ≤ nonZeroDivisors A :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul A
      m.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsDomain Am := IsLocalization.isDomain_of_le_nonZeroDivisors Am hM_nonZero
  intro hm_bad
  rcases hm_bad with ⟨qA, hqA, hqA_contract⟩
  have hcontract : Ideal.comap (algebraMap R A) qA.asIdeal = m.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqA_contract
  have hdisjoint : Disjoint (M : Set A) qA.asIdeal := by
    rw [Set.disjoint_left]
    intro a haM haQ
    rcases haM with ⟨s, hs, rfl⟩
    have hs_comap : s ∈ Ideal.comap (algebraMap R A) qA.asIdeal := by
      exact haQ
    have hs_mem : s ∈ m.asIdeal := by
      simpa [hcontract] using hs_comap
    exact hs hs_mem
  let qSIdeal : Ideal Am := Ideal.map (algebraMap A Am) qA.asIdeal
  have hqS_prime : qSIdeal.IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint M Am qA.asIdeal
      (show qA.asIdeal.IsPrime from inferInstance) hdisjoint
  let qS : PrimeSpectrum Am := ⟨qSIdeal, hqS_prime⟩
  have hqS_comap : Ideal.comap (algebraMap A Am) qS.asIdeal = qA.asIdeal := by
    simpa [qS, qSIdeal] using
      (IsLocalization.comap_map_of_isPrime_disjoint M Am
        (show qA.asIdeal.IsPrime from inferInstance) hdisjoint)
  haveI : qS.asIdeal.IsPrime := qS.2
  have hqS_normal :
      IsIntegrallyClosed (Localization.AtPrime qS.asIdeal) := by
    -- Proof comment: localizing the integrally closed semilocal ring `A_m` at the prime over `qA`
    -- stays integrally closed.
    exact isIntegrallyClosed_of_isLocalization
      (R := Am) (S := Localization.AtPrime qS.asIdeal) (M := qS.asIdeal.primeCompl)
      qS.asIdeal.primeCompl_le_nonZeroDivisors
  let pA : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A Am) qS
  have hpA_normal :
      pA ∈ PrimeSpectrum.normalLocus A := by
    letI : IsIntegrallyClosed (Localization.AtPrime qS.asIdeal) := hqS_normal
    have eLoc :
        Localization.AtPrime (Ideal.comap (algebraMap A Am) qS.asIdeal) ≃ₐ[A]
          Localization.AtPrime qS.asIdeal :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := M) qS.asIdeal
    have hcomap_normal :
        IsIntegrallyClosed (Localization.AtPrime (Ideal.comap (algebraMap A Am) qS.asIdeal)) := by
      exact IsIntegrallyClosed.of_equiv eLoc.symm.toRingEquiv
    exact (PrimeSpectrum.mem_normalLocus_iff_isIntegrallyClosed pA).mpr hcomap_normal
  have hqA_eq : pA = qA := by
    ext y
    change ((algebraMap A Am) y ∈ qS.asIdeal) ↔ y ∈ qA.asIdeal
    simpa [Ideal.mem_comap] using congrArg (fun I : Ideal A => y ∈ I) hqS_comap
  exact hqA (hqA_eq ▸ hpA_normal)

/-- Helper for Lemma 10.161.15: maximal-local `N-1` data should produce a finite intermediate ring
whose bad image avoids the chosen maximal ideal. -/
lemma exists_finite_intermediate_avoiding_bad_image_at_maximal
    (m : MaximalSpectrum R) (hm : IsN1Ring (Localization.AtPrime m.asIdeal)) :
    ∃ A : Subalgebra R (FractionRing R),
      Module.Finite R A ∧ m.toPrimeSpectrum ∉ badImage (R := R) A := by
  classical
  -- Proof comment: follow the source route by generating the local normalization of `R_m` with
  -- finitely many integral elements, lift those generators back to `Frac(R)`, and adjoin them to
  -- `R`. The resulting finite intermediate ring has localization at `m` equal to the local
  -- normalization, so `m` is not in its bad image.
  let K := FractionRing R
  let N : Type u := integralClosure (Localization.AtPrime m.asIdeal) K
  letI : Algebra (Localization.AtPrime m.asIdeal) K := by
    infer_instance
  letI : IsScalarTower R (Localization.AtPrime m.asIdeal) K := by
    infer_instance
  letI : IsFractionRing (Localization.AtPrime m.asIdeal) K := by
    infer_instance
  letI : CommRing N := inferInstance
  letI : Algebra (Localization.AtPrime m.asIdeal) N := inferInstance
  letI : Module (Localization.AtPrime m.asIdeal) N := inferInstance
  have hfinite_local :
      Module.Finite (Localization.AtPrime m.asIdeal) N :=
    moduleFinite_local_normalization_common_fraction_field (R := R) m hm
  letI : Module.Finite (Localization.AtPrime m.asIdeal) N := hfinite_local
  obtain ⟨n, x, _hx⟩ := Module.Finite.exists_fin
    (R := Localization.AtPrime m.asIdeal)
    (M := N)
  letI : IsLocalization (Algebra.algebraMapSubmonoid K m.asIdeal.primeCompl) K := by
    let hunits :
        Algebra.algebraMapSubmonoid K m.asIdeal.primeCompl ≤ IsUnit.submonoid K := by
      rintro _ ⟨r, hr, rfl⟩
      exact IsLocalization.map_units K ⟨r, m.asIdeal.primeCompl_le_nonZeroDivisors hr⟩
    exact IsLocalization.self hunits
  let localMap := integralClosure_to_local_normalization (R := R) m
  letI : Algebra (integralClosure R K) N :=
    localMap.toAlgebra
  letI : IsScalarTower R (integralClosure R K)
      N := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext r
    rfl
  letI : IsScalarTower (integralClosure R K) N K := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext z
    rfl
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl)
        N := by
    exact IsLocalization.integralClosure
      (R := R) (S := K) (Rf := Localization.AtPrime m.asIdeal) (Sf := K) m.asIdeal.primeCompl
  let y : Fin n → integralClosure R K := fun i ↦
    (IsLocalization.sec
      (Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl) (x i)).1
  let A : Subalgebra R K :=
    Algebra.adjoin R (Set.range fun i ↦ ((y i : integralClosure R K) : K))
  have hfiniteA : Module.Finite R A :=
    moduleFinite_adjoin_of_integralClosure_family (R := R) y
  refine ⟨A, hfiniteA, ?_⟩
  have hA_le : A ≤ integralClosure R K := by
    refine Algebra.adjoin_le_iff.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (y i).2
  let inclA : A →ₐ[R] integralClosure R K := Subalgebra.inclusion hA_le
  let phi :
      Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl) →ₐ[
        Localization.AtPrime m.asIdeal] N :=
    IsLocalization.mapₐ
      m.asIdeal.primeCompl
      (Localization.AtPrime m.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl))
      N
      inclA
  have hx_range : ∀ i, x i ∈ AlgHom.range phi := by
    intro i
    let si : Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl :=
      (IsLocalization.sec
        (Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl) (x i)).2
    rcases si.2 with ⟨s, hs, hsi_eq⟩
    have hyiA_mem : ((y i : integralClosure R K) : K) ∈ A := by
      exact Algebra.subset_adjoin (Set.mem_range_self i)
    let yiA : A := ⟨((y i : integralClosure R K) : K), hyiA_mem⟩
    have hsiA_mem :
        algebraMap R A s ∈ Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl := by
      exact Algebra.mem_algebraMapSubmonoid_of_mem ⟨s, hs⟩
    let siA : Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl := ⟨algebraMap R A s, hsiA_mem⟩
    have hsiN_mem :
        algebraMap R (integralClosure R K) s ∈
          Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl := by
      exact
        Algebra.mem_algebraMapSubmonoid_of_mem
          (R := R) (S := integralClosure R K) (M := m.asIdeal.primeCompl) ⟨s, hs⟩
    have hphi_mk :
        phi (IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl))
          yiA siA) =
          IsLocalization.mk' N (y i)
            ⟨algebraMap R (integralClosure R K) s, hsiN_mem⟩ := by
      -- Proof comment: the localized map on the adjoined ring sends the chosen numerator and
      -- denominator to the corresponding data in the localized normalization.
      simpa [phi, inclA, yiA, siA] using
        (IsLocalization.map_mk'
          (S := Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl))
          (Q := N)
          (g := (inclA : A →ₐ[R] integralClosure R K).toRingHom)
          (hy := Algebra.algebraMapSubmonoid_le_comap m.asIdeal.primeCompl inclA)
          yiA siA)
    have hmk :
        IsLocalization.mk' N (y i)
          ⟨algebraMap R (integralClosure R K) s, hsiN_mem⟩ = x i := by
      -- Proof comment: `IsLocalization.sec_spec'` rewrites the local generator `x i` as the
      -- localization fraction coming from its chosen sec-lift in the global normalization.
      have hsi :
          (⟨algebraMap R (integralClosure R K) s, hsiN_mem⟩ :
            Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl) = si := by
        apply Subtype.ext
        exact hsi_eq
      have hmk_si : IsLocalization.mk' N (y i) si = x i := by
        change
          IsLocalization.mk' N
              (IsLocalization.sec
                (Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl)
                (x i)).1
              si = x i
        simpa [si] using
          (IsLocalization.mk'_sec
            (M := Algebra.algebraMapSubmonoid (integralClosure R K) m.asIdeal.primeCompl)
            N (x i))
      exact hsi ▸ hmk_si
    refine ⟨IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl))
      yiA siA, ?_⟩
    exact hphi_mk.trans hmk
  have hspan_le :
      Submodule.span (Localization.AtPrime m.asIdeal) (Set.range x) ≤
        (AlgHom.range phi).toSubmodule := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hx_range i
  have hphi_range_top :
      (AlgHom.range phi : Subalgebra (Localization.AtPrime m.asIdeal) N) = ⊤ := by
    -- Proof comment: once every chosen module generator lies in the range, the spanning equality
    -- from `Module.Finite.exists_fin` forces the localized map to be surjective.
    refine le_antisymm le_top ?_
    intro z hz
    have hz_span :
        z ∈ Submodule.span (Localization.AtPrime m.asIdeal) (Set.range x) := by
      simpa [_hx] using
        (show z ∈ (⊤ : Submodule (Localization.AtPrime m.asIdeal) N) by trivial)
    exact hspan_le hz_span
  have hphi_surj : Function.Surjective phi := by
    intro z
    have hz_range : z ∈ AlgHom.range phi := by
      simpa [hphi_range_top] using
        (show z ∈ (⊤ : Subalgebra (Localization.AtPrime m.asIdeal) N) by trivial)
    rcases hz_range with ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  have hphi_inj : Function.Injective phi := by
    -- Proof comment: the localized map is induced from the inclusion `A ↪ integralClosure R K`,
    -- so injectivity descends from the localization functor.
    exact IsLocalization.mapₐ_injective_of_injective
      m.asIdeal.primeCompl
      (Localization.AtPrime m.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl))
      N
      inclA
      (Subalgebra.inclusion_injective hA_le)
  let e :
      Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl) ≃ₐ[
        Localization.AtPrime m.asIdeal] N :=
    AlgEquiv.ofBijective phi ⟨hphi_inj, hphi_surj⟩
  letI : IsFractionRing N K :=
    integralClosure.isFractionRing_of_finite_extension
      (A := Localization.AtPrime m.asIdeal) (K := K) (L := K)
  have hN_integrallyClosed : IsIntegrallyClosed N := by
    -- Proof comment: the local normalization is integrally closed by construction, once we view
    -- the common fraction field `K` as its fraction field.
    exact (isIntegrallyClosed_iff_isIntegrallyClosedIn (R := N) (K := K)).2 inferInstance
  letI :
      IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid A m.asIdeal.primeCompl)) := by
    letI : IsIntegrallyClosed N := hN_integrallyClosed
    exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv
  -- Route correction: the previous blocked route tried to go straight from the adjoined lifts to
  -- `m ∉ badImage A`. The stable midpoint is first to identify the localization of `A` at
  -- `m.asIdeal.primeCompl` with the local normalization `N`, and only then descend normality to
  -- primes above `m`.
  exact not_mem_badImage_of_isIntegrallyClosed_localization_at_maximal_complement
    (R := R) A m

/-- Helper for Lemma 10.161.15: if a finite intermediate ring over a common fraction field has
empty bad image, then all of its prime localizations are integrally closed. -/
lemma isIntegrallyClosed_of_empty_badImage_commonFractionField
    {S : Type*} [CommRing S] [IsDomain S] {K : Type*} [Field K] [Algebra S K]
    [IsFractionRing S K] (B : Subalgebra S K)
    (hbad : PrimeSpectrum.comap (algebraMap S B) '' (PrimeSpectrum.normalLocus B)ᶜ = ∅) :
    IsIntegrallyClosed B := by
  have hmax :
      ∀ M : MaximalSpectrum B, M.toPrimeSpectrum ∈ PrimeSpectrum.normalLocus B := by
    intro M
    by_contra hM
    have hmem :
        PrimeSpectrum.comap (algebraMap S B) M.toPrimeSpectrum ∈
          PrimeSpectrum.comap (algebraMap S B) '' (PrimeSpectrum.normalLocus B)ᶜ := by
      exact ⟨M.toPrimeSpectrum, hM, rfl⟩
    have : PrimeSpectrum.comap (algebraMap S B) M.toPrimeSpectrum ∈ (∅ : Set (PrimeSpectrum S)) := by
      simpa [hbad] using hmem
    exact this.elim
  -- Proof comment: empty bad image says every maximal point of `Spec(B)` lies in the normal
  -- locus, so the standard maximal-local criterion globalizes integrally closedness.
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun p _ ↦ Localization.AtPrime p)
    fun p hp ↦ by
      let M : MaximalSpectrum B := ⟨p, hp⟩
      exact
        (PrimeSpectrum.mem_normalLocus_iff_isIntegrallyClosed M.toPrimeSpectrum).mp
          (hmax M)

/-- Helper for Lemma 10.161.15: over a common fraction field, a finite intermediate ring with
empty bad image is the integral closure of the base ring. -/
lemma finite_normalization_of_empty_badImage_commonFractionField
    {S : Type*} [CommRing S] [IsDomain S] {K : Type*} [Field K] [Algebra S K]
    [IsFractionRing S K] (B : Subalgebra S K) (hfinite : Module.Finite S B)
    (hbad : PrimeSpectrum.comap (algebraMap S B) '' (PrimeSpectrum.normalLocus B)ᶜ = ∅) :
    Module.Finite S (integralClosure S K) := by
  letI : Algebra.IsIntegral S B := Algebra.IsIntegral.of_finite S B
  letI : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_empty_badImage_commonFractionField (S := S) (K := K) B hbad
  letI : IsIntegralClosure B S K := by
    infer_instance
  let e :
      integralClosure S K ≃ₐ[S] B :=
    IsIntegralClosure.equiv S (integralClosure S K) K B
  -- Proof comment: once the intermediate ring is another integrally closed integral model of the
  -- common fraction field, the canonical equivalence transports finite generation back to the
  -- integral closure.
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Helper for Lemma 10.161.15: the localized finite intermediate ring is represented by the
range of the canonical localized inclusion into the common fraction field. -/
noncomputable abbrev localized_intermediate_range_over_away
    (A : Subalgebra R (FractionRing R)) {g : R} [Algebra (Localization.Away g) (FractionRing R)]
    [IsScalarTower R (Localization.Away g) (FractionRing R)] (hg0 : g ≠ 0) :
    Subalgebra (Localization.Away g) (FractionRing R) :=
  (localized_intermediate_to_fractionRing_over_away_algHom (R := R) A hg0).range

/-- Helper for Lemma 10.161.15: localizing an away-localization at a prime is canonically the same
as localizing the original ring at the contracted prime. -/
noncomputable abbrev away_contracted_localization_compare_to_under
    {A : Type*} [CommRing A] {t : A} (q : Ideal (Localization.Away t)) [q.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) q) ≃ₐ[A]
      Localization.AtPrime q :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := Submonoid.powers t) q

/-- Helper for Lemma 10.161.15: a nonnormal prime of the localized intermediate ring contracts to
a nonnormal prime of the original intermediate ring, and its image in `Spec(R)` lies in the
principal open `D(g)`. -/
lemma localized_range_contracted_prime_mem_badImage
    (A : Subalgebra R (FractionRing R)) {g : R} [Algebra (Localization.Away g) (FractionRing R)]
    [IsScalarTower R (Localization.Away g) (FractionRing R)] (hg0 : g ≠ 0)
    (qL : PrimeSpectrum (Localization.Away (algebraMap R A g)))
    (hqL : qL ∉ PrimeSpectrum.normalLocus (Localization.Away (algebraMap R A g))) :
    ∃ qA : PrimeSpectrum A,
      qA ∉ PrimeSpectrum.normalLocus A ∧
        PrimeSpectrum.comap (algebraMap R A) qA ∈ PrimeSpectrum.basicOpen g := by
  let L : Type u := Localization.Away (algebraMap R A g)
  letI : IsDomain L :=
    isDomain_localizationAway_of_finite_intermediate (R := R) A hg0
  let qA : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A L) qL
  have hqA :
      qA ∉ PrimeSpectrum.normalLocus A := by
    intro hqA_normal
    letI : IsNormalRing (Localization.AtPrime qA.asIdeal) :=
      (PrimeSpectrum.mem_normalLocus qA).mp hqA_normal
    have hqL_normal :
        IsNormalRing (Localization.AtPrime qL.asIdeal) := by
      let eLoc :
          Localization.AtPrime qA.asIdeal ≃ₐ[A] Localization.AtPrime qL.asIdeal := by
        simpa [qA, PrimeSpectrum.comap_asIdeal] using
          (away_contracted_localization_compare_to_under
            (A := A) (t := algebraMap R A g) qL.asIdeal)
      exact isNormalRing_of_equiv eLoc.toRingEquiv
    exact hqL ((PrimeSpectrum.mem_normalLocus qL).2 hqL_normal)
  have hg_not_mem_qL : algebraMap A L (algebraMap R A g) ∉ qL.asIdeal := by
    intro hg_mem
    exact Ideal.IsPrime.ne_top qL.2 <|
      Ideal.eq_top_of_isUnit_mem _ hg_mem
        (IsLocalization.Away.algebraMap_isUnit (algebraMap R A g))
  have hg_not_mem_qA : algebraMap R A g ∉ qA.asIdeal := by
    simpa [qA, PrimeSpectrum.comap_asIdeal] using hg_not_mem_qL
  have hg_not_mem_R :
      g ∉ (PrimeSpectrum.comap (algebraMap R A) qA).asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using hg_not_mem_qA
  refine ⟨qA, hqA, ?_⟩
  -- Proof comment: the localized prime cannot contain the inverted element `g`, so its image in
  -- `Spec(R)` lands in the principal open `D(g)`.
  simpa [PrimeSpectrum.mem_basicOpen] using hg_not_mem_R

/-- Helper for Lemma 10.161.15: if a principal open `D(g)` avoids the bad image of a finite
intermediate ring `A`, then after localizing away from `g` the resulting finite intermediate
range has empty bad image over the localized base ring and common fraction field. -/
lemma localized_range_empty_badImage_of_basicOpen_disjoint
    (A : Subalgebra R (FractionRing R)) {g : R} [Algebra (Localization.Away g) (FractionRing R)]
    [IsScalarTower R (Localization.Away g) (FractionRing R)] (hg0 : g ≠ 0)
    (hdisjoint : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆ (badImage (R := R) A)ᶜ) :
    PrimeSpectrum.comap
        (algebraMap (Localization.Away g)
          (localized_intermediate_range_over_away (R := R) A hg0)) ''
      (PrimeSpectrum.normalLocus
        (localized_intermediate_range_over_away (R := R) A hg0))ᶜ = ∅ := by
  let B : Subalgebra (Localization.Away g) (FractionRing R) :=
    localized_intermediate_range_over_away (R := R) A hg0
  apply Set.eq_empty_iff_forall_notMem.2
  intro p hp
  rcases hp with ⟨q, hq, rfl⟩
  let L : Type u := Localization.Away (algebraMap R A g)
  letI : IsDomain L :=
    isDomain_localizationAway_of_finite_intermediate (R := R) A hg0
  let B : Subalgebra (Localization.Away g) (FractionRing R) :=
    localized_intermediate_range_over_away (R := R) A hg0
  let eRange : L ≃ₐ[Localization.Away g] B :=
    localized_intermediate_range_equiv_over_away (R := R) A hg0
  let qL : PrimeSpectrum L := PrimeSpectrum.comap eRange.toRingHom q
  have hqL :
      qL ∉ PrimeSpectrum.normalLocus L := by
    intro hqL_normal
    letI : IsNormalRing (Localization.AtPrime qL.asIdeal) :=
      (PrimeSpectrum.mem_normalLocus qL).mp hqL_normal
    have hq_normal :
        IsNormalRing (Localization.AtPrime q.asIdeal) := by
      let eRing : L ≃+* B := eRange.toRingEquiv
      let eLoc :
          Localization.AtPrime qL.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
        localizationAtPrimeRingEquiv (R := L) (S := B) eRing q
      exact isNormalRing_of_equiv eLoc
    exact hq ((PrimeSpectrum.mem_normalLocus q).2 hq_normal)
  obtain ⟨qA, hqA, hqA_basic⟩ :=
    localized_range_contracted_prime_mem_badImage (R := R) A hg0 qL hqL
  have hbad :
      PrimeSpectrum.comap (algebraMap R A) qA ∈ badImage (R := R) A := by
    exact ⟨qA, hqA, rfl⟩
  -- Proof comment: every nonnormal prime of the localized range would induce a bad-image point of
  -- `A` inside `D(g)`, contradicting the assumed disjointness.
  exact (hdisjoint hqA_basic) hbad

/-- Helper for Lemma 10.161.15: if a maximal ideal is not in the bad image of a finite
intermediate ring, then some principal neighborhood of that maximal ideal is `N-1`. -/
lemma exists_isN1Ring_localizationAway_of_not_mem_badImage
    (hnormalAway : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f))
    (A : Subalgebra R (FractionRing R)) (hfinite : Module.Finite R A)
    (m : MaximalSpectrum R) (hm : m.toPrimeSpectrum ∉ badImage (R := R) A) :
    ∃ g : R, g ∉ m.asIdeal ∧ ∃ hg0 : g ≠ 0, IsN1Ring (Localization.Away g) := by
  let U : TopologicalSpace.Opens (PrimeSpectrum R) :=
    ⟨(badImage (R := R) A)ᶜ,
      (isClosed_badImage_of_finite_intermediate (R := R) hnormalAway A hfinite).isOpen_compl⟩
  have hmU : m.toPrimeSpectrum ∈ U := hm
  obtain ⟨_, ⟨g, rfl⟩, hm_basic, hgsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmU U.2
  have hgm : g ∉ m.asIdeal := by
    simpa [PrimeSpectrum.mem_basicOpen] using hm_basic
  have hg0 : g ≠ 0 := by
    intro hg
    exact hgm (hg ▸ Ideal.zero_mem _)
  let hpow : Submonoid.powers g ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  letI : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away g) hpow
  letI : Algebra (Localization.Away g) (FractionRing R) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away g) (FractionRing R) (Submonoid.powers g) (nonZeroDivisors R) hpow
  letI : IsScalarTower R (Localization.Away g) (FractionRing R) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away g) (FractionRing R) (Submonoid.powers g) (nonZeroDivisors R) hpow
  letI : IsFractionRing (Localization.Away g) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers g) (Localization.Away g) (FractionRing R)
  let B := localized_intermediate_range_over_away (R := R) A hg0
  have hbad_empty :
      PrimeSpectrum.comap (algebraMap (Localization.Away g) B) ''
        (PrimeSpectrum.normalLocus B)ᶜ = ∅ := by
    exact localized_range_empty_badImage_of_basicOpen_disjoint
      (R := R) A hg0 (show (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
        (badImage (R := R) A)ᶜ from hgsub)
  have hfinite_range : Module.Finite (Localization.Away g) B := by
    exact localized_intermediate_range_finite_over_away (R := R) A hg0 hfinite
  have hfinite_common :
      Module.Finite (Localization.Away g)
        (integralClosure (Localization.Away g) (FractionRing R)) := by
    exact finite_normalization_of_empty_badImage_commonFractionField
      (S := Localization.Away g) (K := FractionRing R) B hfinite_range hbad_empty
  have hfinite_standard :
      Module.Finite (Localization.Away g)
        (integralClosure (Localization.Away g) (FractionRing (Localization.Away g))) := by
    exact Module.Finite.equiv
      (FractionRing.algEquiv (Localization.Away g) (FractionRing R)).mapIntegralClosure.symm.toLinearEquiv
  -- Proof comment: shrinking away from the closed bad image produces a principal-open chart where
  -- the localized finite intermediate range already equals the whole normalization.
  exact ⟨g, hgm, ⟨hg0, IsN1Ring.mk hfinite_standard⟩⟩

/-- Helper for Lemma 10.161.15: if the bad image of a finite intermediate ring is empty, then all
its maximal localizations are normal, hence the intermediate ring is integrally closed. -/
lemma isIntegrallyClosed_of_empty_badImage
    (A : Subalgebra R (FractionRing R))
    (hbad : badImage (R := R) A = ∅) :
    IsIntegrallyClosed A := by
  have hmax :
      ∀ M : MaximalSpectrum A, M.toPrimeSpectrum ∈ PrimeSpectrum.normalLocus A := by
    intro M
    by_contra hM
    have hmem :
        PrimeSpectrum.comap (algebraMap R A) M.toPrimeSpectrum ∈ badImage (R := R) A := by
      exact ⟨M.toPrimeSpectrum, hM, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R A) M.toPrimeSpectrum ∈ (∅ : Set (PrimeSpectrum R)) := by
      simpa [hbad] using hmem
    exact this.elim
  -- Proof comment: empty bad image says every maximal point of `Spec(A)` lies in the normal
  -- locus, so the standard maximal-local criterion globalizes integrally closedness.
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun p _ ↦ Localization.AtPrime p)
    fun p hp ↦ by
      let M : MaximalSpectrum A := ⟨p, hp⟩
      exact
        (PrimeSpectrum.mem_normalLocus_iff_isIntegrallyClosed M.toPrimeSpectrum).mp
          (hmax M)

/-- Helper for Lemma 10.161.15: a finite intermediate ring whose bad image is empty is the global
normalization, hence gives the required finite normalization of `R`. -/
lemma finite_normalization_of_empty_badImage
    (A : Subalgebra R (FractionRing R)) (hfinite : Module.Finite R A)
    (hbad : badImage (R := R) A = ∅) :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  letI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  letI : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_empty_badImage (R := R) A hbad
  letI : IsIntegralClosure A R (FractionRing R) := by
    infer_instance
  let e :
      integralClosure R (FractionRing R) ≃ₐ[R] A :=
    IsIntegralClosure.equiv
      R
      (integralClosure R (FractionRing R))
      (FractionRing R)
      A
  -- Proof comment: once the intermediate ring is integrally closed and still integral over `R`,
  -- it is another model of the integral closure in the common fraction field, so the canonical
  -- equivalence transports finite generation back to `integralClosure R Frac(R)`.
  exact Module.Finite.equiv e.toLinearEquiv.symm

-- Proof sketch: let `M = integralClosure R (FractionRing R)`. The hypothesis `hnormalAway`
-- supplies the source-facing principal-open normality witness needed to control the non-normal
-- locus of finite intermediate rings. For each maximal ideal `m`, the hypothesis `hlocal m` and
-- localization compatibility of integral closure identify `Mₘ` with the finite normalization of
-- `Localization.AtPrime m.asIdeal`. These local finite normalizations glue, via the quasi-compact
-- closed-set argument of the Stacks proof, to a global finite normalization map.
/-- Lemma 10.161.15 (3): if there exists a nonzero `f : R` such that `R_f` is normal, and every
localization `R_𝔪` at a maximal ideal is `N-1`, then `R` is `N-1`. -/
@[stacks 0333]
theorem isN1Ring_of_exists_isNormalRing_localizationAway_of_forall_maximal_isN1Ring_localizationAtMaximal
    (hnormalAway : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f))
    (hlocal : ∀ m : MaximalSpectrum R, IsN1Ring (Localization.AtPrime m.asIdeal)) :
    IsN1Ring R := by
  classical
  rcases hnormalAway with ⟨f, hf0, hAway⟩
  have hpowf : Submonoid.powers f ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  have hdomf : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f) hpowf
  have hwitness :
      ∀ m : MaximalSpectrum R, f ∈ m.asIdeal →
        ∃ g : R, g ∉ m.asIdeal ∧ ∃ hg0 : g ≠ 0, IsN1Ring (Localization.Away g) := by
    intro m hfm
    obtain ⟨A, hfiniteA, hmA⟩ :=
      exists_finite_intermediate_avoiding_bad_image_at_maximal (R := R) m (hlocal m)
    exact exists_isN1Ring_localizationAway_of_not_mem_badImage
      (R := R) ⟨f, hf0, hAway⟩ A hfiniteA m hmA
  obtain ⟨s, hs, hf_mem, hs_prop⟩ :=
    exists_finite_basicOpen_cover_of_maximal_witness
      (R := R) f (fun g ↦ ∃ hg0 : g ≠ 0, IsN1Ring (Localization.Away g)) hwitness
  have hdom : ∀ a : s, IsDomain (Localization.Away a.1) := by
    intro a
    rcases hs_prop a.1 a.2 with rfl | ha
    · simpa using hdomf
    · rcases ha with ⟨ha0, _⟩
      exact IsLocalization.isDomain_of_le_nonZeroDivisors
        (Localization.Away a.1) (powers_le_nonZeroDivisors_of_noZeroDivisors ha0)
  have hN1 : ∀ a : s, let _ : IsDomain (Localization.Away a.1) := hdom a
      IsN1Ring (Localization.Away a.1) := by
    intro a
    rcases hs_prop a.1 a.2 with rfl | ha
    · exact isN1Ring_localizationAway_of_normalAway (R := R) hAway
    · exact ha.2
  -- Proof comment: the original normal-away witness `f` handles the chart `D(f)`, and every
  -- maximal ideal containing `f` supplies an auxiliary principal-open `N-1` chart. The finite
  -- cover produced from those local witnesses now falls under Lemma `10.161.4`.
  exact isN1Ring_of_isN1Ring_localizationAway (R := R) (s := s) hs hdom hN1

end

end
