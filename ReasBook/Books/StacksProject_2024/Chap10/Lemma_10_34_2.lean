import Mathlib
import StacksProject_2024.Chap10.Lemma_10_30_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Localization
open PrimeSpectrum TopologicalSpace

section

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K]

-- Layering for this item:
-- * source-facing: the existence of a nonzero localization `R_f` that is a field and makes the
--   induced map to `K` finite.
-- * core/canonical owners: `Localization.Away`, the canonical lift `awayLift`, and the owner
--   finiteness predicates `RingHom.FiniteType` and `RingHom.Finite`.
-- * bridge/view: `RingHom.FiniteType.of_comp_finiteType` and
--   `RingHom.finite_iff_finiteType_of_isJacobsonRing`.

/-- Helper for Lemma 10.34.2: the image of `Spec K → Spec R` is the generic point when
`R → K` is injective and `K` is a field. -/
lemma comap_image_algebraMap_field_eq_singleton_bot
    [IsDomain R] (hinj : Function.Injective (algebraMap R K)) :
    (PrimeSpectrum.comap (algebraMap R K) '' (Set.univ : Set (PrimeSpectrum K))) =
      ({(⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    -- Every prime ideal of a field is zero, so its contraction is the zero prime.
    apply Set.mem_singleton_iff.mpr
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    rcases Ideal.eq_bot_or_top y.asIdeal with hy | hy
    · rw [hy, Ideal.comap_bot_of_injective _ hinj]
    · exact (y.isPrime.ne_top hy).elim
  · intro hx
    have hbot_mem_univ :
        (⟨(⊥ : Ideal K), Ideal.isPrime_bot⟩ : PrimeSpectrum K) ∈
          (Set.univ : Set (PrimeSpectrum K)) := by
      simp
    refine ⟨(⟨(⊥ : Ideal K), Ideal.isPrime_bot⟩ : PrimeSpectrum K), hbot_mem_univ, ?_⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    -- Contracting the zero prime along an injective map still gives the zero prime.
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_bot_of_injective _ hinj]

/-- Helper for Lemma 10.34.2: finite type over a field image gives a nonzero basic open equal to
the generic point of `Spec R`. -/
lemma exists_nonzero_basicOpen_eq_singleton_bot_of_finiteType_to_field
    [IsDomain R] (hinj : Function.Injective (algebraMap R K)) [Algebra.FiniteType R K] :
    ∃ f : R, f ≠ 0 ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) =
        ({(⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩ : PrimeSpectrum R)} : Set _) := by
  let ξ0 : PrimeSpectrum R := ⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩
  have hfiniteType : (algebraMap R K).FiniteType := by
    exact (RingHom.finiteType_algebraMap).2 (inferInstance : Algebra.FiniteType R K)
  have hξ0_mem_image :
      ξ0 ∈ PrimeSpectrum.comap (algebraMap R K) '' (Set.univ : Set (PrimeSpectrum K)) := by
    rw [comap_image_algebraMap_field_eq_singleton_bot (R := R) (K := K) hinj]
    simp [ξ0]
  obtain ⟨W, hW_dense, hW_subset⟩ :=
    exists_open_dense_subset_closure_singleton_of_mem_comap_image_constructible
      (f := algebraMap R K) (E := (Set.univ : Set (PrimeSpectrum K))) (ξ := ξ0)
      hfiniteType Topology.IsConstructible.univ hξ0_mem_image
  have hclosure_univ :
      closure ({ξ0} : Set (PrimeSpectrum R)) = Set.univ := by
    simpa [ξ0, PrimeSpectrum.closure_singleton, PrimeSpectrum.zeroLocus_singleton_zero]
  have hclosure_open : IsOpen (closure ({ξ0} : Set (PrimeSpectrum R))) := by
    simpa [hclosure_univ] using (isOpen_univ : IsOpen (Set.univ : Set (PrimeSpectrum R)))
  have hclosure_dense : Dense (closure ({ξ0} : Set (PrimeSpectrum R))) := by
    simpa [hclosure_univ] using (dense_univ : Dense (Set.univ : Set (PrimeSpectrum R)))
  obtain ⟨U, hU_dense, hU_subset_closure, hU_preimage⟩ :=
    image_open_dense_of_dense_open_subspace
      (U := closure ({ξ0} : Set (PrimeSpectrum R))) hclosure_open hclosure_dense W.2 hW_dense
  have hU_subset_singleton : (U : Set (PrimeSpectrum R)) ⊆ ({ξ0} : Set (PrimeSpectrum R)) := by
    intro x hxU
    have hxClosure : x ∈ closure ({ξ0} : Set (PrimeSpectrum R)) := hU_subset_closure hxU
    have hxPreimage :
        (⟨x, hxClosure⟩ : closure ({ξ0} : Set (PrimeSpectrum R))) ∈
          ((Subtype.val : closure ({ξ0} : Set (PrimeSpectrum R)) → PrimeSpectrum R) ⁻¹'
            (U : Set (PrimeSpectrum R))) := by
      simpa
    have hxW : (⟨x, hxClosure⟩ : closure ({ξ0} : Set (PrimeSpectrum R))) ∈ (W : Set _) := by
      simpa [hU_preimage] using hxPreimage
    have hxImage :
        x ∈ PrimeSpectrum.comap (algebraMap R K) '' (Set.univ : Set (PrimeSpectrum K)) :=
      hW_subset hxW
    rw [comap_image_algebraMap_field_eq_singleton_bot (R := R) (K := K) hinj] at hxImage
    simpa [ξ0] using hxImage
  have hU_nonempty : Set.Nonempty (U : Set (PrimeSpectrum R)) := by
    by_contra hU_empty
    have hξ0_closure : ξ0 ∈ closure (U : Set (PrimeSpectrum R)) := hU_dense ξ0
    have hU_eq_empty : (U : Set (PrimeSpectrum R)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hU_empty
    simpa [hU_eq_empty] using hξ0_closure
  obtain ⟨x, hxU⟩ := hU_nonempty
  have hx_eq : x = ξ0 := by
    simpa using hU_subset_singleton hxU
  have hξ0_mem_U : ξ0 ∈ (U : Set (PrimeSpectrum R)) := by
    simpa [hx_eq] using hxU
  obtain ⟨_, ⟨f, rfl⟩, hξ0_basicOpen, hbasicOpen_subset⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hξ0_mem_U U.2
  have hf_ne_zero : f ≠ 0 := by
    -- Membership of the zero prime in `D(f)` is equivalent to `f ≠ 0`.
    exact (PrimeSpectrum.mem_basicOpen f ξ0).1 hξ0_basicOpen
  refine ⟨f, hf_ne_zero, ?_⟩
  apply Set.Subset.antisymm
  · exact Set.Subset.trans hbasicOpen_subset hU_subset_singleton
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hξ0_basicOpen

/-- Helper for Lemma 10.34.2: if `D(f)` is the singleton generic point in a domain, then the
localization `R_f` is a field. -/
lemma isField_localizationAway_of_basicOpen_eq_singleton_bot [IsDomain R] {f : R}
    (hbasic :
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) =
        ({(⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩ : PrimeSpectrum R)} : Set _)) :
    IsField (Localization.Away f) := by
  letI : IsLocalization.AtPrime (Localization.Away f) (⊥ : Ideal R) :=
    (PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton hbasic).mp inferInstance
  letI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_atPrime (Localization.Away f) (⊥ : Ideal R)
  have hbot_minimal : (⊥ : Ideal R) ∈ minimalPrimes R := by
    simpa [IsDomain.minimalPrimes_eq_singleton_bot R]
  have hsubsingleton : Subsingleton (PrimeSpectrum (Localization.Away f)) := by
    exact IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
      (p := (⊥ : Ideal R)) hbot_minimal (Localization.Away f)
  -- A reduced ring with a one-point prime spectrum is a field.
  exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced
    (R := Localization.Away f)).mp hsubsingleton

/-- Lemma 10.34.2: if `R ⊆ K` and `K` is a finite type `R`-algebra, then some nonzero
localization `R_f` is a field and the induced map `R_f → K` is finite, i.e. `K / R_f` is a finite
field extension. -/
-- Proof sketch: apply Lemma `10.30.2` to the image of `Spec(K) → Spec(R)` to obtain a nonzero
-- `f : R` with `D(f) = {(0)}`. This makes `Spec(R_f)` a singleton, hence `R_f` a field. The
-- induced map `R_f → K` is still of finite type, and then Hilbert Nullstellensatz
-- (`finite_of_finite_type_of_isJacobsonRing`) yields finiteness over the field `R_f`.
theorem exists_nonzero_localizationAway_isField_and_finite
    (hinj : Function.Injective (algebraMap R K)) [Algebra.FiniteType R K] :
    ∃ (f : R) (hf : f ≠ 0),
      IsField (Localization.Away f) ∧
        RingHom.Finite
          (awayLift (algebraMap R K) f
            (IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R K) hinj).2 hf))) := by
  -- Source-facing primitive step: after shrinking to some basic open `D(f)`, the localization
  -- `R_f` becomes a field.
  have hfield :
      ∃ (f : R) (hf : f ≠ 0), IsField (Localization.Away f) := by
    letI : IsDomain R := Function.Injective.isDomain (algebraMap R K) hinj
    obtain ⟨f, hf, hbasic⟩ :=
      exists_nonzero_basicOpen_eq_singleton_bot_of_finiteType_to_field
        (R := R) (K := K) hinj
    -- Route correction: first obtain `D(f) = {(0)}` from the source-faithful generic-point
    -- argument, then convert that singleton spectrum statement into a field localization.
    refine ⟨f, hf, ?_⟩
    exact isField_localizationAway_of_basicOpen_eq_singleton_bot (R := R) hbasic
  rcases hfield with ⟨f, hf, hfield⟩
  let φ : Localization.Away f →+* K :=
    awayLift (algebraMap R K) f
      (IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R K) hinj).2 hf))
  have hfiniteType : φ.FiniteType := by
    have hcomp : (φ.comp (algebraMap R (Localization.Away f))).FiniteType := by
      simpa [φ] using
        (RingHom.finiteType_algebraMap).2 (inferInstance : Algebra.FiniteType R K)
    exact RingHom.FiniteType.of_comp_finiteType hcomp
  letI : Field (Localization.Away f) := hfield.toField
  have hfinite : φ.Finite := by
    exact (RingHom.finite_iff_finiteType_of_isJacobsonRing).2 hfiniteType
  exact ⟨f, hf, hfield,
    hfinite⟩

end
