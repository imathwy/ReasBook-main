import Mathlib
import StacksProject_2024.Chap10.Definition_10_153_1
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_153_4
import StacksProject_2024.Chap10.Lemma_10_153_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [StrictHenselianLocalRing R]
variable [CommRing S] [Algebra R S] [Algebra.Unramified R S]

/-- Helper for Chap10 Lemma 10 153 8: a globally quasi-finite algebra is quasi-finite at every
prime of the target. -/
private lemma quasiFiniteAt_of_quasiFinite
    {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
    [Algebra.QuasiFinite A T] (q : PrimeSpectrum T) :
    Algebra.QuasiFiniteAt A q.asIdeal := by
  -- Localizing a quasi-finite algebra at a target prime preserves quasi-finiteness.
  change Algebra.QuasiFinite A (Localization.AtPrime q.asIdeal)
  exact Algebra.QuasiFinite.of_isLocalization q.asIdeal.primeCompl

/-- Helper for Chap10 Lemma 10 153 8: once the mapped maximal ideal agrees with the target maximal
ideal, surjectivity on residue fields is exactly surjectivity of the quotient map needed for
Nakayama. -/
private theorem algebraMapQuotient_surjective_of_residueField_surjective_of_mapMaximalIdealEq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    Function.Surjective ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) := by
  -- Identify the quotient by `m_A B` with the quotient by the mapped maximal ideal.
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A B) =
        Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    simp [Ideal.smul_top_eq_map]
  let e₁ :
      (B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) ≃ₗ[A]
        (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A))) :=
    Submodule.quotEquivOfEq _ _ hsmul
  let e₂ :
      B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) →
        ResidueField B :=
    Ideal.quotEquivOfEq hmap
  have he₂inj : Function.Injective e₂ := (Ideal.quotEquivOfEq hmap).injective
  intro x
  -- Use residue-field surjectivity to choose a representative from `A`.
  obtain ⟨y, hy⟩ := hres (e₂ (e₁ x))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hquotientMap :
      ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) := by
    rfl
  have htransport :
      e₁
          (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
            (Submodule.Quotient.mk a)) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A))) := by
    rw [hquotientMap]
    simpa [e₁] using
      (Submodule.quotEquivOfEq_mk hsmul (algebraMap A B a))
  have hleft :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) =
        ResidueField.map (algebraMap A B) (residue A a) := by
    rw [htransport]
    calc
      e₂ (Submodule.Quotient.mk (algebraMap A B a))
          = residue B (algebraMap A B a) := by
              simpa [e₂, IsLocalRing.ResidueField] using
                (Ideal.quotEquivOfEq_mk hmap (algebraMap A B a))
      _ = ResidueField.map (algebraMap A B) (residue A a) := by
            symm
            exact IsLocalRing.ResidueField.map_residue (algebraMap A B) a
  have hy' :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) =
        e₂ (e₁ x) :=
    hleft.trans hy
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  -- Injectivity of the transported quotient map recovers the original quotient class.
  have hquot :
      e₁
          (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
            (Submodule.Quotient.mk a)) =
        e₁ x :=
    he₂inj hy'
  exact e₁.injective hquot

/-- Helper for Chap10 Lemma 10 153 8: a finite local formally unramified algebra over a strictly
henselian local ring is already a surjective quotient of the base ring. -/
private theorem surjective_algebraMap_of_finite_local_formallyUnramified
    {A : Type v} [CommRing A] [Algebra R A] [IsLocalRing A] [Module.Finite R A]
    [Algebra.FormallyUnramified R A] :
    Function.Surjective (algebraMap R A) := by
  letI : IsLocalHom (algebraMap R A) := algebraMap_isLocalHom_of_finite_local
  letI : Algebra.IsSeparable (ResidueField R) (ResidueField A) := inferInstance
  -- Strict henselianity trivializes the separable residue-field extension.
  have hres : Function.Surjective (ResidueField.map (algebraMap R A)) := by
    simpa using (IsSepClosed.algebraMap_surjective (ResidueField R) (ResidueField A))
  have hmap : Ideal.map (algebraMap R A) (maximalIdeal R) = maximalIdeal A := by
    simpa using (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := A))
  -- Nakayama upgrades surjectivity modulo the maximal ideal to surjectivity of the algebra map.
  have hquot :
      Function.Surjective ((Algebra.linearMap R A).quotientMapByIdeal (maximalIdeal R)) :=
    algebraMapQuotient_surjective_of_residueField_surjective_of_mapMaximalIdealEq
      (A := R) (B := A) hres hmap
  refine surjective_of_quotientMap_surjective_of_le_ring_jacobson
    (R := R) (I := maximalIdeal R) (Algebra.linearMap R A) hquot ?_
  simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
    (show maximalIdeal R ≤ maximalIdeal R from le_rfl)

/- Domain-style sampling:
- primary domain: strictly henselian local rings, unramified finite-type algebra maps, and the
  finite/non-quasi-finite product decomposition near the maximal ideal;
- sampled owner declarations in this domain:
  `finite_type_algebra_decomposition_henselian_local`,
  `exists_pi_algEquiv_henselianLocalRing_of_finite`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `Algebra.QuasiFiniteAt`;
- best owner abstraction:
  the decomposition owner remains the henselian-local splitting theorem
  `finite_type_algebra_decomposition_henselian_local`, itself organized around the canonical
  owner `finite_type_algebra_split_finite_nonQuasiFinite_property R`; the present lemma is the
  source-facing strictly-henselian strengthening that upgrades the finite local factors to
  surjective `R`-algebras and removes primes of the remainder over `maximalIdeal R`;
- primitive data:
  a strictly henselian local ring `R` and an unramified `R`-algebra `S`;
- derived API:
  the source-facing decomposition with surjective factors and no prime of the remainder over
  `maximalIdeal R`; the local/finite factor data from Lemma `10.153.5` belong only to a separate
  strengthening theorem.

Source/core/bridge triage:
- `source-facing`: `exists_product_decomposition_surjective_factors_of_unramified`;
- `core/canonical`: `finite_type_algebra_split_finite_nonQuasiFinite_property R` and
  `Algebra.QuasiFiniteAt`;
- `bridge/view`: `exists_product_decomposition_surjective_local_finite_factors_of_unramified`,
  which keeps the local/finite factor data needed for the proof route while the main theorem stays
  source-facing.
-/

-- Proof sketch for the strengthening theorem below: start from the henselian finite-type product
-- decomposition of Lemma `10.153.5`. Each local finite factor `Aᵢ` remains unramified over `R`,
-- so Lemma `10.151.5` makes its residue field a finite separable extension of the residue field of
-- `R`. Since `R` is strictly henselian, that residue field is separably closed, hence the
-- extension is trivial. Nakayama's lemma then upgrades the induced residue-field isomorphism to
-- surjectivity of `R → Aᵢ`. For the remainder `B`, unramified maps are quasi-finite, so the
-- non-quasi-finite alternative from Lemma `10.153.5` rules out primes of `B` over the maximal
-- ideal of `R`.
/-- A strengthening of Lemma `10.153.8` that retains the local and finite factor data coming from
Lemma `10.153.5`. This is a bridge/view theorem; the source-facing main theorem below forgets that
extra structure. -/
theorem exists_product_decomposition_surjective_local_finite_factors_of_unramified :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, Function.Surjective (algebraMap R (A i))) ∧
          ∀ q : PrimeSpectrum B,
            Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R := by
  let decompProp : Prop :=
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        ∀ q : PrimeSpectrum B,
          Ideal.comap (algebraMap R B) q.asIdeal = maximalIdeal R →
            ¬ Algebra.QuasiFiniteAt R q.asIdeal
  -- Start from the henselian decomposition from Lemma `10.153.5`.
  have hdecomp : decompProp := finite_type_algebra_decomposition_henselian_local
  obtain ⟨ι, instFintype, A, instAComm, instAAlg, instALocal, instAFinite, B, instBComm,
    instBAlg, e, hB⟩ := hdecomp
  letI : Fintype ι := instFintype
  letI : ∀ i, CommRing (A i) := instAComm
  letI : ∀ i, Algebra R (A i) := instAAlg
  letI : ∀ i, IsLocalRing (A i) := instALocal
  letI : ∀ i, Module.Finite R (A i) := instAFinite
  letI : CommRing B := instBComm
  letI : Algebra R B := instBAlg
  letI : Algebra.Unramified R (((i : ι) → A i) × B) := Algebra.Unramified.of_equiv e
  refine ⟨ι, instFintype, A, instAComm, instAAlg, instALocal, instAFinite, B, instBComm,
    instBAlg, e, ?_⟩
  constructor
  · intro i
    -- Each factor inherits formal unramifiedness from the product through the projection.
    let φ : (((j : ι) → A j) × B) →ₐ[R] A i :=
      (Pi.evalAlgHom R A i).comp (AlgHom.fst R ((j : ι) → A j) B)
    have hφsurj : Function.Surjective φ :=
      (Function.surjective_eval i).comp Prod.fst_surjective
    letI : Algebra.FormallyUnramified R (A i) := Algebra.FormallyUnramified.of_surjective φ hφsurj
    exact surjective_algebraMap_of_finite_local_formallyUnramified (R := R) (A := A i)
  · intro q hq
    -- The remainder is globally quasi-finite, so Lemma `10.153.5` rules out primes over `m_R`.
    letI : Algebra.QuasiFinite R (((i : ι) → A i) × B) := inferInstance
    letI : Algebra.QuasiFinite R B :=
      Algebra.QuasiFinite.of_surjective_algHom
        (AlgHom.snd R ((i : ι) → A i) B) Prod.snd_surjective
    exact hB q hq (quasiFiniteAt_of_quasiFinite (A := R) (T := B) q)

/-- Chap10 Lemma 10 153 8: if `(R, 𝔪, κ)` is a strictly henselian local ring and `R → S` is
unramified, then `S` decomposes as a finite product `A₁ × ... × Aₙ × B` where each `R → Aᵢ` is
surjective and no prime of `B` lies over the maximal ideal `𝔪` of `R`. -/
@[stacks 04GL]
theorem exists_product_decomposition_surjective_factors_of_unramified
    :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, Function.Surjective (algebraMap R (A i))) ∧
          ∀ q : PrimeSpectrum B,
            Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R := by
  have h :
      ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i))
        (instAAlg : ∀ i, Algebra R (A i))
        (instALocal : ∀ i, IsLocalRing (A i))
        (instAFinite : ∀ i, Module.Finite R (A i))
        (B : Type v) (_ : CommRing B) (_ : Algebra R B),
        letI : ∀ i, CommRing (A i) := instAComm
        letI : ∀ i, Algebra R (A i) := instAAlg
        letI : ∀ i, IsLocalRing (A i) := instALocal
        letI : ∀ i, Module.Finite R (A i) := instAFinite
        ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
          (∀ i, Function.Surjective (algebraMap R (A i))) ∧
            ∀ q : PrimeSpectrum B,
              Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R :=
    exists_product_decomposition_surjective_local_finite_factors_of_unramified
  obtain ⟨ι, instFintype, A, instAComm, instAAlg, _, _, B, instBComm, instBAlg, e, hsurj, hB⟩ := h
  exact ⟨ι, instFintype, A, instAComm, instAAlg, B, instBComm, instBAlg, e, hsurj, hB⟩

end
