import Mathlib
import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_166_1
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap15.Lemma_15_41_2_Regular_is_a_local_property
import StacksProject_2024.Chap15.Lemma_15_41_3_Regular_maps_and_base_change
import StacksProject_2024.Chap15.Lemma_15_41_4_Composition_of_regular_maps
import StacksProject_2024.Chap15.Lemma_15_41_7
import StacksProject_2024.Chap15.Definition_15_50_1
import StacksProject_2024.Chap15.Proposition_15_50_6

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Helper for Lemma 15.50.7: a local ring is already the localization away from its maximal
ideal. -/
lemma self_isLocalization_primeCompl_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalization (maximalIdeal A).primeCompl A := by
  -- Every element outside the maximal ideal is a unit, so the identity map has the localization
  -- universal property.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Lemma 15.50.7: localizing a local ring at its maximal ideal does not change the
ring. -/
noncomputable abbrev localizationAtMaximalIdeal_algEquiv_self
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
  let _ : IsLocalization (maximalIdeal A).primeCompl A :=
    self_isLocalization_primeCompl_maximalIdeal A
  Localization.algEquiv (maximalIdeal A).primeCompl A

/-- Helper for Lemma 15.50.7: a ring equivalence induces a regular ring map. -/
lemma ringEquiv_isRegularRingMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B) :
    e.toRingHom.IsRegularRingMap := by
  -- Compare the equivalence map with the identity after composing with the inverse equivalence.
  have hcomp : (e.symm.toRingHom.comp e.toRingHom).IsRegularRingMap := by
    simpa using (inferInstance : (RingHom.id A).IsRegularRingMap)
  exact
    RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat hcomp
      (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)

/-- Helper for Lemma 15.50.7: a ring equivalence of local rings sends the maximal ideal of the
source onto the maximal ideal of the target. -/
lemma ringEquiv_map_maximalIdeal_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Ideal.map e.toRingHom (maximalIdeal A) = maximalIdeal B := by
  letI : IsLocalHom e.toRingHom := Function.Surjective.isLocalHom _ e.surjective
  -- A surjective local map carries the unique maximal ideal onto the unique maximal ideal.
  simpa using IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

/-- Helper for Lemma 15.50.7: a surjective local homomorphism induces a bijection on residue
fields. -/
lemma residueField_bijective_of_surjective_localHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Nontrivial B]
    (f : A →+* B) (hf_surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  constructor
  · -- The source residue field is a field, so its map into a nontrivial ring is injective.
    exact RingHom.injective (ResidueField.map f)
  · intro z
    -- Lift a residue class through the local quotient and then through the surjective map.
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, rfl⟩ := hf_surj b
    refine ⟨residue A a, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f a

/-- Helper for Lemma 15.50.7: localizing `R_m` again at a prime lying over `p` recovers `R_p`. -/
noncomputable def localizationAtPrime_algEquiv_of_maximalLocalization_comap
    (p : PrimeSpectrum R) (m : MaximalSpectrum R)
    (pm : PrimeSpectrum (Localization.AtPrime m.asIdeal))
    (hpm :
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pm = p) :
    Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime pm.asIdeal := by
  let p' : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pm
  have hp' : p' = p := by
    simpa [p'] using hpm
  let _ : IsLocalization.AtPrime (Localization.AtPrime pm.asIdeal) p'.asIdeal := by
    simpa [p'] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        m.asIdeal.primeCompl (Localization.AtPrime pm.asIdeal) pm.asIdeal)
  let e :
      Localization.AtPrime p'.asIdeal ≃ₐ[R] Localization.AtPrime pm.asIdeal :=
    IsLocalization.algEquiv p'.asIdeal.primeCompl
      (Localization.AtPrime p'.asIdeal) (Localization.AtPrime pm.asIdeal)
  subst hp'
  simpa using e

/-- Helper for Lemma 15.50.7: a regular map from a field has geometrically regular target. -/
theorem Algebra.isGeometricallyRegular_of_regularRingMap_from_field
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (h : (algebraMap k S).IsRegularRingMap) :
    IsGeometricallyRegular k S := by
  -- Geometric regularity is tested after essentially finite type field extensions, and regular
  -- maps stay regular after the same base changes.
  rw [Algebra.isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing]
  intro K _ _ _
  have hbase : (algebraMap K (K ⊗[k] S)).IsRegularRingMap := by
    simpa using
      (RingHom.IsRegularRingMap.baseChange_of_essFiniteType
        (R := k) (R' := K) (Λ := S) h)
  -- Over the test field, a regular structure map is exactly the regularity of the tensor product.
  exact RingHom.IsRegularRingMap.isRegularRing_of_regularRingMap_from_field hbase

/-- Helper for Lemma 15.50.7: if `p ⊆ m`, then `p` defines a prime of the maximal localization
`R_m`. -/
lemma exists_prime_over_specialization_in_localizationAtMaximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p.asIdeal ≤ m.asIdeal) :
    ∃ pm : PrimeSpectrum (Localization.AtPrime m.asIdeal),
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pm = p := by
  let pLoc : Ideal (Localization.AtPrime m.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime m.asIdeal)) p.asIdeal
  have hdisj : Disjoint (m.asIdeal.primeCompl : Set R) p.asIdeal := by
    -- Elements inverted in `R_m` cannot lie in `p`, because `p ⊆ m`.
    refine Set.disjoint_left.mpr fun x hxM hxP ↦ ?_
    exact hxM (hpm hxP)
  have hpLoc_comap :
      Ideal.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pLoc = p.asIdeal := by
    -- The standard localization comap-map identity applies because `p` avoids the inverted set.
    simpa [pLoc] using
      IsLocalization.comap_map_of_isPrime_disjoint
        m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal) p.2 hdisj
  letI : pLoc.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal) p.asIdeal p.2 hdisj
  refine ⟨⟨pLoc, inferInstance⟩, ?_⟩
  -- Contracting the constructed prime recovers the original prime `p`.
  exact PrimeSpectrum.ext hpLoc_comap

/-- Helper for Lemma 15.50.7: after choosing the branch `p ⊂ m`, faithful flatness of the
maximal-ideal completion of `R_m` produces a prime upstairs lying over that branch. -/
lemma exists_branch_prime_over_localized_prime_in_maximal_completion
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p.asIdeal ≤ m.asIdeal) :
    let Rm := Localization.AtPrime m.asIdeal
    let RmHat := AdicCompletion (IsLocalRing.maximalIdeal Rm) Rm
    ∃ pm : PrimeSpectrum Rm,
      PrimeSpectrum.comap (algebraMap R Rm) pm = p ∧
      ∃ pmHat : PrimeSpectrum RmHat,
        PrimeSpectrum.comap (algebraMap Rm RmHat) pmHat = pm := by
  classical
  let Rm := Localization.AtPrime m.asIdeal
  let RmHat := AdicCompletion (IsLocalRing.maximalIdeal Rm) Rm
  obtain ⟨pm, hpm_comap⟩ :=
    exists_prime_over_specialization_in_localizationAtMaximal (R := R) p m hpm
  let hff : RingHom.FaithfullyFlat (algebraMap Rm RmHat) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat Rm
  have hsurj :
      Function.Surjective (PrimeSpectrum.comap (algebraMap Rm RmHat)) :=
    by
      letI : Module.FaithfullyFlat Rm RmHat :=
        RingHom.faithfullyFlat_algebraMap_iff.mp hff
      exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨pmHat, hpmHat_comap⟩ := hsurj pm
  refine ⟨pm, hpm_comap, pmHat, hpmHat_comap⟩

/-- Helper for Lemma 15.50.7: for the algebra structure induced by a ring equivalence, the
resulting algebra map is exactly the underlying ring homomorphism. -/
lemma ringEquiv_toAlgebra_algebraMap_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) :
    @algebraMap A B _ _ e.toRingHom.toAlgebra = e.toRingHom := by
  rfl

/-- Helper for Lemma 15.50.7: the algebra map induced by a local ring equivalence is a local
homomorphism. -/
lemma ringEquiv_algebraMap_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (e : A ≃+* B) (halg : algebraMap A B = e.toRingHom) :
    IsLocalHom (algebraMap A B) := by
  let f : A →+* B := e.toRingHom
  -- Proof comment: rewrite the algebra map into the surjective local map defined by `e`.
  rw [halg]
  exact Function.Surjective.isLocalHom f e.surjective

/-- Helper for Lemma 15.50.7: a ring equivalence between local rings is a local homomorphism. -/
lemma ringEquiv_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalHom e.toRingHom := by
  -- Proof comment: surjectivity of a map between local rings forces locality.
  exact Function.Surjective.isLocalHom _ e.surjective

/-- Helper for Lemma 15.50.7: the algebra map induced by a ring equivalence is flat. -/
lemma ringEquiv_algebraMap_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) [Algebra A B] (halg : algebraMap A B = e.toRingHom) :
    Module.Flat A B := by
  -- Proof comment: a bijective ring map is flat, and we rewrite the algebra map to that map.
  exact RingHom.flat_algebraMap_iff.mp <| by
    rw [halg]
    exact RingHom.Flat.of_bijective e.bijective

/-- Helper for Lemma 15.50.7: the algebra map induced by a local ring equivalence sends the
maximal ideal onto the maximal ideal. -/
lemma ringEquiv_algebraMap_maximalIdeal_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (e : A ≃+* B) (halg : algebraMap A B = e.toRingHom) :
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  -- Proof comment: rewrite the algebra map into the local equivalence map and use the local-ring
  -- maximal-ideal comparison.
  rw [halg]
  exact ringEquiv_map_maximalIdeal_eq e

/-- Helper for Lemma 15.50.7: the algebra map induced by a surjective local ring equivalence
induces a bijection on residue fields. -/
lemma ringEquiv_algebraMap_residueField_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Nontrivial B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (e : A ≃+* B) (halg : algebraMap A B = e.toRingHom) :
    Function.Bijective (ResidueField.map (algebraMap A B)) := by
  let f : A →+* B := e.toRingHom
  letI : IsLocalHom f := Function.Surjective.isLocalHom _ e.surjective
  -- Proof comment: after rewriting the algebra map, this is the residue-field bijection for a
  -- surjective local homomorphism.
  simpa [halg] using
    (residueField_bijective_of_surjective_localHom (f := f) e.surjective)

/-- Helper for Lemma 15.50.7: quotient-stage evaluations on an adic completion commute with the
transition maps of the inverse system. -/
lemma completion_eval_factor
    {S : Type u} [CommRing S] (I : Ideal S)
    {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  let p : AdicCompletion I S → Prop := fun y =>
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n y) =
      AdicCompletion.evalₐ I m y
  change p x
  -- Proof comment: descend to a Cauchy representative and use the defining compatibility of its
  -- quotient classes.
  refine AdicCompletion.induction_on (I := I) (M := S) x ?_
  intro f
  change
    Ideal.Quotient.factorPow I hle
        (AdicCompletion.evalₐ I n (AdicCompletion.mk I S f)) =
      AdicCompletion.evalₐ I m (AdicCompletion.mk I S f)
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simpa using (AdicCompletion.Ideal.mk_eq_mk (I := I) hle f)

/-- Helper for Lemma 15.50.7: under a local ring equivalence, powers of the source maximal ideal
map into the corresponding powers of the target maximal ideal. -/
lemma ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    maximalIdeal A ^ n ≤ Ideal.comap e.toRingHom (maximalIdeal B ^ n) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom e
  -- Proof comment: this is the standard maximal-ideal power containment for local homomorphisms.
  simpa using pow_maximalIdeal_le_comap_pow_maximalIdeal e.toRingHom n

/-- Helper for Lemma 15.50.7: pulling back a power of the target maximal ideal along a local ring
equivalence recovers the corresponding power of the source maximal ideal. -/
lemma ringEquiv_comap_maximalIdeal_pow_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    Ideal.comap e.toRingHom (maximalIdeal B ^ n) = maximalIdeal A ^ n := by
  -- Proof comment: identify the target power with the image of the source power and contract it
  -- back along the surjective equivalence.
  have hker : Ideal.comap e.toRingHom (⊥ : Ideal B) = ⊥ := by
    ext x
    simp [Ideal.mem_comap]
  have hmap :
      Ideal.map e.toRingHom (maximalIdeal A ^ n) = maximalIdeal B ^ n := by
    calc
      Ideal.map e.toRingHom (maximalIdeal A ^ n)
          = Ideal.map e.toRingHom (maximalIdeal A) ^ n := by rw [Ideal.map_pow]
      _ = maximalIdeal B ^ n := by rw [ringEquiv_map_maximalIdeal_eq (e := e)]
  calc
    Ideal.comap e.toRingHom (maximalIdeal B ^ n)
        = Ideal.comap e.toRingHom (Ideal.map e.toRingHom (maximalIdeal A ^ n)) := by rw [hmap]
    _ = maximalIdeal A ^ n ⊔ Ideal.comap e.toRingHom (⊥ : Ideal B) := by
          exact Ideal.comap_map_of_surjective e.toRingHom e.surjective (maximalIdeal A ^ n)
    _ = maximalIdeal A ^ n := by rw [hker, sup_bot_eq]

/-- Helper for Lemma 15.50.7: the quotient map induced by a local ring equivalence on maximal-ideal
powers is bijective. -/
lemma ringEquiv_quotient_maximalIdeal_pow_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
        (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal (e := e) n)) := by
  let qPow :
      A ⧸ Ideal.comap e.toRingHom (maximalIdeal B ^ n) →+* B ⧸ maximalIdeal B ^ n :=
    Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom le_rfl
  let eSource :
      A ⧸ Ideal.comap e.toRingHom (maximalIdeal B ^ n) ≃+* A ⧸ maximalIdeal A ^ n :=
    Ideal.quotEquivOfEq (ringEquiv_comap_maximalIdeal_pow_eq (e := e) (n := n))
  have hEq :
      Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
          (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal (e := e) n) =
        qPow.comp eSource.symm.toRingHom := by
    -- Proof comment: both quotient maps send the class of `a` to the class of `e a`.
    apply Ideal.Quotient.ringHom_ext
    ext x
    have hs :
        eSource.symm ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x) =
          Ideal.Quotient.mk (Ideal.comap e.toRingHom (maximalIdeal B ^ n)) x := by
      apply eSource.symm_apply_eq.2
      rw [Ideal.quotEquivOfEq_mk]
    calc
      (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
          (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal (e := e) n))
          ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x)
          = (Ideal.Quotient.mk (maximalIdeal B ^ n)) (e.toRingHom x) := by
              rw [Ideal.quotientMap_mk]
      _ = qPow (eSource.symm ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x)) := by
              rw [hs, Ideal.quotientMap_mk]
  have hqPow_inj : Function.Injective qPow := by
    -- Proof comment: quotienting by the contracted ideal is the injective case of
    -- `Ideal.quotientMap`.
    change Function.Injective (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom le_rfl)
    exact Ideal.quotientMap_injective
  have hqPow_surj : Function.Surjective qPow := by
    -- Proof comment: surjectivity comes directly from surjectivity of the ring equivalence `e`.
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, rfl⟩ := e.surjective b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    rfl
  rw [hEq]
  constructor
  · intro x y hxy
    apply eSource.symm.injective
    exact hqPow_inj hxy
  · intro z
    obtain ⟨w, hw⟩ := hqPow_surj z
    refine ⟨eSource w, ?_⟩
    change qPow (eSource.symm (eSource w)) = z
    rw [eSource.symm_apply_apply]
    exact hw

/-- Helper for Lemma 15.50.7: a local ring equivalence induces quotient-power equivalences on the
maximal-ideal inverse systems. -/
noncomputable abbrev ringEquiv_quotient_maximalIdeal_pow
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
  let _ : IsLocalHom e.toRingHom := ringEquiv_isLocalHom e
  RingEquiv.ofBijective
    (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
      (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal (e := e) n))
    (ringEquiv_quotient_maximalIdeal_pow_bijective (e := e) n)

/-- Helper for Lemma 15.50.7: the quotient-power equivalences commute with the transition maps of
the maximal-ideal inverse systems. -/
lemma ringEquiv_quotient_maximalIdeal_pow_compatible
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp
        (ringEquiv_quotient_maximalIdeal_pow (e := e) n).toRingHom =
      (ringEquiv_quotient_maximalIdeal_pow (e := e) m).toRingHom.comp
        (Ideal.Quotient.factorPow (maximalIdeal A) hle) := by
  letI : IsLocalHom e.toRingHom := Function.Surjective.isLocalHom _ e.surjective
  -- Proof comment: both quotient routes send the class of `a` to the class of `e a` in the
  -- smaller target quotient.
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [ringEquiv_quotient_maximalIdeal_pow, Ideal.quotientMap_mk]

/-- Helper for Lemma 15.50.7: the canonical map on maximal-ideal completions induced by a local
ring equivalence. -/
noncomputable abbrev ringEquiv_completionMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  let _ : IsLocalHom e.toRingHom := ringEquiv_isLocalHom e
  maximalIdealCompletionMap e.toRingHom

/-- Helper for Lemma 15.50.7: a local ring equivalence induces a bijection on maximal-ideal
completions. -/
lemma maximalIdealCompletionMap_bijective_of_local_ring_equiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Function.Bijective (ringEquiv_completionMap e) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom e
  change Function.Bijective (maximalIdealCompletionMap e.toRingHom)
  let π : ∀ n : ℕ, A ⧸ maximalIdeal A ^ n →+* B ⧸ maximalIdeal B ^ n :=
    fun n ↦ (ringEquiv_quotient_maximalIdeal_pow (e := e) n).toRingHom
  let eQuot : ∀ n : ℕ, A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
    fun n ↦ ringEquiv_quotient_maximalIdeal_pow (e := e) n
  let q : ∀ n : ℕ, AdicCompletion (maximalIdeal B) B →+* A ⧸ maximalIdeal A ^ n :=
    fun n ↦ (eQuot n).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal B) n)
  have hπ_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp (π n) =
          (π m).comp (Ideal.Quotient.factorPow (maximalIdeal A) hle) := by
    intro m n hle
    -- Proof comment: this is the quotient-stage compatibility already built into the stage
    -- equivalences.
    simpa [π, eQuot] using
      ringEquiv_quotient_maximalIdeal_pow_compatible (e := e) hle
  have hq_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (q n) = q m := by
    intro m n hle
    ext x
    -- Proof comment: compare after postcomposing with the quotient equivalence `π m`.
    apply (eQuot m).injective
    calc
      π m ((Ideal.Quotient.factorPow (maximalIdeal A) hle) (q n x)) =
          (Ideal.Quotient.factorPow (maximalIdeal B) hle) (π n (q n x)) := by
            symm
            exact DFunLike.congr_fun (hπ_compat hle) (q n x)
      _ = (Ideal.Quotient.factorPow (maximalIdeal B) hle)
            (AdicCompletion.evalₐ (maximalIdeal B) n x) := by
              congr 1
              exact RingEquiv.apply_symm_apply (eQuot n) (AdicCompletion.evalₐ (maximalIdeal B) n x)
      _ = AdicCompletion.evalₐ (maximalIdeal B) m x := by
              simpa using
                completion_eval_factor (S := B) (I := maximalIdeal B) hle x
      _ = π m (q m x) := by
              exact
                (RingEquiv.apply_symm_apply
                  (eQuot m) (AdicCompletion.evalₐ (maximalIdeal B) m x)).symm
  let ψ : AdicCompletion (maximalIdeal B) B →+*
      AdicCompletion (maximalIdeal A) A :=
    AdicCompletion.liftRingHom (maximalIdeal A) q hq_compat
  let φ : AdicCompletion (maximalIdeal A) A →+*
      AdicCompletion (maximalIdeal B) B :=
    maximalIdealCompletionMap e.toRingHom
  have hφ_eval :
      ∀ n : ℕ, ∀ x : AdicCompletion (maximalIdeal A) A,
        AdicCompletion.evalₐ (maximalIdeal B) n (φ x) =
          π n (AdicCompletion.evalₐ (maximalIdeal A) n x) := by
    intro n x
    let p : AdicCompletion (maximalIdeal A) A → Prop := fun y =>
      AdicCompletion.evalₐ (maximalIdeal B) n (φ y) =
        π n (AdicCompletion.evalₐ (maximalIdeal A) n y)
    change p x
    -- Proof comment: check the stage formula on Cauchy representatives, where it is definitional.
    refine AdicCompletion.induction_on (I := maximalIdeal A) (M := A) x ?_
    intro f
    rfl
  have hleft : ψ.comp φ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    -- Proof comment: both completion endomorphisms agree on every quotient stage of `A^∧`.
    apply AdicCompletion.ext_evalₐ (I := maximalIdeal A)
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal A) n ((ψ.comp φ) x)
          = q n (φ x) := by
              simp [ψ]
      _ = (eQuot n).symm (AdicCompletion.evalₐ (maximalIdeal B) n (φ x)) := by
              rfl
      _ = (eQuot n).symm (π n (AdicCompletion.evalₐ (maximalIdeal A) n x)) := by
              rw [hφ_eval n x]
      _ = AdicCompletion.evalₐ (maximalIdeal A) n x := by
              exact
                RingEquiv.symm_apply_apply
                  (eQuot n) (AdicCompletion.evalₐ (maximalIdeal A) n x)
  have hright : φ.comp ψ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    -- Proof comment: the same quotientwise computation shows the opposite composite is the
    -- identity on `B^∧`.
    apply AdicCompletion.ext_evalₐ (I := maximalIdeal B)
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal B) n ((φ.comp ψ) x)
          = π n (AdicCompletion.evalₐ (maximalIdeal A) n (ψ x)) := by
              change AdicCompletion.evalₐ (maximalIdeal B) n (φ (ψ x)) =
                π n (AdicCompletion.evalₐ (maximalIdeal A) n (ψ x))
              rw [hφ_eval n (ψ x)]
      _ = π n (q n x) := by
              simp [ψ]
      _ = π n ((eQuot n).symm (AdicCompletion.evalₐ (maximalIdeal B) n x)) := by
              rfl
      _ = AdicCompletion.evalₐ (maximalIdeal B) n x := by
              exact
                RingEquiv.apply_symm_apply
                  (eQuot n) (AdicCompletion.evalₐ (maximalIdeal B) n x)
  exact ⟨
    -- Proof comment: a left inverse for `φ` gives injectivity.
    Function.LeftInverse.injective (fun x ↦ by
      simpa using DFunLike.congr_fun hleft x)
    ,
    -- Proof comment: a right inverse for `φ` gives surjectivity.
    Function.RightInverse.surjective (fun x ↦ by
      simpa using DFunLike.congr_fun hright x)⟩

/-- Helper for Lemma 15.50.7: a local ring equivalence induces a ring equivalence on maximal-ideal
completions. -/
noncomputable def completion_compare_ringEquiv_of_local_ring_equiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+*
      AdicCompletion (maximalIdeal B) B :=
  RingEquiv.ofBijective
    (ringEquiv_completionMap e)
    (maximalIdealCompletionMap_bijective_of_local_ring_equiv (e := e))

/-- Helper for Lemma 15.50.7: the completion equivalence intertwines the canonical completion maps.
-/
lemma completion_compare_ringEquiv_comp
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    (completion_compare_ringEquiv_of_local_ring_equiv e).toRingHom.comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp e.toRingHom := by
  letI : IsLocalHom e.toRingHom := Function.Surjective.isLocalHom _ e.surjective
  -- Proof comment: the completion comparison was defined from the canonical completion map.
  simpa [completion_compare_ringEquiv_of_local_ring_equiv] using
    (maximalIdealCompletionMap_comp e.toRingHom)

/-- Helper for Lemma 15.50.7: regularity of the maximal-ideal completion map is invariant under a
local ring equivalence. -/
lemma regular_completion_map_of_local_ring_equiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B)
    (hA : (algebraMap A (AdicCompletion (maximalIdeal A) A)).IsRegularRingMap) :
    (algebraMap B (AdicCompletion (maximalIdeal B) B)).IsRegularRingMap := by
  let eCompletion := completion_compare_ringEquiv_of_local_ring_equiv e
  have htransport :
      (eCompletion.toRingHom.comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))).IsRegularRingMap := by
    -- Compose the given regular completion map with the completion comparison equivalence.
    simpa [eCompletion] using
      (RingHom.IsRegularRingMap.comp_of_noetherianFibers hA
        (ringEquiv_isRegularRingMap eCompletion)
        (by intro p; infer_instance))
  have htransport' :
      ((algebraMap B (AdicCompletion (maximalIdeal B) B)).comp e.toRingHom).IsRegularRingMap := by
    -- Rewrite the transported composite in terms of the original equivalence `e`.
    rw [completion_compare_ringEquiv_comp (e := e)] at htransport
    exact htransport
  have hcancel :
      (((algebraMap B (AdicCompletion (maximalIdeal B) B)).comp e.toRingHom).comp
        e.symm.toRingHom).IsRegularRingMap := by
    -- Postcompose with `e.symm` to cancel the source equivalence.
    simpa [RingHom.comp_assoc] using
      (RingHom.IsRegularRingMap.comp_of_noetherianFibers
        (ringEquiv_isRegularRingMap e.symm) htransport'
        (by intro p; infer_instance))
  simpa [RingHom.comp_assoc] using hcancel

/-- Helper for Lemma 15.50.7: for a Noetherian local `G`-ring, the concrete completion map
`A → A^∧` is regular. -/
lemma local_completionMap_isRegular_of_isGRing
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsGRing A] :
    (algebraMap A (AdicCompletion (maximalIdeal A) A)).IsRegularRingMap := by
  let pA : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  let e := (localizationAtMaximalIdeal_algEquiv_self A).toRingEquiv
  -- Transport the owner field at the closed point to the concrete local completion map.
  simpa [pA, e] using
    regular_completion_map_of_local_ring_equiv e
      (IsGRing.regular_localization_completion (R := A) pA)

/-- Helper for Lemma 15.50.7: the `G`-ring property descends from `R` to every maximal
localization `R_𝔪`. -/
lemma localizationAtMaximal_isGRing_of_isGRing
    (hR : IsGRing R) (m : MaximalSpectrum R) :
    IsGRing (Localization.AtPrime m.asIdeal) := by
  letI : IsGRing R := hR
  refine isGRing_iff_forall_regular_localization_completion.2 ?_
  intro pm
  let p : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal)) pm
  let e :=
    (localizationAtPrime_algEquiv_of_maximalLocalization_comap
      (R := R) p m pm rfl).toRingEquiv
  -- Transport the regular completion map from the prime `p` of `R` to the corresponding prime of
  -- the maximal localization.
  simpa [p, e] using
    regular_completion_map_of_local_ring_equiv e
      (IsGRing.regular_localization_completion (R := R) p)

-- Proof sketch: the forward implication is stability of the `G`-ring owner under localization.
-- For the converse, fix `p : Spec R`, choose `m ⊇ p`, and view `R_p` as the localization of the
-- already-assumed `G`-ring `R_m` at the corresponding prime `p_A`; the required regular
-- completion map for `R_p` is then obtained by transporting the prime-local completion map of
-- `R_m` across the canonical equivalence `((R_m)_{p_A} ≃ R_p)`.
/-- Lemma 15.50.7: for a Noetherian ring `R`, `R` is a `G`-ring if and only if every localization
`R_𝔪` at a maximal ideal is a `G`-ring, equivalently every `R_𝔪` has geometrically regular formal
fibers. -/
@[stacks 07PT]
theorem isGRing_iff_forall_localizationAtMaximal_isGRing :
    IsGRing R ↔ ∀ m : MaximalSpectrum R, IsGRing (Localization.AtPrime m.asIdeal) := by
  constructor
  · intro hR
    -- The forward implication is pure transport of the `G`-ring owner along the localization
    -- equivalence `((R_𝔪)_𝔭 ≃ R_𝔭)`.
    exact localizationAtMaximal_isGRing_of_isGRing (R := R) hR
  · intro hmax
    -- Route correction: once the hypothesis is stated as `IsGRing (R_𝔪)`, the needed prime case
    -- is obtained by localizing that `G`-ring again at the prime of `R_𝔪` lying over `p`.
    refine isGRing_iff_forall_regular_localization_completion.2 ?_
    intro p
    obtain ⟨m, hmmax, hpm⟩ := p.asIdeal.exists_le_maximal p.2.1
    let m' : MaximalSpectrum R := ⟨m, hmmax⟩
    let A := Localization.AtPrime m'.asIdeal
    letI : IsGRing A := hmax m'
    let pA : PrimeSpectrum A :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso A m'.asIdeal).symm ⟨p, hpm⟩
    have hpA :
        PrimeSpectrum.comap (algebraMap R A) pA = p := by
      -- Proof comment: `pA` was chosen as the prime of `R_𝔪` corresponding to `p ⊆ m`.
      exact Subtype.ext_iff.mp <|
        (IsLocalization.AtPrime.primeSpectrumOrderIso A m'.asIdeal).apply_symm_apply ⟨p, hpm⟩
    let e :=
      (localizationAtPrime_algEquiv_of_maximalLocalization_comap
        (R := R) p m' pA hpA).symm.toRingEquiv
    -- Proof comment: transport the regular completion map for the prime `pA` of `R_𝔪` back to
    -- the original prime `p` of `R`.
    simpa [A, pA, e] using
      regular_completion_map_of_local_ring_equiv e
        (IsGRing.regular_localization_completion (R := A) pA)

end
