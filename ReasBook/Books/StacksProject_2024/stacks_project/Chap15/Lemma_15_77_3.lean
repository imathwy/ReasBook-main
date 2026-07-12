import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.Chap13.Remark_13_12_4
import StacksProject_2024.Chap15.Lemma_15_33_3
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_67_4
import StacksProject_2024.Chap15.Lemma_15_67_5
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_75_2
import StacksProject_2024.Chap15.Lemma_15_75_4
import StacksProject_2024.Chap15.Lemma_15_65_17
import StacksProject_2024.Chap15.Lemma_15_77_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: localization and three-term truncation splittings for pseudo-coherent derived
  objects, combining the chapter owners for perfectness and tor-amplitude with the module-level
  owners for finiteness, freeness, and single-degree embeddings of localized homology;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `Module.Free`,
  `Module.Finite`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: this source-facing theorem should expose the localized upper-truncation
  properties, the finiteness/free-ness of the middle homology module, and the existence of the
  three-term decomposition directly, using the canonical owners
  `K ⊗[R]^L[Localization.Away f]`, `LocalizedModule.Away`, and
  `DerivedCategory.singleFunctor`, rather than local wrapper aliases;
- primitive data: the localized object, its lower and upper truncations, the localized middle
  homology module, and the three-term biproduct object;
- derived API: perfectness and tor-amplitude of the upper truncation, finiteness/free-ness of the
  middle term, and existence of the decomposition isomorphism.

Source/core/bridge triage:
- `source-facing`: the existential three-term localization theorem below;
- `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, `Module.Free`, and
  `Module.Finite`;
- `bridge/view`: the explicit isomorphism to the three-summand object, which is an existence claim
  and not a second owner abstraction.
-/

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField

/-- Helper for Lemma 15.77.3: the upper truncation of `τ≤ i` is canonically the single object on
the degree-`i` homology of the original complex. -/
noncomputable def truncGE_truncLE_iso_single_homology
    (X : DMod) (i : ℤ) :
    ((t.truncGE i).obj ((t.truncLE i).obj X)) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj ((H i).obj X) := by
  -- Proof comment: rewrite `τ≤ i` as `τ< i + 1` and then apply the canonical one-step truncation
  -- identification from Remark `13.12.4`.
  simpa [t.truncLE, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (_root_.truncLE_step_termIso (K := X) (a := i - 1))

/-- Helper for Lemma 15.77.3: shifting translates the lower tor-amplitude cutoff by the same
amount. -/
private theorem hasTorAmplitudeGE_shift_iff
    (X : DMod) (n a : ℤ) :
    HasTorAmplitudeGE (X⟦n⟧) a ↔ HasTorAmplitudeGE X (a + n) := by
  -- Proof comment: rewrite lower tor-amplitude through homology vanishing and then transport
  -- those vanishings across the canonical tensor-shift homology comparison.
  rw [hasTorAmplitudeGE_iff, hasTorAmplitudeGE_iff]
  constructor
  · intro h M j hj
    have hj' : j - n < a := by
      omega
    have hz :
        IsZero ((H (j - n)).obj ((X⟦n⟧) ⊗[R]^L
          (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) :=
      h M (j - n) hj'
    simpa [sub_eq_add_neg, add_assoc] using
      hz.of_iso (homology_tensor_single_shift_iso (R := R) X M (j - n) n).symm
  · intro h M j hj
    have hj' : j + n < a + n := by
      omega
    have hz :
        IsZero ((H (j + n)).obj (X ⊗[R]^L
          (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) :=
      h M (j + n) hj'
    exact hz.of_iso (homology_tensor_single_shift_iso (R := R) X M j n)

/-- Helper for Lemma 15.77.3: lower tor-amplitude is invariant under isomorphism. -/
private theorem has_tor_amplitude_ge_iff_of_iso
    {X Y : DMod} {a : ℤ} (e : X ≅ Y) :
    HasTorAmplitudeGE X a ↔ HasTorAmplitudeGE Y a := by
  -- Proof comment: tensoring with a degree-zero module preserves the given isomorphism, so the
  -- defining homology-vanishing test for lower tor-amplitude is unchanged.
  rw [hasTorAmplitudeGE_iff, hasTorAmplitudeGE_iff]
  constructor
  · intro h M j hj
    exact
      (h M j hj).of_iso
        ((H j).mapIso
          ((derivedTensorProduct
            ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M)).mapIso e.symm))
  · intro h M j hj
    exact
      (h M j hj).of_iso
        ((H j).mapIso
          ((derivedTensorProduct
            ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M)).mapIso e))

/-- Helper for Lemma 15.77.3: perfectness of a shifted single object is equivalent to
perfectness of the underlying module in degree `0`. -/
private theorem module_isPerfect_of_single_isPerfect
    (M : ModuleCat R) (i : ℤ)
    (hM : ((DerivedCategory.singleFunctor (ModuleCat R) i).obj M).IsPerfect) :
    M.IsPerfect := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) i).obj M)⟦i⟧) ≅
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso i 0 i (by simp)).app M
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) i).obj M)⟦i⟧).IsPerfect :=
    isPerfect_shift (R := R) _ i hM
  -- Proof comment: after shifting the degree-`i` single object to degree `0`, the defining
  -- module-level perfectness predicate is exactly the resulting degree-zero single object.
  rw [ModuleCat.IsPerfect]
  exact ObjectProperty.prop_of_iso (P := PerfectObj) e hShift

/-- Helper for Lemma 15.77.3: a perfect module stays perfect when regarded as a single object in
any degree. -/
private theorem single_isPerfect_of_module_isPerfect
    (M : ModuleCat R) (i : ℤ) (hM : M.IsPerfect) :
    ((DerivedCategory.singleFunctor (ModuleCat R) i).obj M).IsPerfect := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) i).obj M)⟦i⟧) ≅
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso i 0 i (by simp)).app M
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) i).obj M)⟦i⟧).IsPerfect := by
    -- Proof comment: degree-zero module perfectness is the canonical shifted form of the
    -- degree-`i` single object.
    rw [ModuleCat.IsPerfect] at hM
    exact ObjectProperty.prop_of_iso (P := PerfectObj) e.symm hM
  exact ObjectProperty.prop_of_iso (P := PerfectObj) (shiftShiftNeg _ i) <|
    isPerfect_shift (R := R) _ (-i) hShift

/-- Helper for Lemma 15.77.3: over a local ring, a perfect single object with lower tor-amplitude
starting in its displayed degree comes from a finite free module. -/
private theorem module_free_and_finite_of_single_isPerfect_of_hasTorAmplitudeGE_of_isLocalRing
    [IsLocalRing R]
    (M : ModuleCat R) (i : ℤ)
    (hPerf : ((DerivedCategory.singleFunctor (ModuleCat R) i).obj M).IsPerfect)
    (hTor : HasTorAmplitudeGE ((DerivedCategory.singleFunctor (ModuleCat R) i).obj M) i) :
    Module.Free R M ∧ Module.Finite R M := by
  let Xi := (DerivedCategory.singleFunctor (ModuleCat R) i).obj M
  let X0 := (ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M
  let eShift : Xi⟦i⟧ ≅ X0 :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso i 0 i (by simp)).app M
  have hTorShift : HasTorAmplitudeGE (Xi⟦i⟧) 0 := by
    -- Proof comment: shifting by `i` moves the tor-amplitude cutoff from degree `i` to `0`.
    exact (hasTorAmplitudeGE_shift_iff (R := R) Xi i 0).2 hTor
  have hTor0 : HasTorAmplitudeGE X0 0 := by
    -- Proof comment: identify the shifted single object with the degree-zero single object.
    exact (has_tor_amplitude_ge_iff_of_iso (R := R) eShift).1 hTorShift
  have hMtor0 : ModuleHasTorDimensionLE M 0 := by
    intro N j hj
    by_cases hneg : j < 0
    · -- Proof comment: negative homology vanishes directly by the degree-zero tor-amplitude
      -- statement for `M[0]`.
      rw [hasTorAmplitudeGE_iff] at hTor0
      exact hTor0 N j hneg
    · have hpos : 0 < j := by
        have hj_ne : j ≠ 0 := by
          intro hEq
          apply hj
          simpa [hEq]
        omega
      have hLE :
          (((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) ⊗[R]^L
            ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)).IsLE 0 :=
        tensor_single_isLE_zero_of_isLE_zero (R := R)
          (K := (ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) inferInstance N
      rw [DerivedCategory.isLE_iff] at hLE
      exact hLE j hpos
  have hMflat : Module.Flat R M :=
    (ModuleCat.hasTorDimensionLE_zero_iff_flat (R := R) (M := M)).1 hMtor0
  have hMperfect : M.IsPerfect :=
    module_isPerfect_of_single_isPerfect (R := R) M i hPerf
  have hMpc : M.IsPseudoCoherent :=
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension M).1 hMperfect |>.1
  have hMfinite : Module.Finite R M := by
    -- Proof comment: perfect modules are pseudo-coherent, and pseudo-coherent modules are finite.
    exact (_root_.Module.isPseudoCoherent_iff_finite (R := R) (M := M)).1 <| by
      simpa using hMpc
  let _ : Module.Flat R M := hMflat
  have hMfree : Module.Free R M := Module.free_of_flat_of_isLocalRing (R := R) (M := M)
  exact ⟨hMfree, hMfinite⟩

/-- Helper for Lemma 15.77.3: the prime of `R_f` corresponding to `𝔭` is the extension of
`𝔭`. -/
private theorem localizationAway_prime_asIdeal
    (f : R) (hf : f ∉ 𝔭.asIdeal) :
    let q : PrimeSpectrum (Localization.Away f) :=
      (primeSpectrum_localizationAway_homeomorph_D f).symm ⟨𝔭, hf⟩
    q.asIdeal = Ideal.map (algebraMap R (Localization.Away f)) 𝔭.asIdeal := by
  -- Proof comment: the localization-away spectrum homeomorphism identifies the pulled-back prime
  -- with the extension of the original prime ideal.
  simpa using
    (primeSpectrum_localizationAway_homeomorph_D_symm_asIdeal f ⟨𝔭, hf⟩)

/-- Helper for Lemma 15.77.3: the prime of `R_f` corresponding to `𝔭` contracts back to `𝔭`. -/
private theorem localizationAway_prime_under_eq
    (f : R) (hf : f ∉ 𝔭.asIdeal) :
    let q : PrimeSpectrum (Localization.Away f) :=
      (primeSpectrum_localizationAway_homeomorph_D f).symm ⟨𝔭, hf⟩
    q.asIdeal.under R = 𝔭.asIdeal := by
  let q : PrimeSpectrum (Localization.Away f) :=
    (primeSpectrum_localizationAway_homeomorph_D f).symm ⟨𝔭, hf⟩
  have hq :
      (primeSpectrum_localizationAway_homeomorph_D f q).1 = 𝔭 := by
    -- Proof comment: `q` was chosen as the inverse image of `𝔭` under the standard-open
    -- homeomorphism, so applying the homeomorphism returns `𝔭`.
    simpa [q] using congrArg Subtype.val
      ((primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply ⟨𝔭, hf⟩)
  simpa [q, primeSpectrum_localizationAway_homeomorph_D_apply] using hq

/-- Helper for Lemma 15.77.3: once a prime of an `R`-algebra contracts to `𝔭`, the induced
residue-field map identifies the direct map `R → κ(q)` with the composite through `κ(𝔭)`. -/
private theorem residueField_map_comp_algebraMap_of_under_eq
    {A : Type u} [CommRing A] [Algebra R A]
    (q : PrimeSpectrum A) (hq_under : q.asIdeal.under R = 𝔭.asIdeal) :
    (Ideal.ResidueField.map 𝔭.asIdeal q.asIdeal (algebraMap R A) hq_under.symm).comp
        (algebraMap R 𝔭.asIdeal.ResidueField) =
      algebraMap R q.asIdeal.ResidueField := by
  -- Proof comment: both ring homomorphisms send an element of `R` to the class of the same
  -- element in `κ(q)`, so it suffices to check equality on generators.
  ext r
  simpa using
    (Ideal.ResidueField.map_algebraMap 𝔭.asIdeal q.asIdeal (algebraMap R A) hq_under.symm r)

/-- Helper for Lemma 15.77.3: the ideal-quotient residue field of a local ring agrees with the
ambient local residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A).ResidueField ≃+* IsLocalRing.ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal A))).symm

/-- Helper for Lemma 15.77.3: the quotient-model and local-model residue fields send a residue
class of `a` to the same element. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (A : Type*) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdeal_residueField_equiv A
        (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a) =
      IsLocalRing.residue A a := by
  -- Proof comment: both residue-field models represent the same class of `a`.
  rw [show algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a =
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.maximalIdeal A).ResidueField
        (IsLocalRing.residue A a) by
      rfl]
  change
    maximalIdeal_residueField_equiv A
        ((maximalIdeal_residueField_equiv A).symm (IsLocalRing.residue A a)) =
      IsLocalRing.residue A a
  exact (maximalIdeal_residueField_equiv A).apply_symm_apply (IsLocalRing.residue A a)

/-- Helper for Lemma 15.77.3: after identifying ideal residue fields with local residue fields,
the ideal-level residue-field map becomes the canonical local residue-field map. -/
private theorem maximalIdeal_residueField_equiv_comp_residueFieldMap
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal_residueField_equiv B).toRingHom.comp
        (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (IsLocalRing.ResidueField.map f).comp (maximalIdeal_residueField_equiv A).toRingHom := by
  -- Proof comment: both maps agree on residue classes of elements of `A`, which generate the
  -- quotient-model residue field.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdeal_residueField_equiv B
        (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a)) =
      IsLocalRing.ResidueField.map f
        (maximalIdeal_residueField_equiv A
          (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdeal_residueField_equiv_apply_algebraMap,
    maximalIdeal_residueField_equiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 15.77.3: a surjective local homomorphism induces a bijection on local
residue fields. -/
private theorem residueField_map_bijective_of_surjective_localHom
    {A : Type u} {B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Nontrivial B]
    (f : A →+* B) (hf_surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  constructor
  · exact RingHom.injective (IsLocalRing.ResidueField.map f)
  · intro b
    -- Proof comment: every residue class of `B` comes from a residue class of a preimage in `A`.
    obtain ⟨a, rfl⟩ := hf_surj b
    refine ⟨IsLocalRing.residue A a, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f a

/-- Helper for Lemma 15.77.3: localizing at a prime ideal does not change its residue field. -/
private noncomputable abbrev prime_localization_residueField_equiv
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    IsLocalRing.ResidueField (Localization.AtPrime p) ≃+* p.ResidueField :=
  -- Proof comment: compare the prime residue field with the residue field of the local ring
  -- `A_p` through the maximal ideal of `A_p`.
  (maximalIdeal_residueField_equiv (Localization.AtPrime p)).symm.trans <|
    by
      change (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ≃+* p.ResidueField
      exact maximalIdeal_residueField_equiv (Localization.AtPrime p)

/-- Helper for Lemma 15.77.3: after localizing away from `f ∉ 𝔭`, localizing further at the
corresponding prime `q` canonically recovers the prime localization `R_𝔭`. -/
private noncomputable abbrev localizationAway_atPrime_algEquiv
    (f : R) (hf : f ∉ 𝔭.asIdeal) :
    let A := Localization.Away f
    let q : PrimeSpectrum A :=
      (primeSpectrum_localizationAway_homeomorph_D f).symm ⟨𝔭, hf⟩
    Localization.AtPrime 𝔭.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal := by
  let A := Localization.Away f
  let q : PrimeSpectrum A :=
    (primeSpectrum_localizationAway_homeomorph_D f).symm ⟨𝔭, hf⟩
  have hq :
      PrimeSpectrum.comap (algebraMap R A) q = 𝔭 := by
    -- Proof comment: `q` was chosen as the inverse image of `𝔭` under the localization-away
    -- homeomorphism, so its contraction is exactly `𝔭`.
    simpa [A, q, primeSpectrum_localizationAway_homeomorph_D_apply] using congrArg Subtype.val
      ((primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply ⟨𝔭, hf⟩)
  -- Proof comment: compare the iterated localization `(R_f)_q` directly with `R_𝔭` via the
  -- canonical mathlib iterated-localization equivalence.
  simpa [A, q, hq] using
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers f) q.asIdeal : Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap R A) q).asIdeal ≃ₐ[R]
          Localization.AtPrime q.asIdeal)

/-- Helper for Lemma 15.77.3: the prime-local residue-field equivalence sends the canonical
local residue class of a base element to its prime-residue-field class. -/
private theorem prime_localization_residueField_equiv_apply_algebraMap
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    prime_localization_residueField_equiv (p := p)
        (algebraMap (Localization.AtPrime p)
          (IsLocalRing.ResidueField (Localization.AtPrime p))
          (algebraMap A (Localization.AtPrime p) a)) =
      algebraMap A p.ResidueField a := by
  -- Proof comment: both residue-field descriptions of `A_p` carry the class of `a`.
  simpa [prime_localization_residueField_equiv, RingEquiv.trans_apply] using
    maximalIdeal_residueField_equiv_apply_algebraMap (Localization.AtPrime p)
      (algebraMap A (Localization.AtPrime p) a)

/-- Helper for Lemma 15.77.3: the inverse prime-local residue-field equivalence sends the
prime-residue-field class of a base element to the canonical local residue class. -/
private theorem prime_localization_residueField_equiv_symm_apply_algebraMap
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    (prime_localization_residueField_equiv (p := p)).symm (algebraMap A p.ResidueField a) =
      algebraMap (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p))
        (algebraMap A (Localization.AtPrime p) a) := by
  -- Proof comment: apply the forward evaluation formula and invert the resulting equivalence.
  exact (prime_localization_residueField_equiv (p := p)).injective <|
    by
      rw [RingEquiv.apply_symm_apply, prime_localization_residueField_equiv_apply_algebraMap]

/-- Helper for Lemma 15.77.3: the ideal residue-field map `κ(𝔭) → κ(q)` for the localized prime
agrees with the source-faithful composite through the two local residue fields. -/
private theorem localizedAway_residueField_map_eq_prime_localization_composite
    (f : R) (hf : f ∉ 𝔭.asIdeal) :
    let A := Localization.Away f
    let q : PrimeSpectrum A :=
      (primeSpectrum_localizationAway_homeomorph_D f).symm ⟨𝔭, hf⟩
    Ideal.ResidueField.map 𝔭.asIdeal q.asIdeal (algebraMap R A)
        ((localizationAway_prime_under_eq (𝔭 := 𝔭) f hf).symm) =
      (prime_localization_residueField_equiv (p := q.asIdeal)).toRingHom.comp
        ((IsLocalRing.ResidueField.map
            ((localizationAway_atPrime_algEquiv (𝔭 := 𝔭) f hf).toRingHom)).comp
          ((prime_localization_residueField_equiv (p := 𝔭.asIdeal)).symm.toRingHom)) := by
  let A := Localization.Away f
  let q : PrimeSpectrum A := (primeSpectrum_localizationAway_homeomorph_D f).symm ⟨𝔭, hf⟩
  let e := localizationAway_atPrime_algEquiv (𝔭 := 𝔭) f hf
  have hq_under : q.asIdeal.under R = 𝔭.asIdeal := by
    -- Proof comment: `q` was chosen as the prime above `𝔭` in the standard-open localization.
    simpa [A, q] using localizationAway_prime_under_eq (𝔭 := 𝔭) f hf
  -- Proof comment: compare both residue-field maps on classes of elements of `R`, which generate
  -- `κ(𝔭)` as an ideal quotient.
  apply Ideal.ResidueField.ringHom_ext
  ext r
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  rw [Ideal.ResidueField.map_algebraMap 𝔭.asIdeal q.asIdeal (algebraMap R A) hq_under.symm r]
  rw [prime_localization_residueField_equiv_symm_apply_algebraMap (p := 𝔭.asIdeal) (a := r)]
  rw [IsLocalRing.ResidueField.map_residue]
  have he_r :
      e.toRingHom (algebraMap R (Localization.AtPrime 𝔭.asIdeal) r) =
        algebraMap A (Localization.AtPrime q.asIdeal) (algebraMap R A r) := by
    simpa [A] using e.commutes r
  rw [he_r]
  rw [prime_localization_residueField_equiv_apply_algebraMap (p := q.asIdeal)
    (a := algebraMap R A r)]

/-- Helper for Lemma 15.77.3: the lower truncation inclusion preserves homology strictly below
the cutoff. In the proof we only use the predecessor degree `i - 1`. -/
private theorem isIso_homologyMap_truncLEι_pred
    {A : Type u} [CommRing A]
    (X : DerivedCategory (ModuleCat A)) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) (i - 1)).map
      ((t.truncLEι i).app X)) := by
  -- Proof comment: rewrite `τ≤ i` as `τ< i + 1` and then apply the standard owner theorem that
  -- upper truncation isomorphically preserves homology in all strictly lower degrees.
  simpa [t.truncLE, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (homology_map_truncLTι_isIso_of_lt
      (𝒜 := ModuleCat A) X (i - 1) (i + 1) (by omega))

/-- Helper for Lemma 15.77.3: after tensoring with the residue field of `q`, the lower
truncation inclusion induces an isomorphism on predecessor homology as soon as the discarded upper
tail has tor-amplitude at least `i + 1`. -/
private theorem homology_map_truncLE_tensor_residue_isIso_of_tail_hasTorAmplitudeGE
    {A : Type u} [CommRing A]
    (q : PrimeSpectrum A) (X : DerivedCategory (ModuleCat A)) (i : ℤ)
    (hTail : HasTorAmplitudeGE ((t.truncGE (i + 1)).obj X) (i + 1)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat q.asIdeal.ResidueField) (i - 1)).map
      ((derivedTensorWithAlgebra (algebraMap A q.asIdeal.ResidueField)).map
        ((t.truncLEι i).app X))) := by
  let Hq := DerivedCategory.homologyFunctor (ModuleCat q.asIdeal.ResidueField)
  let F := derivedTensorWithAlgebra (algebraMap A q.asIdeal.ResidueField)
  let T : Triangle (DerivedCategory (ModuleCat A)) := (t.triangleLTGE (i + 1)).obj X
  let Tq : Triangle (DerivedCategory (ModuleCat q.asIdeal.ResidueField)) := F.mapTriangle.obj T
  have hT : T ∈ distTriang (DerivedCategory (ModuleCat A)) := by
    -- Proof comment: start from the canonical truncation triangle whose first morphism is
    -- `τ≤ i ⟶ X`.
    simpa [T] using t.triangleLTGE_distinguished (i + 1) X
  have hTq : Tq ∈ distTriang (DerivedCategory (ModuleCat q.asIdeal.ResidueField)) := by
    -- Proof comment: derived tensor with the residue field is triangulated, so it preserves the
    -- distinguished truncation triangle.
    simpa [Tq] using F.map_distinguished T hT
  rw [hasTorAmplitudeGE_iff] at hTail
  have hmor₂_zero : (Hq (i - 1)).map Tq.mor₂ = 0 := by
    -- Proof comment: the upper tail contributes no degree-`i - 1` homology after tensoring with
    -- `κ(q)`.
    exact (hTail (ModuleCat.of A q.asIdeal.ResidueField) (i - 1) (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ Tq (i - 2) (i - 1) (by omega) = 0 := by
    -- Proof comment: the connecting morphism starts in another vanishing degree of the same tail.
    exact (hTail (ModuleCat.of A q.asIdeal.ResidueField) (i - 2) (by omega)).eq_of_src _ _
  letI : Epi ((Hq (i - 1)).map Tq.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff Tq hTq (i - 1)).2 hmor₂_zero
  letI : Mono ((Hq (i - 1)).map Tq.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff Tq hTq (i - 2) (i - 1) (by omega)).2 hδ_zero
  -- Proof comment: once the rightmost term is invisible in degrees `i - 2` and `i - 1`, the
  -- long exact sequence identifies the tensor-side map on predecessor homology as an isomorphism.
  simpa [Hq, F, T, Tq, t.truncLE, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (isIso_of_mono_of_epi ((Hq (i - 1)).map Tq.mor₁))

/-- Helper for Lemma 15.77.3: surjectivity of a module map is preserved by conjugating it with
source and target isomorphisms. -/
private theorem Function.Surjective.of_iso_conjugate
    {A : Type u} [CommRing A]
    {M M' N N' : ModuleCat A}
    (eM : M ≅ M') (eN : N ≅ N')
    {f : M' ⟶ N'} (hf : Function.Surjective f.hom) :
    Function.Surjective ((eM.inv ≫ f ≫ eN.hom).hom) := by
  intro y
  rcases hf (eN.inv y) with ⟨x, hx⟩
  refine ⟨eM.hom x, ?_⟩
  -- Proof comment: pull the target element back across the target isomorphism, choose a preimage
  -- there, and then return it to the original source via the source isomorphism.
  change eN.hom (f (eM.inv (eM.hom x))) = y
  simpa using congrArg (fun z ↦ eN.hom z) hx

/-- Helper for Lemma 15.77.3: epimorphy of module maps is preserved by conjugation with source
and target isomorphisms. -/
private theorem epi_of_iso_conjugate
    {A : Type u} [CommRing A]
    {M M' N N' : ModuleCat A}
    (eM : M ≅ M') (eN : N ≅ N')
    {f : M' ⟶ N'} [Epi f] :
    Epi (eM.inv ≫ f ≫ eN.hom) := by
  -- Proof comment: in `ModuleCat`, epimorphy is exactly surjectivity on the underlying linear
  -- map, so the previous surjectivity transport closes the categorical statement.
  refine (ModuleCat.epi_iff_surjective _).2 ?_
  exact Function.Surjective.of_iso_conjugate eM eN
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Helper for Lemma 15.77.3: in a commutative square of module maps, epimorphy transfers from
the bottom edge to the top edge once the vertical maps are isomorphisms. -/
private theorem epi_of_comm_square_of_isIso
    {A : Type u} [CommRing A]
    {M M' N N' : ModuleCat A}
    {f : M ⟶ N} {g : M' ⟶ N'}
    (eM : M' ≅ M) (eN : N' ≅ N)
    (hcomm : eM.hom ≫ f = g ≫ eN.hom) [Epi f] :
    Epi g := by
  have hg : g = eM.hom ≫ f ≫ eN.inv := by
    calc
      g = g ≫ eN.hom ≫ eN.inv := by simp [Category.assoc]
      _ = eM.hom ≫ f ≫ eN.inv := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eN.inv) hcomm
  -- Proof comment: rewrite the top map as the conjugate of the bottom map and invoke the
  -- previous epimorphy transport.
  simpa [hg, Category.assoc] using
    (epi_of_iso_conjugate (A := A) eM.symm eN.symm (f := f))

-- Proof sketch: apply Lemma `15.77.2` in degree `i` to split off
-- `τ_{\ge i + 1}(K \otimes_R^{\mathbf L} R_f)`, then apply the same lemma in degree `i - 1` to
-- the lower truncation to split off `H^i(K)_f[-i]`. The second application makes `H^i(K)_f`
-- finite projective; after shrinking once more, replace finite projective by finite free and
-- compose the two splittings.
/-- Lemma 15.77.3: let `R` be a commutative ring, let `𝔭` be a prime ideal of `R` represented by
`𝔭 : PrimeSpectrum R`, and let `K^•` be a pseudo-coherent object of `D(R)`. Assume the
canonical base-change maps
`H^i(K^•) ⊗_R κ(𝔭) ⟶ H^i(K^• \otimes_R^{\mathbf L} κ(𝔭))`
and
`H^(i - 1)(K^•) ⊗_R κ(𝔭) ⟶ H^(i - 1)(K^• \otimes_R^{\mathbf L} κ(𝔭))`
are surjective. Then there exists `f ∈ R` with `f ∉ 𝔭` such that
`τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)` is perfect with tor-amplitude in `[i + 1, ∞]`,
the localized degree-`i` homology `H^i(K^•)_f` is a finite free `R_f`-module, and
`K^• \otimes_R^{\mathbf L} R_f` decomposes in `D(R_f)` as
`τ_{\le i - 1}(K^• \otimes_R^{\mathbf L} R_f) ⊕ H^i(K^•)_f[-i] ⊕
  τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)`. -/
theorem exists_localizationAway_threeTermSplit_of_residueField_homology_surjective
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj_i : Epi (derivedTensorWithAlgebraHomologyComparison κ K i))
    (hsurj_im1 : Epi (derivedTensorWithAlgebraHomologyComparison κ K (i - 1))) :
    ∃ f : R,
        ∃ e :
          K ⊗[R]^L[Localization.Away f] ≅
            ((t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) i).obj
                  (ModuleCat.of (Localization.Away f) (Away f ((H i).obj K))))) ⊞
              (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
        f ∉ 𝔭.asIdeal ∧
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
            HasTorAmplitudeGE
              ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
              (i + 1) ∧
              Module.Free (Localization.Away f) (Away f ((H i).obj K)) ∧
                Module.Finite (Localization.Away f) (Away f ((H i).obj K)) := by
  -- Proof comment: the first source-faithful step is exactly Lemma 15.77.2 in degree `i`,
  -- which splits off the perfect upper tail after one localization away from `𝔭`.
  rcases
      exists_localizationAway_split_of_residueField_homology_surjective
        (𝔭 := 𝔭) K i hK hsurj_i with
    ⟨f₁, hf₁, hPerf₁, hAmp₁, hsplit₁⟩
  let A := Localization.Away f₁
  let K₁ : DerivedCategory (ModuleCat A) := K ⊗[R]^L[A]
  let q : PrimeSpectrum A := (primeSpectrum_localizationAway_homeomorph_D f₁).symm ⟨𝔭, hf₁⟩
  rcases hsplit₁ with ⟨e₁, he₁, huniq₁⟩
  have hq_asIdeal :
      q.asIdeal = Ideal.map (algebraMap R A) 𝔭.asIdeal := by
    -- Proof comment: cache the exact localized prime ideal now so the second localization step
    -- can talk about `κ(q)` without re-expanding the homeomorphism each time.
    simpa [A, q] using localizationAway_prime_asIdeal (𝔭 := 𝔭) f₁ hf₁
  have hq_under : q.asIdeal.under R = 𝔭.asIdeal := by
    -- Proof comment: the same chosen prime contracts back to the original prime `𝔭`.
    simpa [A, q] using localizationAway_prime_under_eq (𝔭 := 𝔭) f₁ hf₁
  have hq_comp :
      (Ideal.ResidueField.map 𝔭.asIdeal q.asIdeal (algebraMap R A) hq_under.symm).comp
          (algebraMap R 𝔭.asIdeal.ResidueField) =
        algebraMap R q.asIdeal.ResidueField := by
    -- Proof comment: record the exact algebra-map comparison now so the later base-change square
    -- can use a named ring-hom equality rather than reopening the contraction calculation.
    exact residueField_map_comp_algebraMap_of_under_eq (𝔭 := 𝔭) q hq_under
  have hK₁_tail :
      HasTorAmplitudeGE ((t.truncGE (i + 1)).obj K₁) (i + 1) := by
    simpa [A, K₁] using hAmp₁
  -- Route correction: the previous attempt left the whole theorem blocked. The source-faithful
  -- boundary is smaller: first transport the degree-`i - 1` comparison to `K₁` at the localized
  -- prime `q`, then pass it through `τ≤ i` using the vanishing of the upper tail.
  have hsurj_im1_localized :
      Epi (derivedTensorWithAlgebraHomologyComparison q.asIdeal.ResidueField K₁ (i - 1)) := by
    -- TODO(Lemma 15.77.3): prove the base-change adapter
    -- `epi_homologyComparison_after_localizationAway`. The remaining work is to identify
    -- `q.asIdeal.ResidueField` with `κ(𝔭)` via the now-available prime-local comparison
    -- `localizationAway_atPrime_algEquiv`, then transport `hsurj_im1` across
    -- `derivedTensorWithAlgebraCompIso`.
    let _ := hq_asIdeal
    let _ := hq_under
    let _ := hq_comp
    let _ := localizationAway_atPrime_algEquiv (𝔭 := 𝔭) f₁ hf₁
    let _ := prime_localization_residueField_equiv (p := 𝔭.asIdeal)
    let _ := prime_localization_residueField_equiv (p := q.asIdeal)
    let _ := hsurj_im1
    sorry
  have hsurj_im1_trunc :
      Epi (derivedTensorWithAlgebraHomologyComparison q.asIdeal.ResidueField
        ((t.truncLE i).obj K₁) (i - 1)) := by
    have hsource_iso :
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) (i - 1)).map
          ((t.truncLEι i).app K₁)) := by
      -- Proof comment: the source-side vertical map in the comparison square is already an
      -- isomorphism; only the tensor-side vertical map still needs the truncation-triangle input.
      simpa [A, K₁] using isIso_homologyMap_truncLEι_pred (X := K₁) i
    have htarget_iso :
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat q.asIdeal.ResidueField) (i - 1)).map
          ((derivedTensorWithAlgebra (algebraMap A q.asIdeal.ResidueField)).map
            ((t.truncLEι i).app K₁))) := by
      -- Proof comment: the tensor-side vertical map is an isomorphism because the discarded upper
      -- tail has no predecessor homology after tensoring with `κ(q)`.
      simpa [A, K₁] using
        homology_map_truncLE_tensor_residue_isIso_of_tail_hasTorAmplitudeGE
          (q := q) (X := K₁) i hK₁_tail
    let eSource :
        (ModuleCat.extendScalars (algebraMap A q.asIdeal.ResidueField)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat A) (i - 1)).obj
              ((t.truncLE i).obj K₁)) ≅
          (ModuleCat.extendScalars (algebraMap A q.asIdeal.ResidueField)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat A) (i - 1)).obj K₁) :=
      (ModuleCat.extendScalars (algebraMap A q.asIdeal.ResidueField)).mapIso <|
        asIso ((DerivedCategory.homologyFunctor (ModuleCat A) (i - 1)).map
          ((t.truncLEι i).app K₁))
    let eTarget :
        (DerivedCategory.homologyFunctor (ModuleCat q.asIdeal.ResidueField) (i - 1)).obj
            ((derivedTensorWithAlgebra (algebraMap A q.asIdeal.ResidueField)).obj
              ((t.truncLE i).obj K₁)) ≅
          (DerivedCategory.homologyFunctor (ModuleCat q.asIdeal.ResidueField) (i - 1)).obj
            ((derivedTensorWithAlgebra (algebraMap A q.asIdeal.ResidueField)).obj K₁) :=
      (DerivedCategory.homologyFunctor (ModuleCat q.asIdeal.ResidueField) (i - 1)).mapIso <|
        asIso ((derivedTensorWithAlgebra (algebraMap A q.asIdeal.ResidueField)).map
          ((t.truncLEι i).app K₁))
    have hcomm :
        eSource.hom ≫
            derivedTensorWithAlgebraHomologyComparison q.asIdeal.ResidueField K₁ (i - 1) =
          derivedTensorWithAlgebraHomologyComparison q.asIdeal.ResidueField
              ((t.truncLE i).obj K₁) (i - 1) ≫
            eTarget.hom := by
      -- TODO(Lemma 15.77.3): prove the specialized naturality square
      -- `homologyComparison_truncLE_pred_naturality`. The source vertical map is the predecessor
      -- homology map of `t.truncLEι`, and the target vertical map is the predecessor homology map
      -- of its image under derived tensor with `κ(q)`.
      let _ := hsource_iso
      let _ := htarget_iso
      sorry
    -- Proof comment: after isolating the exact comparison square, epimorphy transfers across the
    -- two vertical isomorphisms by the general `ModuleCat` conjugation lemma above.
    exact
      epi_of_comm_square_of_isIso (A := q.asIdeal.ResidueField)
        (f := derivedTensorWithAlgebraHomologyComparison q.asIdeal.ResidueField K₁ (i - 1))
        (g := derivedTensorWithAlgebraHomologyComparison q.asIdeal.ResidueField
          ((t.truncLE i).obj K₁) (i - 1))
        eSource eTarget hcomm
  let _ := e₁
  let _ := he₁
  let _ := huniq₁
  -- TODO(Lemma 15.77.3): apply Lemma `15.77.2` a second time over `A` to `τ≤ i` using
  -- `hsurj_im1_trunc`, identify the new upper summand with the degree-`i` single object via
  -- `truncGE_truncLE_iso_single_homology`, convert that single object to a finite free module
  -- after shrinking once more away from `q`, and then compose the two biproduct splittings.
  sorry

end

end CategoryTheory
