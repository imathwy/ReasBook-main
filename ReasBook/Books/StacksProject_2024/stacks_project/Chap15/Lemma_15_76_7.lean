import Mathlib
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_75_9
import StacksProject_2024.Chap15.Lemma_15_76_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxAway[" f "]" => CochainComplex (ModuleCat (Localization.Away f)) ℤ
local notation "CpxAtPrime[" p "]" =>
  CochainComplex (ModuleCat (Localization.AtPrime p.asIdeal)) ℤ
local notation "FiniteFreeClassAway[" f "]" =>
  (fun M : ModuleCat (Localization.Away f) ↦
    Module.Free (Localization.Away f) M ∧ Module.Finite (Localization.Away f) M)
local notation "BoundedFiniteFreeCpxAway[" f "]" =>
  CochainComplex.MinusWithTermsIn FiniteFreeClassAway[f]
local notation "FiniteFreeClassAtPrime[" p "]" =>
  (fun M : ModuleCat (Localization.AtPrime p.asIdeal) ↦
    Module.Free (Localization.AtPrime p.asIdeal) M ∧
      Module.Finite (Localization.AtPrime p.asIdeal) M)
local notation "BoundedFiniteFreeCpxAtPrime[" p "]" =>
  CochainComplex.MinusWithTermsIn FiniteFreeClassAtPrime[p]

/- Domain-style sampling for Lemma 15.76.7:
- primary domain: perfect derived complexes over a commutative ring, measured by residue-field
  fibers at a prime and represented after shrinking by finite-free localization complexes;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: `K.IsPerfect` remains the source-facing owner, while the explicit
  localized finite-free representative in part `(2)` should reuse the bounded-above owner
  `CochainComplex.MinusWithTermsIn`; the lower support bound is separate source-facing data, and
  upper boundedness stays inside that owner;
- primitive vs. derived:
  primitive data are the prime `p`, the perfect object `K`, the rank function `d`, and the
  localized owner complex;
  derived API is the finite-support residue-field homology conclusion in part `(1)` and the
  termwise rank identifications plus derived isomorphism in part `(2)`;
- source/core/bridge triage:
  `source-facing`: the two numbered clauses of Lemma `15.76.7`;
  `core/canonical`: `K.IsPerfect`, `CochainComplex.MinusWithTermsIn`, and the localized finite-
    free term property;
  `bridge/view`: `primeResidueFieldDerivedHomology` and the localized termwise rank condition on
    the chosen owner complex.
-/

/-- The degree-`i` homology of `K ⊗_R^L κ(𝔭)`. -/
abbrev primeResidueFieldDerivedHomology (p : PrimeSpectrum R) (K : DModR) (i : ℤ) :
    ModuleCat p.asIdeal.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat p.asIdeal.ResidueField) i).obj
    (K ⊗[R]^L[p.asIdeal.ResidueField])

/-- Helper for Lemma 15.76.7: for a local ring, quotienting by the maximal ideal identifies the
residue field defined via the local-ring API with the ideal-quotient residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Lemma 15.76.7: localizing at a prime ideal does not change its residue field. -/
private noncomputable abbrev prime_localization_maximalResidueField_equiv
    (p : Ideal R) [p.IsPrime] :
    (maximalIdeal (Localization.AtPrime p)).ResidueField ≃+* p.ResidueField := by
  -- Proof comment: reinterpret the prime residue field as the local residue field of `R_p`.
  change
    (maximalIdeal (Localization.AtPrime p)).ResidueField ≃+*
      ResidueField (Localization.AtPrime p)
  exact maximalIdeal_residueField_equiv (Localization.AtPrime p)

/-- Helper for Lemma 15.76.7: localizing at a prime ideal does not change its residue field. -/
private noncomputable abbrev prime_localization_residueField_equiv
    (p : Ideal R) [p.IsPrime] :
    ResidueField (Localization.AtPrime p) ≃+* p.ResidueField :=
  -- Proof comment: identify the local-ring residue field of `R_p` with the quotient by the
  -- maximal ideal, then use the canonical prime-local quotient description of that maximal ideal.
  (maximalIdeal_residueField_equiv (Localization.AtPrime p)).symm.trans
    (prime_localization_maximalResidueField_equiv p)

/-- Helper for Lemma 15.76.7: the maximal-ideal residue-field identification sends a residue
class to the canonical local residue class. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (A : Type*) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdeal_residueField_equiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      IsLocalRing.residue A a := by
  -- Proof comment: both residue-field models carry the same class of `a`.
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (IsLocalRing.residue A a) by rfl]
  change
    maximalIdeal_residueField_equiv A
        ((maximalIdeal_residueField_equiv A).symm (IsLocalRing.residue A a)) =
      IsLocalRing.residue A a
  exact (maximalIdeal_residueField_equiv A).apply_symm_apply (IsLocalRing.residue A a)

/-- Helper for Lemma 15.76.7: after identifying ideal residue fields with local residue fields,
the ideal residue-field map becomes the canonical local residue-field map. -/
private theorem maximalIdeal_residueField_equiv_comp_residueFieldMap
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal_residueField_equiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdeal_residueField_equiv A).toRingHom := by
  -- Proof comment: the two maps agree on residue classes of elements of `A`, which generate the
  -- ideal quotient residue field.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdeal_residueField_equiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (maximalIdeal_residueField_equiv A (algebraMap A (maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdeal_residueField_equiv_apply_algebraMap,
    maximalIdeal_residueField_equiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 15.76.7: tensoring over a ring with the degree-zero complex on the regular
module identifies a derived object with itself. -/
noncomputable def regular_single0_derivedTensor_iso_for_prime_residue_field
    {S : Type u} [CommRing S]
    (L : DerivedCategory (ModuleCat S)) :
    L ⊗[S]^L (DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj (ModuleCat.of S S) ≅ L := by
  let eUnit :
      (DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj (ModuleCat.of S S) ≅
        𝟙_ (DerivedCategory (ModuleCat S)) :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app
        (ModuleCat.of S S)) ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat S)).app
          ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj
            (ModuleCat.of S S))).symm
  -- Proof comment: commute the tensor factors, identify `S[0]` with the tensor unit, and then
  -- apply the left unitor.
  exact
    (derivedTensorProduct_comm L
      ((DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj (ModuleCat.of S S))) ≪≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct
        ((DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj (ModuleCat.of S S)) L).symm ≪≫
        whiskerRightIso eUnit L ≪≫
          λ_ L

/-- Helper for Lemma 15.76.7: tor-amplitude of the derived fiber over `κ(𝔭)` forces the prime
residue-field homology to vanish outside the chosen interval. -/
lemma primeResidueFieldDerivedHomology_isZero_of_hasTorAmplitudeIn_outside
    (p : PrimeSpectrum R) (K : DModR) {a b i : ℤ}
    (hamp : HasTorAmplitudeIn (K ⊗[R]^L[p.asIdeal.ResidueField]) a b)
    (hi : i ∉ Set.Icc a b) :
    IsZero (primeResidueFieldDerivedHomology p K i) := by
  let κ := p.asIdeal.ResidueField
  -- Proof comment: test the tor-amplitude condition against the unit module `κ`, then remove the
  -- redundant tensor factor `κ[0]` by the canonical unit isomorphism.
  have hzero_tensor :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
          ((K ⊗[R]^L[κ]) ⊗[κ]^L
            (DerivedCategory.singleFunctor (ModuleCat κ) (0 : ℤ)).obj (ModuleCat.of κ κ))) :=
    hamp (ModuleCat.of κ κ) i hi
  exact
    hzero_tensor.of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat κ) i).mapIso
        (regular_single0_derivedTensor_iso_for_prime_residue_field
          (L := K ⊗[R]^L[κ])))

-- Proof sketch: base change the perfect complex `K` from `R` to the residue field `κ(𝔭)` by
-- derived tensor product. Over a field, a perfect complex is represented by a bounded complex of
-- finite-dimensional vector spaces, so each homology group is finite-dimensional and only finitely
-- many degrees contribute nonzero homology.
/-- Lemma 15.76.7 (1): if `K` is perfect over `R`, then the homology of `K ⊗_R^L κ(𝔭)` is
finite-dimensional over `κ(𝔭)` in every degree and nonzero in only finitely many degrees. -/
theorem primeResidueFieldDerivedHomology_finiteDimensional_and_finiteSupport_of_isPerfect
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) :
    (∀ i : ℤ, FiniteDimensional p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i)) ∧
      Set.Finite {i : ℤ | ¬ IsZero (primeResidueFieldDerivedHomology p K i)} := by
  let κ := p.asIdeal.ResidueField
  have hKκPerfect : (K ⊗[R]^L[κ]).IsPerfect :=
    derivedTensorWithAlgebra_isPerfect K hK
  have hKκBase :
      (K ⊗[R]^L[κ]).IsPseudoCoherent ∧
        HasFiniteTorDimension (K ⊗[R]^L[κ]) :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (K ⊗[R]^L[κ])).1 hKκPerfect
  have hKκCoh :
      (K ⊗[R]^L[κ]).IsPseudoCoherent := hKκBase.1
  have hKκFinite :
      (DerivedCategory.tStructure (ModuleCat κ)).Minus (K ⊗[R]^L[κ]) ∧
        ∀ i : ℤ, Module.Finite κ (primeResidueFieldDerivedHomology p K i) :=
    (isPseudoCoherent_iff_boundedAbove_and_homology_finite
      (R := κ) (K := K ⊗[R]^L[κ])).1 hKκCoh
  constructor
  · intro i
    -- Proof comment: over the field `κ(𝔭)`, finite modules are exactly finite-dimensional vector
    -- spaces.
    let _ : Module.Finite κ (primeResidueFieldDerivedHomology p K i) := hKκFinite.2 i
    infer_instance
  · rcases (hasFiniteTorDimension_iff (K ⊗[R]^L[κ])).1 hKκBase.2 with ⟨a, b, hAmp⟩
    -- Proof comment: outside the tor-amplitude interval, the prime fiber homology is zero, so
    -- the support is contained in the finite set `Icc a b`.
    refine (Set.finite_Icc a b).subset ?_
    intro i hiNonzero
    by_contra hiOutside
    exact hiNonzero <|
      primeResidueFieldDerivedHomology_isZero_of_hasTorAmplitudeIn_outside
        (p := p) (K := K) hAmp hiOutside

/-- Helper for Lemma 15.76.7: the only remaining local transport is the source proof's comparison
between the residue field of `R_𝔭` and the prime residue field `κ(𝔭)` on derived homology. -/
private theorem at_prime_residueFieldDerivedHomology_iso
    (p : PrimeSpectrum R) (K : DModR) (i : ℤ) :
    let Rp := Localization.AtPrime p.asIdeal
    let _ : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp p.asIdeal
    residueFieldDerivedHomology (R := Rp) (K ⊗[R]^L[Rp]) i ≅
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (prime_localization_residueField_equiv p.asIdeal)).functor.obj
        (primeResidueFieldDerivedHomology p K i)) := by
  let Rp := Localization.AtPrime p.asIdeal
  let _ : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp p.asIdeal
  let kp := ResidueField Rp
  let e := prime_localization_residueField_equiv p.asIdeal
  have hcomp :
      (algebraMap Rp kp).comp (algebraMap R Rp) = algebraMap R kp := by
    -- Proof comment: the iterated scalar extension `R → R_𝔭 → κ(R_𝔭)` is the direct map
    -- `R → κ(R_𝔭)`.
    ext r
    rfl
  let eBase :
      ((K ⊗[R]^L[Rp]) ⊗[Rp]^L[kp]) ≅ K ⊗[R]^L[kp] :=
    (derivedTensorWithAlgebraCompIso
      (algebraMap R Rp)
      (algebraMap Rp kp)
      (algebraMap R kp)
      hcomp).app K
  -- Proof comment: after identifying `κ(𝔭)` with `κ(R_𝔭)`, the only remaining step is the
  -- canonical iterated-vs-direct derived tensor comparison `R → R_𝔭 → κ(R_𝔭)`.
  simpa [residueFieldDerivedHomology, primeResidueFieldDerivedHomology, Rp, kp,
    prime_localization_residueField_equiv, prime_localization_maximalResidueField_equiv] using
    (DerivedCategory.homologyFunctor (ModuleCat kp) i).mapIso eBase

/-- Helper for Lemma 15.76.7: restricting scalars along a field equivalence carries the standard
coordinate module to the standard coordinate module of the same rank. -/
private noncomputable def restrictScalars_fin_iso
    {k : Type*} {k' : Type*} [Field k] [Field k'] (e : k ≃+* k') (n : ℕ) :
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.obj
      (ModuleCat.of k' (Fin n → k'))) ≅
      ModuleCat.of k (Fin n → k) := by
  -- Proof comment: the restricted module is the same additive group, and coordinatewise `e.symm`
  -- converts the transported scalar action back to the standard one on `k^n`.
  refine LinearEquiv.toModuleIso
    { toFun := fun v j ↦ e.symm (v j)
      invFun := fun v j ↦ e (v j)
      left_inv := by
        intro v
        ext j
        simp
      right_inv := by
        intro v
        ext j
        simp
      map_add' := by
        intro v w
        ext j
        simp
      map_smul' := by
        intro a v
        ext j
        simp [smul_eq_mul, map_mul] }

lemma at_prime_residueFieldDerivedHomology_linearEquiv_of_finrank
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) (d : ℤ → ℕ)
    (hd :
      ∀ i : ℤ,
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = d i) :
    let Rp := Localization.AtPrime p.asIdeal
    let _ : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp p.asIdeal
    ∀ i : ℤ,
      Nonempty
        ((residueFieldDerivedHomology (R := Rp) (K ⊗[R]^L[Rp]) i) ≃ₗ[ResidueField Rp]
          (Fin (d i) → ResidueField Rp)) := by
  let Rp := Localization.AtPrime p.asIdeal
  let _ : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp p.asIdeal
  let F :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (prime_localization_residueField_equiv p.asIdeal)).functor
  let hprimeFinite :=
    (primeResidueFieldDerivedHomology_finiteDimensional_and_finiteSupport_of_isPerfect
      (p := p) (K := K) hK).1
  intro i
  let _ : FiniteDimensional p.asIdeal.ResidueField
      (primeResidueFieldDerivedHomology p K i) :=
    hprimeFinite i
  let b :
      Module.Basis (Fin (d i)) p.asIdeal.ResidueField
        (primeResidueFieldDerivedHomology p K i) :=
    Module.finBasisOfFinrankEq
      p.asIdeal.ResidueField
      (primeResidueFieldDerivedHomology p K i)
      (hd i)
  have hcoords :
      F.obj (primeResidueFieldDerivedHomology p K i) ≅
        ModuleCat.of (ResidueField Rp) (Fin (d i) → ResidueField Rp) := by
    -- Proof comment: choose the `κ(𝔭)`-basis prescribed by `hd`, transport it through the
    -- restriction-of-scalars equivalence, and then identify the restricted standard module with
    -- the standard module over `κ(R_p)`.
    exact
      (F.mapIso (LinearEquiv.toModuleIso b.equivFun)) ≪≫
        restrictScalars_fin_iso
          (e := prime_localization_residueField_equiv p.asIdeal)
          (n := d i)
  -- Proof comment: once the prime fiber is transported to the local residue field, the chosen
  -- coordinate basis yields the required linear equivalence for Lemma `15.76.6`.
  exact
    ⟨((at_prime_residueFieldDerivedHomology_iso (p := p) (K := K) (i := i)).trans
      hcoords).toLinearEquiv⟩

/-- Helper for Lemma 15.76.7: the local step of the source proof produces the prescribed bounded
above finite-free representative over the local ring `R_𝔭`. -/
lemma exists_local_termwiseFree_representative_at_prime
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) (d : ℤ → ℕ)
    (hd :
      ∀ i : ℤ,
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = d i) :
    let Rp := Localization.AtPrime p.asIdeal
    let _ : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp p.asIdeal
    ∃ P : BoundedFiniteFreeCpxAtPrime[p],
      (∀ i : ℤ,
        Nonempty (((P : CpxAtPrime[p]).X i) ≃ₗ[Rp] (Fin (d i) → Rp))) ∧
        Nonempty ((K ⊗[R]^L[Rp]) ≅ DerivedCategory.Q.obj (P : CpxAtPrime[p])) := by
  let Rp := Localization.AtPrime p.asIdeal
  let _ : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp p.asIdeal
  have hKpPerfect : (K ⊗[R]^L[Rp]).IsPerfect :=
    derivedTensorWithAlgebra_isPerfect K hK
  have hKpPseudo : (K ⊗[R]^L[Rp]).IsPseudoCoherent :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
      (K ⊗[R]^L[Rp])).1 hKpPerfect |>.1
  have hlin :
      ∀ i : ℤ,
        Nonempty
          ((residueFieldDerivedHomology (R := Rp) (K ⊗[R]^L[Rp]) i) ≃ₗ[ResidueField Rp]
            (Fin (d i) → ResidueField Rp)) :=
    at_prime_residueFieldDerivedHomology_linearEquiv_of_finrank
      (p := p) (K := K) hK d hd
  -- Proof comment: once the residue-field dimensions have been transported to the local ring
  -- `R_𝔭`, Lemma `15.76.6` gives the bounded-above finite-free representative directly.
  simpa [Rp] using
    exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology
      (R := Rp) (K := K ⊗[R]^L[Rp]) hKpPseudo d hlin

/-- Helper for Lemma 15.76.7: a term linearly equivalent to the rank-zero standard free module is
the zero module. -/
private theorem isZero_of_linearEquiv_fin_zero
    {S : Type*} [CommRing S] (M : ModuleCat S)
    (hM : Nonempty (M ≃ₗ[S] (Fin 0 → S))) :
    IsZero M := by
  rcases hM with ⟨e⟩
  rw [ModuleCat.isZero_iff_subsingleton]
  -- Proof comment: the standard rank-zero free module is subsingleton, so any linearly
  -- equivalent module is subsingleton as well.
  exact e.injective.subsingleton

/-- Helper for Lemma 15.76.7: the local finite-free model obtained over `R_𝔭` is supported on a
finite interval because the prescribed ranks `d i` vanish outside the finite support of the prime
residue-field homology. -/
private lemma exists_finite_interval_of_local_termwiseFree_model
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) (d : ℤ → ℕ)
    (hd :
      ∀ i : ℤ,
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = d i)
    (Pp : BoundedFiniteFreeCpxAtPrime[p])
    (hPpTerms :
      ∀ i : ℤ,
        Nonempty (((Pp : CpxAtPrime[p]).X i) ≃ₗ[Localization.AtPrime p.asIdeal]
          (Fin (d i) → Localization.AtPrime p.asIdeal))) :
    ∃ a b : ℤ,
      (Pp : CpxAtPrime[p]).IsStrictlyGE a ∧
        (Pp : CpxAtPrime[p]).IsStrictlyLE b := by
  let support : Set ℤ := {i : ℤ | d i ≠ 0}
  obtain ⟨hprimeFinite, hprimeSupportFinite⟩ :=
    primeResidueFieldDerivedHomology_finiteDimensional_and_finiteSupport_of_isPerfect
      (p := p) (K := K) hK
  have hsupportFinite : support.Finite := by
    refine hprimeSupportFinite.subset ?_
    intro i hi
    have hfd :
        FiniteDimensional p.asIdeal.ResidueField
          (primeResidueFieldDerivedHomology p K i) :=
      hprimeFinite i
    by_contra hzero
    have hfinrankZero :
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = 0 := by
      rw [Module.finrank_eq_zero_iff p.asIdeal.ResidueField]
      exact (ModuleCat.isZero_iff_subsingleton).1 hzero
    exact hi <| by simpa [hd i] using hfinrankZero
  obtain ⟨a, ha⟩ := hsupportFinite.bddBelow
  obtain ⟨b, hPpLE⟩ := CochainComplex.MinusWithTermsIn.exists_isStrictlyLE
    (P := FiniteFreeClassAtPrime[p]) Pp
  refine ⟨a, b, ?_, hPpLE⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hdiZero : d i = 0 := by
    by_contra hdi
    have hmem : i ∈ support := hdi
    exact not_lt_of_ge (ha hmem) hi
  -- Proof comment: below the lower bound, the prescribed rank is zero, so the chosen standard
  -- coordinate description identifies the term with the zero module.
  exact isZero_of_linearEquiv_fin_zero ((Pp : CpxAtPrime[p]).X i) <| by
    simpa [hdiZero] using hPpTerms i

/-- Helper for Lemma 15.76.7: the standard degree-`n` denominator in the away localization
`R_f` is the power `f ^ n`. -/
private abbrev away_power (f : R) (n : ℕ) : Submonoid.powers f :=
  ⟨f ^ n, ⟨n, rfl⟩⟩

/-- Helper for Lemma 15.76.7: an element outside the prime ideal defines a canonical element of
the prime complement. -/
private abbrev prime_compl_of_not_mem
    (p : PrimeSpectrum R) {r : R} (hr : r ∉ p.asIdeal) :
    p.asIdeal.primeCompl :=
  ⟨r, hr⟩

/-- Helper for Lemma 15.76.7: if `f ∉ p`, then every power of `f` also avoids `p`. -/
private theorem pow_not_mem_prime
    (p : PrimeSpectrum R) {f : R} (hf : f ∉ p.asIdeal) (n : ℕ) :
    f ^ n ∉ p.asIdeal := by
  -- Proof comment: prime ideals are radical, so membership of a power would force membership of
  -- the base element.
  intro hpow
  exact hf (p.asIdeal.isPrime.mem_of_pow_mem n hpow)

/-- Helper for Lemma 15.76.7: a finite product of elements outside `p` still lies outside `p`. -/
private theorem finset_prod_not_mem_prime
    {α : Type*} [DecidableEq α]
    (p : PrimeSpectrum R) (t : Finset α) (s : α → R)
    (hs : ∀ a ∈ t, s a ∉ p.asIdeal) :
    ∏ a in t, s a ∉ p.asIdeal := by
  classical
  -- Proof comment: a prime ideal contains a finite product only if it contains one factor.
  refine Finset.induction_on t ?_ ?_
  · simp
  · intro a t ha hrec
    have ha_mem : a ∈ insert a t := by
      simp
    have hsa : s a ∉ p.asIdeal := hs a ha_mem
    have hst : ∏ b in t, s b ∉ p.asIdeal := by
      apply hrec
      intro b hb
      have hb_mem : b ∈ insert a t := by
        simp [hb]
      exact hs b hb_mem
    intro hprod
    rw [Finset.prod_insert ha] at hprod
    exact (p.asIdeal.isPrime.mem_or_mem hprod).elim hsa hst

/-- Helper for Lemma 15.76.7: if `f ∉ p`, then every power of `f` maps into the prime-complement
submonoid used to define `R_𝔭`. -/
private theorem powers_le_primeCompl_comap_of_not_mem
    (p : PrimeSpectrum R) {f : R} (hf : f ∉ p.asIdeal) :
    Submonoid.powers f ≤ Submonoid.comap (RingHom.id R) p.asIdeal.primeCompl := by
  -- Proof comment: the identity map preserves the fact that every power of `f` stays outside the
  -- prime ideal.
  intro x hx
  rcases hx with ⟨n, rfl⟩
  simpa using pow_not_mem_prime (p := p) (f := f) hf n

/-- Helper for Lemma 15.76.7: if `f ∉ p`, there is a canonical comparison map `R_f → R_𝔭`. -/
private noncomputable abbrev awayToAtPrime
    (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal) :
    Localization.Away f →+* Localization.AtPrime p.asIdeal :=
  IsLocalization.map
    (Localization.AtPrime p.asIdeal)
    (RingHom.id R)
    (powers_le_primeCompl_comap_of_not_mem (p := p) (f := f) hf)

/-- Helper for Lemma 15.76.7: the canonical map `R_f → R_𝔭` sends the standard fraction
`r / f^n` to the same fraction in the prime localization. -/
private theorem awayToAtPrime_map_mk'
    (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal) (r : R) (n : ℕ) :
    awayToAtPrime p f hf
        (IsLocalization.mk' (Localization.Away f) r (away_power f n)) =
      IsLocalization.mk' (Localization.AtPrime p.asIdeal) r
        (prime_compl_of_not_mem p (pow_not_mem_prime (p := p) (f := f) hf n)) := by
  -- Proof comment: `IsLocalization.map_mk'` is the strict transport formula for localization
  -- maps once the denominator submonoid inclusion is fixed.
  simpa [awayToAtPrime, away_power, prime_compl_of_not_mem] using
    (IsLocalization.map_mk'
      (Q := Localization.AtPrime p.asIdeal)
      (g := RingHom.id R)
      (powers_le_primeCompl_comap_of_not_mem (p := p) (f := f) hf)
      r
      (away_power f n))

/-- Helper for Lemma 15.76.7: extension of scalars on module categories is canonically tensoring
with the target ring. -/
private noncomputable def moduleCat_extendScalars_tensor_iso
    {A : Type u} [CommRing A] [Algebra R A]
    (M : Type u) [AddCommGroup M] [Module R M] :
    (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R M) ≅
      ModuleCat.of A (A ⊗[R] M) := by
  -- Proof comment: `ModuleCat.extendScalars` is defined by tensoring with the target algebra.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv R A)
      (LinearEquiv.refl R M)).toModuleIso

/-- Helper for Lemma 15.76.7: after extending scalars from `R_f` to `R_𝔭`, the standard free
module of rank `n` becomes the standard free `R_𝔭`-module of the same rank. -/
private noncomputable def away_to_at_prime_standard_free_iso
    (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal) (n : ℕ) :
    (ModuleCat.extendScalars (awayToAtPrime p f hf)).obj
      (ModuleCat.of (Localization.Away f) (Fin n → Localization.Away f)) ≅
      ModuleCat.of (Localization.AtPrime p.asIdeal) (Fin n → Localization.AtPrime p.asIdeal) := by
  -- Proof comment: first rewrite scalar extension as tensor product over `R_f`, then use the
  -- standard tensor-vs-product identification for a finite coordinate module.
  exact
    moduleCat_extendScalars_tensor_iso
        (R := Localization.Away f)
        (A := Localization.AtPrime p.asIdeal)
        (M := Fin n → Localization.Away f) ≪≫
      (TensorProduct.piScalarRight
        (Localization.Away f)
        (Localization.AtPrime p.asIdeal)
        (Localization.Away f)
        (Fin n)).toModuleIso

/-- Helper for Lemma 15.76.7: finitely many elements of `R_𝔭` lift to one away localization
`R_f`. This isolates the coefficient-denominator clearing step of the source proof. -/
private theorem exists_not_mem_prime_common_denominator_of_finset
    {α : Type*} [DecidableEq α]
    (p : PrimeSpectrum R) (t : Finset α) (z : α → Localization.AtPrime p.asIdeal) :
    ∃ (f : R) (hf : f ∉ p.asIdeal),
      ∀ a ∈ t, ∃ y : Localization.Away f, awayToAtPrime p f hf y = z a := by
  classical
  let Rp := Localization.AtPrime p.asIdeal
  let num : α → R := fun a ↦ (IsLocalization.mk'_surjective p.asIdeal.primeCompl (z a)).choose.1
  let den : α → p.asIdeal.primeCompl :=
    fun a ↦ (IsLocalization.mk'_surjective p.asIdeal.primeCompl (z a)).choose.2
  have hz :
      ∀ a : α, IsLocalization.mk' Rp (num a) (den a) = z a := by
    intro a
    exact (IsLocalization.mk'_surjective p.asIdeal.primeCompl (z a)).choose_spec
  let f : R := ∏ a in t, (den a : R)
  have hf : f ∉ p.asIdeal := by
    -- Proof comment: the common denominator is the finite product of the chosen local
    -- denominators, hence still outside the prime ideal.
    apply finset_prod_not_mem_prime (p := p) (t := t) (s := fun a ↦ (den a : R))
    intro a ha
    exact (den a).2
  refine ⟨f, hf, ?_⟩
  intro a ha
  let d : R := ∏ b in t.erase a, (den b : R)
  let y : Localization.Away f :=
    IsLocalization.mk' (Localization.Away f) (d * num a) (away_power f 1)
  refine ⟨y, ?_⟩
  have hprod : d * (den a : R) = f := by
    -- Proof comment: the chosen factor `d` is exactly the product of all denominators except the
    -- `a`-th one, so reinserting that factor recovers the common denominator.
    simpa [d, f] using
      (Finset.prod_erase_mul (s := t) (f := fun b ↦ (den b : R)) (a := a) ha)
  have hfrac :
      algebraMap R Rp (num a) = z a * algebraMap R Rp (den a : R) := by
    -- Proof comment: rewriting the chosen fraction representative for `z a` gives the standard
    -- numerator-denominator identity in the localization.
    exact
      (IsLocalization.mk'_eq_iff_eq_mul
        (M := p.asIdeal.primeCompl)
        (S := Rp)
        (x := num a)
        (y := den a)
        (z := z a)).mp
        (hz a)
  rw [awayToAtPrime_map_mk' (p := p) (f := f) (hf := hf) (r := d * num a) (n := 1)]
  apply
    (IsLocalization.mk'_eq_iff_eq_mul
      (M := p.asIdeal.primeCompl)
      (S := Rp)
      (x := d * num a)
      (y := prime_compl_of_not_mem p hf)
      (z := z a)).2
  -- Proof comment: multiply the numerator identity for `z a` by the complementary product `d`
  -- and replace `d * den a` with the common denominator `f`.
  calc
    algebraMap R Rp (d * num a)
        = algebraMap R Rp d * algebraMap R Rp (num a) := by
            simp
    _ = algebraMap R Rp d * (z a * algebraMap R Rp (den a : R)) := by
          rw [hfrac]
    _ = z a * algebraMap R Rp (d * (den a : R)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = z a * algebraMap R Rp f := by
          rw [hprod]

/-- Helper for Lemma 15.76.7: if finitely many elements of `R_f` vanish after mapping to `R_𝔭`,
then one further localization `R_{f * g}` already kills all of them. -/
private theorem exists_refinement_killing_finite_family_under_away_to_at_prime
    {α : Type*} [DecidableEq α]
    (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal)
    (t : Finset α) (x : α → Localization.Away f)
    (hx : ∀ a ∈ t, awayToAtPrime p f hf (x a) = 0) :
    ∃ (g : R) (hg : g ∉ p.asIdeal),
      ∀ a ∈ t,
        IsLocalization.Away.awayToAwayRight f g (x a) = 0 := by
  classical
  have hrepr :
      ∀ a : α, ∃ r : R, ∃ n : ℕ,
        IsLocalization.mk' (Localization.Away f) r (away_power f n) = x a := by
    intro a
    rcases IsLocalization.mk'_surjective (Submonoid.powers f) (x a) with ⟨⟨r, s⟩, hs⟩
    rcases s with ⟨_, ⟨n, rfl⟩⟩
    exact ⟨r, n, hs⟩
  choose num pow hnum using hrepr
  have hclear :
      ∀ a ∈ t, ∃ u : p.asIdeal.primeCompl, (u : R) * num a = 0 := by
    intro a ha
    have hx' :
        awayToAtPrime p f hf
            (IsLocalization.mk' (Localization.Away f) (num a) (away_power f (pow a))) = 0 := by
      simpa [hnum a] using hx a ha
    rw [awayToAtPrime_map_mk' (p := p) (f := f) (hf := hf) (r := num a) (n := pow a)] at hx'
    exact
      (IsLocalization.mk'_eq_zero_iff
        (S := Localization.AtPrime p.asIdeal)
        (x := num a)
        (s := prime_compl_of_not_mem p (pow_not_mem_prime (p := p) (f := f) hf (pow a)))).mp hx'
  choose u hu using hclear
  let s : α → R := fun a ↦ if ha : a ∈ t then (u a ha : R) else 1
  let g : R := ∏ a in t, s a
  have hs_not_mem : ∀ a ∈ t, s a ∉ p.asIdeal := by
    intro a ha
    simp [s, ha, (u a ha).2]
  have hg : g ∉ p.asIdeal := by
    -- Proof comment: the refinement denominator is the product of finitely many annihilators,
    -- hence it still avoids the prime ideal.
    exact finset_prod_not_mem_prime (p := p) (t := t) (s := s) hs_not_mem
  refine ⟨g, hg, ?_⟩
  intro a ha
  have hprod :
      (∏ b in t.erase a, s b) * s a = g := by
    -- Proof comment: isolate the `a`-th annihilator from the common denominator product.
    simpa [g] using
      (Finset.prod_erase_mul (s := t) (f := s) (a := a) ha)
  have hmul_zero : g * num a = 0 := by
    -- Proof comment: one factor of `g` already annihilates the chosen numerator of `x a`.
    calc
      g * num a = ((∏ b in t.erase a, s b) * s a) * num a := by rw [hprod]
      _ = (∏ b in t.erase a, s b) * (s a * num a) := by simp [mul_assoc]
      _ = 0 := by
        simp [s, ha, hu a ha]
  have hnum_zero :
      algebraMap R (Localization.Away (f * g)) (num a) = 0 := by
    -- Proof comment: multiplying the numerator by `f * g` gives zero in `R`, so its image
    -- already vanishes in the refined localization.
    refine (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (f * g)) (Localization.Away (f * g)) (num a)).2 ?_
    refine ⟨away_power (f * g) 1, ?_⟩
    simpa [away_power, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : R ↦ f * z) hmul_zero
  rw [← hnum a]
  -- Proof comment: once the refined localization kills the chosen numerator, the whole fraction
  -- representing `x a` maps to zero under the canonical comparison `R_f → R_{f * g}`.
  refine
    (show IsLocalization.Away.awayToAwayRight f g
        (IsLocalization.mk' (Localization.Away f) (num a) (away_power f (pow a))) = 0 from ?_)
  rw [show (0 : Localization.Away (f * g)) = 0 by rfl]
  refine
    (IsLocalization.lift_mk'_spec
      (S := Localization.Away f)
      (P := Localization.Away (f * g))
      (M := Submonoid.powers f)
      (g := algebraMap R (Localization.Away (f * g)))
      (hg := fun y ↦ by
        rcases y with ⟨y, hy⟩
        rcases hy with ⟨n, rfl⟩
        simpa [map_pow] using
          (IsUnit.map (powMonoidHom n)
            (isUnit_of_dvd (f * g) (dvd_mul_right f g)))
      (x := num a)
      (v := (0 : Localization.Away (f * g)))
      (y := away_power f (pow a))).2 ?_
  simpa [hnum_zero]

/-- Helper for Lemma 15.76.7: the local part of the source proof can be packaged as one
finite-interval free model over `R_𝔭`, together with the prescribed coordinate identifications
and the derived representing isomorphism. -/
private theorem exists_local_interval_model_at_prime
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) (d : ℤ → ℕ)
    (hd :
      ∀ i : ℤ,
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = d i) :
    ∃ (a b : ℤ) (Pp : BoundedFiniteFreeCpxAtPrime[p]),
      (Pp : CpxAtPrime[p]).IsStrictlyGE a ∧
        (Pp : CpxAtPrime[p]).IsStrictlyLE b ∧
        (∀ i : ℤ,
          Nonempty (((Pp : CpxAtPrime[p]).X i) ≃ₗ[Localization.AtPrime p.asIdeal]
            (Fin (d i) → Localization.AtPrime p.asIdeal))) ∧
        Nonempty ((K ⊗[R]^L[Localization.AtPrime p.asIdeal]) ≅
          DerivedCategory.Q.obj (Pp : CpxAtPrime[p])) := by
  obtain ⟨Pp, hPpTerms, hPpRep⟩ :=
    exists_local_termwiseFree_representative_at_prime
      (p := p) (K := K) hK d hd
  obtain ⟨a, b, hPpGE, hPpLE⟩ :=
    exists_finite_interval_of_local_termwiseFree_model
      (p := p) (K := K) (hK := hK) d hd Pp hPpTerms
  -- Proof comment: the already-proved local existence theorem provides the model `Pp`, and the
  -- finite-support argument upgrades it to a fixed interval `[a, b]`.
  exact ⟨a, b, Pp, hPpGE, hPpLE, hPpTerms, hPpRep⟩

/-- Helper for Lemma 15.76.7: once the local interval model over `R_𝔭` is fixed, the remaining
source-faithful step is to descend that strict finite free complex and its representing
isomorphism to a single away localization `R_f`. -/
private theorem exists_away_termwiseFree_representative_of_local_interval_model
    (p : PrimeSpectrum R) (K : DModR) (d : ℤ → ℕ)
    (a b : ℤ) (Pp : BoundedFiniteFreeCpxAtPrime[p])
    (hPpGE : (Pp : CpxAtPrime[p]).IsStrictlyGE a)
    (hPpLE : (Pp : CpxAtPrime[p]).IsStrictlyLE b)
    (hPpTerms :
      ∀ i : ℤ,
        Nonempty (((Pp : CpxAtPrime[p]).X i) ≃ₗ[Localization.AtPrime p.asIdeal]
          (Fin (d i) → Localization.AtPrime p.asIdeal)))
    (hPpRep :
      Nonempty ((K ⊗[R]^L[Localization.AtPrime p.asIdeal]) ≅
        DerivedCategory.Q.obj (Pp : CpxAtPrime[p]))) :
    ∃ (f : R) (_ : f ∉ p.asIdeal) (P : BoundedFiniteFreeCpxAway[f]),
      (P : CpxAway[f]).IsStrictlyGE a ∧
        (∀ i : ℤ,
          Nonempty (((P : CpxAway[f]).X i) ≃ₗ[Localization.Away f]
            (Fin (d i) → Localization.Away f))) ∧
        Nonempty ((K ⊗[R]^L[Localization.Away f]) ≅ DerivedCategory.Q.obj (P : CpxAway[f])) := by
  let _ : (Pp : CpxAtPrime[p]).IsStrictlyGE a := hPpGE
  let _ : (Pp : CpxAtPrime[p]).IsStrictlyLE b := hPpLE
  let _ :
      Nonempty ((K ⊗[R]^L[Localization.AtPrime p.asIdeal]) ≅
        DerivedCategory.Q.obj (Pp : CpxAtPrime[p])) := hPpRep
  -- TODO: follow the fixed source route on the interval `[a, b]`: write the differentials of
  -- `Pp` in the standard coordinates from `hPpTerms`, clear denominators for the finitely many
  -- matrix coefficients with `exists_not_mem_prime_common_denominator_of_finset`, refine once via
  -- `exists_refinement_killing_finite_family_under_away_to_at_prime` so all finitely many
  -- relations `d ≫ d = 0` hold literally over one away stage, package those descended maps as a
  -- bounded finite-free away complex, and then descend the representing isomorphism along
  -- `R_𝔭 = colim_{f ∉ 𝔭} R_f`.
  sorry

-- Proof sketch: apply part `(1)` to see that each residue-field homology group
-- `H^i(K ⊗_R^L κ(𝔭))` is finite-dimensional. Localize `R` at `𝔭`, so that `K ⊗_R^L R_𝔭` is a
-- perfect complex over the local ring `R_𝔭`. Apply the local lifting statement to obtain a
-- bounded-above finite-free representative in the canonical owner
-- `CochainComplex.MinusWithTermsIn`, with those homology dimensions as termwise ranks, and then
-- descend that representative from `R_𝔭 = colim_{f ∉ 𝔭} R_f` to some away localization `R_f`,
-- keeping the lower support bound separate from the bounded-above owner data.
/-- Lemma 15.76.7 (2): if `d i = dim_{κ(𝔭)} H^i(K ⊗_R^L κ(𝔭))`, then after inverting some
`f ∉ 𝔭` the derived localization `K ⊗_R^L R_f` is represented by a bounded-above finite-free
complex with some lower support bound, whose degree-`i` term is free of rank `d i`. -/
theorem exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPerfect
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) (d : ℤ → ℕ)
    (hd :
      ∀ i : ℤ,
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = d i) :
    ∃ (f : R) (_ : f ∉ p.asIdeal) (a : ℤ) (P : BoundedFiniteFreeCpxAway[f]),
      (P : CpxAway[f]).IsStrictlyGE a ∧
        (∀ i : ℤ,
          Nonempty (((P : CpxAway[f]).X i) ≃ₗ[Localization.Away f]
            (Fin (d i) → Localization.Away f))) ∧
        Nonempty ((K ⊗[R]^L[Localization.Away f]) ≅ DerivedCategory.Q.obj (P : CpxAway[f])) := by
  obtain ⟨a, b, Pp, hPpGE, hPpLE, hPpTerms, hPpRep⟩ :=
    exists_local_interval_model_at_prime
      (p := p) (K := K) hK d hd
  -- Proof comment: the main theorem now exactly matches the source outline: first fix the local
  -- finite-interval model over `R_𝔭`, then descend that explicit model to one away stage.
  exact
    exists_away_termwiseFree_representative_of_local_interval_model
      (p := p) (K := K) (d := d) a b Pp hPpGE hPpLE hPpTerms hPpRep

end

end CategoryTheory
