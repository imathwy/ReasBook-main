import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_10
import StacksProject_2024.stacks_project.Chap15.Definition_15_112_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_11
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_116_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_108_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_112_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_115_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v w x uA vA wA xA

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/- Domain-style sampling for Lemma 15.116.5:
- primary domain: ramification-eliminating base change for extensions of discrete valuation
  rings, expressed through the chapter solution predicates and strict-henselization existence;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `IsStrictHenselizationOf`;
- best owner abstraction: the solution notions already belong to the chapter owners from
  `Definition_15_116_1`, so this lemma should remain a source-facing existence theorem relating
  those owners rather than introduce a second bundled square owner;
- primitive-vs-derived split: the primitive witness data are the DVR extensions `A → A'`,
  `B → B'`, `A' → B'`, the compatible fraction fields `K'`, `L'`, and the residue-field
  comparison algebras; the three descent clauses are derived API and should therefore be phrased
  directly with `IsWeakSolutionFor`, `IsSolutionFor`, and `IsSeparableSolutionFor`.

Source/core/bridge triage:
- `source-facing`: the existence theorem for a ramification-eliminating square;
- `core/canonical`: `IsWeakSolutionFor`, `IsSolutionFor`, `IsSeparableSolutionFor`, and the
  strict-henselization owner `IsStrictHenselizationOf` used in the proof sketch;
- `bridge/view`: the explicit existential witness rings and fields together with their algebraic
  and residue-field comparison properties.
-/

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Helper for Lemma 15.116.5: the residue field at the zero prime of a domain is canonically its
fraction field. -/
private noncomputable def zeroPrime_residueField_algEquiv_fractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) := by
  let e : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) := (AlgEquiv.quotientBot R R).symm
  letI : IsFractionRing R ((⊥ : Ideal R).ResidueField) := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap R ((⊥ : Ideal R).ResidueField) x =
      algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    exact show
        algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField)
            (Ideal.Quotient.mk (⊥ : Ideal R) x) =
          algebraMap R ((⊥ : Ideal R).ResidueField) x by
      rfl
  -- The zero-prime residue field is already a fraction ring, so the standard owner equivalence
  -- identifies it with `FractionRing R`.
  exact FractionRing.algEquiv R ((⊥ : Ideal R).ResidueField)

/-- Helper for Lemma 15.116.5: a strict henselization of a discrete valuation ring is again a
discrete valuation ring, and the structural map is an extension of discrete valuation rings. -/
private theorem strict_henselization_isExtensionOfDiscreteValuationRings
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Rsh : Type*) [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh] :
    ∃ (_ : IsDomain Rsh) (_ : IsDiscreteValuationRing Rsh),
      IsExtensionOfDiscreteValuationRings R Rsh := by
  obtain ⟨Rh, _, _, hRh⟩ := exists_henselization R
  letI : IsHenselizationOf R Rh := hRh
  have hTFAE :
      List.TFAE
        [(∃ (_ : IsDomain R), IsDiscreteValuationRing R),
          (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh),
          (∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh)] :=
    discreteValuationRing_tfae_of_henselization_and_strictHenselization
      (R := R) (Rh := Rh) (Rsh := Rsh)
  have hRsh :
      ∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh :=
    (hTFAE.out 0 2).mp ⟨inferInstance, inferInstance⟩
  rcases hRsh with ⟨hDomain, hDvr⟩
  letI : IsDomain Rsh := hDomain
  letI : IsDiscreteValuationRing Rsh := hDvr
  have hinj : Function.Injective (algebraMap R Rsh) :=
    RingHom.FaithfullyFlat.injective
      (strictHenselizationMap_faithfullyFlat (R := R) (Rsh := Rsh))
  -- Once the target is known to be a DVR, faithful flatness supplies injectivity and the local
  -- map condition is already part of the strict-henselization owner.
  exact
    ⟨hDomain, hDvr,
      { toIsLocalHom := inferInstance
        algebraMap_injective := hinj }⟩

/-- Helper for Lemma 15.116.5: the generic-fiber statement from Lemma `15.45.13` applied at the
zero prime yields an algebraic and separable extension on the corresponding zero-prime residue
fields. -/
private theorem zero_prime_strictHenselization_residueField_isAlgebraic_and_separable
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Rsh : Type*} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [IsDomain Rsh] [IsDiscreteValuationRing Rsh] [IsExtensionOfDiscreteValuationRings R Rsh] :
    Algebra.IsAlgebraic ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) ∧
      Algebra.IsSeparable ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) := by
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  letI : (⊥ : Ideal Rsh).LiesOver (⊥ : Ideal R) :=
    bot_lies_over_bot_of_injective
      (hinj := (inferInstance : IsExtensionOfDiscreteValuationRings R Rsh).algebraMap_injective)
  let q0 : p0.asIdeal.primesOver Rsh := Ideal.primesOver.mk p0.asIdeal (⊥ : Ideal Rsh)
  -- The source proof uses the zero prime to pass from residue fields to the generic fiber.
  simpa [p0, PrimeSpectrum.asIdeal_bot] using
    strictHenselization_residueField_isAlgebraic_and_separable
      (R := R) (Rsh := Rsh) p0 q0

/-- Helper for Lemma 15.116.5: the residue field of a strict henselization of a discrete
valuation ring is a separable closure of the original residue field. -/
private theorem strict_henselization_residueField_isSepClosure
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Rsh : Type*} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [IsDomain Rsh] [IsDiscreteValuationRing Rsh] [IsExtensionOfDiscreteValuationRings R Rsh] :
    IsSepClosure (ResidueField R) (ResidueField Rsh) := by
  let p : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
  letI : (maximalIdeal Rsh).LiesOver (maximalIdeal R) :=
    (Ideal.liesOver_iff (maximalIdeal Rsh) (maximalIdeal R)).2 <|
      (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm
  let q : p.asIdeal.primesOver Rsh := Ideal.primesOver.mk p.asIdeal (maximalIdeal Rsh)
  have hAlg :
      Algebra.IsAlgebraic (ResidueField R) (ResidueField Rsh) := by
    -- Apply the strict-henselization residue-field theorem at the closed point.
    simpa [p] using
      (strictHenselization_residueField_isAlgebraic_and_separable
        (R := R) (Rsh := Rsh) p q).1
  let _ : Algebra.IsAlgebraic (ResidueField R) (ResidueField Rsh) := hAlg
  -- A strictly henselian local ring has separably closed residue field, so algebraicity upgrades
  -- the extension to a separable closure.
  infer_instance

/-- Helper for Lemma 15.116.5: transport the algebraic zero-prime residue-field statement to the
chosen fraction fields. -/
private theorem fraction_field_transport_of_zeroPrime_residueField_isAlgebraic
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Rsh : Type*} [CommRing Rsh] [IsDomain Rsh] [IsDiscreteValuationRing Rsh]
    [Algebra R Rsh] [IsExtensionOfDiscreteValuationRings R Rsh]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ksh : Type*} [Field Ksh] [Algebra Rsh Ksh] [IsFractionRing Rsh Ksh]
    [Algebra K Ksh] [Algebra R Ksh] [IsScalarTower R K Ksh]
    (hzero : Algebra.IsAlgebraic ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField)) :
    Algebra.IsAlgebraic K Ksh := by
  let eFrac : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let eZero : FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing R
  let eBase : K ≃ₐ[R] ((⊥ : Ideal R).ResidueField) := eFrac.symm.trans eZero
  let eFracSh : FractionRing Rsh ≃ₐ[Rsh] Ksh := FractionRing.algEquiv Rsh Ksh
  let eZeroSh : FractionRing Rsh ≃ₐ[Rsh] ((⊥ : Ideal Rsh).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing Rsh
  let eTop : Ksh ≃ₐ[Rsh] ((⊥ : Ideal Rsh).ResidueField) := eFracSh.symm.trans eZeroSh
  letI : Algebra K ((⊥ : Ideal R).ResidueField) := eBase.toRingHom.toAlgebra
  letI : Algebra K ((⊥ : Ideal Rsh).ResidueField) :=
    ((algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField)).comp
      (algebraMap K ((⊥ : Ideal R).ResidueField))).toAlgebra
  letI : IsScalarTower K ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hbase_alg : Algebra.IsAlgebraic K ((⊥ : Ideal R).ResidueField) := by
    -- The chosen fraction field `K` is equivalent to the zero-prime residue field of `R`.
    rw [Algebra.isAlgebraic_iff_isIntegral]
    intro x
    refine ⟨Polynomial.X - Polynomial.C (eBase.symm x), ?_, ?_⟩
    · simpa using Polynomial.monic_X_sub_C (eBase.symm x)
    · simp [eBase]
  have hcomm (x : K) :
      eTop (algebraMap K Ksh x) =
        algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) (eBase x) := by
    have hfrac :
        algebraMap K Ksh x =
          eFracSh (algebraMap (FractionRing R) (FractionRing Rsh) (eFrac.symm x)) := by
      -- First compare the chosen fraction fields with the canonical fraction-ring models.
      simpa [eFrac] using
        IsFractionRing.algEquiv_commutes eFrac eFracSh (eFrac.symm x)
    have hzero_comm :
        algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) (eBase x) =
          eZeroSh (algebraMap (FractionRing R) (FractionRing Rsh) (eFrac.symm x)) := by
      -- Then transport the same element through the zero-prime residue-field identifications.
      simpa [eBase, eZero] using
        IsFractionRing.algEquiv_commutes eZero eZeroSh (eFrac.symm x)
    calc
      eTop (algebraMap K Ksh x)
          = eZeroSh (algebraMap (FractionRing R) (FractionRing Rsh) (eFrac.symm x)) := by
              rw [hfrac]
              simp [eTop]
      _ =
        algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) (eBase x) := by
          simpa using hzero_comm.symm
  let _ : Algebra.IsAlgebraic K ((⊥ : Ideal R).ResidueField) := hbase_alg
  let _ : Algebra.IsAlgebraic ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) :=
    hzero
  let _ : Algebra.IsAlgebraic K ((⊥ : Ideal Rsh).ResidueField) :=
    Algebra.IsAlgebraic.trans K ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField)
  let eTopK : Ksh →ₐ[K] ((⊥ : Ideal Rsh).ResidueField) where
    toRingHom := eTop.toRingHom
    commutes' := hcomm
  -- The zero-prime residue-field model is algebraic over `K`, and `eTop` is injective.
  exact Algebra.IsAlgebraic.of_injective eTopK eTop.injective

/-- Helper for Lemma 15.116.5: the separability half of the zero-prime residue-field transport
to the chosen fraction fields is a pure equivalence argument. -/
private theorem fraction_field_transport_of_zeroPrime_residueField_isSeparable
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Rsh : Type*} [CommRing Rsh] [IsDomain Rsh] [IsDiscreteValuationRing Rsh]
    [Algebra R Rsh] [IsExtensionOfDiscreteValuationRings R Rsh]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ksh : Type*} [Field Ksh] [Algebra Rsh Ksh] [IsFractionRing Rsh Ksh]
    [Algebra K Ksh] [Algebra R Ksh] [IsScalarTower R K Ksh]
    (hzero : Algebra.IsSeparable ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField)) :
    Algebra.IsSeparable K Ksh := by
  let eFrac : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let eZero : FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing R
  let eBase : K ≃ₐ[R] ((⊥ : Ideal R).ResidueField) := eFrac.symm.trans eZero
  let eFracSh : FractionRing Rsh ≃ₐ[Rsh] Ksh := FractionRing.algEquiv Rsh Ksh
  let eZeroSh : FractionRing Rsh ≃ₐ[Rsh] ((⊥ : Ideal Rsh).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing Rsh
  let eTop : Ksh ≃ₐ[Rsh] ((⊥ : Ideal Rsh).ResidueField) := eFracSh.symm.trans eZeroSh
  letI : Algebra K ((⊥ : Ideal R).ResidueField) := eBase.toRingHom.toAlgebra
  letI : Algebra K ((⊥ : Ideal Rsh).ResidueField) :=
    ((algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField)).comp
      (algebraMap K ((⊥ : Ideal R).ResidueField))).toAlgebra
  letI : IsScalarTower K ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eBaseK : K ≃ₐ[K] ((⊥ : Ideal R).ResidueField) where
    toRingEquiv := eBase.toRingEquiv
    commutes' x := rfl
  have hcomm (x : K) :
      eTop (algebraMap K Ksh x) =
        algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) (eBase x) := by
    have hfrac :
        algebraMap K Ksh x =
          eFracSh (algebraMap (FractionRing R) (FractionRing Rsh) (eFrac.symm x)) := by
      -- Compare the chosen fraction fields with the canonical fraction rings on the generic fiber.
      simpa [eFrac] using
        IsFractionRing.algEquiv_commutes eFrac eFracSh (eFrac.symm x)
    have hzero_comm :
        algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) (eBase x) =
          eZeroSh (algebraMap (FractionRing R) (FractionRing Rsh) (eFrac.symm x)) := by
      -- The zero-prime residue-field equivalences satisfy the same compatibility.
      simpa [eBase, eZero] using
        IsFractionRing.algEquiv_commutes eZero eZeroSh (eFrac.symm x)
    calc
      eTop (algebraMap K Ksh x)
          = eZeroSh (algebraMap (FractionRing R) (FractionRing Rsh) (eFrac.symm x)) := by
              rw [hfrac]
              simp [eTop]
      _ =
        algebraMap ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) (eBase x) := by
          simpa using hzero_comm.symm
  let eTopK : Ksh ≃ₐ[K] ((⊥ : Ideal Rsh).ResidueField) where
    toRingEquiv := eTop.toRingEquiv
    commutes' := hcomm
  let _ : Algebra.IsSeparable K ((⊥ : Ideal R).ResidueField) :=
    AlgEquiv.Algebra.isSeparable eBaseK
  let _ : Algebra.IsSeparable ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) :=
    hzero
  let _ : Algebra.IsSeparable K ((⊥ : Ideal Rsh).ResidueField) :=
    Algebra.IsSeparable.trans K ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField)
  -- After rewriting both source and target by the canonical fraction-ring models, separability
  -- is preserved by the resulting `K`-algebra equivalence.
  exact AlgEquiv.Algebra.isSeparable eTopK.symm

/-- Helper for Lemma 15.116.5: combine the algebraic and separable generic-fiber transports after
the transport-heavy residue-field/fraction-field identifications have been separated. -/
private theorem fraction_field_transport_of_zeroPrime_residueField_isAlgebraic_and_separable
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Rsh : Type*} [CommRing Rsh] [IsDomain Rsh] [IsDiscreteValuationRing Rsh]
    [Algebra R Rsh] [IsExtensionOfDiscreteValuationRings R Rsh]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ksh : Type*} [Field Ksh] [Algebra Rsh Ksh] [IsFractionRing Rsh Ksh]
    [Algebra K Ksh] [Algebra R Ksh] [IsScalarTower R K Ksh]
    (hzero :
      Algebra.IsAlgebraic ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField) ∧
        Algebra.IsSeparable ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal Rsh).ResidueField)) :
    Algebra.IsAlgebraic K Ksh ∧
      Algebra.IsSeparable K Ksh := by
  -- Route correction: the mixed transport was too opaque, so split the algebraic and separable
  -- parts and recombine them after the fraction-ring identifications are in place.
  exact
    ⟨fraction_field_transport_of_zeroPrime_residueField_isAlgebraic
        (R := R) (Rsh := Rsh) (K := K) (Ksh := Ksh) hzero.1,
      fraction_field_transport_of_zeroPrime_residueField_isSeparable
        (R := R) (Rsh := Rsh) (K := K) (Ksh := Ksh) hzero.2⟩

/-- Helper for Lemma 15.116.5: chosen strict henselizations of an extension of discrete valuation
rings admit a compatible map between the canonical separable closures of their residue fields. -/
private theorem separableClosure_lift_of_residueField_map
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S] :
    ∃ φ : SeparableClosure (ResidueField R) →+* SeparableClosure (ResidueField S),
      φ.comp (algebraMap (ResidueField R) (SeparableClosure (ResidueField R))) =
        (algebraMap (ResidueField S) (SeparableClosure (ResidueField S))).comp
          (ResidueField.map (algebraMap R S)) := by
  -- Route correction: the source proof first compares the residue fields through canonical
  -- separable closures, and only then feeds that map into the strict-henselization comparison.
  letI : Algebra (ResidueField R) (SeparableClosure (ResidueField S)) :=
    ((algebraMap (ResidueField S) (SeparableClosure (ResidueField S))).comp
      (ResidueField.map (algebraMap R S))).toAlgebra
  let φ : SeparableClosure (ResidueField R) →ₐ[ResidueField R]
      SeparableClosure (ResidueField S) :=
    IsSepClosed.lift (SeparableClosure (ResidueField R))
  refine ⟨φ.toRingHom, ?_⟩
  -- The chosen lift is an algebra map over `ResidueField R`, so it commutes with the base map.
  ext x
  exact φ.commutes x

/-- Helper for Lemma 15.116.5: chosen strict henselizations of an extension of discrete valuation
rings admit a compatible comparison map, and that comparison is again an extension of discrete
valuation rings. -/
private theorem strict_henselization_comparison_extension
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    {Rsh : Type*} [CommRing Rsh] [IsDomain Rsh] [IsDiscreteValuationRing Rsh]
    [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [IsExtensionOfDiscreteValuationRings R Rsh]
    {Ssh : Type*} [CommRing Ssh] [IsDomain Ssh] [IsDiscreteValuationRing Ssh]
    [Algebra S Ssh] [IsStrictHenselizationOf S Ssh]
    [IsExtensionOfDiscreteValuationRings S Ssh] :
    ∃ (_ : Algebra Rsh Ssh) (_ : Algebra R Ssh) (_ : IsScalarTower R Rsh Ssh)
      (_ : IsScalarTower R S Ssh) (_ : IsExtensionOfDiscreteValuationRings Rsh Ssh),
      True := by
  -- Route correction: stop constructing a direct map `ResidueField Rsh → ResidueField Ssh`.
  -- Instead, identify both residue fields with canonical separable closures and compare those.
  letI : Algebra R Ssh := ((algebraMap S Ssh).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S Ssh := IsScalarTower.of_algebraMap_eq' rfl
  let KsepR := SeparableClosure (ResidueField R)
  let KsepS := SeparableClosure (ResidueField S)
  let _ : Field KsepR := inferInstance
  let _ : Algebra (ResidueField R) KsepR := inferInstance
  let _ : IsSepClosure (ResidueField R) KsepR := inferInstance
  let _ : Field KsepS := inferInstance
  let _ : Algebra (ResidueField S) KsepS := inferInstance
  let _ : IsSepClosure (ResidueField S) KsepS := inferInstance
  let ιR : ResidueField Rsh ≃+* KsepR :=
    (IsSepClosure.equiv (ResidueField R) (ResidueField Rsh) KsepR).toRingEquiv
  let ιS : ResidueField Ssh ≃+* KsepS :=
    (IsSepClosure.equiv (ResidueField S) (ResidueField Ssh) KsepS).toRingEquiv
  have hιR :
      ιR.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) KsepR := by
    -- The chosen identification of `ResidueField Rsh` with the canonical separable closure is
    -- compatible with the residue-field map from `R`.
    ext x
    exact (IsSepClosure.equiv (ResidueField R) (ResidueField Rsh) KsepR).commutes x
  have hιS :
      ιS.toRingHom.comp (ResidueField.map (algebraMap S Ssh)) =
        algebraMap (ResidueField S) KsepS := by
    -- The same compatibility holds on the `S`-side strict henselization.
    ext x
    exact (IsSepClosure.equiv (ResidueField S) (ResidueField Ssh) KsepS).commutes x
  obtain ⟨φ, hφ⟩ := separableClosure_lift_of_residueField_map (R := R) (S := S)
  rcases
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (R := R) (S := S) (Rsh := Rsh) (Ssh := Ssh)
        ιR hιR ιS hιS φ hφ with
    ⟨f, hf, _⟩
  letI : Algebra Rsh Ssh := f.toRingHom.toAlgebra
  letI : IsScalarTower R Rsh Ssh :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  have hf_injective : Function.Injective (f : Rsh →+* Ssh) := by
    letI : IsExtensionOfDiscreteValuationRings R Ssh :=
      IsExtensionOfDiscreteValuationRings.of_tower R S Ssh
    have hbase_injective : Function.Injective (algebraMap R Ssh) :=
      (inferInstance : IsExtensionOfDiscreteValuationRings R Ssh).algebraMap_injective
    rw [RingHom.injective_iff_ker_eq_bot]
    refine le_antisymm ?_ bot_le
    intro x hx
    by_contra hx0
    obtain ⟨π, hπirr, hπmax⟩ := exists_uniformizer_generator Rsh
    obtain ⟨n, hxassoc⟩ :=
      associated_uniformizer_pow_of_nonzero (R := Rsh) π x hπmax hx0
    have hx_nonunit : ¬ IsUnit x := by
      intro hx_unit
      have hx_image_unit : IsUnit (f x) := hx_unit.map (f : Rsh →+* Ssh)
      simpa [RingHom.mem_ker.mp hx] using hx_image_unit
    have hn_ne_zero : n ≠ 0 := by
      intro hn
      subst hn
      have hx_unit : IsUnit x := by
        rcases hxassoc with ⟨u, hu⟩
        -- If `x` were associated to `1`, then `x` itself would be a unit.
        exact isUnit_of_mul_isUnit_left <| by
          rw [hu, pow_zero]
          exact isUnit_one
      exact hx_nonunit hx_unit
    have hpow_zero : f (π ^ n) = 0 := by
      rcases hxassoc with ⟨u, hu⟩
      -- Apply `f` to the associated-power relation coming from the DVR structure.
      calc
        f (π ^ n) = f (x * ↑u) := by rw [← hu]
        _ = f x * f ↑u := by simp
        _ = 0 := by simp [RingHom.mem_ker.mp hx]
    have hπ_zero : f π = 0 := by
      -- In the domain `Ssh`, a vanishing positive power forces the element itself to vanish.
      apply eq_zero_of_pow_eq_zero
      simpa [map_pow] using hpow_zero
    have hmaximal_le_ker : maximalIdeal Rsh ≤ RingHom.ker (f : Rsh →+* Ssh) := by
      rw [hπmax]
      refine Ideal.span_le.2 ?_
      intro y hy
      rcases hy with rfl
      simpa using RingHom.mem_ker.mpr hπ_zero
    obtain ⟨ρ, hρirr, hρmax⟩ := exists_uniformizer_generator R
    have hρ_mem_max : ρ ∈ maximalIdeal R := by
      rw [hρmax]
      exact Ideal.subset_span (by simp)
    have hρ_nonunit : ¬ IsUnit ρ := by
      rw [← IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hρ_mem_max
    have hρ_mem_max_sh : algebraMap R Rsh ρ ∈ maximalIdeal Rsh := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact IsLocalHom.map_nonunit ρ hρ_nonunit
    have hρ_mem_ker : algebraMap R Rsh ρ ∈ RingHom.ker (f : Rsh →+* Ssh) :=
      hmaximal_le_ker hρ_mem_max_sh
    have hρ_zero_sh : f (algebraMap R Rsh ρ) = 0 := RingHom.mem_ker.mp hρ_mem_ker
    have hρ_zero : algebraMap R Ssh ρ = 0 := by
      simpa using (f.commutes ρ).symm.trans hρ_zero_sh
    exact (map_ne_zero hbase_injective hρirr.ne_zero) hρ_zero
  exact
    ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      { toIsLocalHom := hf.1
        algebraMap_injective := hf_injective },
      trivial⟩

/-- Helper for Lemma 15.116.5: a witness field over `Ash` and `Ksh` already carries the induced
`A0`- and `K0`-algebra structures coming from the ambient strict-henselization tower. -/
private theorem strict_henselization_witness_base_structures
    {A0 : Type*} [CommRing A0]
    {K0 : Type*} [Field K0] [Algebra A0 K0]
    {Ash : Type*} [CommRing Ash] [Algebra A0 Ash]
    {Ksh : Type*} [Field Ksh] [Algebra Ash Ksh] [Algebra K0 Ksh] [Algebra A0 Ksh]
    [IsScalarTower A0 Ash Ksh] [IsScalarTower A0 K0 Ksh]
    {K1prime : Type*} [Field K1prime] [Algebra Ash K1prime] [Algebra Ksh K1prime]
    [IsScalarTower Ash Ksh K1prime] :
    ∃ (_ : Algebra A0 K1prime) (_ : Algebra K0 K1prime)
      (_ : IsScalarTower A0 K0 K1prime) (_ : IsScalarTower A0 Ash K1prime),
      True := by
  letI : Algebra A0 K1prime := ((algebraMap Ash K1prime).comp (algebraMap A0 Ash)).toAlgebra
  letI : Algebra K0 K1prime := ((algebraMap Ksh K1prime).comp (algebraMap K0 Ksh)).toAlgebra
  letI : IsScalarTower A0 Ash K1prime := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A0 K0 K1prime := by
    -- Both routes from `A0` to `K1prime` factor through the common map `A0 → Ksh`.
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change algebraMap Ksh K1prime (algebraMap K0 Ksh (algebraMap A0 K0 x)) =
      algebraMap Ash K1prime (algebraMap A0 Ash x)
    rw [IsScalarTower.algebraMap_eq A0 K0 Ksh, IsScalarTower.algebraMap_eq A0 Ash Ksh]
    rfl
  -- The induced structures are exactly the composed algebra maps through the strict henselization.
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩

/-- Helper for Lemma 15.116.5: a formally smooth extension of discrete valuation rings is already
a solution after any finite extension of the source fraction field. -/
private theorem isSolutionFor_of_formally_smooth_for_adic
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    {K1 : Type*} [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
    [FiniteDimensional K K1]
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    IsSolutionFor A B K L K1 := by
  intro p hp q hq hq_over
  let _ : p.IsMaximal := hp
  let _ : q.IsMaximal := hq
  let _ : q.LiesOver p := hq_over
  -- The source proof packages every branch after finite base change inside the Chapter 15
  -- base-change theorem for formal smoothness.
  exact
    formallySmoothForAdic_localization_baseChange_integralClosure
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) hfs p q

/-- Helper for Lemma 15.116.5: the weak-solution branch now has a single remaining blocker,
namely the source-faithful descent of the finite witness field from `Ash` to one localized étale
stage under `A0`, after which Lemma `15.116.4 (3)` applies to `A0 → A_stage → Bsh`. -/
private theorem strict_henselization_weak_solution_descent_to_right_strict_henselization
    {A0 : Type*} [CommRing A0] [IsDomain A0] [IsDiscreteValuationRing A0]
    {B0 : Type*} [CommRing B0] [IsDomain B0] [IsDiscreteValuationRing B0]
    [Algebra A0 B0] [IsExtensionOfDiscreteValuationRings A0 B0]
    {K0 : Type*} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0]
    {L0 : Type*} [Field L0] [Algebra A0 L0] [Algebra B0 L0] [Algebra K0 L0]
    [IsFractionRing B0 L0] [IsScalarTower A0 B0 L0] [IsScalarTower A0 K0 L0]
    {Ash : Type*} [CommRing Ash] [IsDomain Ash] [IsDiscreteValuationRing Ash]
    [Algebra A0 Ash] [IsExtensionOfDiscreteValuationRings A0 Ash]
    {Bsh : Type*} [CommRing Bsh] [IsDomain Bsh] [IsDiscreteValuationRing Bsh]
    [Algebra B0 Bsh] [Algebra Ash Bsh] [Algebra A0 Bsh]
    [IsScalarTower A0 Ash Bsh] [IsScalarTower A0 B0 Bsh]
    [IsExtensionOfDiscreteValuationRings B0 Bsh]
    [IsExtensionOfDiscreteValuationRings Ash Bsh]
    {Ksh : Type*} [Field Ksh] [Algebra Ash Ksh] [IsFractionRing Ash Ksh]
    [Algebra K0 Ksh] [Algebra A0 Ksh] [IsScalarTower A0 Ash Ksh] [IsScalarTower A0 K0 Ksh]
    {Lsh : Type*} [Field Lsh] [Algebra A0 Lsh] [Algebra Bsh Lsh] [Algebra K0 Lsh]
    [IsFractionRing Bsh Lsh] [IsScalarTower A0 Bsh Lsh] [IsScalarTower A0 K0 Lsh]
    [Algebra Ksh Lsh] [Algebra Ash Lsh] [IsScalarTower Ash Bsh Lsh] [IsScalarTower Ash Ksh Lsh]
    [IsExtensionOfDiscreteValuationRings A0 Bsh] :
    ((∃ (K1prime : Type*) (_ : Field K1prime) (_ : Algebra Ash K1prime)
        (_ : Algebra Ksh K1prime) (_ : IsScalarTower Ash Ksh K1prime)
        (_ : FiniteDimensional Ksh K1prime),
        IsWeakSolutionFor Ash Bsh Ksh Lsh K1prime) →
      ∃ (K1 : Type*) (_ : Field K1) (_ : Algebra A0 K1) (_ : Algebra K0 K1)
        (_ : IsScalarTower A0 K0 K1) (_ : FiniteDimensional K0 K1),
        IsWeakSolutionFor A0 Bsh K0 Lsh K1) := by
  intro hprime
  rcases hprime with ⟨K1prime, hField, hAshK1prime, hKshK1prime, hTowerKsh, hFiniteKsh, hWeak⟩
  letI : Field K1prime := hField
  letI : Algebra Ash K1prime := hAshK1prime
  letI : Algebra Ksh K1prime := hKshK1prime
  letI : IsScalarTower Ash Ksh K1prime := hTowerKsh
  letI : FiniteDimensional Ksh K1prime := hFiniteKsh
  obtain ⟨hA0K1prime, hK0K1prime, hTowerK0, hTowerA0, _⟩ :=
    strict_henselization_witness_base_structures
      (A0 := A0) (K0 := K0) (Ash := Ash) (Ksh := Ksh) (K1prime := K1prime)
  letI : Algebra A0 K1prime := hA0K1prime
  letI : Algebra K0 K1prime := hK0K1prime
  letI : IsScalarTower A0 K0 K1prime := hTowerK0
  letI : IsScalarTower A0 Ash K1prime := hTowerA0
  let _ := hWeak
  -- Route correction: the old monolithic proof obscured where the source argument actually stops.
  -- TODO: descend the finite integral-closure model from `Ash` to a localized étale stage,
  -- transfer the strict-henselian branch data to the factor fields of that stage, and conclude via
  -- `weakSolutionFor_comp_of_weakSolutionFor_of_reducedTensorProductFactors`.
  sorry

/-- Helper for Lemma 15.116.5: the honest-solution branch has the same finite-stage descent
frontier as the weak branch, but finishes with the formal-smoothness composition theorem
`Lemma 15.116.4 (4)`. -/
private theorem strict_henselization_solution_descent_to_right_strict_henselization
    {A0 : Type*} [CommRing A0] [IsDomain A0] [IsDiscreteValuationRing A0]
    {B0 : Type*} [CommRing B0] [IsDomain B0] [IsDiscreteValuationRing B0]
    [Algebra A0 B0] [IsExtensionOfDiscreteValuationRings A0 B0]
    {K0 : Type*} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0]
    {L0 : Type*} [Field L0] [Algebra A0 L0] [Algebra B0 L0] [Algebra K0 L0]
    [IsFractionRing B0 L0] [IsScalarTower A0 B0 L0] [IsScalarTower A0 K0 L0]
    {Ash : Type*} [CommRing Ash] [IsDomain Ash] [IsDiscreteValuationRing Ash]
    [Algebra A0 Ash] [IsExtensionOfDiscreteValuationRings A0 Ash]
    {Bsh : Type*} [CommRing Bsh] [IsDomain Bsh] [IsDiscreteValuationRing Bsh]
    [Algebra B0 Bsh] [Algebra Ash Bsh] [Algebra A0 Bsh]
    [IsScalarTower A0 Ash Bsh] [IsScalarTower A0 B0 Bsh]
    [IsExtensionOfDiscreteValuationRings B0 Bsh]
    [IsExtensionOfDiscreteValuationRings Ash Bsh]
    {Ksh : Type*} [Field Ksh] [Algebra Ash Ksh] [IsFractionRing Ash Ksh]
    [Algebra K0 Ksh] [Algebra A0 Ksh] [IsScalarTower A0 Ash Ksh] [IsScalarTower A0 K0 Ksh]
    {Lsh : Type*} [Field Lsh] [Algebra A0 Lsh] [Algebra Bsh Lsh] [Algebra K0 Lsh]
    [IsFractionRing Bsh Lsh] [IsScalarTower A0 Bsh Lsh] [IsScalarTower A0 K0 Lsh]
    [Algebra Ksh Lsh] [Algebra Ash Lsh] [IsScalarTower Ash Bsh Lsh] [IsScalarTower Ash Ksh Lsh]
    [IsExtensionOfDiscreteValuationRings A0 Bsh] :
    ((∃ (K1prime : Type*) (_ : Field K1prime) (_ : Algebra Ash K1prime)
        (_ : Algebra Ksh K1prime) (_ : IsScalarTower Ash Ksh K1prime)
        (_ : FiniteDimensional Ksh K1prime),
        IsSolutionFor Ash Bsh Ksh Lsh K1prime) →
      ∃ (K1 : Type*) (_ : Field K1) (_ : Algebra A0 K1) (_ : Algebra K0 K1)
        (_ : IsScalarTower A0 K0 K1) (_ : FiniteDimensional K0 K1),
        IsSolutionFor A0 Bsh K0 Lsh K1) := by
  intro hprime
  rcases hprime with ⟨K1prime, hField, hAshK1prime, hKshK1prime, hTowerKsh, hFiniteKsh, hSol⟩
  letI : Field K1prime := hField
  letI : Algebra Ash K1prime := hAshK1prime
  letI : Algebra Ksh K1prime := hKshK1prime
  letI : IsScalarTower Ash Ksh K1prime := hTowerKsh
  letI : FiniteDimensional Ksh K1prime := hFiniteKsh
  obtain ⟨hA0K1prime, hK0K1prime, hTowerK0, hTowerA0, _⟩ :=
    strict_henselization_witness_base_structures
      (A0 := A0) (K0 := K0) (Ash := Ash) (Ksh := Ksh) (K1prime := K1prime)
  letI : Algebra A0 K1prime := hA0K1prime
  letI : Algebra K0 K1prime := hK0K1prime
  letI : IsScalarTower A0 K0 K1prime := hTowerK0
  letI : IsScalarTower A0 Ash K1prime := hTowerA0
  let _ := hSol
  -- TODO: run the same localized étale stage descent as in the weak branch, then close with
  -- `solutionFor_comp_of_solutionFor_of_reducedTensorProductFactors`.
  sorry

/-- Helper for Lemma 15.116.5: the separable-solution branch reduces to the solution descent plus
the extra task of preserving separability along the descended finite étale generic fiber. -/
private theorem strict_henselization_separable_solution_descent_to_right_strict_henselization
    {A0 : Type*} [CommRing A0] [IsDomain A0] [IsDiscreteValuationRing A0]
    {B0 : Type*} [CommRing B0] [IsDomain B0] [IsDiscreteValuationRing B0]
    [Algebra A0 B0] [IsExtensionOfDiscreteValuationRings A0 B0]
    {K0 : Type*} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0]
    {L0 : Type*} [Field L0] [Algebra A0 L0] [Algebra B0 L0] [Algebra K0 L0]
    [IsFractionRing B0 L0] [IsScalarTower A0 B0 L0] [IsScalarTower A0 K0 L0]
    {Ash : Type*} [CommRing Ash] [IsDomain Ash] [IsDiscreteValuationRing Ash]
    [Algebra A0 Ash] [IsExtensionOfDiscreteValuationRings A0 Ash]
    {Bsh : Type*} [CommRing Bsh] [IsDomain Bsh] [IsDiscreteValuationRing Bsh]
    [Algebra B0 Bsh] [Algebra Ash Bsh] [Algebra A0 Bsh]
    [IsScalarTower A0 Ash Bsh] [IsScalarTower A0 B0 Bsh]
    [IsExtensionOfDiscreteValuationRings B0 Bsh]
    [IsExtensionOfDiscreteValuationRings Ash Bsh]
    {Ksh : Type*} [Field Ksh] [Algebra Ash Ksh] [IsFractionRing Ash Ksh]
    [Algebra K0 Ksh] [Algebra A0 Ksh] [IsScalarTower A0 Ash Ksh] [IsScalarTower A0 K0 Ksh]
    {Lsh : Type*} [Field Lsh] [Algebra A0 Lsh] [Algebra Bsh Lsh] [Algebra K0 Lsh]
    [IsFractionRing Bsh Lsh] [IsScalarTower A0 Bsh Lsh] [IsScalarTower A0 K0 Lsh]
    [Algebra Ksh Lsh] [Algebra Ash Lsh] [IsScalarTower Ash Bsh Lsh] [IsScalarTower Ash Ksh Lsh]
    [IsExtensionOfDiscreteValuationRings A0 Bsh] :
    ((∃ (K1prime : Type*) (_ : Field K1prime) (_ : Algebra Ash K1prime)
        (_ : Algebra Ksh K1prime) (_ : IsScalarTower Ash Ksh K1prime)
        (_ : FiniteDimensional Ksh K1prime),
        IsSeparableSolutionFor Ash Bsh Ksh Lsh K1prime) →
      ∃ (K1 : Type*) (_ : Field K1) (_ : Algebra A0 K1) (_ : Algebra K0 K1)
        (_ : IsScalarTower A0 K0 K1) (_ : FiniteDimensional K0 K1),
        IsSeparableSolutionFor A0 Bsh K0 Lsh K1) := by
  intro hprime
  rcases hprime with
    ⟨K1prime, hField, hAshK1prime, hKshK1prime, hTowerKsh, hFiniteKsh, hSep⟩
  letI : Field K1prime := hField
  letI : Algebra Ash K1prime := hAshK1prime
  letI : Algebra Ksh K1prime := hKshK1prime
  letI : IsScalarTower Ash Ksh K1prime := hTowerKsh
  letI : FiniteDimensional Ksh K1prime := hFiniteKsh
  obtain ⟨hA0K1prime, hK0K1prime, hTowerK0, hTowerA0, _⟩ :=
    strict_henselization_witness_base_structures
      (A0 := A0) (K0 := K0) (Ash := Ash) (Ksh := Ksh) (K1prime := K1prime)
  letI : Algebra A0 K1prime := hA0K1prime
  letI : Algebra K0 K1prime := hK0K1prime
  letI : IsScalarTower A0 K0 K1prime := hTowerK0
  letI : IsScalarTower A0 Ash K1prime := hTowerA0
  let _ := hSep
  -- TODO: combine the solution descent above with the separability transport from the descended
  -- stage field `F` to `K0 → K1` furnished by the finite étale generic fiber.
  sorry

/-- Helper for Lemma 15.116.5: once a weak solution witness has been descended to the right-hand
extension `A0 → Bsh`, Lemma `15.116.4 (1)` carries it back to `A0 → B0`. -/
private theorem weak_solution_descends_along_right_extension
    {A0 : Type*} [CommRing A0] [IsDomain A0] [IsDiscreteValuationRing A0]
    {B0 : Type*} [CommRing B0] [IsDomain B0] [IsDiscreteValuationRing B0]
    [Algebra A0 B0] [IsExtensionOfDiscreteValuationRings A0 B0]
    {K0 : Type*} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0]
    {L0 : Type*} [Field L0] [Algebra A0 L0] [Algebra B0 L0] [Algebra K0 L0]
    [IsFractionRing B0 L0] [IsScalarTower A0 B0 L0] [IsScalarTower A0 K0 L0]
    {Bsh : Type*} [CommRing Bsh] [IsDomain Bsh] [IsDiscreteValuationRing Bsh]
    [Algebra B0 Bsh] [Algebra A0 Bsh] [IsScalarTower A0 B0 Bsh]
    [IsExtensionOfDiscreteValuationRings B0 Bsh]
    [IsExtensionOfDiscreteValuationRings A0 Bsh]
    {Lsh : Type*} [Field Lsh] [Algebra A0 Lsh] [Algebra B0 Lsh] [Algebra Bsh Lsh]
    [Algebra L0 Lsh] [Algebra K0 Lsh] [IsFractionRing Bsh Lsh]
    [IsScalarTower A0 Bsh Lsh] [IsScalarTower A0 K0 Lsh]
    [IsScalarTower B0 Bsh Lsh] [IsScalarTower B0 L0 Lsh]
    {K1 : Type*} [Field K1] [Algebra A0 K1] [Algebra K0 K1] [IsScalarTower A0 K0 K1]
    [FiniteDimensional K0 K1]
    (hWeak : IsWeakSolutionFor A0 Bsh K0 Lsh K1) :
    IsWeakSolutionFor A0 B0 K0 L0 K1 := by
  -- Apply the chapter weak-solution descent theorem to the right-hand tower `B0 → Bsh`.
  exact
    weakSolutionFor_of_weakSolutionFor_comp
      (A := A0) (B := B0) (C := Bsh) (K := K0) (L := L0) (M := Lsh) hWeak

/-- Helper for Lemma 15.116.5: once a solution witness has been descended to the right-hand
extension `A0 → Bsh`, Lemma `15.116.4 (2)` carries it back to `A0 → B0`. -/
private theorem solution_descends_along_right_extension
    {A0 : Type*} [CommRing A0] [IsDomain A0] [IsDiscreteValuationRing A0]
    {B0 : Type*} [CommRing B0] [IsDomain B0] [IsDiscreteValuationRing B0]
    [Algebra A0 B0] [IsExtensionOfDiscreteValuationRings A0 B0]
    {K0 : Type*} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0]
    {L0 : Type*} [Field L0] [Algebra A0 L0] [Algebra B0 L0] [Algebra K0 L0]
    [IsFractionRing B0 L0] [IsScalarTower A0 B0 L0] [IsScalarTower A0 K0 L0]
    {Bsh : Type*} [CommRing Bsh] [IsDomain Bsh] [IsDiscreteValuationRing Bsh]
    [Algebra B0 Bsh] [Algebra A0 Bsh] [IsScalarTower A0 B0 Bsh]
    [IsExtensionOfDiscreteValuationRings B0 Bsh]
    [IsExtensionOfDiscreteValuationRings A0 Bsh]
    {Lsh : Type*} [Field Lsh] [Algebra A0 Lsh] [Algebra B0 Lsh] [Algebra Bsh Lsh]
    [Algebra L0 Lsh] [Algebra K0 Lsh] [IsFractionRing Bsh Lsh]
    [IsScalarTower A0 Bsh Lsh] [IsScalarTower A0 K0 Lsh]
    [IsScalarTower B0 Bsh Lsh] [IsScalarTower B0 L0 Lsh]
    {K1 : Type*} [Field K1] [Algebra A0 K1] [Algebra K0 K1] [IsScalarTower A0 K0 K1]
    [FiniteDimensional K0 K1]
    (hSol : IsSolutionFor A0 Bsh K0 Lsh K1) :
    IsSolutionFor A0 B0 K0 L0 K1 := by
  -- The same tower descent works for honest solutions.
  exact
    solutionFor_of_solutionFor_comp
      (A := A0) (B := B0) (C := Bsh) (K := K0) (L := L0) (M := Lsh) hSol

/-- Helper for Lemma 15.116.5: separability is unchanged when the solution part descends along the
right-hand extension `B0 → Bsh`. -/
private theorem separable_solution_descends_along_right_extension
    {A0 : Type*} [CommRing A0] [IsDomain A0] [IsDiscreteValuationRing A0]
    {B0 : Type*} [CommRing B0] [IsDomain B0] [IsDiscreteValuationRing B0]
    [Algebra A0 B0] [IsExtensionOfDiscreteValuationRings A0 B0]
    {K0 : Type*} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0]
    {L0 : Type*} [Field L0] [Algebra A0 L0] [Algebra B0 L0] [Algebra K0 L0]
    [IsFractionRing B0 L0] [IsScalarTower A0 B0 L0] [IsScalarTower A0 K0 L0]
    {Bsh : Type*} [CommRing Bsh] [IsDomain Bsh] [IsDiscreteValuationRing Bsh]
    [Algebra B0 Bsh] [Algebra A0 Bsh] [IsScalarTower A0 B0 Bsh]
    [IsExtensionOfDiscreteValuationRings B0 Bsh]
    [IsExtensionOfDiscreteValuationRings A0 Bsh]
    {Lsh : Type*} [Field Lsh] [Algebra A0 Lsh] [Algebra B0 Lsh] [Algebra Bsh Lsh]
    [Algebra L0 Lsh] [Algebra K0 Lsh] [IsFractionRing Bsh Lsh]
    [IsScalarTower A0 Bsh Lsh] [IsScalarTower A0 K0 Lsh]
    [IsScalarTower B0 Bsh Lsh] [IsScalarTower B0 L0 Lsh]
    {K1 : Type*} [Field K1] [Algebra A0 K1] [Algebra K0 K1] [IsScalarTower A0 K0 K1]
    [FiniteDimensional K0 K1]
    (hSep : IsSeparableSolutionFor A0 Bsh K0 Lsh K1) :
    IsSeparableSolutionFor A0 B0 K0 L0 K1 := by
  -- Only the solution component changes; the separable field-extension datum is preserved.
  exact
    ⟨solution_descends_along_right_extension
        (A0 := A0) (B0 := B0) (Bsh := Bsh) (K0 := K0) (L0 := L0) (Lsh := Lsh) hSep.1,
      hSep.2⟩

/-- Helper for Lemma 15.116.5: any weak solution, solution, or separable solution over the chosen
strict-henselization square descends to the original extension of discrete valuation rings. -/
private theorem strict_henselization_solution_descent
    {A0 : Type*} [CommRing A0] [IsDomain A0] [IsDiscreteValuationRing A0]
    {B0 : Type*} [CommRing B0] [IsDomain B0] [IsDiscreteValuationRing B0]
    [Algebra A0 B0] [IsExtensionOfDiscreteValuationRings A0 B0]
    {K0 : Type*} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0]
    {L0 : Type*} [Field L0] [Algebra A0 L0] [Algebra B0 L0] [Algebra K0 L0]
    [IsFractionRing B0 L0] [IsScalarTower A0 B0 L0] [IsScalarTower A0 K0 L0]
    {Ash : Type*} [CommRing Ash] [IsDomain Ash] [IsDiscreteValuationRing Ash]
    [Algebra A0 Ash] [IsExtensionOfDiscreteValuationRings A0 Ash]
    {Bsh : Type*} [CommRing Bsh] [IsDomain Bsh] [IsDiscreteValuationRing Bsh]
    [Algebra B0 Bsh] [Algebra Ash Bsh] [Algebra A0 Bsh]
    [IsScalarTower A0 Ash Bsh] [IsScalarTower A0 B0 Bsh]
    [IsExtensionOfDiscreteValuationRings B0 Bsh]
    [IsExtensionOfDiscreteValuationRings Ash Bsh]
    {Ksh : Type*} [Field Ksh] [Algebra Ash Ksh] [IsFractionRing Ash Ksh]
    [Algebra K0 Ksh] [Algebra A0 Ksh] [IsScalarTower A0 Ash Ksh] [IsScalarTower A0 K0 Ksh]
    {Lsh : Type*} [Field Lsh] [Algebra Bsh Lsh] [IsFractionRing Bsh Lsh]
    [Algebra L0 Lsh] [Algebra B0 Lsh] [IsScalarTower B0 Bsh Lsh] [IsScalarTower B0 L0 Lsh]
    [Algebra Ksh Lsh] [Algebra Ash Lsh]
    [IsScalarTower Ash Bsh Lsh] [IsScalarTower Ash Ksh Lsh] :
    ((∃ (K1prime : Type*) (_ : Field K1prime) (_ : Algebra Ash K1prime)
        (_ : Algebra Ksh K1prime) (_ : IsScalarTower Ash Ksh K1prime)
        (_ : FiniteDimensional Ksh K1prime),
        IsWeakSolutionFor Ash Bsh Ksh Lsh K1prime) →
      ∃ (K1 : Type*) (_ : Field K1) (_ : Algebra A0 K1) (_ : Algebra K0 K1)
        (_ : IsScalarTower A0 K0 K1) (_ : FiniteDimensional K0 K1),
        IsWeakSolutionFor A0 B0 K0 L0 K1) ∧
    ((∃ (K1prime : Type*) (_ : Field K1prime) (_ : Algebra Ash K1prime)
        (_ : Algebra Ksh K1prime) (_ : IsScalarTower Ash Ksh K1prime)
        (_ : FiniteDimensional Ksh K1prime),
        IsSolutionFor Ash Bsh Ksh Lsh K1prime) →
      ∃ (K1 : Type*) (_ : Field K1) (_ : Algebra A0 K1) (_ : Algebra K0 K1)
        (_ : IsScalarTower A0 K0 K1) (_ : FiniteDimensional K0 K1),
        IsSolutionFor A0 B0 K0 L0 K1) ∧
    ((∃ (K1prime : Type*) (_ : Field K1prime) (_ : Algebra Ash K1prime)
        (_ : Algebra Ksh K1prime) (_ : IsScalarTower Ash Ksh K1prime)
        (_ : FiniteDimensional Ksh K1prime),
        IsSeparableSolutionFor Ash Bsh Ksh Lsh K1prime) →
      ∃ (K1 : Type*) (_ : Field K1) (_ : Algebra A0 K1) (_ : Algebra K0 K1)
        (_ : IsScalarTower A0 K0 K1) (_ : FiniteDimensional K0 K1),
        IsSeparableSolutionFor A0 B0 K0 L0 K1) := by
  letI : Algebra A0 Lsh := ((algebraMap B0 Lsh).comp (algebraMap A0 B0)).toAlgebra
  letI : Algebra K0 Lsh := ((algebraMap L0 Lsh).comp (algebraMap K0 L0)).toAlgebra
  letI : IsScalarTower A0 B0 Lsh := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A0 Bsh Lsh := by
    -- Compare the two routes `A0 → B0 → Lsh` and `A0 → Bsh → Lsh` through the given DVR tower.
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change algebraMap B0 Lsh (algebraMap A0 B0 x) =
      algebraMap Bsh Lsh (algebraMap A0 Bsh x)
    rw [IsScalarTower.algebraMap_eq A0 B0 Bsh]
    simp [IsScalarTower.algebraMap_eq B0 Bsh Lsh]
  letI : IsScalarTower A0 K0 Lsh := by
    -- The same comparison identifies the `A0 → Lsh` map with the route through `K0`.
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change algebraMap B0 Lsh (algebraMap A0 B0 x) =
      algebraMap L0 Lsh (algebraMap K0 L0 (algebraMap A0 K0 x))
    rw [IsScalarTower.algebraMap_eq B0 L0 Lsh, ← IsScalarTower.algebraMap_eq A0 B0 L0]
    rw [IsScalarTower.algebraMap_eq A0 K0 L0]
  letI : IsExtensionOfDiscreteValuationRings A0 Bsh :=
    IsExtensionOfDiscreteValuationRings.of_tower A0 B0 Bsh
  have hWeakToBsh :=
    strict_henselization_weak_solution_descent_to_right_strict_henselization
      (A0 := A0) (B0 := B0) (K0 := K0) (L0 := L0)
      (Ash := Ash) (Bsh := Bsh) (Ksh := Ksh) (Lsh := Lsh)
  have hSolToBsh :=
    strict_henselization_solution_descent_to_right_strict_henselization
      (A0 := A0) (B0 := B0) (K0 := K0) (L0 := L0)
      (Ash := Ash) (Bsh := Bsh) (Ksh := Ksh) (Lsh := Lsh)
  have hSepToBsh :=
    strict_henselization_separable_solution_descent_to_right_strict_henselization
      (A0 := A0) (B0 := B0) (K0 := K0) (L0 := L0)
      (Ash := Ash) (Bsh := Bsh) (Ksh := Ksh) (Lsh := Lsh)
  refine ⟨?_, ?_, ?_⟩
  · intro hprime
    rcases hWeakToBsh hprime with ⟨K1, hField, hA0K1, hK0K1, hTower, hFinite, hWeak⟩
    letI : Field K1 := hField
    letI : Algebra A0 K1 := hA0K1
    letI : Algebra K0 K1 := hK0K1
    letI : IsScalarTower A0 K0 K1 := hTower
    letI : FiniteDimensional K0 K1 := hFinite
    -- Delegate the final right-edge descent to the dedicated helper above.
    exact ⟨K1, hField, hA0K1, hK0K1, hTower, hFinite,
      weak_solution_descends_along_right_extension
        (A0 := A0) (B0 := B0) (Bsh := Bsh) (K0 := K0) (L0 := L0) (Lsh := Lsh) hWeak⟩
  · intro hprime
    rcases hSolToBsh hprime with ⟨K1, hField, hA0K1, hK0K1, hTower, hFinite, hSol⟩
    letI : Field K1 := hField
    letI : Algebra A0 K1 := hA0K1
    letI : Algebra K0 K1 := hK0K1
    letI : IsScalarTower A0 K0 K1 := hTower
    letI : FiniteDimensional K0 K1 := hFinite
    -- The same helper packaging works for honest solutions.
    exact ⟨K1, hField, hA0K1, hK0K1, hTower, hFinite,
      solution_descends_along_right_extension
        (A0 := A0) (B0 := B0) (Bsh := Bsh) (K0 := K0) (L0 := L0) (Lsh := Lsh) hSol⟩
  · intro hprime
    rcases hSepToBsh hprime with ⟨K1, hField, hA0K1, hK0K1, hTower, hFinite, hSep⟩
    letI : Field K1 := hField
    letI : Algebra A0 K1 := hA0K1
    letI : Algebra K0 K1 := hK0K1
    letI : IsScalarTower A0 K0 K1 := hTower
    letI : FiniteDimensional K0 K1 := hFinite
    -- Separability is unchanged, so only the solution component needs the right-edge descent.
    exact ⟨K1, hField, hA0K1, hK0K1, hTower, hFinite,
      separable_solution_descends_along_right_extension
        (A0 := A0) (B0 := B0) (Bsh := Bsh) (K0 := K0) (L0 := L0) (Lsh := Lsh) hSep⟩

-- Proof sketch: choose `A'` as a directed colimit of finite étale local extensions of `A` whose
-- residue field is a separable closure of `ResidueField A`, choose `B'` as a strict henselization
-- of `B`, and use the strict-henselian lifting lemma to produce the commutative square. The
-- fraction-field and residue-field conditions come from the chosen constructions together with the
-- canonical tower compatibilities for the induced comparison maps, while descent of weak
-- solutions, solutions, and separable solutions follows by approximating a solution over
-- `A' → B'` at a finite étale stage and then applying Lemma `15.116.4`.
/-- Lemma 15.116.5: for an extension `A → B` of discrete valuation rings with fraction fields
`K ⊂ L`, there exist extensions of discrete valuation rings `A → A'`, `B → B'`, and
`A' → B'` with compatible induced maps on fraction fields and residue fields such that `K' / K`
and `L' / L` are separable algebraic, the residue fields of `A'` and `B'` are separable closures
of those of `A` and `B`, and the existence of a weak solution, a solution, or a separable
solution for `A' → B'` implies the corresponding existence statement for `A → B`. -/
theorem exists_ramificationEliminationSquare :
    ∃ (Aprime : Type uA) (_ : CommRing Aprime) (_ : IsDomain Aprime)
      (_ : IsDiscreteValuationRing Aprime) (_ : Algebra A Aprime)
      (_ : IsExtensionOfDiscreteValuationRings A Aprime)
      (Bprime : Type vA) (_ : CommRing Bprime) (_ : IsDomain Bprime)
      (_ : IsDiscreteValuationRing Bprime) (_ : Algebra B Bprime) (_ : Algebra Aprime Bprime)
      (_ : Algebra A Bprime) (_ : IsScalarTower A Aprime Bprime) (_ : IsScalarTower A B Bprime)
      (_ : IsExtensionOfDiscreteValuationRings B Bprime)
      (_ : IsExtensionOfDiscreteValuationRings Aprime Bprime)
      (Kprime : Type wA) (_ : Field Kprime) (_ : Algebra Aprime Kprime)
      (_ : IsFractionRing Aprime Kprime) (_ : Algebra K Kprime) (_ : Algebra A Kprime)
      (_ : IsScalarTower A Aprime Kprime) (_ : IsScalarTower A K Kprime)
      (Lprime : Type xA) (_ : Field Lprime) (_ : Algebra Bprime Lprime)
      (_ : IsFractionRing Bprime Lprime) (_ : Algebra L Lprime) (_ : Algebra B Lprime)
      (_ : IsScalarTower B Bprime Lprime) (_ : IsScalarTower B L Lprime)
      (_ : Algebra Kprime Lprime) (_ : Algebra Aprime Lprime)
      (_ : IsScalarTower Aprime Bprime Lprime) (_ : IsScalarTower Aprime Kprime Lprime)
      (_ : Algebra (ResidueField A) (ResidueField Aprime))
      (_ : Algebra (ResidueField B) (ResidueField Bprime))
      (_ : Algebra (ResidueField Aprime) (ResidueField Bprime))
      (_ : Algebra (ResidueField A) (ResidueField Bprime))
      (_ : IsScalarTower (ResidueField A) (ResidueField Aprime) (ResidueField Bprime))
      (_ : IsScalarTower (ResidueField A) (ResidueField B) (ResidueField Bprime)),
      Algebra.IsAlgebraic K Kprime ∧
        Algebra.IsSeparable K Kprime ∧
        Algebra.IsAlgebraic L Lprime ∧
        Algebra.IsSeparable L Lprime ∧
        IsSepClosure (ResidueField A) (ResidueField Aprime) ∧
        IsSepClosure (ResidueField B) (ResidueField Bprime) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsWeakSolutionFor A B K L K1) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsSolutionFor A B K L K1) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsSeparableSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsSeparableSolutionFor A B K L K1) := by
  -- Route correction: follow the source proof via strict henselizations of `A` and `B`, then
  -- compare them through a residue-field embedding instead of switching to an ad hoc field route.
  obtain ⟨Aprime, _, _, hAprimeStrict⟩ := exists_strictHenselization A
  letI : IsStrictHenselizationOf A Aprime := hAprimeStrict
  obtain ⟨hAprimeDomain, hAprimeDvr, hAAprime⟩ :=
    strict_henselization_isExtensionOfDiscreteValuationRings (R := A) (Rsh := Aprime)
  letI : IsDomain Aprime := hAprimeDomain
  letI : IsDiscreteValuationRing Aprime := hAprimeDvr
  letI : IsExtensionOfDiscreteValuationRings A Aprime := hAAprime
  obtain ⟨Bprime, _, _, hBprimeStrict⟩ := exists_strictHenselization B
  letI : IsStrictHenselizationOf B Bprime := hBprimeStrict
  obtain ⟨hBprimeDomain, hBprimeDvr, hBBprime⟩ :=
    strict_henselization_isExtensionOfDiscreteValuationRings (R := B) (Rsh := Bprime)
  letI : IsDomain Bprime := hBprimeDomain
  letI : IsDiscreteValuationRing Bprime := hBprimeDvr
  letI : IsExtensionOfDiscreteValuationRings B Bprime := hBBprime
  let Kprime := FractionRing Aprime
  let Lprime := FractionRing Bprime
  have hAprime_zero :
      Algebra.IsAlgebraic ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal Aprime).ResidueField) ∧
        Algebra.IsSeparable ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal Aprime).ResidueField) :=
    zero_prime_strictHenselization_residueField_isAlgebraic_and_separable
      (R := A) (Rsh := Aprime)
  have hBprime_zero :
      Algebra.IsAlgebraic ((⊥ : Ideal B).ResidueField) ((⊥ : Ideal Bprime).ResidueField) ∧
        Algebra.IsSeparable ((⊥ : Ideal B).ResidueField) ((⊥ : Ideal Bprime).ResidueField) :=
    zero_prime_strictHenselization_residueField_isAlgebraic_and_separable
      (R := B) (Rsh := Bprime)
  have hAprime_zero_equiv :
      Kprime ≃ₐ[Aprime] ((⊥ : Ideal Aprime).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing Aprime
  have hBprime_zero_equiv :
      Lprime ≃ₐ[Bprime] ((⊥ : Ideal Bprime).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing Bprime
  have hKprime :
      Algebra.IsAlgebraic K Kprime ∧
        Algebra.IsSeparable K Kprime :=
    fraction_field_transport_of_zeroPrime_residueField_isAlgebraic_and_separable
      (R := A) (Rsh := Aprime) (K := K) (Ksh := Kprime) hAprime_zero
  have hLprime :
      Algebra.IsAlgebraic L Lprime ∧
        Algebra.IsSeparable L Lprime :=
    fraction_field_transport_of_zeroPrime_residueField_isAlgebraic_and_separable
      (R := B) (Rsh := Bprime) (K := L) (Ksh := Lprime) hBprime_zero
  have hAprimeSep :
      IsSepClosure (ResidueField A) (ResidueField Aprime) :=
    strict_henselization_residueField_isSepClosure
      (R := A) (Rsh := Aprime)
  have hBprimeSep :
      IsSepClosure (ResidueField B) (ResidueField Bprime) :=
    strict_henselization_residueField_isSepClosure
      (R := B) (Rsh := Bprime)
  obtain ⟨hAprimeBprimeAlg, hABprimeAlg, hAAprimeBprime, hABBprime,
      hAprimeBprime, _⟩ :=
    strict_henselization_comparison_extension
      (R := A) (S := B) (Rsh := Aprime) (Ssh := Bprime)
  letI : Algebra Aprime Bprime := hAprimeBprimeAlg
  letI : Algebra A Bprime := hABprimeAlg
  letI : IsScalarTower A Aprime Bprime := hAAprimeBprime
  letI : IsScalarTower A B Bprime := hABBprime
  letI : IsExtensionOfDiscreteValuationRings Aprime Bprime := hAprimeBprime
  have hDescent :
      ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
          (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
          (_ : IsScalarTower Aprime Kprime K1prime)
          (_ : FiniteDimensional Kprime K1prime),
          IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime) →
        ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
          (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
          IsWeakSolutionFor A B K L K1) ∧
      ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
          (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
          (_ : IsScalarTower Aprime Kprime K1prime)
          (_ : FiniteDimensional Kprime K1prime),
          IsSolutionFor Aprime Bprime Kprime Lprime K1prime) →
        ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
          (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
          IsSolutionFor A B K L K1) ∧
      ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
          (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
          (_ : IsScalarTower Aprime Kprime K1prime)
          (_ : FiniteDimensional Kprime K1prime),
          IsSeparableSolutionFor Aprime Bprime Kprime Lprime K1prime) →
        ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
          (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
          IsSeparableSolutionFor A B K L K1) :=
    strict_henselization_solution_descent
      (A0 := A) (B0 := B) (K0 := K) (L0 := L)
      (Ash := Aprime) (Bsh := Bprime) (Ksh := Kprime) (Lsh := Lprime)
  -- The remaining proof is now reduced to the two source-faithful blockers packaged above:
  -- building the comparison `Aprime → Bprime` and descending solution witnesses through a finite
  -- étale stage of `A`.
  refine ⟨Aprime, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Bprime, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Kprime, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    Lprime, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ?_⟩
  exact ⟨hKprime.1, hKprime.2, hLprime.1, hLprime.2, hAprimeSep, hBprimeSep,
    hDescent.1, hDescent.2.1, hDescent.2.2⟩

end
