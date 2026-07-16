import Mathlib
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import stacks_proof.stacks_project.Chap10.Definition_10_153_1
import stacks_proof.stacks_project.Chap10.Lemma_10_154_2
import stacks_proof.stacks_project.Chap10.Lemma_10_154_3
import stacks_proof.stacks_project.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and strict henselizations;
- sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`,
  `IsHenselizationOf`;
- best owner abstraction: there is no upstream bundled strict-henselization owner in mathlib, so
  the source-facing owner here is `IsStrictHenselizationOf R S`, built from the canonical owners
  above;
- primitive data: strict henselianity of the target, locality of `R → S`, the filtered-colimit-
  of-étale presentation, and the maximal-ideal image equality;
- derived API: any choice of henselization-to-strict-henselization comparison map and any chosen
  residue-field identification with a separable closure.

Source/core/bridge triage:
- `source-facing`: `IsStrictHenselizationOf` and
  `exists_henselization_to_strictHenselization`;
- `core/canonical`: `StrictHenselianLocalRing`, `IsLocalHom`, and
  `RingHom.IsFilteredColimitOfEtale`;
- `bridge/view`: `exists_strictHenselization`, which forgets the auxiliary chosen separable-closure
  identification and keeps only the strict-henselization owner.
-/
/-- A strict henselization of the local ring `R` is an `R`-algebra `S` for which `R → S` is a
local map, `S` is strictly henselian, `S` is a filtered colimit of étale `R`-algebras, and the
maximal ideal of `S` is the image of the maximal ideal of `R`. -/
class IsStrictHenselizationOf : Prop extends StrictHenselianLocalRing S,
  IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap R S)
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S

variable (Ksep : Type u) [Field Ksep] [Algebra (ResidueField R) Ksep]
variable [IsSepClosure (ResidueField R) Ksep]

/-- Helper for Chap10 Lemma 10 155 2: the separable closure of `ResidueField R` is viewed as an
algebra over the residue field of a chosen henselization by transporting scalars through the
canonical residue-field equivalence. -/
private noncomputable abbrev transportedResidueFieldAlgebra
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh] :
    Algebra (ResidueField Rh) Ksep :=
  RingHom.toAlgebra ((algebraMap (ResidueField R) Ksep).comp
    (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom)

/-- Helper for Chap10 Lemma 10 155 2: after transporting the residue-field algebra structure
along a henselization, the chosen separable closure remains separably closed, separable, and
algebraic over the transported base field. -/
private theorem transportedResidueFieldAlgebraFacts
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh] :
    letI : Algebra (ResidueField Rh) Ksep := transportedResidueFieldAlgebra R Ksep Rh
    IsSepClosed Ksep ∧ Algebra.IsSeparable (ResidueField Rh) Ksep ∧
      Algebra.IsAlgebraic (ResidueField Rh) Ksep := by
  -- Proof comment: the algebra structure is just scalar transport across a field equivalence, so
  -- mathlib's invariance instances recover separability and algebraicity automatically.
  letI : Algebra (ResidueField Rh) Ksep := transportedResidueFieldAlgebra R Ksep Rh
  let e : ResidueField R ≃+* ResidueField Rh :=
    IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)
  have halgebraMap :
      algebraMap (ResidueField Rh) Ksep =
        (algebraMap (ResidueField R) Ksep).comp e.symm.toRingHom :=
    rfl
  have hcomp :
      (algebraMap (ResidueField Rh) Ksep).comp e.toRingHom =
        (RingEquiv.refl Ksep).toRingHom.comp (algebraMap (ResidueField R) Ksep) := by
    -- Proof comment: separability and algebraicity transport along the residue-field equivalence,
    -- so first record the exact compatibility square for the transported algebra map.
    rw [halgebraMap]
    ext x
    simp [e]
  have hsep : Algebra.IsSeparable (ResidueField Rh) Ksep :=
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl Ksep) hcomp
  have halg : Algebra.IsAlgebraic (ResidueField Rh) Ksep :=
    (Algebra.isAlgebraic_ringHom_iff_of_comp_eq e (RingEquiv.refl Ksep) hcomp).2
      inferInstance
  exact ⟨IsSepClosure.sep_closed (ResidueField R), hsep, halg⟩

omit [IsLocalRing R] [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: separable closedness of fields transports backwards
through a ring equivalence. -/
private theorem isSepClosed_of_ringEquiv
    {k K : Type u} [Field k] [Field K] [IsSepClosed K] (e : k ≃+* K) :
    IsSepClosed k := by
  -- Proof comment: split after mapping to the separably closed field, then pull the roots back
  -- across the equivalence.
  refine ⟨fun p hp ↦ ?_⟩
  refine Polynomial.Splits.of_splits_map e.toRingHom ?_ ?_
  · exact IsSepClosed.splits_of_separable (p.map e.toRingHom) hp.map
  · intro a _
    exact ⟨e.symm a, by simp⟩

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: a henselian local algebra with an ind-etale structural map,
the expected maximal-ideal image, and separably closed residue field is a strict henselization. -/
private theorem isStrictHenselizationOf_of_henselianResidueEquiv
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [HenselianLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hEtale : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B))
    (hMax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    {K : Type u} [Field K] [IsSepClosed K] (e : ResidueField B ≃+* K) :
    IsStrictHenselizationOf A B := by
  -- Proof comment: all owner fields are supplied directly; only separable closedness of the
  -- residue field is transported across the chosen residue-field equivalence.
  refine
    { toStrictHenselianLocalRing :=
        { toHenselianLocalRing := inferInstance
          toIsSepClosed := isSepClosed_of_ringEquiv e }
      toIsLocalHom := inferInstance
      isFilteredColimitOfEtale := hEtale
      map_maximalIdeal := hMax }

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: in the finite-type formally unramified local case,
mathlib's local unramified criterion gives the expected maximal-ideal image. -/
private theorem map_maximalIdeal_eq_of_local_formallyUnramified
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] :
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  -- Proof comment: the finite-type formally unramified criterion is already packaged by
  -- mathlib, so this helper records the exact local-algebra spelling needed here.
  exact Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B)

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: a local ind-etale map sends the maximal ideal of the
source onto the maximal ideal of the target. -/
private theorem map_maximalIdeal_eq_of_local_isFilteredColimitOfEtale
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hEtale : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B)) :
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  -- TODO: prove this by passing to the closed fiber over `ResidueField A`; base change preserves
  -- the ind-etale presentation, and a local ind-etale algebra over a field is a field, forcing
  -- the quotient by the image of `maximalIdeal A` to have zero maximal ideal.
  sorry

/-- Helper for Chap10 Lemma 10 155 2: fixed-base non-henselian construction without the
maximal-ideal assertion. It realizes a separable algebraic residue-field extension by a local
ind-etale algebra. -/
private theorem existsIndEtaleLocalAlgebraWithResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (ResidueField A) K]
    [Algebra.IsSeparable (ResidueField A) K] [Algebra.IsAlgebraic (ResidueField A) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B)
      (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B))
      (_ : ResidueField B ≃ₐ[ResidueField A] K),
      RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) := by
  -- TODO: prove this from a dependency-safe extraction of the no-max
  -- `ResidueExtensionStage` top-stage construction.
  sorry

/-- Helper for Chap10 Lemma 10 155 2: fixed-base non-henselian construction expected from the
source proof. It realizes a separable algebraic residue-field extension by a local ind-etale
algebra with the expected maximal-ideal image.
-/
private theorem existsIndEtaleLocalAlgebraWithResidueFieldEquivAndMapMax
    (A : Type u) [CommRing A] [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (ResidueField A) K]
    [Algebra.IsSeparable (ResidueField A) K] [Algebra.IsAlgebraic (ResidueField A) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B)
      (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B))
      (_ : ResidueField B ≃ₐ[ResidueField A] K),
      RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) ∧
        Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  -- Route correction: the stage recursion only needs to produce a no-max local ind-etale
  -- residue-extension algebra; the maximal-ideal equality follows abstractly from ind-etaleness.
  obtain ⟨B, hBComm, hBLocal, hBAlg, hBLocalHom, e, hEtale⟩ :=
    existsIndEtaleLocalAlgebraWithResidueFieldEquiv A K
  letI : CommRing B := hBComm
  letI : IsLocalRing B := hBLocal
  letI : Algebra A B := hBAlg
  letI : IsLocalHom (algebraMap A B) := hBLocalHom
  have hMax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    map_maximalIdeal_eq_of_local_isFilteredColimitOfEtale A B hEtale
  exact ⟨B, inferInstance, inferInstance, inferInstance, hBLocalHom, e, hEtale, hMax⟩

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: residue-field maps compose according to a scalar tower of
local algebra maps. -/
private theorem residueField_map_comp_of_scalarTower
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (C : Type u) [CommRing C] [IsLocalRing C] [Algebra B C] [IsLocalHom (algebraMap B C)]
    [Algebra A C] [IsScalarTower A B C] [IsLocalHom (algebraMap A C)] :
    ResidueField.map (algebraMap A C) =
      (ResidueField.map (algebraMap B C)).comp
        (ResidueField.map (algebraMap A B)) := by
  -- Proof comment: the canonical `ResidueField.map_comp` statement is phrased for the explicit
  -- composite; the scalar-tower equation rewrites that composite to the installed `A`-algebra map.
  have hcomp := IsLocalRing.ResidueField.map_comp (algebraMap A B) (algebraMap B C)
  simpa [IsScalarTower.algebraMap_eq A B C] using hcomp

/-- Helper for Chap10 Lemma 10 155 2: the residue-field equivalence from a local algebra
transports across its henselization as an algebra equivalence over the original residue field. -/
private noncomputable def residueFieldAlgEquivOfHenselization
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] [IsLocalHom (algebraMap A Bh)]
    (K : Type u) [Field K] [Algebra (ResidueField A) K]
    (eB : ResidueField B ≃ₐ[ResidueField A] K) :
    ResidueField Bh ≃ₐ[ResidueField A] K where
  toRingEquiv :=
    (IsHenselizationOf.residueFieldEquiv (R := B) (S := Bh)).symm.trans eB.toRingEquiv
  commutes' := by
    -- Proof comment: the residue map `A → Bh` factors through the residue map `A → B`, and the
    -- henselization residue-field equivalence is induced by `B → Bh`.
    intro x
    let eH : ResidueField B ≃+* ResidueField Bh :=
      IsHenselizationOf.residueFieldEquiv (R := B) (S := Bh)
    have hcomp :
        ResidueField.map (algebraMap A Bh) =
          (ResidueField.map (algebraMap B Bh)).comp
            (ResidueField.map (algebraMap A B)) :=
      residueField_map_comp_of_scalarTower A B Bh
    have hmap :
        eH (algebraMap (ResidueField A) (ResidueField B) x) =
          algebraMap (ResidueField A) (ResidueField Bh) x := by
      change
        ResidueField.map (algebraMap B Bh)
            (ResidueField.map (algebraMap A B) x) =
          ResidueField.map (algebraMap A Bh) x
      exact congrArg (fun f : ResidueField A →+* ResidueField Bh ↦ f x) hcomp.symm
    have hpre :
        eH.symm (algebraMap (ResidueField A) (ResidueField Bh) x) =
          algebraMap (ResidueField A) (ResidueField B) x := by
      exact eH.symm_apply_eq.mpr hmap.symm
    calc
      ((IsHenselizationOf.residueFieldEquiv (R := B) (S := Bh)).symm.trans eB.toRingEquiv)
          (algebraMap (ResidueField A) (ResidueField Bh) x)
          = eB (eH.symm (algebraMap (ResidueField A) (ResidueField Bh) x)) := rfl
      _ = eB (algebraMap (ResidueField A) (ResidueField B) x) := by rw [hpre]
      _ = algebraMap (ResidueField A) K x := eB.commutes x

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: the composite from a local algebra to its henselization is
a local homomorphism. -/
private theorem isLocalHom_comp_henselization
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] :
    IsLocalHom (algebraMap A Bh) := by
  -- Proof comment: spell the structural map as the composite through `B`, where both factors are
  -- local maps.
  rw [IsScalarTower.algebraMap_eq A B Bh]
  infer_instance

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: ind-etaleness of a local algebra map is preserved after
composing with a henselization. -/
private theorem isFilteredColimitOfEtale_comp_henselization
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [IsScalarTower A B Bh]
    (hEtale : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B)) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A Bh) := by
  -- Proof comment: compose the ind-etale presentation for `A → B` with the henselization
  -- presentation for `B → Bh`, then rewrite the composite to the installed `A`-algebra map.
  have hcomp := RingHom.isFilteredColimitOfEtale_comp (algebraMap A B) (algebraMap B Bh)
    hEtale (IsHenselizationOf.isFilteredColimitOfEtale (R := B) (S := Bh))
  rwa [← IsScalarTower.algebraMap_eq A B Bh] at hcomp

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: maximal ideals map correctly after passing a local algebra
to its henselization. -/
private theorem map_maximalIdeal_comp_base_henselization
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [IsScalarTower A B Bh]
    (hMax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    Ideal.map (algebraMap A Bh) (maximalIdeal A) = maximalIdeal Bh := by
  -- Proof comment: compute the image through the composite `A → B → Bh`, using first the
  -- supplied maximal-ideal identity for `B` and then the henselization identity.
  calc
    Ideal.map (algebraMap A Bh) (maximalIdeal A)
        = Ideal.map ((algebraMap B Bh).comp (algebraMap A B)) (maximalIdeal A) := by
            rw [IsScalarTower.algebraMap_eq A B Bh]
    _ = Ideal.map (algebraMap B Bh) (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
            rw [Ideal.map_map]
    _ = Ideal.map (algebraMap B Bh) (maximalIdeal B) := by
            rw [hMax]
    _ = maximalIdeal Bh := IsHenselizationOf.map_maximalIdeal (R := B) (S := Bh)

/-- Helper for Chap10 Lemma 10 155 2: fixed-base construction expected from the source proof.
It realizes a separable algebraic residue-field extension by a henselian local ind-etale algebra.
-/
private theorem existsHenselianFilteredColimitOfEtaleLocalAlgebraWithResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (K : Type u) [Field K] [Algebra (ResidueField A) K]
    [Algebra.IsSeparable (ResidueField A) K] [Algebra.IsAlgebraic (ResidueField A) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : HenselianLocalRing B)
      (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B))
      (_ : ResidueField B ≃ₐ[ResidueField A] K),
      RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) ∧
        Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  -- Route correction: the residue-extension recursion only needs to construct a local ind-etale
  -- algebra; henselianity is then added by taking its henselization.
  obtain ⟨B, hBComm, hBLocal, hBAlg, hBLocalHom, eB, hEtaleB, hMaxB⟩ :=
    existsIndEtaleLocalAlgebraWithResidueFieldEquivAndMapMax A K
  letI : CommRing B := hBComm
  letI : IsLocalRing B := hBLocal
  letI : Algebra A B := hBAlg
  letI : IsLocalHom (algebraMap A B) := hBLocalHom
  obtain ⟨Bh, hBhComm, hBhAlg, hBhHensel⟩ := exists_henselization B
  letI : CommRing Bh := hBhComm
  letI : Algebra B Bh := hBhAlg
  letI : IsHenselizationOf B Bh := hBhHensel
  letI : Algebra A Bh := ((algebraMap B Bh).comp (algebraMap A B)).toAlgebra
  letI : IsScalarTower A B Bh := IsScalarTower.of_algebraMap_eq' rfl
  have hLocalBh : IsLocalHom (algebraMap A Bh) :=
    isLocalHom_comp_henselization A B Bh
  letI : IsLocalHom (algebraMap A Bh) := hLocalBh
  have hEtaleBh : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A Bh) :=
    isFilteredColimitOfEtale_comp_henselization A B Bh hEtaleB
  have hMaxBh : Ideal.map (algebraMap A Bh) (maximalIdeal A) = maximalIdeal Bh :=
    map_maximalIdeal_comp_base_henselization A B Bh hMaxB
  exact
    ⟨Bh, inferInstance, inferInstance, inferInstance, inferInstance, hLocalBh,
      residueFieldAlgEquivOfHenselization A B Bh K eB, hEtaleBh, hMaxBh⟩

omit [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 155 2: maximal ideals map correctly after composing a
henselization with a strict henselization over it. -/
private theorem map_maximalIdeal_comp_henselization
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra Rh Rsh] [IsStrictHenselizationOf Rh Rsh]
    [Algebra R Rsh] [IsScalarTower R Rh Rsh] :
    Ideal.map (algebraMap R Rsh) (maximalIdeal R) = maximalIdeal Rsh := by
  -- Proof comment: compute the image through the composite `R → Rh → Rsh`, using the
  -- maximal-ideal identities for the henselization and then for the strict henselization.
  calc
    Ideal.map (algebraMap R Rsh) (maximalIdeal R)
        = Ideal.map ((algebraMap Rh Rsh).comp (algebraMap R Rh)) (maximalIdeal R) := by
            rw [IsScalarTower.algebraMap_eq R Rh Rsh]
    _ = Ideal.map (algebraMap Rh Rsh)
          (Ideal.map (algebraMap R Rh) (maximalIdeal R)) := by
            rw [Ideal.map_map]
    _ = Ideal.map (algebraMap Rh Rsh) (maximalIdeal Rh) := by
            rw [IsHenselizationOf.map_maximalIdeal (R := R) (S := Rh)]
    _ = maximalIdeal Rsh := IsStrictHenselizationOf.map_maximalIdeal (R := Rh) (S := Rsh)

/-- Helper for Chap10 Lemma 10 155 2: a strict henselization over a henselization composes to a
strict henselization over the original local ring. -/
private theorem isStrictHenselizationOf_comp_henselization
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra Rh Rsh] [IsStrictHenselizationOf Rh Rsh]
    [Algebra R Rsh] [IsScalarTower R Rh Rsh] :
    IsStrictHenselizationOf R Rsh := by
  -- Proof comment: compose the local and ind-etale owner fields, then transport the maximal
  -- ideal identity through the scalar-tower spelling of the composite map.
  refine
    { toStrictHenselianLocalRing := inferInstance
      toIsLocalHom := ?_
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_ }
  · -- Locality is stable under composition of the henselization map and the strict map.
    rw [IsScalarTower.algebraMap_eq R Rh Rsh]
    infer_instance
  · -- Ind-etaleness is the Chapter 10 composition theorem for filtered colimits of etale maps.
    have hcomp := RingHom.isFilteredColimitOfEtale_comp (algebraMap R Rh) (algebraMap Rh Rsh)
      (IsHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rh))
      (IsStrictHenselizationOf.isFilteredColimitOfEtale (R := Rh) (S := Rsh))
    rwa [← IsScalarTower.algebraMap_eq R Rh Rsh] at hcomp
  · -- The maximal ideal image is computed by mapping first to `Rh`, then to `Rsh`.
    exact map_maximalIdeal_comp_henselization R Rh Rsh

omit [IsSepClosure (ResidueField R) Ksep] in
/-- Helper for Chap10 Lemma 10 155 2: residue-field compatibility over a henselization transports
back to compatibility over the original local ring. -/
private theorem residueField_comp_henselization_compat
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra Rh Rsh] [IsStrictHenselizationOf Rh Rsh]
    [Algebra R Rsh] [IsScalarTower R Rh Rsh] [IsLocalHom (algebraMap R Rsh)]
    (φ : ResidueField Rsh ≃+* Ksep)
    (hφ : φ.toRingHom.comp (ResidueField.map (algebraMap Rh Rsh)) =
        (algebraMap (ResidueField R) Ksep).comp
          (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom) :
    φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
      algebraMap (ResidueField R) Ksep := by
  -- Proof comment: factor the residue map through `ResidueField Rh`, where the fixed-base
  -- compatibility hypothesis applies, and cancel the henselization residue-field equivalence.
  let e : ResidueField R ≃+* ResidueField Rh :=
    IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)
  have he : e.toRingHom = ResidueField.map (algebraMap R Rh) := rfl
  have hmap :
      ResidueField.map (algebraMap R Rsh) =
        (ResidueField.map (algebraMap Rh Rsh)).comp
          (ResidueField.map (algebraMap R Rh)) :=
    residueField_map_comp_of_scalarTower R Rh Rsh
  calc
    φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh))
        = φ.toRingHom.comp
            ((ResidueField.map (algebraMap Rh Rsh)).comp
              (ResidueField.map (algebraMap R Rh))) := by
              rw [hmap]
    _ = (φ.toRingHom.comp (ResidueField.map (algebraMap Rh Rsh))).comp
          (ResidueField.map (algebraMap R Rh)) := by
          ext x
          rfl
    _ = ((algebraMap (ResidueField R) Ksep).comp e.symm.toRingHom).comp e.toRingHom := by
          rw [hφ, he]
    _ = algebraMap (ResidueField R) Ksep := by
          ext x
          simp [e]

/-- Helper for Chap10 Lemma 10 155 2: the remaining fixed-base construction is a strict
henselization of the chosen henselization whose residue field is the transported separable
closure. -/
private theorem existsStrictHenselizationOverHenselianBase
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra Rh Rsh)
      (_ : IsStrictHenselizationOf Rh Rsh) (φ : ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (ResidueField.map (algebraMap Rh Rsh)) =
        (algebraMap (ResidueField R) Ksep).comp
          (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom := by
  -- Proof comment: this is the finite separable residue-extension direct-limit construction over
  -- the henselian base `Rh`; the transport back to `R` is now separated and proved below.
  -- Normalize the residue-field base once; the remaining construction should use this
  -- `ResidueField Rh`-algebra structure throughout the stage recursion.
  letI : Algebra (ResidueField Rh) Ksep := transportedResidueFieldAlgebra R Ksep Rh
  have hTransport := transportedResidueFieldAlgebraFacts R Ksep Rh
  letI : IsSepClosed Ksep := hTransport.1
  letI : Algebra.IsSeparable (ResidueField Rh) Ksep := hTransport.2.1
  letI : Algebra.IsAlgebraic (ResidueField Rh) Ksep := hTransport.2.2
  obtain ⟨Rsh, hRshComm, hRshLocal, hRshHenselian, hAlg, hLocalHom, e, hEtale, hMax⟩ :=
    existsHenselianFilteredColimitOfEtaleLocalAlgebraWithResidueFieldEquiv Rh Ksep
  letI : CommRing Rsh := hRshComm
  letI : IsLocalRing Rsh := hRshLocal
  letI : HenselianLocalRing Rsh := hRshHenselian
  letI : Algebra Rh Rsh := hAlg
  letI : IsLocalHom (algebraMap Rh Rsh) := hLocalHom
  have hStrict : IsStrictHenselizationOf Rh Rsh :=
    isStrictHenselizationOf_of_henselianResidueEquiv Rh Rsh hEtale hMax e.toRingEquiv
  have hCompat :
      e.toRingEquiv.toRingHom.comp (ResidueField.map (algebraMap Rh Rsh)) =
        algebraMap (ResidueField Rh) Ksep := by
    -- Proof comment: the algebra-equivalence compatibility field is exactly the residue-field
    -- square for the constructed algebra.
    ext x
    exact e.commutes x
  refine ⟨Rsh, inferInstance, inferInstance, hStrict, e.toRingEquiv, ?_⟩
  simpa [transportedResidueFieldAlgebra] using hCompat

/-- Helper for Chap10 Lemma 10 155 2: after a henselization `Rh` has been chosen, the fixed-base
strict construction packages into the source-facing strict henselization over `R`. -/
private theorem existsStrictHenselizationOverHenselization
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
      (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
      (_ : IsLocalHom (algebraMap Rh Rsh)) (φ : ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep := by
  -- Proof comment: unpack the fixed-base construction, install the composite `R`-algebra
  -- structure, and apply the two transport helpers just proved.
  obtain ⟨Rsh, hRshComm, hRhRshAlg, hStrictRh, φ, hφ⟩ :=
    existsStrictHenselizationOverHenselianBase R Ksep Rh
  letI : CommRing Rsh := hRshComm
  letI : Algebra Rh Rsh := hRhRshAlg
  letI : IsStrictHenselizationOf Rh Rsh := hStrictRh
  letI : Algebra R Rsh := ((algebraMap Rh Rsh).comp (algebraMap R Rh)).toAlgebra
  letI : IsScalarTower R Rh Rsh := IsScalarTower.of_algebraMap_eq' rfl
  have hStrictR : IsStrictHenselizationOf R Rsh :=
    isStrictHenselizationOf_comp_henselization R Rh Rsh
  letI : IsStrictHenselizationOf R Rsh := hStrictR
  have hLocalRh : IsLocalHom (algebraMap Rh Rsh) := inferInstance
  have hCompatR :
      φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep :=
    residueField_comp_henselization_compat R Ksep Rh Rsh φ hφ
  exact
    ⟨Rsh, inferInstance, inferInstance, hStrictR, inferInstance, inferInstance, hLocalRh, φ,
      hCompatR⟩

omit [IsSepClosure (ResidueField R) Ksep] in
/-- Helper for Chap10 Lemma 10 155 2: a strict extension over a fixed henselization packages
back into the existential statement that also remembers the chosen henselization. -/
private theorem existsHenselizationToStrictHenselizationOfChosenHenselization
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (hstrict :
      ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
        (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
        (_ : IsLocalHom (algebraMap Rh Rsh)) (φ : ResidueField Rsh ≃+* Ksep),
        φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
          algebraMap (ResidueField R) Ksep) :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsHenselizationOf R Rh)
      (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
      (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
      (_ : IsLocalHom (algebraMap Rh Rsh)) (φ : ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep := by
  -- Proof comment: unpack the strict-extension witness and reinsert the already chosen
  -- henselization data as the first four existential components.
  obtain ⟨Rsh, hRshComm, hRshAlg, hRshStrict, hRhRshAlg, hTower, hLocal, φ, hφ⟩ := hstrict
  exact
    ⟨Rh, inferInstance, inferInstance, inferInstance, Rsh, hRshComm, hRshAlg, hRshStrict,
      hRhRshAlg, hTower, hLocal, φ, hφ⟩

-- Proof sketch: repeat the filtered-colimit construction of the henselization, but index stages
-- by triples `(S, 𝔮, α)` where `R → S` is étale, `𝔮` lies over `maximalIdeal R`, and `α`
-- embeds the stage residue field into `Ksep`. The colimit then carries compatible maps from both
-- a henselization `Rʰ` and the chosen separable closure of the residue field, while
-- `Lemma 10.154.8` and `Definition 10.153.1` give strict henselianity from the separably closed
-- residue field.
/-- Lemma 10.155.2: given a separable closure `Ksep` of the residue field of a local ring `R`,
there exist a henselization `Rʰ` of `R`, a strict henselization `Rˢʰ` of `R`, a local map
`Rʰ → Rˢʰ`, and a residue-field isomorphism from `ResidueField Rˢʰ` to `Ksep` compatible with the
canonical map from `ResidueField R`. -/
@[stacks 04GP]
theorem exists_henselization_to_strictHenselization :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsHenselizationOf R Rh)
      (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
      (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
      (_ : IsLocalHom (algebraMap Rh Rsh)) (φ : ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep := by
  -- Proof comment: first choose a henselization of the base, then delegate only the strict
  -- extension over that fixed henselian base to the construction helper above.
  obtain ⟨Rh, hRhComm, hRhAlg, hRhHensel⟩ := exists_henselization R
  letI : CommRing Rh := hRhComm
  letI : Algebra R Rh := hRhAlg
  letI : IsHenselizationOf R Rh := hRhHensel
  exact existsHenselizationToStrictHenselizationOfChosenHenselization R Ksep Rh
    (existsStrictHenselizationOverHenselization R Ksep Rh)

-- Proof sketch: apply Lemma `10.155.2` with the canonical separable closure
-- `SeparableClosure (ResidueField R)` and discard the auxiliary henselization and residue-field
-- comparison data. The strict-henselization owner is the primitive public output.
/-- Every local ring admits a strict henselization. This is the owner-level existence theorem
obtained from Lemma `10.155.2` by choosing the canonical separable closure of the residue field
and forgetting the auxiliary comparison data. -/
theorem exists_strictHenselization :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh), IsStrictHenselizationOf R Rsh := by
  let Ksep := SeparableClosure (ResidueField R)
  let _ : Field Ksep := inferInstance
  let _ : Algebra (ResidueField R) Ksep := inferInstance
  let _ : IsSepClosure (ResidueField R) Ksep := inferInstance
  obtain ⟨_, _, _, _, Rsh, _, _, hRsh, _, _, _, _, _⟩ :=
    exists_henselization_to_strictHenselization R Ksep
  exact ⟨Rsh, inferInstance, inferInstance, hRsh⟩

end
