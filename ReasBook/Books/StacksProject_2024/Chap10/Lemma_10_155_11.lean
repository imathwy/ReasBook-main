import Mathlib
import StacksProject_2024.Chap10.Lemma_10_127_4
import StacksProject_2024.Chap10.Lemma_10_155_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

noncomputable section

section LocalRingLocalization

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private instance self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := sorry

/-- The canonical algebra equivalence from the localization of a local ring at the complement of
its maximal ideal back to the ring itself. -/
private abbrev localRing_atMaximalIdeal_algEquiv :
    Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
  IsLocalization.algEquiv
    (maximalIdeal A).primeCompl
    (Localization.AtPrime (maximalIdeal A))
    A

end LocalRingLocalization

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]
variable {Ksep : Type u} [Field Ksep]
variable [Algebra R Ksep] [Algebra p.ResidueField Ksep] [IsScalarTower R p.ResidueField Ksep]
variable [IsSepClosure p.ResidueField Ksep]

/- Domain-style sampling:
* primary domain: strict henselization of `Rₚ` presented by the filtered category of étale
  neighborhoods `(S, q, φ)` of the chosen prime `p` equipped with a residue-field map into the
  chosen separable closure `Ksep`;
* sampled owner declarations of the same kind:
  - `selectedAlgebrasOverTargetDiagram`;
  - `etaleResidueFieldNeighborhoodSourceDiagram`;
  - `etaleResidueFieldNeighborhoodLocalizationDiagram`;
  - `existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap`;
* best owner abstraction:
  - `source-facing`: the explicit-prime neighborhood category indexed by triples
    `(S, q, φ)` over the fixed prime `p`, together with its source and localized diagrams;
  - `core/canonical`: the chapter owners `selectedAlgebrasOverTargetDiagram`,
    `IsStrictHenselizationOf`, and the residue-field lifting theorem
    `existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap`;
  - `bridge/view`: the cocones from those source-facing diagrams to a chosen strict henselization
    of `Rₚ`.
 * primitive data:
  - the ambient over-category `Over (CommAlgCat.of R Ksep)`;
  - the internal étale object property on that category;
  - the chosen prime `p`, kept explicit only on the source-facing neighborhood owner because
    `Ksep` is fixed as a separable closure of `κ(p)`.
* derived API:
  - the source diagram in `CommAlgCat R`;
  - the localized diagram in `CommAlgCat Rₚ`;
  - the filteredness theorem and the strict-henselization colimit cocones.

This file therefore follows the owner pattern of `Lemma_10_155_7`: keep `p` explicit, keep the
source and localization diagrams in the ambient algebra categories, and make the strict
henselization output an explicit cocone-plus-`IsColimit` construction rather than an existential
`CommRingCat` package.
-/

/-- Internal shorthand for the ambient over-category of `R`-algebras equipped with a chosen map
to `Ksep`. -/
private abbrev SepClosurePointedAlgebraCategory (R : Type u) [CommRing R]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] :=
  Over (CommAlgCat.of R Ksep)

/-- Internal helper selecting those pointed `R`-algebras over `Ksep` whose structure map from `R`
is étale. -/
private abbrev etaleSepClosurePointedAlgebraProperty (R : Type u) [CommRing R]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] :
    ObjectProperty (SepClosurePointedAlgebraCategory R Ksep) :=
  fun A ↦ RingHom.Etale (algebraMap R A.left)

/-- The category of étale neighborhoods `(S, q, φ)` of `p` with `φ : κ(q) → Ksep`. -/
abbrev EtaleSepClosureNeighborhoodCategory (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep] :=
  (etaleSepClosurePointedAlgebraProperty R Ksep).FullSubcategory

/-- The diagram sending `(S, q, φ)` to the underlying `R`-algebra `S`. -/
abbrev etaleSepClosureNeighborhoodSourceDiagram (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep] :
    EtaleSepClosureNeighborhoodCategory R p Ksep ⥤ CommAlgCat R :=
  selectedAlgebrasOverTargetDiagram (etaleSepClosurePointedAlgebraProperty R Ksep)

/-- The structure map from an object over `Ksep` to the fixed target `Ksep`. -/
private noncomputable abbrev sepClosurePointedAlgebraToSepClosure
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    A.left →+* Ksep :=
  let φ := (forget₂ (CommAlgCat R) CommRingCat).map A.hom
  φ.hom

/-- The underlying ring homomorphism of a morphism over `Ksep`. -/
private abbrev sepClosurePointedAlgebraHom (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : SepClosurePointedAlgebraCategory R Ksep} (f : A ⟶ B) :
    A.left →+* B.left :=
  let φ := f.left
  φ.hom

/-- The underlying ring homomorphism of a morphism in the full subcategory of étale neighborhoods
over `Ksep`. -/
private abbrev etaleSepClosureNeighborhoodHom (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) :
    A.obj.left →+* B.obj.left :=
  sepClosurePointedAlgebraHom R p Ksep f.hom

/-- The prime ideal attached to an object over `Ksep` is the kernel of its structural map to
`Ksep`. -/
private noncomputable abbrev sepClosurePointedAlgebraKernel
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    Ideal A.left :=
  RingHom.ker (sepClosurePointedAlgebraToSepClosure R p Ksep A)

/-- The chosen prime of the source object is the comap of the chosen prime of the target. -/
private theorem sepClosurePointedAlgebraKernel_comap (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : SepClosurePointedAlgebraCategory R Ksep} (f : A ⟶ B) :
    sepClosurePointedAlgebraKernel R p Ksep A =
      Ideal.comap (sepClosurePointedAlgebraHom R p Ksep f)
        (sepClosurePointedAlgebraKernel R p Ksep B) := sorry

/-- The kernel of a map to the field `Ksep` is prime. -/
private instance sepClosurePointedAlgebraKernel_isPrime
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    (sepClosurePointedAlgebraKernel R p Ksep A).IsPrime :=
  RingHom.ker_isPrime _

/-- The chosen prime of an object over `Ksep` lies over the fixed prime `p`. -/
private theorem sepClosurePointedAlgebraKernel_comap_algebraMap
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    p = Ideal.comap (algebraMap R A.left) (sepClosurePointedAlgebraKernel R p Ksep A) := sorry

/-- The canonical `Rₚ`-algebra map to the localization of an étale neighborhood at its chosen
prime. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationAlgebraMap
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    Localization.AtPrime p →+* Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) :=
  Localization.localRingHom
    p
    (sepClosurePointedAlgebraKernel R p Ksep A.obj)
    (algebraMap R A.obj.left)
    (sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj)

/-- The localization map induced by the identity morphism is the identity. -/
private theorem sepClosurePointedAlgebraLocalization_map_id (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    Localization.localRingHom
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (RingHom.id A.obj.left)
        (sepClosurePointedAlgebraKernel_comap R p Ksep (𝟙 A.obj)) =
      RingHom.id _ := sorry

/-- Localization along a composite morphism agrees with the composite of the localization maps. -/
private theorem sepClosurePointedAlgebraLocalization_map_comp (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B C : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) (g : B ⟶ C) :
    Localization.localRingHom
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (sepClosurePointedAlgebraKernel R p Ksep C.obj)
        ((etaleSepClosureNeighborhoodHom R p Ksep g).comp
          (etaleSepClosureNeighborhoodHom R p Ksep f))
        (sepClosurePointedAlgebraKernel_comap R p Ksep (f.hom ≫ g.hom)) =
      (Localization.localRingHom
          (sepClosurePointedAlgebraKernel R p Ksep B.obj)
          (sepClosurePointedAlgebraKernel R p Ksep C.obj)
          (etaleSepClosureNeighborhoodHom R p Ksep g)
          (sepClosurePointedAlgebraKernel_comap R p Ksep g.hom)).comp
        (Localization.localRingHom
          (sepClosurePointedAlgebraKernel R p Ksep A.obj)
          (sepClosurePointedAlgebraKernel R p Ksep B.obj)
          (etaleSepClosureNeighborhoodHom R p Ksep f)
          (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)) := sorry

/-- The transition maps in the localized neighborhood diagram are `Rₚ`-algebra maps. -/
private theorem etaleSepClosureNeighborhoodLocalization_map_commutes
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) :
    (Localization.localRingHom
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (sepClosurePointedAlgebraKernel R p Ksep B.obj)
        (etaleSepClosureNeighborhoodHom R p Ksep f)
        (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)).comp
      (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A) =
        etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep B := sorry

/-- The localized neighborhood `(S, q, φ) ↦ S_q` viewed as an `Rₚ`-algebra. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationObject
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    CommAlgCat (Localization.AtPrime p) :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  CommAlgCat.of (Localization.AtPrime p)
    (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))

/-- The induced `Rₚ`-algebra map on localized neighborhoods. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationMorphism
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) :
    etaleSepClosureNeighborhoodLocalizationObject R p Ksep A ⟶
      etaleSepClosureNeighborhoodLocalizationObject R p Ksep B :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep B.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep B)
  CommAlgCat.ofHom <|
    { toRingHom :=
        Localization.localRingHom
          (sepClosurePointedAlgebraKernel R p Ksep A.obj)
          (sepClosurePointedAlgebraKernel R p Ksep B.obj)
          (etaleSepClosureNeighborhoodHom R p Ksep f)
        (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)
      commutes' := by
        intro x
        exact congrArg
          (fun g :
            Localization.AtPrime p →+*
              Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep B.obj) ↦ g x)
          (etaleSepClosureNeighborhoodLocalization_map_commutes R p Ksep f) }

/-- The localized neighborhood diagram sending `(S, q, φ)` to the `Rₚ`-algebra `S_q`. -/
noncomputable def etaleSepClosureNeighborhoodLocalizationDiagram
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep] :
    EtaleSepClosureNeighborhoodCategory R p Ksep ⥤ CommAlgCat (Localization.AtPrime p) where
  obj A := etaleSepClosureNeighborhoodLocalizationObject R p Ksep A
  map f := etaleSepClosureNeighborhoodLocalizationMorphism R p Ksep f
  map_id A := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun g :
          Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+*
            Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) ↦ g x)
        (sepClosurePointedAlgebraLocalization_map_id R p Ksep A)
  map_comp {A B C} f g := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun h :
          Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+*
            Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep C.obj) ↦ h x)
        (sepClosurePointedAlgebraLocalization_map_comp R p Ksep f g)

/-- The canonical equivalence between the residue field of the local ring `A` and the residue
field defined using its maximal ideal. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- The canonical equivalence carries residue classes of elements to their local-ring residues. -/
private theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type*) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (residue A a) by rfl]
  change
    maximalIdealResidueFieldEquiv A ((maximalIdealResidueFieldEquiv A).symm (residue A a)) =
      residue A a
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

/-- For local maps, the maximal-ideal residue-field map agrees with the local-ring
residue-field map through the canonical equivalences. -/
private theorem maximalIdealResidueFieldEquiv_comp_residueFieldMap
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdealResidueFieldEquiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdealResidueFieldEquiv A).toRingHom := by
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdealResidueFieldEquiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdealResidueFieldEquiv_apply_algebraMap,
    maximalIdealResidueFieldEquiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- For a prime localization, the residue field of the maximal ideal is the prime residue field. -/
private noncomputable abbrev primeLocalizationMaximalResidueFieldEquiv
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] :
    (maximalIdeal (Localization.AtPrime I)).ResidueField ≃+* I.ResidueField := by
  change (maximalIdeal (Localization.AtPrime I)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime I)
  exact maximalIdealResidueFieldEquiv (Localization.AtPrime I)

/-- For a prime localization, the local-ring residue field is canonically the prime residue
field. -/
private noncomputable abbrev primeLocalizationResidueFieldEquiv
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] :
    ResidueField (Localization.AtPrime I) ≃+* I.ResidueField :=
  (maximalIdealResidueFieldEquiv (Localization.AtPrime I)).symm.trans
    (primeLocalizationMaximalResidueFieldEquiv I)

/-- The canonical map from the residue field of `Rₚ` to the chosen separable closure `Ksep`. -/
private noncomputable abbrev localizationAtPrimeMaximalResidueFieldToSepClosure
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep] :
    (maximalIdeal (Localization.AtPrime p)).ResidueField →+* Ksep :=
  (algebraMap p.ResidueField Ksep).comp
    (primeLocalizationMaximalResidueFieldEquiv p).toRingHom

/-- The canonical map from the local-ring residue field of `Rₚ` to the chosen separable closure
`Ksep`. -/
private noncomputable abbrev localizationAtPrimeResidueFieldToSepClosure
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep] :
    ResidueField (Localization.AtPrime p) →+* Ksep :=
  (algebraMap p.ResidueField Ksep).comp
    (primeLocalizationResidueFieldEquiv p).toRingHom

/-- The canonical map from `ResidueField (Rₚ)` restricts along the maximal-ideal residue-field
equivalence to the canonical map from `κ(p)`. -/
private theorem localizationAtPrimeResidueFieldToSepClosure_comp_maximalIdealResidueFieldEquiv
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep] :
    (localizationAtPrimeResidueFieldToSepClosure p Ksep).comp
        (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom =
      localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
  ext x
  simp [localizationAtPrimeResidueFieldToSepClosure,
    localizationAtPrimeMaximalResidueFieldToSepClosure, primeLocalizationResidueFieldEquiv]

/-- The canonical map from the residue field `κ(q)` of the chosen prime of an object over `Ksep`
to `Ksep`. -/
private theorem sepClosurePointedAlgebraKernel_le_ker
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    sepClosurePointedAlgebraKernel R p Ksep A ≤
      RingHom.ker (sepClosurePointedAlgebraToSepClosure R p Ksep A) := by
  intro x hx
  exact hx

/-- Elements outside the kernel map to units in the field `Ksep`. -/
private theorem sepClosurePointedAlgebraKernelPrimeCompl_toSepClosure_units
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    (sepClosurePointedAlgebraKernel R p Ksep A).primeCompl ≤
      (IsUnit.submonoid Ksep).comap (sepClosurePointedAlgebraToSepClosure R p Ksep A) := by
  intro x hx
  exact isUnit_iff_ne_zero.mpr fun hx0 ↦ hx <| by
    simpa [sepClosurePointedAlgebraKernel] using hx0

/-- The residue-field map `κ(q) → Ksep` induced by the structural map `S → Ksep`. -/
private noncomputable abbrev sepClosurePointedAlgebraKernelResidueFieldToSepClosure
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    (sepClosurePointedAlgebraKernel R p Ksep A).ResidueField →+* Ksep :=
  Ideal.ResidueField.lift
    (sepClosurePointedAlgebraKernel R p Ksep A)
    (sepClosurePointedAlgebraToSepClosure R p Ksep A)
    (sepClosurePointedAlgebraKernel_le_ker p A)
    (sepClosurePointedAlgebraKernelPrimeCompl_toSepClosure_units p A)

/-- The localization `S_q` of an étale neighborhood is étale over `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_etale
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) := by
  sorry

/-- The maximal ideal of `S_q` lies over the maximal ideal of `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_maximalIdeal_under
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).under
        (Localization.AtPrime p) =
      maximalIdeal (Localization.AtPrime p) := by
  sorry

/-- The residue-field map from `κ(maximalIdeal S_q)` to `Ksep`. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).ResidueField →+*
      Ksep :=
  (sepClosurePointedAlgebraKernelResidueFieldToSepClosure p A.obj).comp
    (primeLocalizationMaximalResidueFieldEquiv
      (sepClosurePointedAlgebraKernel R p Ksep A.obj)).toRingHom

/-- The localized residue-field map is compatible with the canonical map from `κ(p)` to `Ksep`. -/
private theorem etaleSepClosureNeighborhoodLocalization_residueFieldToSepClosure_comp
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep :=
      RingHom.toAlgebra (localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep)
    (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A).comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p))
          (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
          (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
          (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A).symm) =
      (algebraMap (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep).comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p))
          (maximalIdeal (Localization.AtPrime p))
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal_comap
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime p))).symm) := by
  sorry

section StrictHenselizationTarget

/-- The canonical residue-field identification of a chosen strict henselization, expressed on the
maximal-ideal residue field for use with the source lifting theorem. -/
private noncomputable abbrev strictHenselizationMaximalIdealResidueFieldEquiv
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep) :
    (maximalIdeal Rsh).ResidueField ≃+* Ksep :=
  (maximalIdealResidueFieldEquiv Rsh).trans ι

/-- The local-ring residue-field compatibility rewrites to the maximal-ideal residue-field form
required by `Lemma_10_155_9`. -/
private theorem strictHenselizationMaximalIdealResidueFieldCompat
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
          (algebraMap (Localization.AtPrime p) Rsh)
          (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh)).symm) =
      localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
  calc
    (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
          (algebraMap (Localization.AtPrime p) Rsh)
          (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh)).symm)
      = ι.toRingHom.comp
          ((ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)).comp
            (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom) := by
          change
            (ι.toRingHom.comp (maximalIdealResidueFieldEquiv Rsh).toRingHom).comp
                (Ideal.ResidueField.map (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
                  (algebraMap (Localization.AtPrime p) Rsh)
                  (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh)).symm) =
              _
          rw [RingHom.comp_assoc]
          rw [maximalIdealResidueFieldEquiv_comp_residueFieldMap
            (algebraMap (Localization.AtPrime p) Rsh)]
    _ = (ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh))).comp
          (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom := by
          rw [RingHom.comp_assoc]
    _ = (localizationAtPrimeResidueFieldToSepClosure p Ksep).comp
          (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom := by
          rw [hι]
    _ = localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
          rw [localizationAtPrimeResidueFieldToSepClosure_comp_maximalIdealResidueFieldEquiv]

/-- The localized neighborhood `S_q` admits a unique `Rₚ`-algebra map to a chosen strict
henselization of `Rₚ` compatible with the chosen residue-field map to `Ksep`. -/
private theorem etaleSepClosureNeighborhoodLocalization_existsUnique_toStrictHenselization
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    ∃! f :
        Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →ₐ[Localization.AtPrime p] Rsh,
      ∃ hfq :
          maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) =
            Ideal.comap (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
              (maximalIdeal Rsh),
        (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
            (Ideal.ResidueField.map
              (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
              (maximalIdeal Rsh)
              (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
              hfq) =
          etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A := by
  let _ : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep :=
    RingHom.toAlgebra (localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep)
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  let _ : Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    etaleSepClosureNeighborhoodLocalization_etale p A
  exact
    existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap
      (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
      (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A)
      (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι)
      (strictHenselizationMaximalIdealResidueFieldCompat p Rsh ι hι)
      (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A)
      (etaleSepClosureNeighborhoodLocalization_residueFieldToSepClosure_comp p A)

/-- The canonical morphism from the localized neighborhood `S_q` to a chosen strict
henselization `(Rₚ)^sh`. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    (etaleSepClosureNeighborhoodLocalizationDiagram R p Ksep).obj A ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  CommAlgCat.ofHom <|
    Classical.choose <|
      etaleSepClosureNeighborhoodLocalization_existsUnique_toStrictHenselization p Rsh ι hι A

/-- The chosen strict henselization `(Rₚ)^sh`, viewed as an `R`-algebra by restriction of
scalars. -/
private noncomputable abbrev etaleSepClosureNeighborhoodSourceStrictHenselizationPoint
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh] :
    CommAlgCat R :=
  let _ : Algebra R Rsh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rsh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.of R Rsh

/-- The canonical morphism from the source neighborhood `S` to a chosen strict henselization
`(Rₚ)^sh`, obtained by composing `S → S_q` with the canonical localized map `S_q → (Rₚ)^sh`. -/
private noncomputable def etaleSepClosureNeighborhoodSourceToStrictHenselizationHom
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    (etaleSepClosureNeighborhoodSourceDiagram R p Ksep).obj A ⟶
      etaleSepClosureNeighborhoodSourceStrictHenselizationPoint p Rsh :=
  let _ : Algebra R Rsh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rsh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.ofHom <|
    { toRingHom :=
        (etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
          p Rsh ι hι A).hom.toRingHom.comp
          (algebraMap A.obj.left (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
      commutes' := by
        sorry }

/-- The canonical cocone from the localized neighborhood diagram to a chosen strict
henselization `(Rₚ)^sh`. -/
noncomputable def etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselization
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    Cocone (etaleSepClosureNeighborhoodLocalizationDiagram R p Ksep) where
  pt := CommAlgCat.of (Localization.AtPrime p) Rsh
  ι :=
    { app := etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
        p Rsh ι hι
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

/-- The canonical cocone from the source neighborhood diagram to a chosen strict henselization
`(Rₚ)^sh`, viewed in `CommAlgCat R`. -/
noncomputable def etaleSepClosureNeighborhoodSourceCoconeToStrictHenselization
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    Cocone (etaleSepClosureNeighborhoodSourceDiagram R p Ksep) where
  pt := etaleSepClosureNeighborhoodSourceStrictHenselizationPoint p Rsh
  ι :=
    { app := etaleSepClosureNeighborhoodSourceToStrictHenselizationHom
        p Rsh ι hι
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

-- Proof sketch: the triple `(R, p, κ(p) → Ksep)` gives an initial source of objects; tensor
-- products of étale neighborhoods remain étale and their induced maps to `Ksep` determine common
-- refinements; and the standard iterated fiber-product construction over `Ksep` equalizes
-- parallel morphisms.
/-- Lemma 10.155.11 (1): the category of triples `(S, q, φ)` with `R → S` étale, `q` lying over
`p`, and `φ : κ(q) → Ksep` a `κ(p)`-algebra map is filtered. -/
theorem etaleSepClosureNeighborhoodCategory_isFiltered :
    IsFiltered (EtaleSepClosureNeighborhoodCategory R p Ksep) := sorry

-- Proof sketch: localizing at the chosen prime of each triple produces the standard strict
-- étale-neighborhood diagram of `Rₚ`; the chosen map to `Ksep` fixes the residue-field comparison
-- to the strict henselization; and Lemma `10.155.9` gives the compatible maps into a chosen
-- strict henselization with residue field identified with `Ksep`.
/-- Lemma 10.155.11 (2): the canonical cocone from the source diagram `(S, q, φ) ↦ S` to a chosen
strict henselization `(Rₚ)^sh`, viewed in `CommAlgCat R`, is colimiting. -/
noncomputable def etaleSepClosureNeighborhoodSourceCoconeToStrictHenselizationIsColimit
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    IsColimit (etaleSepClosureNeighborhoodSourceCoconeToStrictHenselization p Rsh ι hι) := by
  sorry

-- Proof sketch: after replacing each object `(S, q, φ)` by its localization `S_q`, the filtered
-- diagram is the standard strict étale-neighborhood presentation of `(Rₚ)^sh`; the residue-field
-- comparison with `Ksep` fixes the canonical morphisms into the chosen strict henselization.
/-- Lemma 10.155.11 (3): the canonical cocone from the localized neighborhood diagram
`(S, q, φ) ↦ S_q` to a chosen strict henselization `(Rₚ)^sh` is colimiting. -/
noncomputable def etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselizationIsColimit
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    IsColimit (etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselization p Rsh ι hι) := by
  sorry

end StrictHenselizationTarget

end
