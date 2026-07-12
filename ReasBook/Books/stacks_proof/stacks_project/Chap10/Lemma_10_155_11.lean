import Mathlib
import StacksProject_2024.Chap10.Lemma_10_127_4
import StacksProject_2024.Chap10.Lemma_10_154_2
import StacksProject_2024.Chap10.Lemma_10_154_6
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
    IsLocalization (maximalIdeal A).primeCompl A := by
  -- Proof comment: outside the maximal ideal of a local ring means not a nonunit, hence a unit.
  apply IsLocalization.at_units
  intro x hx
  change IsUnit x
  have hx' : x ∉ maximalIdeal A := by
    simpa [Ideal.primeCompl] using hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx'
  exact not_not.mp hx'

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

/-- Helper for Chap10 Lemma 10 155 11: a morphism over `Ksep` preserves the chosen structural
map to `Ksep`. -/
private theorem sepClosurePointedAlgebraStructureMap_comp
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : SepClosurePointedAlgebraCategory R Ksep} (f : A ⟶ B) :
    (sepClosurePointedAlgebraToSepClosure R p Ksep B).comp
        (sepClosurePointedAlgebraHom R p Ksep f) =
      sepClosurePointedAlgebraToSepClosure R p Ksep A := by
  -- Proof comment: the statement is exactly the triangle identity of a morphism in the
  -- over-category, read after forgetting to ring homomorphisms.
  ext x
  simpa [sepClosurePointedAlgebraToSepClosure, sepClosurePointedAlgebraHom,
    RingHom.comp_apply] using ConcreteCategory.congr_hom f.w x

/-- Helper for Chap10 Lemma 10 155 11: the structural map to `Ksep` is an `R`-algebra map. -/
private theorem sepClosurePointedAlgebraToSepClosure_algebraMap
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : SepClosurePointedAlgebraCategory R Ksep) (x : R) :
    sepClosurePointedAlgebraToSepClosure R p Ksep A (algebraMap R A.left x) =
      algebraMap R Ksep x := by
  -- Proof comment: this is the algebra-map compatibility carried by the `CommAlgCat R` map
  -- from the object to the fixed target.
  simpa [sepClosurePointedAlgebraToSepClosure] using A.hom.hom.commutes x

/-- The chosen prime of the source object is the comap of the chosen prime of the target. -/
private theorem sepClosurePointedAlgebraKernel_comap (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : SepClosurePointedAlgebraCategory R Ksep} (f : A ⟶ B) :
    sepClosurePointedAlgebraKernel R p Ksep A =
      Ideal.comap (sepClosurePointedAlgebraHom R p Ksep f)
        (sepClosurePointedAlgebraKernel R p Ksep B) := by
  -- Proof comment: after replacing the two maps to `Ksep` by the over-category triangle,
  -- equality of kernels is pointwise equality of zero fibers.
  have hcomp := sepClosurePointedAlgebraStructureMap_comp R p Ksep f
  ext x
  change (sepClosurePointedAlgebraToSepClosure R p Ksep A x = 0) ↔
    (sepClosurePointedAlgebraToSepClosure R p Ksep B
      (sepClosurePointedAlgebraHom R p Ksep f x) = 0)
  rw [← congrFun (congrArg DFunLike.coe hcomp) x]
  rfl

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
    p = Ideal.comap (algebraMap R A.left) (sepClosurePointedAlgebraKernel R p Ksep A) := by
  -- Proof comment: contracting the kernel along `R → A` gives the kernel of
  -- `R → κ(p) → Ksep`; the second map is injective because both rings are fields.
  ext x
  change x ∈ p ↔ sepClosurePointedAlgebraToSepClosure R p Ksep A (algebraMap R A.left x) = 0
  rw [sepClosurePointedAlgebraToSepClosure_algebraMap R p Ksep A x]
  rw [IsScalarTower.algebraMap_apply R p.ResidueField Ksep x]
  constructor
  · intro hx
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hx]
    simp
  · intro hx
    have hx' :
        (algebraMap p.ResidueField Ksep) (algebraMap R p.ResidueField x) =
          (algebraMap p.ResidueField Ksep) 0 := by
      simpa using hx
    have hxres : algebraMap R p.ResidueField x = 0 :=
      (algebraMap p.ResidueField Ksep).injective hx'
    exact Ideal.algebraMap_residueField_eq_zero.mp hxres

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
      RingHom.id _ := by
  -- Proof comment: identity functoriality is the canonical identity theorem for prime
  -- localization maps.
  simpa using
    (Localization.localRingHom_id
      (I := sepClosurePointedAlgebraKernel R p Ksep A.obj))

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
          (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)) := by
  -- Proof comment: the composite transition is exactly the canonical composition theorem for
  -- local maps between prime localizations.
  simpa [etaleSepClosureNeighborhoodHom] using
    (Localization.localRingHom_comp
      (I := sepClosurePointedAlgebraKernel R p Ksep A.obj)
      (J := sepClosurePointedAlgebraKernel R p Ksep B.obj)
      (K := sepClosurePointedAlgebraKernel R p Ksep C.obj)
      (f := etaleSepClosureNeighborhoodHom R p Ksep f)
      (hIJ := sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)
      (g := etaleSepClosureNeighborhoodHom R p Ksep g)
      (hJK := sepClosurePointedAlgebraKernel_comap R p Ksep g.hom))

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
        etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep B := by
  -- Proof comment: first identify the raw square over `R`, then localize that square by
  -- `Localization.localRingHom_comp`.
  have hcomp :
      (etaleSepClosureNeighborhoodHom R p Ksep f).comp (algebraMap R A.obj.left) =
        algebraMap R B.obj.left := by
    ext x
    simpa [etaleSepClosureNeighborhoodHom, sepClosurePointedAlgebraHom, RingHom.comp_apply] using
      f.hom.left.hom.commutes x
  simpa [etaleSepClosureNeighborhoodLocalizationAlgebraMap, hcomp] using
    (Localization.localRingHom_comp
      (I := p)
      (J := sepClosurePointedAlgebraKernel R p Ksep A.obj)
      (K := sepClosurePointedAlgebraKernel R p Ksep B.obj)
      (f := algebraMap R A.obj.left)
      (hIJ := sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj)
      (g := etaleSepClosureNeighborhoodHom R p Ksep f)
      (hJK := sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)).symm

/-- The localized neighborhood `(S, q, φ) ↦ S_q` viewed as an `Rₚ`-algebra. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationObject
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    CommAlgCat (Localization.AtPrime p) :=
  letI : Algebra (Localization.AtPrime p)
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
  letI : Algebra (Localization.AtPrime p)
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

/-- Helper for Chap10 Lemma 10 155 11: in prime-residue-field form, the residue map induced by
the structural map to `Ksep` is compatible with the fixed map from `κ(p)` to `Ksep`. -/
private theorem sepClosureKernelResidueFieldToSepClosure_comp_algebraMapResidue
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    (sepClosurePointedAlgebraKernelResidueFieldToSepClosure p A).comp
        (Ideal.ResidueField.map p (sepClosurePointedAlgebraKernel R p Ksep A)
          (algebraMap R A.left)
          (sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A)) =
      algebraMap p.ResidueField Ksep := by
  -- Proof comment: residue-field maps are determined by classes of elements of `R`; on those
  -- generators the lift out of `κ(ker(S → Ksep))` computes by the structural map.
  apply Ideal.ResidueField.ringHom_ext
  ext x
  simp [Ideal.ResidueField.map_algebraMap,
    sepClosurePointedAlgebraKernelResidueFieldToSepClosure,
    sepClosurePointedAlgebraToSepClosure_algebraMap,
    IsScalarTower.algebraMap_apply R p.ResidueField Ksep]

/-- Helper for Chap10 Lemma 10 155 11: an étale algebra map is a one-object filtered colimit of
étale algebras. -/
private theorem isFilteredColimitOfEtale_of_etaleAlgebraMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : (algebraMap A B).Etale) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) := by
  -- Proof comment: translate the source-facing owner to the raw categorical `ind` owner and use
  -- the canonical inclusion of étale maps into ind-étale maps.
  rw [← RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale]
  exact
    (CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale))
      (CommRingCat.ofHom (algebraMap A B))
      (by simpa [CommRingCat.etale] using hAB)

/-- Helper for Chap10 Lemma 10 155 11: composing an étale algebra map with an ind-étale
algebra map is ind-étale. -/
private theorem isFilteredColimitOfEtale_comp_etale
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : (algebraMap A B).Etale)
    (hBC : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap B C)) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A C) := by
  -- Proof comment: promote the étale first leg to an ind-étale map, compose the two
  -- ind-étale maps, then identify the composite with the tower algebra map.
  have hABind : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) :=
    isFilteredColimitOfEtale_of_etaleAlgebraMap hAB
  have hcomp :
      RingHom.IsFilteredColimitOfEtale.{u, u, u}
        ((algebraMap B C).comp (algebraMap A B)) :=
    RingHom.isFilteredColimitOfEtale_comp (algebraMap A B) (algebraMap B C) hABind hBC
  simpa [IsScalarTower.algebraMap_eq A B C] using hcomp

/-- Helper for Chap10 Lemma 10 155 11: a bijective ring map is ind-étale. -/
private theorem isFilteredColimitOfEtale_of_bijective
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} f := by
  -- Proof comment: give the target the algebra structure induced by `f`; bijective maps are
  -- étale, and the one-object étale adapter records this as an ind-étale presentation.
  letI : Algebra A B := f.toAlgebra
  have hfEtale : f.Etale := RingHom.Etale.of_bijective hf
  have halgEtale : (algebraMap A B).Etale := by
    simpa [RingHom.algebraMap_toAlgebra] using hfEtale
  simpa [RingHom.algebraMap_toAlgebra] using
    isFilteredColimitOfEtale_of_etaleAlgebraMap (A := A) (B := B) halgEtale

/-- Helper for Chap10 Lemma 10 155 11: ind-étaleness transports across an algebra equivalence
of targets. -/
private theorem isFilteredColimitOfEtale_of_algEquiv
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C)
    (hAB : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B)) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A C) := by
  -- Proof comment: compose the given ind-étale algebra map with the ind-étale map underlying
  -- the equivalence, then rewrite the composite to the target algebra map.
  have he : RingHom.IsFilteredColimitOfEtale.{u, u, u} e.toRingHom :=
    isFilteredColimitOfEtale_of_bijective e.toRingHom e.bijective
  have hcomp :
      RingHom.IsFilteredColimitOfEtale.{u, u, u}
        (e.toRingHom.comp (algebraMap A B)) :=
    RingHom.isFilteredColimitOfEtale_comp (algebraMap A B) e.toRingHom hAB he
  have hmap : e.toRingHom.comp (algebraMap A B) = algebraMap A C := by
    ext x
    exact e.commutes x
  rw [hmap] at hcomp
  exact hcomp

/-- Helper for Chap10 Lemma 10 155 11: the localization `S_q` of an étale neighborhood is
étale over `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_etale
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    letI : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) := by
  -- Proof comment: after installing the algebra structure induced by the local homomorphism,
  -- mathlib's localization/base-change instances recognize the localized étale map.
  -- TODO: supply the finite-presentation/base-change theorem for localization at the prime
  -- selected by the map to `Ksep`; the formal-étale part is standard localization stability,
  -- but the current API does not synthesize the full `Algebra.Etale` instance automatically.
  sorry

/-- Helper for Chap10 Lemma 10 155 11: the localization `S_q` of an étale neighborhood is an
ind-étale algebra over `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_isFilteredColimitOfEtale
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    letI : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))) := by
  -- Route correction: instead of constructing a separate prime-localization colimit, use the
  -- localized finite-stage étale map and then convert that single stage to the ind-étale owner.
  -- Proof comment: use the finite-stage étale result for the localized map, then regard that
  -- single étale stage as an ind-étale presentation.
  letI : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  have hEtale : (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).Etale := by
    exact (RingHom.etale_algebraMap (R := Localization.AtPrime p)
      (S := Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).2
      (etaleSepClosureNeighborhoodLocalization_etale p A)
  exact isFilteredColimitOfEtale_of_etaleAlgebraMap hEtale

/-- The maximal ideal of `S_q` lies over the maximal ideal of `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_maximalIdeal_under
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).under
        (Localization.AtPrime p) =
      maximalIdeal (Localization.AtPrime p) := by
  -- Proof comment: after installing the algebra structure coming from the localized map, the
  -- map is local by the canonical localization API, so maximal ideals contract canonically.
  dsimp only
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  let _ : IsLocalHom (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))) := by
    simpa [RingHom.algebraMap_toAlgebra, etaleSepClosureNeighborhoodLocalizationAlgebraMap] using
      (Localization.isLocalHom_localRingHom p
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (algebraMap R A.obj.left)
        (sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj))
  simpa [Ideal.under_def] using
    (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))))

/-- Helper for Chap10 Lemma 10 155 11: after identifying the closed points of prime
localizations with prime residue fields, the residue-field map of the localized algebra map is
the original residue-field map. -/
private theorem primeLocalResidueFieldMap_compat
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hq : p = Ideal.comap (algebraMap A B) q) :
    let f := Localization.localRingHom p q (algebraMap A B) hq
    (maximalIdealResidueFieldEquiv (Localization.AtPrime q)).toRingHom.comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p))
          (maximalIdeal (Localization.AtPrime q))
          f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (Ideal.ResidueField.map p q (algebraMap A B) hq).comp
        (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom := by
  -- Proof comment: this is exactly the local-ring residue-field compatibility theorem, with the
  -- local map specialized to the canonical map between prime localizations.
  let f := Localization.localRingHom p q (algebraMap A B) hq
  simpa [f] using
    (maximalIdealResidueFieldEquiv_comp_residueFieldMap (f := f))

/-- Helper for Chap10 Lemma 10 155 11: the residue-field map induced by the identity map of a
local ring is the identity. -/
private theorem maximalIdealResidueField_map_id
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal A)
      (algebraMap A A)
      (IsLocalRing.maximalIdeal_comap (algebraMap A A)).symm =
      RingHom.id _ := by
  -- Proof comment: residue-field maps are determined by residue classes of elements, where the
  -- identity local homomorphism acts trivially.
  apply Ideal.ResidueField.ringHom_ext
  ext x
  simp [Ideal.ResidueField.map_algebraMap]

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
  -- Route correction: avoid generatorwise simplification on `Localization.AtPrime p`; compare
  -- the whole RingHom composition through the prime-local residue-field compatibility theorem.
  dsimp only
  let _ : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep :=
    RingHom.toAlgebra (localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep)
  have hsource :
      (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A).comp
          (Ideal.ResidueField.map
            (maximalIdeal (Localization.AtPrime p))
            (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
            (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
            (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A).symm) =
        localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
    -- Proof comment: the local residue map between prime localizations is the original prime
    -- residue-field map after the two maximal-ideal identifications.
    calc
      (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A).comp
          (Ideal.ResidueField.map
            (maximalIdeal (Localization.AtPrime p))
            (maximalIdeal
              (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
            (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
            (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A).symm)
        =
          (sepClosurePointedAlgebraKernelResidueFieldToSepClosure p A.obj).comp
            ((primeLocalizationMaximalResidueFieldEquiv
              (sepClosurePointedAlgebraKernel R p Ksep A.obj)).toRingHom.comp
              (Ideal.ResidueField.map
                (maximalIdeal (Localization.AtPrime p))
                (maximalIdeal
                  (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
                (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
                (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A).symm)) := by
            rw [etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure,
              RingHom.comp_assoc]
      _ =
          (sepClosurePointedAlgebraKernelResidueFieldToSepClosure p A.obj).comp
            ((Ideal.ResidueField.map p (sepClosurePointedAlgebraKernel R p Ksep A.obj)
              (algebraMap R A.obj.left)
              (sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj)).comp
              (primeLocalizationMaximalResidueFieldEquiv p).toRingHom) := by
            exact congrArg
              (fun g ↦ (sepClosurePointedAlgebraKernelResidueFieldToSepClosure p A.obj).comp g)
              (by
                simpa [primeLocalizationMaximalResidueFieldEquiv,
                  etaleSepClosureNeighborhoodLocalizationAlgebraMap] using
                  (primeLocalResidueFieldMap_compat (p := p)
                    (q := sepClosurePointedAlgebraKernel R p Ksep A.obj)
                    (hq := sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj)))
      _ =
          ((sepClosurePointedAlgebraKernelResidueFieldToSepClosure p A.obj).comp
            (Ideal.ResidueField.map p (sepClosurePointedAlgebraKernel R p Ksep A.obj)
              (algebraMap R A.obj.left)
              (sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj))).comp
              (primeLocalizationMaximalResidueFieldEquiv p).toRingHom := by
            rw [RingHom.comp_assoc]
      _ = localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
            rw [sepClosureKernelResidueFieldToSepClosure_comp_algebraMapResidue]
  have htarget :
      (algebraMap (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep).comp
          (Ideal.ResidueField.map
            (maximalIdeal (Localization.AtPrime p))
            (maximalIdeal (Localization.AtPrime p))
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime p))
            (IsLocalRing.maximalIdeal_comap
              (algebraMap (Localization.AtPrime p) (Localization.AtPrime p))).symm) =
        localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
    -- Proof comment: the target-side map is the chosen residue map followed by the identity
    -- residue map of `R_p`.
    rw [maximalIdealResidueField_map_id (Localization.AtPrime p)]
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply, RingHom.algebraMap_toAlgebra]
  rw [hsource, htarget]

/-- Helper for Chap10 Lemma 10 155 11: the localized residue-field comparison computes on
residue classes coming from `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_residueFieldToSepClosure_apply
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) (x : Localization.AtPrime p) :
    (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A)
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p))
          (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
          (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
          (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A).symm
          (algebraMap (Localization.AtPrime p)
            (maximalIdeal (Localization.AtPrime p)).ResidueField x)) =
      localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep
        (algebraMap (Localization.AtPrime p)
          (maximalIdeal (Localization.AtPrime p)).ResidueField x) := by
  -- Proof comment: specialize the already proved RingHom equality to the residue class of `x`
  -- and normalize the target-side identity residue map.
  let _ : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep :=
    RingHom.toAlgebra (localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep)
  have h := congrFun (congrArg DFunLike.coe
    (etaleSepClosureNeighborhoodLocalization_residueFieldToSepClosure_comp p A))
    (algebraMap (Localization.AtPrime p)
      (maximalIdeal (Localization.AtPrime p)).ResidueField x)
  rw [maximalIdealResidueField_map_id (Localization.AtPrime p)] at h
  simpa [Ideal.ResidueField.map_algebraMap, RingHom.algebraMap_toAlgebra] using h

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

/-- Helper for Chap10 Lemma 10 155 11: the strict-henselization residue-field comparison
computes on residue classes coming from `Rₚ`. -/
private theorem strictHenselizationMaximalIdealResidueFieldCompat_apply
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (x : Localization.AtPrime p) :
    ι
        (maximalIdealResidueFieldEquiv Rsh
          (Ideal.ResidueField.map
            (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
            (algebraMap (Localization.AtPrime p) Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh)).symm
            (algebraMap (Localization.AtPrime p)
              (maximalIdeal (Localization.AtPrime p)).ResidueField x))) =
      localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep
        (algebraMap (Localization.AtPrime p)
          (maximalIdeal (Localization.AtPrime p)).ResidueField x) := by
  -- Proof comment: specialize the strict residue-field RingHom equality to the residue class
  -- of `x` and compute the residue-field map on that class.
  have h := congrFun (congrArg DFunLike.coe
    (strictHenselizationMaximalIdealResidueFieldCompat p Rsh ι hι))
    (algebraMap (Localization.AtPrime p)
      (maximalIdeal (Localization.AtPrime p)).ResidueField x)
  simpa [RingHom.comp_apply] using h

/-- Helper for Chap10 Lemma 10 155 11: a residue-field condition after identifying
`κ(Rsh)` with `Ksep` is equivalent to the transported condition valued in `κ(Rsh)`. -/
private theorem strictHenselizationResidueMap_eq_iff
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    ∀ (f :
        Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →ₐ[
          Localization.AtPrime p] Rsh)
      (hfq :
        maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) =
          Ideal.comap
            (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
            (maximalIdeal Rsh)),
      (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
          (Ideal.ResidueField.map
            (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
            (maximalIdeal Rsh)
            (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
            hfq) =
        etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A ↔
      Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
          (maximalIdeal Rsh)
          (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
          hfq =
        (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).symm.toRingHom.comp
          (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A) := by
  dsimp only
  intro f hfq
  constructor
  · intro h
    -- Proof comment: insert the inverse residue equivalence on the left and then use the
    -- given `Ksep`-valued equality.
    calc
      Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
          (maximalIdeal Rsh)
          (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
          hfq
        =
          (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).symm.toRingHom.comp
            ((strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
              (Ideal.ResidueField.map
                (maximalIdeal
                  (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
                (maximalIdeal Rsh)
                (f :
                  Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
                hfq)) := by
            ext x
            simp [RingHom.comp_apply]
      _ =
          (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).symm.toRingHom.comp
            (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A) := by
            rw [h]
  · intro h
    -- Proof comment: after rewriting to the inverse-transported map, the equivalence cancels
    -- its inverse pointwise.
    calc
      (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
          (Ideal.ResidueField.map
            (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
            (maximalIdeal Rsh)
            (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
            hfq)
        =
          (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
            ((strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).symm.toRingHom.comp
              (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A)) := by
            rw [h]
      _ = etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A := by
            ext x
            simp [RingHom.comp_apply]

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
  -- Proof comment: apply the ind-étale henselian lifting theorem to the local ring map
  -- `Rₚ → S_q`, then transport its residue-field conclusion across the chosen strict residue
  -- equivalence to the `Ksep`-valued formulation of this file.
  dsimp only
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  let q : Ideal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))
  let τ : q.ResidueField →+* (maximalIdeal Rsh).ResidueField :=
    (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).symm.toRingHom.comp
      (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A)
  have hq : q.under (Localization.AtPrime p) = (maximalIdeal Rsh).under (Localization.AtPrime p) := by
    dsimp [q]
    calc
      (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).under
          (Localization.AtPrime p)
        = maximalIdeal (Localization.AtPrime p) :=
            etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A
      _ = (maximalIdeal Rsh).under (Localization.AtPrime p) := by
            symm
            simpa [Ideal.under_def] using
              (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh))
  have hτ :
      τ.comp (Ideal.ResidueField.map (q.under (Localization.AtPrime p)) q
        (algebraMap (Localization.AtPrime p)
          (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))) rfl) =
        Ideal.ResidueField.map (q.under (Localization.AtPrime p)) (maximalIdeal Rsh)
          (algebraMap (Localization.AtPrime p) Rsh) hq := by
    -- TODO: prove this by a transport-stable residue-field generator lemma for
    -- `q.under (Localization.AtPrime p) = maximalIdeal (Localization.AtPrime p)`. Direct
    -- rewriting changes the dependent `ResidueField` source and blocks simplification.
    sorry
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap
      (hA := etaleSepClosureNeighborhoodLocalization_isFilteredColimitOfEtale p A)
      (q := q) hq τ hτ
  refine ⟨f, ?_, ?_⟩
  · rcases hf with ⟨hfq, hfτ⟩
    refine ⟨hfq, ?_⟩
    exact (strictHenselizationResidueMap_eq_iff p Rsh ι A f hfq).mpr hfτ
  · intro g hg
    apply huniq g
    rcases hg with ⟨hgq, hgτ⟩
    refine ⟨hgq, ?_⟩
    exact (strictHenselizationResidueMap_eq_iff p Rsh ι A g hgq).mp hgτ

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

/-- Helper for Chap10 Lemma 10 155 11: the source-to-strict-henselization map respects the
restricted `R`-algebra structures. -/
private theorem etaleSepClosureNeighborhoodSourceToStrictHenselizationHom_commutes
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) (x : R) :
    (etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
        p Rsh ι hι A).hom.toRingHom
      (algebraMap A.obj.left
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))
        (algebraMap R A.obj.left x)) =
      ((algebraMap (Localization.AtPrime p) Rsh).comp
        (algebraMap R (Localization.AtPrime p))) x := by
  -- Proof comment: replace the source localization map by the `Rₚ`-algebra structure map, then
  -- use the `Rₚ`-linearity of the chosen strict-henselization morphism.
  have hloc :
      etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A
          (algebraMap R (Localization.AtPrime p) x) =
        algebraMap A.obj.left
          (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))
          (algebraMap R A.obj.left x) :=
    Localization.localRingHom_to_map p
      (sepClosurePointedAlgebraKernel R p Ksep A.obj)
      (algebraMap R A.obj.left)
      (sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj)
      x
  rw [← hloc]
  exact (etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
    p Rsh ι hι A).hom.commutes (algebraMap R (Localization.AtPrime p) x)

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
      commutes' := etaleSepClosureNeighborhoodSourceToStrictHenselizationHom_commutes
        p Rsh ι hι A }

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
        -- TODO: prove both sides satisfy the same strict-henselian lifting specification and
        -- identify them by uniqueness from
        -- `etaleSepClosureNeighborhoodLocalization_existsUnique_toStrictHenselization`.
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
        -- Proof comment: reduce source naturality to localized naturality and compute the
        -- localized transition map on source-ring generators.
        ext x
        have hnat :=
          (etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselization p Rsh ι hι).w f
        have hx :=
          congrFun (congrArg DFunLike.coe (congrArg CommAlgCat.Hom.hom hnat))
            (algebraMap A.obj.left
              (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) x)
        have hmap := Localization.localRingHom_to_map
          (sepClosurePointedAlgebraKernel R p Ksep A.obj)
          (sepClosurePointedAlgebraKernel R p Ksep B.obj)
          (etaleSepClosureNeighborhoodHom R p Ksep f)
          (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom) x
        have hxmap := congrArg
          (fun y =>
            (etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
              p Rsh ι hι B).hom.toRingHom y)
          hmap
        exact hxmap.symm.trans hx }

-- Proof sketch: the triple `(R, p, κ(p) → Ksep)` gives an initial source of objects; tensor
-- products of étale neighborhoods remain étale and their induced maps to `Ksep` determine common
-- refinements; and the standard iterated fiber-product construction over `Ksep` equalizes
-- parallel morphisms.
/-- Lemma 10.155.11 (1): the category of triples `(S, q, φ)` with `R → S` étale, `q` lying over
`p`, and `φ : κ(q) → Ksep` a `κ(p)`-algebra map is filtered. -/
@[stacks 04GW]
theorem etaleSepClosureNeighborhoodCategory_isFiltered :
    IsFiltered (EtaleSepClosureNeighborhoodCategory R p Ksep) := by
  -- TODO: construct common refinements by tensor products of étale neighborhoods and equalize
  -- parallel morphisms after the standard separably closed residue-field refinement.
  sorry

-- Proof sketch: localizing at the chosen prime of each triple produces the standard strict
-- étale-neighborhood diagram of `Rₚ`; the chosen map to `Ksep` fixes the residue-field comparison
-- to the strict henselization; and Lemma `10.155.9` gives the compatible maps into a chosen
-- strict henselization with residue field identified with `Ksep`.
/-- Lemma 10.155.11 (2): the canonical cocone from the source diagram `(S, q, φ) ↦ S` to a chosen
strict henselization `(Rₚ)^sh`, viewed in `CommAlgCat R`, is colimiting. -/
@[stacks 04GW]
noncomputable def etaleSepClosureNeighborhoodSourceCoconeToStrictHenselizationIsColimit
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    IsColimit (etaleSepClosureNeighborhoodSourceCoconeToStrictHenselization p Rsh ι hι) := by
  -- TODO: compare the source diagram with the localized strict-henselization presentation by
  -- denominator-inversion refinements, then transport the colimit structure.
  sorry

-- Proof sketch: after replacing each object `(S, q, φ)` by its localization `S_q`, the filtered
-- diagram is the standard strict étale-neighborhood presentation of `(Rₚ)^sh`; the residue-field
-- comparison with `Ksep` fixes the canonical morphisms into the chosen strict henselization.
/-- Lemma 10.155.11 (3): the canonical cocone from the localized neighborhood diagram
`(S, q, φ) ↦ S_q` to a chosen strict henselization `(Rₚ)^sh` is colimiting. -/
@[stacks 04GW]
noncomputable def etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselizationIsColimit
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    IsColimit (etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselization p Rsh ι hι) := by
  -- TODO: identify the localized neighborhood diagram with the canonical ind-étale
  -- strict-henselization diagram and use the owner colimit theorem.
  sorry

end StrictHenselizationTarget

end
