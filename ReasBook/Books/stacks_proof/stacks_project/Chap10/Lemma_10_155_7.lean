import Mathlib
import StacksProject_2024.Chap10.Lemma_10_154_6
import StacksProject_2024.Chap10.Lemma_10_154_2
import StacksProject_2024.Chap10.Lemma_10_154_5
import StacksProject_2024.Chap10.Lemma_10_127_4
import StacksProject_2024.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]

open RingHom

/- Domain-style sampling:
* primary domain: local commutative algebra of henselizations of `Localization.AtPrime p`,
  expressed through filtered colimits of étale neighborhoods with fixed residue field `κ(p)`;
* sampled owner declarations of the same kind:
  - `RingHom.IsFilteredColimitOfEtale`;
  - `IsHenselizationOf`;
  - `selectedAlgebrasOverTargetDiagram`;
  - `CommAlgCat.of`.
* best owner abstraction:
  - `source-facing`: the category of étale neighborhoods `(S, q)` of `p` with residue field
    identified with `κ(p)`, together with its canonical source diagram in `CommAlgCat R` and its
    localized diagram in `CommAlgCat (Localization.AtPrime p)`;
  - `core/canonical`: the owner property
    `(algebraMap (Localization.AtPrime p) Rh).IsFilteredColimitOfEtale`;
  - `bridge/view`: colimit comparisons from those source-facing diagrams to a chosen
    henselization `Rh`.
* primitive data:
  - the pointed over-category `Over (CommAlgCat.of R p.ResidueField)`;
  - the étale object property on that over-category;
  - the canonical source diagram and the localized `Localization.AtPrime p`-algebra diagram.
* derived API:
  - the filteredness of the neighborhood category;
  - the colimit realizations of those two diagrams by a chosen henselization.

This file should therefore keep the neighborhood diagrams as source-facing input data, but the main
henselization outputs should prove those diagrams realize the henselization colimit in the ambient
algebra categories, leaving the owner property itself to `IsHenselizationOf`.
-/

/-- The over-category of `R`-algebras equipped with a chosen `R`-algebra map to `κ(p)`. Such a
map packages a prime over `p` with residue field `κ(p)`. -/
abbrev ResidueFieldPointedAlgebraCategory (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :=
  Over (CommAlgCat.of R p.ResidueField)

/-- The object property selecting those `R`-algebras over `κ(p)` whose structure map from `R` is
étale. -/
abbrev etaleResidueFieldPointedAlgebraProperty (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] :
    ObjectProperty (ResidueFieldPointedAlgebraCategory R p) :=
  fun A ↦ RingHom.Etale (algebraMap R A.left)

/-- The category of étale neighborhoods of `p` with residue field identified with `κ(p)`. -/
abbrev EtaleResidueFieldNeighborhoodCategory (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] :=
  (etaleResidueFieldPointedAlgebraProperty R p).FullSubcategory

/-- The diagram sending an étale neighborhood `(S, q)` of `p` to its underlying `R`-algebra `S`. -/
abbrev etaleResidueFieldNeighborhoodSourceDiagram (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] :
    EtaleResidueFieldNeighborhoodCategory R p ⥤ CommAlgCat R :=
  selectedAlgebrasOverTargetDiagram (etaleResidueFieldPointedAlgebraProperty R p)

/-- The structure map from an object over `κ(p)` to the fixed target object of the over-category. -/
private noncomputable abbrev residueFieldPointedAlgebraToResidueField
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : ResidueFieldPointedAlgebraCategory R p) :
    A.left →+* p.ResidueField :=
  let φ := (forget₂ (CommAlgCat R) CommRingCat).map A.hom
  φ.hom

/-- The underlying ring homomorphism of a morphism over `κ(p)`. -/
private abbrev residueFieldPointedAlgebraHom (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    {A B : ResidueFieldPointedAlgebraCategory R p} (f : A ⟶ B) :
    A.left →+* B.left :=
  let φ := f.left
  φ.hom

/-- The underlying ring homomorphism of a morphism in the full subcategory of étale
neighborhoods. -/
private abbrev etaleResidueFieldNeighborhoodHom (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    A.obj.left →+* B.obj.left :=
  residueFieldPointedAlgebraHom R p f.hom

/-- The prime ideal of an object over `κ(p)` is the kernel of its structure map to the fixed
target object. -/
private noncomputable abbrev residueFieldPointedAlgebraKernel
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : ResidueFieldPointedAlgebraCategory R p) :
    Ideal A.left :=
  RingHom.ker (residueFieldPointedAlgebraToResidueField R p A)

-- Proof sketch: for a morphism of objects over `κ(p)`, the defining commutative triangle says that
-- the two maps to `κ(p)` agree after precomposition with the underlying algebra map. Taking kernels
-- gives the required equality of primes.
/-- The chosen prime of the source object is the comap of the chosen prime of the target. -/
private theorem residueFieldPointedAlgebraKernel_comap (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime]
    {A B : ResidueFieldPointedAlgebraCategory R p} (f : A ⟶ B) :
    residueFieldPointedAlgebraKernel R p A =
      Ideal.comap (residueFieldPointedAlgebraHom R p f) (residueFieldPointedAlgebraKernel R p B) :=
  by
    -- Proof comment: rewrite the contraction of a kernel as the kernel of the composite map,
    -- then identify that composite with the source structure map using the over-category triangle.
    rw [residueFieldPointedAlgebraKernel, RingHom.comap_ker]
    have hmap :
        residueFieldPointedAlgebraToResidueField R p A =
          (residueFieldPointedAlgebraToResidueField R p B).comp
            (residueFieldPointedAlgebraHom R p f) := by
      simpa [residueFieldPointedAlgebraToResidueField, residueFieldPointedAlgebraHom] using
        (congrArg (fun e : A.left ⟶ CommAlgCat.of R p.ResidueField =>
          ((forget₂ (CommAlgCat R) CommRingCat).map e).hom) f.w).symm
    exact congrArg RingHom.ker hmap

/-- The kernel of a morphism to the residue field `κ(p)` is a prime ideal. -/
private instance residueFieldPointedAlgebraKernel_isPrime (A : ResidueFieldPointedAlgebraCategory R p) :
    (residueFieldPointedAlgebraKernel R p A).IsPrime :=
  RingHom.ker_isPrime _

-- Proof sketch: the structural map `A.left → κ(p)` is an `R`-algebra map, so its composite with
-- `R → A.left` is the canonical residue map `R → κ(p)`. Taking kernels identifies the chosen
-- prime of `A` with the extension of `p`.
/-- The chosen prime of an object over `κ(p)` lies over `p`. -/
private theorem residueFieldPointedAlgebraKernel_comap_algebraMap
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : ResidueFieldPointedAlgebraCategory R p) :
    p = Ideal.comap (algebraMap R A.left) (residueFieldPointedAlgebraKernel R p A) :=
  by
    -- Proof comment: contraction of the kernel is the kernel of the composite `R → A → κ(p)`.
    -- Since `A.hom` is an `R`-algebra morphism, that composite is the canonical residue map.
    rw [residueFieldPointedAlgebraKernel, RingHom.comap_ker]
    have hmap :
        (residueFieldPointedAlgebraToResidueField R p A).comp (algebraMap R A.left) =
          algebraMap R p.ResidueField := by
      ext x
      simp [residueFieldPointedAlgebraToResidueField]
    rw [hmap, Ideal.ker_algebraMap_residueField]

/-- The canonical `R_p`-algebra map to the localization of an étale neighborhood at its chosen
prime. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationAlgebraMap
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : EtaleResidueFieldNeighborhoodCategory R p) :
    Localization.AtPrime p →+* Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) :=
  Localization.localRingHom
    p
    (residueFieldPointedAlgebraKernel R p A.obj)
    (algebraMap R A.obj.left)
    (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj)

-- Proof sketch: the identity morphism in the over-category induces the identity map on local
-- rings because both maps agree on the image of the source ring, and `Localization.localRingHom`
-- is uniquely determined by that property.
/-- The localization map induced by an identity morphism is the identity. -/
private theorem residueFieldPointedAlgebraLocalization_map_id (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p A.obj)
        (RingHom.id A.obj.left)
        (residueFieldPointedAlgebraKernel_comap R p (𝟙 A.obj)) =
      RingHom.id (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) := by
  -- Proof comment: this is exactly the canonical identity law for `Localization.localRingHom`.
  simpa [etaleResidueFieldNeighborhoodHom, residueFieldPointedAlgebraHom] using
    (Localization.localRingHom_id (I := residueFieldPointedAlgebraKernel R p A.obj))

-- Proof sketch: both sides are local ring maps from the localization of the source to the
-- localization of the target induced by the same composite algebra map. They agree on the image of
-- the source ring, so uniqueness of `Localization.localRingHom` identifies them.
/-- Localization along a composite morphism agrees with the composite of the localization maps. -/
private theorem residueFieldPointedAlgebraLocalization_map_comp (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    {A B C : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) (g : B ⟶ C) :
    Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p C.obj)
        ((etaleResidueFieldNeighborhoodHom R p g).comp (etaleResidueFieldNeighborhoodHom R p f))
        (residueFieldPointedAlgebraKernel_comap R p (f.hom ≫ g.hom)) =
      (Localization.localRingHom
          (residueFieldPointedAlgebraKernel R p B.obj)
          (residueFieldPointedAlgebraKernel R p C.obj)
          (etaleResidueFieldNeighborhoodHom R p g)
          (residueFieldPointedAlgebraKernel_comap R p g.hom)).comp
        (Localization.localRingHom
          (residueFieldPointedAlgebraKernel R p A.obj)
          (residueFieldPointedAlgebraKernel R p B.obj)
          (etaleResidueFieldNeighborhoodHom R p f)
          (residueFieldPointedAlgebraKernel_comap R p f.hom)) := by
  -- Proof comment: the target is precisely the functoriality theorem for
  -- `Localization.localRingHom`, after expanding the underlying over-category morphisms.
  simpa [etaleResidueFieldNeighborhoodHom, residueFieldPointedAlgebraHom] using
    (Localization.localRingHom_comp
      (residueFieldPointedAlgebraKernel R p A.obj)
      (residueFieldPointedAlgebraKernel R p B.obj)
      (residueFieldPointedAlgebraKernel R p C.obj)
      (etaleResidueFieldNeighborhoodHom R p f)
      (residueFieldPointedAlgebraKernel_comap R p f.hom)
      (etaleResidueFieldNeighborhoodHom R p g)
      (residueFieldPointedAlgebraKernel_comap R p g.hom))

-- Proof sketch: both sides are local ring maps from `R_p` to `T_r`, induced by the same composite
-- `R → S → T`, and they agree on the image of `R`, so uniqueness of `Localization.localRingHom`
-- identifies them.
/-- The transition maps in the localized neighborhood diagram are `R_p`-algebra maps. -/
private theorem etaleResidueFieldNeighborhoodLocalization_map_commutes
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    (Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p B.obj)
        (etaleResidueFieldNeighborhoodHom R p f)
        (residueFieldPointedAlgebraKernel_comap R p f.hom)).comp
      (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A) =
        etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p B :=
  by
    -- Proof comment: functoriality of `Localization.localRingHom` identifies the composite; the
    -- residual simplification is exactly algebra-linearity of the underlying neighborhood map.
    simpa [etaleResidueFieldNeighborhoodLocalizationAlgebraMap,
      etaleResidueFieldNeighborhoodHom, residueFieldPointedAlgebraHom,
      RingHom.algebraMap_toAlgebra] using
      (Localization.localRingHom_comp
        p
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p B.obj)
        (algebraMap R A.obj.left)
        (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj)
        (etaleResidueFieldNeighborhoodHom R p f)
        (residueFieldPointedAlgebraKernel_comap R p f.hom)).symm

/-- Helper for Chap10 Lemma 10 155 7: the localized transition map is compatible with
the `R_p`-algebra structures pointwise. -/
private theorem etaleResidueFieldNeighborhoodLocalizationMorphism_commutes
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    ∀ x : Localization.AtPrime p,
      (Localization.localRingHom
          (residueFieldPointedAlgebraKernel R p A.obj)
          (residueFieldPointedAlgebraKernel R p B.obj)
          (etaleResidueFieldNeighborhoodHom R p f)
          (residueFieldPointedAlgebraKernel_comap R p f.hom))
        ((etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A) x) =
        (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p B) x := by
  intro x
  -- Proof comment: apply the ring-hom equality from the functoriality lemma to the chosen
  -- element of `R_p`.
  exact congrArg
    (fun g : Localization.AtPrime p →+*
        Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj) ↦ g x)
    (etaleResidueFieldNeighborhoodLocalization_map_commutes R p f)

/-- The localized neighborhood diagram sending `(S, q)` to the `R_p`-algebra `S_q`. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationObject
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : EtaleResidueFieldNeighborhoodCategory R p) :
    CommAlgCat (Localization.AtPrime p) :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  CommAlgCat.of (Localization.AtPrime p)
    (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))

/-- The induced `R_p`-algebra map on localized neighborhoods. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationMorphism
    (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    etaleResidueFieldNeighborhoodLocalizationObject R p A ⟶
      etaleResidueFieldNeighborhoodLocalizationObject R p B :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p B)
  CommAlgCat.ofHom <|
    { toRingHom :=
        Localization.localRingHom
          (residueFieldPointedAlgebraKernel R p A.obj)
          (residueFieldPointedAlgebraKernel R p B.obj)
          (etaleResidueFieldNeighborhoodHom R p f)
          (residueFieldPointedAlgebraKernel_comap R p f.hom)
      commutes' := etaleResidueFieldNeighborhoodLocalizationMorphism_commutes R p f }

/-- Helper for Chap10 Lemma 10 155 7: the localized diagram sends identity morphisms to
identity morphisms. -/
private theorem etaleResidueFieldNeighborhoodLocalizationMorphism_id
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    etaleResidueFieldNeighborhoodLocalizationMorphism R p (𝟙 A) =
      𝟙 (etaleResidueFieldNeighborhoodLocalizationObject R p A) := by
  -- Proof comment: reduce morphism equality to equality of underlying localized ring maps and use
  -- the identity law for `Localization.localRingHom`.
  apply CommAlgCat.hom_ext
  exact DFunLike.ext _ _ fun x ↦
    congrArg
      (fun g : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+*
          Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) ↦ g x)
      (residueFieldPointedAlgebraLocalization_map_id R p A)

/-- Helper for Chap10 Lemma 10 155 7: the localized diagram preserves composition of
morphisms. -/
private theorem etaleResidueFieldNeighborhoodLocalizationMorphism_comp
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    {A B C : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) (g : B ⟶ C) :
    etaleResidueFieldNeighborhoodLocalizationMorphism R p (f ≫ g) =
      etaleResidueFieldNeighborhoodLocalizationMorphism R p f ≫
        etaleResidueFieldNeighborhoodLocalizationMorphism R p g := by
  -- Proof comment: reduce to localized ring maps and use the composition law for
  -- `Localization.localRingHom`.
  apply CommAlgCat.hom_ext
  exact DFunLike.ext _ _ fun x ↦
    congrArg
      (fun h : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+*
          Localization.AtPrime (residueFieldPointedAlgebraKernel R p C.obj) ↦ h x)
      (residueFieldPointedAlgebraLocalization_map_comp R p f g)

/-- Helper for Chap10 Lemma 10 155 7: a transition map between localized neighborhoods
contracts the target maximal ideal to the source maximal ideal. -/
private theorem etaleResidueFieldNeighborhoodLocalizationMorphism_comap_maximalIdeal
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) :
    Ideal.comap
      (Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p B.obj)
        (etaleResidueFieldNeighborhoodHom R p f)
        (residueFieldPointedAlgebraKernel_comap R p f.hom))
      (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj))) =
        maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) := by
  -- Proof comment: `Localization.localRingHom` is a local homomorphism, so local-ring maximal
  -- ideals contract along it.
  let _ : IsLocalHom
      (Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p B.obj)
        (etaleResidueFieldNeighborhoodHom R p f)
        (residueFieldPointedAlgebraKernel_comap R p f.hom)) :=
    Localization.isLocalHom_localRingHom
      (residueFieldPointedAlgebraKernel R p A.obj)
      (residueFieldPointedAlgebraKernel R p B.obj)
      (etaleResidueFieldNeighborhoodHom R p f)
      (residueFieldPointedAlgebraKernel_comap R p f.hom)
  simpa using
    (IsLocalRing.maximalIdeal_comap
      (Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p B.obj)
        (etaleResidueFieldNeighborhoodHom R p f)
        (residueFieldPointedAlgebraKernel_comap R p f.hom)))

/-- The diagram sending an étale neighborhood `(S, q)` of `p` to the localized `R_p`-algebra
`S_q`. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationDiagram (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    EtaleResidueFieldNeighborhoodCategory R p ⥤ CommAlgCat (Localization.AtPrime p) where
  obj A := etaleResidueFieldNeighborhoodLocalizationObject R p A
  map f := etaleResidueFieldNeighborhoodLocalizationMorphism R p f
  map_id A := etaleResidueFieldNeighborhoodLocalizationMorphism_id R p A
  map_comp f g := etaleResidueFieldNeighborhoodLocalizationMorphism_comp R p f g

private noncomputable abbrev etaleResidueFieldNeighborhoodSourceHenselizationPoint
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh] :
    CommAlgCat R :=
  let _ : Algebra R Rh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.of R Rh

/-- Helper for Chap10 Lemma 10 155 7: an étale algebra map is a one-stage ind-étale map. -/
private theorem isFilteredColimitOfEtale_of_etaleAlgebraMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : (algebraMap A B).Etale) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) := by
  -- Proof comment: translate to the raw categorical ind-owner and include the single étale
  -- stage as an ind-étale presentation.
  rw [← RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale]
  exact
    (CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale))
      (CommRingCat.ofHom (algebraMap A B))
      (by simpa [CommRingCat.etale] using hAB)

/-- Helper for Chap10 Lemma 10 155 7: a bijective ring map is ind-étale. -/
private theorem isFilteredColimitOfEtale_of_bijective
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} f := by
  -- Proof comment: use the algebra structure induced by the isomorphism, then apply the
  -- one-stage étale adapter.
  letI : Algebra A B := f.toAlgebra
  have hfEtale : f.Etale := RingHom.Etale.of_bijective hf
  have halgEtale : (algebraMap A B).Etale := by
    simpa [RingHom.algebraMap_toAlgebra] using hfEtale
  simpa [RingHom.algebraMap_toAlgebra] using
    isFilteredColimitOfEtale_of_etaleAlgebraMap (A := A) (B := B) halgEtale

/-- Helper for Chap10 Lemma 10 155 7: an away localization is ind-étale over its source. -/
private theorem isFilteredColimitOfEtale_of_isLocalizationAway
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (r : A)
    [IsLocalization.Away r B] :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) := by
  -- Proof comment: mathlib recognizes away localizations as étale, and the previous helper
  -- converts the finite stage to the chapter's ind-étale owner.
  have hEtale : (algebraMap A B).Etale := by
    exact (RingHom.etale_algebraMap (R := A) (S := B)).2
      (Algebra.Etale.of_isLocalizationAway r)
  exact isFilteredColimitOfEtale_of_etaleAlgebraMap hEtale

/-- Helper for Chap10 Lemma 10 155 7: elements of a submonoid, ordered by divisibility, index
the principal localizations used to present an arbitrary localization. -/
private abbrev AwayLocalizationIndex (A : Type u) [CommRing A] (M : Submonoid A) := M

namespace AwayLocalizationIndex

variable {A : Type u} [CommRing A]

/-- Helper for Chap10 Lemma 10 155 7: divisibility supplies the preorder on localization
indices. -/
private instance instLE (M : Submonoid A) : LE (AwayLocalizationIndex A M) where
  le m n := (m : A) ∣ (n : A)

/-- Helper for Chap10 Lemma 10 155 7: divisibility in the ambient ring is a preorder on
submonoid elements. -/
private instance instPreorder (M : Submonoid A) : Preorder (AwayLocalizationIndex A M) where
  le_refl _ := dvd_rfl
  le_trans _ _ _ hmn hnk := dvd_trans hmn hnk
  lt m n := (m : A) ∣ (n : A) ∧ ¬ (n : A) ∣ (m : A)
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Helper for Chap10 Lemma 10 155 7: multiplication gives common upper bounds for the
divisibility preorder. -/
private instance instDirectedOrder (M : Submonoid A) :
    IsDirectedOrder (AwayLocalizationIndex A M) where
  directed m n := by
    -- Proof comment: the product `m * n` is divisible by each factor.
    refine ⟨m * n, ?_, ?_⟩
    · refine ⟨(n : A), ?_⟩
      rfl
    · refine ⟨(m : A), ?_⟩
      change (m : A) * (n : A) = (n : A) * (m : A)
      rw [mul_comm]

/-- Helper for Chap10 Lemma 10 155 7: if `m ∣ n`, then localizing away from `n` inverts every
power of `m`. -/
private lemma transition_mapsUnits {M : Submonoid A}
    {m n : AwayLocalizationIndex A M} (h : m ≤ n) :
    ∀ y : Submonoid.powers (m : A),
      IsUnit (algebraMap A (Localization.Away (n : A)) y) := by
  -- Proof comment: powers preserve divisibility, so every `m`-denominator divides a power of
  -- the inverted element `n`.
  intro y
  rw [IsLocalization.Away.algebraMap_isUnit_iff
    (S := Localization.Away (n : A)) (x := (n : A))]
  rcases (Submonoid.mem_powers_iff y.1 (m : A)).mp y.2 with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [← hk]
  exact pow_dvd_pow_of_dvd h k

/-- Helper for Chap10 Lemma 10 155 7: the transition map between principal localizations. -/
private noncomputable def transition {M : Submonoid A}
    {m n : AwayLocalizationIndex A M} (h : m ≤ n) :
    Localization.Away (m : A) →ₐ[A] Localization.Away (n : A) :=
  IsLocalization.liftAlgHom (A := A) (R := A) (M := Submonoid.powers (m : A))
    (S := Localization.Away (m : A)) (P := Localization.Away (n : A))
    (f := Algebra.ofId A (Localization.Away (n : A))) (transition_mapsUnits h)

/-- Helper for Chap10 Lemma 10 155 7: a principal-localization transition restricts to the
target algebra map on the source ring. -/
private lemma transition_comp_algebraMap {M : Submonoid A}
    {m n : AwayLocalizationIndex A M} (h : m ≤ n) :
    (transition h).toRingHom.comp (algebraMap A (Localization.Away (m : A))) =
      algebraMap A (Localization.Away (n : A)) := by
  -- Proof comment: this is the computation rule for the localization lift.
  exact IsLocalization.lift_comp (M := Submonoid.powers (m : A))
    (S := Localization.Away (m : A)) (g := algebraMap A (Localization.Away (n : A)))
    (transition_mapsUnits h)

/-- Helper for Chap10 Lemma 10 155 7: the identity divisibility relation gives the identity
transition. -/
private lemma transition_refl {M : Submonoid A} (m : AwayLocalizationIndex A M) :
    transition (show m ≤ m from le_rfl) = AlgHom.id A (Localization.Away (m : A)) := by
  -- Proof comment: maps out of a localization are determined by their values on the source.
  apply IsLocalization.algHom_ext (Submonoid.powers (m : A))
  exact AlgHom.coe_ringHom_injective (transition_comp_algebraMap (show m ≤ m from le_rfl))

/-- Helper for Chap10 Lemma 10 155 7: principal-localization transitions compose along
divisibility chains. -/
private lemma transition_trans {M : Submonoid A}
    {m n k : AwayLocalizationIndex A M} (hmn : m ≤ n) (hnk : n ≤ k) :
    transition (le_trans hmn hnk) = (transition hnk).comp (transition hmn) := by
  -- Proof comment: compare both maps from `A[1/m]` on the source ring.
  apply IsLocalization.algHom_ext (Submonoid.powers (m : A))
  ext

/-- Helper for Chap10 Lemma 10 155 7: principal localization maps to the full localization
because every generated denominator lies in the submonoid. -/
private lemma toLocalization_mapsUnits {M : Submonoid A}
    (m : AwayLocalizationIndex A M) :
    ∀ y : Submonoid.powers (m : A),
      IsUnit (algebraMap A (Localization M) y) := by
  -- Proof comment: the principal powers of `m` are contained in `M`.
  intro y
  exact IsLocalization.map_units (M := M) (Localization M)
    ⟨y.1, (Submonoid.powers_le.mpr m.2) y.2⟩

/-- Helper for Chap10 Lemma 10 155 7: the canonical map from `A[1/m]` to `M⁻¹A`. -/
private noncomputable def toLocalization {M : Submonoid A}
    (m : AwayLocalizationIndex A M) :
    Localization.Away (m : A) →ₐ[A] Localization M :=
  IsLocalization.liftAlgHom (A := A) (R := A) (M := Submonoid.powers (m : A))
    (S := Localization.Away (m : A)) (P := Localization M)
    (f := Algebra.ofId A (Localization M)) (toLocalization_mapsUnits m)

/-- Helper for Chap10 Lemma 10 155 7: the canonical map `A[1/m] → M⁻¹A` restricts to the
localization map from `A`. -/
private lemma toLocalization_comp_algebraMap {M : Submonoid A}
    (m : AwayLocalizationIndex A M) :
    (toLocalization m).toRingHom.comp (algebraMap A (Localization.Away (m : A))) =
      algebraMap A (Localization M) := by
  -- Proof comment: this is the computation rule for the localization lift.
  exact IsLocalization.lift_comp (M := Submonoid.powers (m : A))
    (S := Localization.Away (m : A)) (g := algebraMap A (Localization M))
    (toLocalization_mapsUnits m)

/-- Helper for Chap10 Lemma 10 155 7: the maps to `M⁻¹A` are compatible with transition maps. -/
private lemma toLocalization_comp_transition {M : Submonoid A}
    {m n : AwayLocalizationIndex A M} (h : m ≤ n) :
    (toLocalization n).comp (transition h) = toLocalization m := by
  -- Proof comment: both sides are maps out of `A[1/m]` with the same restriction to `A`.
  apply IsLocalization.algHom_ext (Submonoid.powers (m : A))
  ext

/-- Helper for Chap10 Lemma 10 155 7: the identity morphism law for the principal-localization
diagram. -/
private lemma diagram_map_id {M : Submonoid A}
    (m : AwayLocalizationIndex A M) :
    CommRingCat.ofHom (transition (leOfHom (𝟙 m))).toRingHom =
      𝟙 (CommRingCat.of (Localization.Away (m : A))) := by
  -- Proof comment: compare both endomorphisms after restricting to `A`.
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (m : A))
  simpa using transition_comp_algebraMap (leOfHom (𝟙 m))

/-- Helper for Chap10 Lemma 10 155 7: the composition law for the principal-localization
diagram. -/
private lemma diagram_map_comp {M : Submonoid A}
    {m n k : AwayLocalizationIndex A M} (hmn : m ⟶ n) (hnk : n ⟶ k) :
    CommRingCat.ofHom (transition (leOfHom (hmn ≫ hnk))).toRingHom =
      CommRingCat.ofHom (transition (leOfHom hmn)).toRingHom ≫
        CommRingCat.ofHom (transition (leOfHom hnk)).toRingHom := by
  -- Proof comment: compare the long transition with the categorical composite on `A`.
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (m : A))
  calc
    (CommRingCat.Hom.hom
        (CommRingCat.ofHom (transition (leOfHom (hmn ≫ hnk))).toRingHom)).comp
        (algebraMap A (Localization.Away (m : A))) =
      algebraMap A (Localization.Away (k : A)) := by
        simpa using transition_comp_algebraMap (leOfHom (hmn ≫ hnk))
    _ = ((transition (leOfHom hnk)).toRingHom.comp
        (transition (leOfHom hmn)).toRingHom).comp
        (algebraMap A (Localization.Away (m : A))) := by
        rw [RingHom.comp_assoc, transition_comp_algebraMap, transition_comp_algebraMap]
    _ = (CommRingCat.Hom.hom
        (CommRingCat.ofHom (transition (leOfHom hmn)).toRingHom ≫
          CommRingCat.ofHom (transition (leOfHom hnk)).toRingHom)).comp
        (algebraMap A (Localization.Away (m : A))) := by
        rfl

/-- Helper for Chap10 Lemma 10 155 7: the filtered diagram of principal localizations. -/
private noncomputable def diagram (M : Submonoid A) :
    AwayLocalizationIndex A M ⥤ CommRingCat where
  obj m := CommRingCat.of (Localization.Away (m : A))
  map {_ _} h := CommRingCat.ofHom (transition (leOfHom h)).toRingHom
  map_id := diagram_map_id
  map_comp := diagram_map_comp

/-- Helper for Chap10 Lemma 10 155 7: the canonical maps to `M⁻¹A` form a cocone. -/
private lemma cocone_naturality {M : Submonoid A}
    {m n : AwayLocalizationIndex A M} (h : m ⟶ n) :
    (diagram M).map h ≫ CommRingCat.ofHom (toLocalization n).toRingHom =
      CommRingCat.ofHom (toLocalization m).toRingHom := by
  -- Proof comment: naturality is the transition compatibility of `toLocalization`.
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (toLocalization_comp_transition (leOfHom h))

/-- Helper for Chap10 Lemma 10 155 7: the principal-localization cocone with vertex `M⁻¹A`. -/
private noncomputable def cocone (M : Submonoid A) : Cocone (diagram (A := A) M) where
  pt := CommRingCat.of (Localization M)
  ι :=
    { app := fun m => CommRingCat.ofHom (toLocalization m).toRingHom
      naturality := fun _ _ h => cocone_naturality h }

/-- Helper for Chap10 Lemma 10 155 7: source maps into principal localizations form a natural
transformation from the constant source diagram. -/
private lemma sourceNat_naturality {M : Submonoid A}
    {m n : AwayLocalizationIndex A M} (h : m ⟶ n) :
    CommRingCat.ofHom (algebraMap A (Localization.Away (m : A))) ≫
        (diagram M).map h =
      CommRingCat.ofHom (algebraMap A (Localization.Away (n : A))) := by
  -- Proof comment: this is the transition computation rule in categorical form.
  apply CommRingCat.hom_ext
  exact transition_comp_algebraMap (leOfHom h)

/-- Helper for Chap10 Lemma 10 155 7: the fixed source map for the principal-localization
diagram. -/
private noncomputable def sourceNat (M : Submonoid A) :
    (Functor.const (AwayLocalizationIndex A M)).obj (CommRingCat.of A) ⟶
      diagram (A := A) M where
  app m := CommRingCat.ofHom (algebraMap A (Localization.Away (m : A)))
  naturality := fun _ _ h => (sourceNat_naturality h).symm

/-- Helper for Chap10 Lemma 10 155 7: the principal-localization cocone is compatible with the
fixed source `A`. -/
private lemma sourceNat_comp_cocone {M : Submonoid A}
    (m : AwayLocalizationIndex A M) :
    (sourceNat M).app m ≫ (cocone M).ι.app m =
      CommRingCat.ofHom (algebraMap A (Localization M)) := by
  -- Proof comment: compatibility is the computation rule for `A[1/m] → M⁻¹A`.
  apply CommRingCat.hom_ext
  exact toLocalization_comp_algebraMap m

/-- Helper for Chap10 Lemma 10 155 7: any cocone over principal localizations has the same
base map from `A[1]` as from every stage after restriction to `A`. -/
private lemma coconeBaseMap_eq_stage {M : Submonoid A}
    (s : Cocone (diagram (A := A) M)) (m : AwayLocalizationIndex A M)
    (x : A) :
    ((s.ι.app (1 : AwayLocalizationIndex A M)).hom.comp
        (algebraMap A (Localization.Away (1 : A)))) x =
      (s.ι.app m).hom ((algebraMap A (Localization.Away (m : A))) x) := by
  -- Proof comment: move from the `1`-stage to the `m`-stage using the cocone identity.
  let h : (1 : AwayLocalizationIndex A M) ≤ m := ⟨(m : A), by simp⟩
  have hnat' :
      ((s.ι.app m).hom.comp ((diagram M).map (homOfLE h)).hom) =
        (s.ι.app (1 : AwayLocalizationIndex A M)).hom := by
    exact congrArg CommRingCat.Hom.hom (s.w (homOfLE h))
  have htrans' :
      ((diagram M).map (homOfLE h)).hom
          ((algebraMap A (Localization.Away (1 : A))) x) =
        (algebraMap A (Localization.Away (m : A))) x := by
    exact congrFun (congrArg DFunLike.coe (transition_comp_algebraMap h)) x
  calc
    ((s.ι.app (1 : AwayLocalizationIndex A M)).hom.comp
        (algebraMap A (Localization.Away (1 : A)))) x =
      (((s.ι.app m).hom.comp ((diagram M).map (homOfLE h)).hom).comp
        (algebraMap A (Localization.Away (1 : A)))) x := by
        rw [hnat']
        rfl
    _ = (s.ι.app m).hom ((algebraMap A (Localization.Away (m : A))) x) := by
        exact congrArg (fun z => (s.ι.app m).hom z) htrans'

/-- Helper for Chap10 Lemma 10 155 7: the base map from `A[1]` into an arbitrary cocone point
inverts every element of `M`. -/
private lemma coconeBaseMap_mapsUnits {M : Submonoid A}
    (s : Cocone (diagram (A := A) M)) :
    ∀ y : M, IsUnit (((s.ι.app (1 : AwayLocalizationIndex A M)).hom.comp
      (algebraMap A (Localization.Away (1 : A)))) y) := by
  -- Proof comment: compare with the stage indexed by `y`, where `y` is inverted.
  intro y
  rw [coconeBaseMap_eq_stage s y (y : A)]
  have hunitAway : IsUnit ((algebraMap A (Localization.Away (y : A))) (y : A)) :=
    IsLocalization.Away.algebraMap_isUnit (y : A)
  exact IsUnit.map (s.ι.app y).hom hunitAway

/-- Helper for Chap10 Lemma 10 155 7: the universal morphism from `M⁻¹A` to an arbitrary
cocone point. -/
private noncomputable def coconeDesc {M : Submonoid A}
    (s : Cocone (diagram (A := A) M)) : (cocone (A := A) M).pt ⟶ s.pt :=
  CommRingCat.ofHom (IsLocalization.lift (coconeBaseMap_mapsUnits s))

/-- Helper for Chap10 Lemma 10 155 7: the universal morphism factors through each principal
localization stage. -/
private lemma cocone_fac {M : Submonoid A}
    (s : Cocone (diagram (A := A) M)) (m : AwayLocalizationIndex A M) :
    (cocone M).ι.app m ≫ coconeDesc s = s.ι.app m := by
  -- Proof comment: check the factorization after restricting to the source ring.
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (R := A) (S := Localization.Away (m : A))
    (Submonoid.powers (m : A))
  calc
    (CommRingCat.Hom.hom
        (CommRingCat.ofHom (toLocalization m).toRingHom ≫
          CommRingCat.ofHom (IsLocalization.lift (coconeBaseMap_mapsUnits s)))).comp
        (algebraMap A (Localization.Away (m : A))) =
      ((IsLocalization.lift (coconeBaseMap_mapsUnits s)).comp
        (toLocalization m).toRingHom).comp
        (algebraMap A (Localization.Away (m : A))) := by
        rfl
    _ =
      (IsLocalization.lift (coconeBaseMap_mapsUnits s)).comp
        (algebraMap A (Localization M)) := by
        rw [RingHom.comp_assoc]
        rw [toLocalization_comp_algebraMap]
    _ = (s.ι.app (1 : AwayLocalizationIndex A M)).hom.comp
        (algebraMap A (Localization.Away (1 : A))) := by
        exact IsLocalization.lift_comp (M := M) (S := Localization M)
          (g := (s.ι.app (1 : AwayLocalizationIndex A M)).hom.comp
            (algebraMap A (Localization.Away (1 : A))))
          (coconeBaseMap_mapsUnits s)
    _ = (s.ι.app m).hom.comp (algebraMap A (Localization.Away (m : A))) := by
        ext x
        exact coconeBaseMap_eq_stage s m x

/-- Helper for Chap10 Lemma 10 155 7: the universal morphism from `M⁻¹A` is unique among maps
factoring the principal-localization cocone. -/
private lemma cocone_uniq {M : Submonoid A}
    (s : Cocone (diagram (A := A) M)) (f : (cocone (A := A) M).pt ⟶ s.pt)
    (hf : ∀ m : AwayLocalizationIndex A M, (cocone M).ι.app m ≫ f = s.ι.app m) :
    f = coconeDesc s := by
  -- Proof comment: localization extensionality reduces uniqueness to the `A[1]` stage.
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (R := A) (S := Localization M) M
  calc
    (CommRingCat.Hom.hom f).comp (algebraMap A (Localization M)) =
      ((CommRingCat.Hom.hom f).comp
        (toLocalization (1 : AwayLocalizationIndex A M)).toRingHom).comp
        (algebraMap A (Localization.Away (1 : A))) := by
        exact congrArg (fun g => (CommRingCat.Hom.hom f).comp g)
          (toLocalization_comp_algebraMap (1 : AwayLocalizationIndex A M)).symm
    _ =
      ((CommRingCat.ofHom (toLocalization
          (1 : AwayLocalizationIndex A M)).toRingHom ≫ f).hom).comp
        (algebraMap A (Localization.Away (1 : A))) := by
        rfl
    _ = (s.ι.app (1 : AwayLocalizationIndex A M)).hom.comp
        (algebraMap A (Localization.Away (1 : A))) := by
        exact congrArg (fun g => g.comp (algebraMap A (Localization.Away (1 : A))))
          (congrArg CommRingCat.Hom.hom
            (hf (1 : AwayLocalizationIndex A M)))
    _ = (IsLocalization.lift (coconeBaseMap_mapsUnits s)).comp
        (algebraMap A (Localization M)) := by
        exact (IsLocalization.lift_comp (M := M) (S := Localization M)
          (g := (s.ι.app (1 : AwayLocalizationIndex A M)).hom.comp
            (algebraMap A (Localization.Away (1 : A))))
          (coconeBaseMap_mapsUnits s)).symm

/-- Helper for Chap10 Lemma 10 155 7: the principal-localization cocone has colimit `M⁻¹A`. -/
private noncomputable def cocone_isColimit (M : Submonoid A) :
    IsColimit (cocone (A := A) M) :=
  IsColimit.mk (fun s => coconeDesc s) (fun s m => cocone_fac s m)
    (fun s f hf => cocone_uniq s f hf)

end AwayLocalizationIndex

/-- Helper for Chap10 Lemma 10 155 7: an arbitrary localization map is ind-étale over its
source. -/
private theorem isFilteredColimitOfEtale_localizationMap
    {A : Type u} [CommRing A] (M : Submonoid A) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A (Localization M)) := by
  -- Proof comment: present `M⁻¹A` as the filtered colimit of principal localizations `A[1/m]`,
  -- whose structure maps are étale and therefore ind-étale.
  let F : AwayLocalizationIndex A M ⥤ Under (CommRingCat.of A) :=
    Under.lift (AwayLocalizationIndex.diagram (A := A) M)
      (AwayLocalizationIndex.sourceNat (A := A) M)
  let c : Cocone F :=
    Under.liftCocone (AwayLocalizationIndex.diagram (A := A) M)
      (AwayLocalizationIndex.sourceNat (A := A) M)
      (AwayLocalizationIndex.cocone (A := A) M)
      (CommRingCat.ofHom (algebraMap A (Localization M)))
      (AwayLocalizationIndex.sourceNat_comp_cocone (A := A))
  have hc : IsColimit c := by
    exact Under.isColimitLiftCocone
      (AwayLocalizationIndex.diagram (A := A) M)
      (AwayLocalizationIndex.sourceNat (A := A) M)
      (AwayLocalizationIndex.cocone (A := A) M)
      (CommRingCat.ofHom (algebraMap A (Localization M)))
      (AwayLocalizationIndex.sourceNat_comp_cocone (A := A))
      (AwayLocalizationIndex.cocone_isColimit (A := A) M)
  have hStages :
      ∀ m : AwayLocalizationIndex A M,
        CategoryTheory.MorphismProperty.ind.{u, u, u + 1} CommRingCat.etale
          (F.obj m).hom := by
    intro m
    -- Proof comment: each stage is an away localization and hence a one-stage ind-étale map.
    simpa [F, AwayLocalizationIndex.sourceNat] using
      (RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale.2
        (isFilteredColimitOfEtale_of_isLocalizationAway
          (A := A) (B := Localization.Away (m : A)) (r := (m : A))))
  exact RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit
    (F := F) c hc (Iso.refl _) hStages

/-- Helper for Chap10 Lemma 10 155 7: the localization `S_q` of an étale residue-field
neighborhood is ind-étale over `R_p`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_isFilteredColimitOfEtale
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) := by
  -- Proof comment: first make both `R_p` and `S_q` ind-étale over `R`, then use the
  -- common-base comparison theorem for the structural map `R_p → S_q`.
  dsimp only
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  have hRp : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap R (Localization.AtPrime p)) :=
    isFilteredColimitOfEtale_localizationMap p.primeCompl
  have hRS : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap R A.obj.left) := by
    exact isFilteredColimitOfEtale_of_etaleAlgebraMap (A := R) (B := A.obj.left) A.property
  have hSqOverS : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap A.obj.left
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) :=
    isFilteredColimitOfEtale_localizationMap
      (residueFieldPointedAlgebraKernel R p A.obj).primeCompl
  have hRSq : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap R
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) := by
    have hcomp :=
      RingHom.isFilteredColimitOfEtale_comp
        (algebraMap R A.obj.left)
        (algebraMap A.obj.left
          (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
        hRS hSqOverS
    simpa [IsScalarTower.algebraMap_eq R A.obj.left
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))] using hcomp
  have hTower : IsScalarTower R (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (Localization.localRingHom_to_map p
      (residueFieldPointedAlgebraKernel R p A.obj)
      (algebraMap R A.obj.left)
      (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj) x).symm
  let _ : IsScalarTower R (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) := hTower
  exact RingHom.isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
    (R := R) (A := Localization.AtPrime p)
    (B := Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) hRp hRSq

/-- The maximal ideal of `S_q` lies over the maximal ideal of `R_p`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).under
      (Localization.AtPrime p) =
      maximalIdeal (Localization.AtPrime p) := by
  -- Proof comment: the localized structure map is a local homomorphism, so the maximal ideal of
  -- the target local ring contracts to the maximal ideal of the source.
  dsimp only
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  let _ : IsLocalHom (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) := by
    simpa [RingHom.algebraMap_toAlgebra, etaleResidueFieldNeighborhoodLocalizationAlgebraMap] using
      (Localization.isLocalHom_localRingHom p
        (residueFieldPointedAlgebraKernel R p A.obj)
        (algebraMap R A.obj.left)
        (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj))
  simpa [Ideal.under_def] using
    (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))))

/-- Helper for Chap10 Lemma 10 155 7: residue-field maps compose as expected. -/
private theorem residueFieldMap_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (K : Ideal C) [K.IsPrime]
    (f : A →+* B) (g : B →+* C)
    (hf : I = Ideal.comap f J) (hg : J = Ideal.comap g K)
    (hgf : I = Ideal.comap (g.comp f) K) :
    (Ideal.ResidueField.map J K g hg).comp (Ideal.ResidueField.map I J f hf) =
      Ideal.ResidueField.map I K (g.comp f) hgf := by
  -- Proof comment: residue-field maps are determined by their values on source generators,
  -- where the composition rule is just functoriality of ring homomorphisms.
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]

/-- Helper for Chap10 Lemma 10 155 7: the pointed kernel has residue field `κ(p)`. -/
private theorem residueFieldPointedAlgebraKernel_residueFieldMap_bijective
    (A : ResidueFieldPointedAlgebraCategory R p) :
    Function.Bijective
      (Ideal.ResidueField.map p (residueFieldPointedAlgebraKernel R p A)
        (algebraMap R A.left) (residueFieldPointedAlgebraKernel_comap_algebraMap R p A)) := by
  -- Proof comment: compare the source map with the residue-field map induced by the pointed
  -- structure map `A → κ(p)`; both maps become the canonical residue map into `κ(p)`.
  let q : Ideal A.left := residueFieldPointedAlgebraKernel R p A
  let φ : A.left →+* p.ResidueField := residueFieldPointedAlgebraToResidueField R p A
  have hq_bot : q = Ideal.comap φ (⊥ : Ideal p.ResidueField) := by
    ext x
    rfl
  have hφ_comp :
      φ.comp (algebraMap R A.left) = algebraMap R p.ResidueField := by
    ext x
    simp [φ, residueFieldPointedAlgebraToResidueField]
  have hcomp_bot : p = Ideal.comap (φ.comp (algebraMap R A.left)) (⊥ : Ideal p.ResidueField) := by
    -- Proof comment: after identifying the composite with `R → κ(p)`, the comap of `⊥`
    -- is the defining kernel of the residue-field map.
    have hbase_bot :
        p = Ideal.comap (algebraMap R p.ResidueField) (⊥ : Ideal p.ResidueField) := by
      simpa [RingHom.ker, Ideal.comap] using
        (Ideal.ker_algebraMap_residueField (I := p)).symm
    simpa [hφ_comp] using hbase_bot
  let sourceMap : p.ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.map p q (algebraMap R A.left)
      (residueFieldPointedAlgebraKernel_comap_algebraMap R p A)
  let pointedMap : q.ResidueField →+* (⊥ : Ideal p.ResidueField).ResidueField :=
    Ideal.ResidueField.map q (⊥ : Ideal p.ResidueField) φ hq_bot
  have hpointedSOS : φ.SurjectiveOnStalks := by
    -- Proof comment: `R → κ(p)` is surjective on stalks, and the pointed map is its right
    -- factor through `A`.
    have hcompSOS : (φ.comp (algebraMap R A.left)).SurjectiveOnStalks := by
      simpa [hφ_comp] using Ideal.surjectiveOnStalks_residueField p
    exact RingHom.SurjectiveOnStalks.of_comp hcompSOS
  have hpointedBij : Function.Bijective pointedMap := by
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      hpointedSOS q (⊥ : Ideal p.ResidueField) hq_bot
  have hbaseBij :
      Function.Bijective
        (Ideal.ResidueField.map p (⊥ : Ideal p.ResidueField)
          (φ.comp (algebraMap R A.left)) hcomp_bot) := by
    -- Proof comment: this is the residue-field map of `R → κ(p)` at the surviving prime.
    have hbase_bot :
        p = Ideal.comap (algebraMap R p.ResidueField) (⊥ : Ideal p.ResidueField) := by
      simpa [RingHom.ker, Ideal.comap] using
        (Ideal.ker_algebraMap_residueField (I := p)).symm
    simpa [hφ_comp] using
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (Ideal.surjectiveOnStalks_residueField p)
        p (⊥ : Ideal p.ResidueField) hbase_bot)
  have hcomp :
      pointedMap.comp sourceMap =
        Ideal.ResidueField.map p (⊥ : Ideal p.ResidueField)
          (φ.comp (algebraMap R A.left)) hcomp_bot := by
    exact residueFieldMap_comp p q (⊥ : Ideal p.ResidueField)
      (algebraMap R A.left) φ
      (residueFieldPointedAlgebraKernel_comap_algebraMap R p A) hq_bot hcomp_bot
  have hcompBij : Function.Bijective (pointedMap.comp sourceMap) := by
    rw [hcomp]
    exact hbaseBij
  -- Proof comment: the right factor and the composite are bijective, so the source residue
  -- comparison is bijective.
  exact (hpointedBij.of_comp_iff' sourceMap).mp (by
    simpa [RingHom.coe_comp] using hcompBij)

/-- Helper for Chap10 Lemma 10 155 7: the residue-field map induced by the localized
neighborhood structure map is bijective. -/
private theorem etaleResidueFieldNeighborhoodLocalization_residueFieldMap_bijective
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    Function.Bijective
      (Ideal.ResidueField.map
        (maximalIdeal (Localization.AtPrime p))
        (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
        (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
        (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm) := by
  -- Proof comment: first prove the comparison before localization, then conjugate it by the
  -- two residue-field maps induced by localizing at the source and target primes.
  let q : Ideal A.obj.left := residueFieldPointedAlgebraKernel R p A.obj
  let Rp : Type u := Localization.AtPrime p
  let Sq : Type u := Localization.AtPrime q
  let sourceLoc : p.ResidueField →+* (maximalIdeal Rp).ResidueField :=
    Ideal.ResidueField.map p (maximalIdeal Rp) (algebraMap R Rp)
      (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p)).symm
  let targetLoc : q.ResidueField →+* (maximalIdeal Sq).ResidueField :=
    Ideal.ResidueField.map q (maximalIdeal Sq) (algebraMap A.obj.left Sq)
      (Localization.AtPrime.comap_maximalIdeal (R := A.obj.left) (I := q)).symm
  let sourceMap : p.ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.map p q (algebraMap R A.obj.left)
      (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj)
  let localizedMap : (maximalIdeal Rp).ResidueField →+* (maximalIdeal Sq).ResidueField :=
    Ideal.ResidueField.map (maximalIdeal Rp) (maximalIdeal Sq)
      (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
      (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm
  have hsourceLocBij : Function.Bijective sourceLoc := by
    -- Proof comment: localizing `R` at `p` does not alter the residue field at `p`.
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization p.primeCompl Rp)
      p (maximalIdeal Rp)
      (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p)).symm
  have htargetLocBij : Function.Bijective targetLoc := by
    -- Proof comment: the same localization residue-field invariance applies to `A` at `q`.
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization q.primeCompl Sq)
      q (maximalIdeal Sq)
      (Localization.AtPrime.comap_maximalIdeal (R := A.obj.left) (I := q)).symm
  have hsourceMapBij : Function.Bijective sourceMap := by
    exact residueFieldPointedAlgebraKernel_residueFieldMap_bijective p A.obj
  have hsquare : localizedMap.comp sourceLoc = targetLoc.comp sourceMap := by
    -- Proof comment: both composites are maps out of `κ(p)`; on generators from `R`, they
    -- reduce to the defining computation rule for `Localization.localRingHom`.
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro x
    dsimp [sourceLoc, targetLoc, sourceMap, localizedMap]
    simp only [Ideal.ResidueField.map_algebraMap]
    rw [Localization.localRingHom_to_map
      p q (algebraMap R A.obj.left)
      (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj) x]
  have hrightBij : Function.Bijective (targetLoc.comp sourceMap) :=
    htargetLocBij.comp hsourceMapBij
  have hleftBij : Function.Bijective (localizedMap.comp sourceLoc) := by
    simpa [hsquare] using hrightBij
  -- Proof comment: cancel the bijective source localization map from the right of the composite.
  exact (hsourceLocBij.of_comp_iff localizedMap).mp hleftBij

/-- Helper for Chap10 Lemma 10 155 7: bijectivity of residue-field maps is unchanged by
transporting the source ideal along an equality. -/
private theorem residueFieldMap_bijective_congr_source
    {A B : Type u} [CommRing A] [CommRing B]
    (I I' : Ideal A) [I.IsPrime] [I'.IsPrime]
    (J : Ideal B) [J.IsPrime] (f : A →+* B)
    (hII' : I = I') (hI : I = Ideal.comap f J) (hI' : I' = Ideal.comap f J)
    (hbij : Function.Bijective (Ideal.ResidueField.map I J f hI)) :
    Function.Bijective (Ideal.ResidueField.map I' J f hI') := by
  -- Proof comment: isolate the dependent transport; after substituting the ideal equality, proof
  -- irrelevance identifies the two map proofs.
  subst hII'
  simpa using hbij

/-- Helper for Chap10 Lemma 10 155 7: the source residue-field map in the `q.under` normal form
is bijective. -/
private theorem etaleResidueFieldNeighborhoodLocalization_residueFieldMap_under_bijective
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    Function.Bijective
      (Ideal.ResidueField.map
        ((maximalIdeal
          (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).under
          (Localization.AtPrime p))
        (maximalIdeal
          (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
        (algebraMap (Localization.AtPrime p)
          (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
        rfl) := by
  -- Proof comment: transport the maximal-ideal-indexed source bijectivity to the exact
  -- `q.under` source spelling required by the lifting theorem.
  dsimp only
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  refine residueFieldMap_bijective_congr_source
    (I := maximalIdeal (Localization.AtPrime p))
    (I' := (maximalIdeal
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).under
      (Localization.AtPrime p))
    (J := maximalIdeal
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
    (f := algebraMap (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
    ?_ ?_ rfl
    (etaleResidueFieldNeighborhoodLocalization_residueFieldMap_bijective p A)
  · exact (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm
  · exact (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm

/-- The localization `S_q` has the same residue field as `R_p`, through the canonical
residue-field map. -/
private noncomputable def etaleResidueFieldNeighborhoodLocalization_residueFieldEquiv
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (maximalIdeal (Localization.AtPrime p)).ResidueField ≃+*
      (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).ResidueField :=
  RingEquiv.ofBijective
    (Ideal.ResidueField.map
      (maximalIdeal (Localization.AtPrime p))
      (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
      (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
      (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm)
    (etaleResidueFieldNeighborhoodLocalization_residueFieldMap_bijective p A)

/-- The localized residue-field equivalence is the equivalence attached to the canonical
residue-field map. -/
private theorem etaleResidueFieldNeighborhoodLocalization_residueFieldEquiv_spec
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (etaleResidueFieldNeighborhoodLocalization_residueFieldEquiv p A).toRingHom =
      Ideal.ResidueField.map
        (maximalIdeal (Localization.AtPrime p))
        (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
        (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
        (etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A).symm :=
  rfl

/-- Helper for Chap10 Lemma 10 155 7: the maximal ideal of a henselization of `R_p` contracts
to the maximal ideal of `R_p`. -/
private theorem henselization_maximalIdeal_under
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    (maximalIdeal Rh).under (Localization.AtPrime p) =
      maximalIdeal (Localization.AtPrime p) := by
  -- Proof comment: this is the local-hom field of the henselization owner, expressed in the
  -- `Ideal.under` spelling used by the residue-field lifting theorem.
  simpa [Ideal.under_def] using
    (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rh))

/-- The localized neighborhood `S_q` admits a unique `R_p`-algebra map to any chosen
henselization `R_p^h`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_existsUnique_toHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    ∃! f :
        Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →ₐ[Localization.AtPrime p] Rh,
      maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) =
        Ideal.comap (f : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+* Rh)
          (maximalIdeal Rh) := by
  -- Route correction: keep the lifting theorem in the `q.under` source-normal form rather than
  -- rewriting dependent residue-field source ideals inside the final application.
  dsimp only
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  let q : Ideal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))
  have hq : q.under (Localization.AtPrime p) = (maximalIdeal Rh).under (Localization.AtPrime p) := by
    -- Proof comment: both maximal ideals contract to the maximal ideal of the base local ring.
    dsimp [q]
    calc
      (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).under
          (Localization.AtPrime p) = maximalIdeal (Localization.AtPrime p) :=
        etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under p A
      _ = (maximalIdeal Rh).under (Localization.AtPrime p) := by
        symm
        exact henselization_maximalIdeal_under p Rh
  let sourceMap : (q.under (Localization.AtPrime p)).ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.map (q.under (Localization.AtPrime p)) q
      (algebraMap (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) rfl
  have hsourceBij : Function.Bijective sourceMap := by
    -- Proof comment: consume the source-ideal transport adapter once, at the lifting API
    -- boundary.
    dsimp [sourceMap, q]
    exact etaleResidueFieldNeighborhoodLocalization_residueFieldMap_under_bijective p A
  let sourceEquiv : (q.under (Localization.AtPrime p)).ResidueField ≃+* q.ResidueField :=
    RingEquiv.ofBijective sourceMap hsourceBij
  let targetMap : (q.under (Localization.AtPrime p)).ResidueField →+*
      (maximalIdeal Rh).ResidueField :=
    Ideal.ResidueField.map (q.under (Localization.AtPrime p)) (maximalIdeal Rh)
      (algebraMap (Localization.AtPrime p) Rh) hq
  let τ : q.ResidueField →+* (maximalIdeal Rh).ResidueField :=
    targetMap.comp sourceEquiv.symm.toRingHom
  have hτ :
      τ.comp (Ideal.ResidueField.map (q.under (Localization.AtPrime p)) q
        (algebraMap (Localization.AtPrime p)
          (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) rfl) =
        Ideal.ResidueField.map (q.under (Localization.AtPrime p)) (maximalIdeal Rh)
          (algebraMap (Localization.AtPrime p) Rh) hq := by
    -- Proof comment: the chosen target residue map was defined by precomposing with the inverse
    -- of the source residue-field equivalence, so composing with the source map cancels.
    apply RingHom.ext
    intro x
    exact congrArg (fun y => targetMap y) (sourceEquiv.symm_apply_apply x)
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap
      (hA := etaleResidueFieldNeighborhoodLocalization_isFilteredColimitOfEtale p A)
      (q := q) hq τ hτ
  refine ⟨f, ?_, ?_⟩
  · -- Proof comment: forget the residue-field clause from the lifting theorem's existence part.
    exact hf.1
  · intro g hg
    apply huniq g
    refine ⟨hg, ?_⟩
    -- Proof comment: precompose both residue maps with the surjective source residue-field map
    -- from `R_p`; `R_p`-linearity of `g` makes the left composite the target map defining `τ`.
    have hleft :
        (Ideal.ResidueField.map q (maximalIdeal Rh) (g : _ →+* Rh) hg).comp
            (Ideal.ResidueField.map (q.under (Localization.AtPrime p)) q
              (algebraMap (Localization.AtPrime p)
                (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) rfl) =
          Ideal.ResidueField.map (q.under (Localization.AtPrime p)) (maximalIdeal Rh)
            (algebraMap (Localization.AtPrime p) Rh) hq := by
      apply Ideal.ResidueField.ringHom_ext
      apply RingHom.ext
      intro x
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      exact congrArg (algebraMap Rh (maximalIdeal Rh).ResidueField) (g.commutes x)
    apply RingHom.ext
    intro z
    obtain ⟨x, rfl⟩ := hsourceBij.surjective z
    have hx := congrFun (congrArg DFunLike.coe hleft) x
    have hτx := congrFun (congrArg DFunLike.coe hτ) x
    exact hx.trans hτx.symm

/-- The canonical morphism from the localized neighborhood `S_q` to a chosen henselization
`R_p^h`. -/
private noncomputable abbrev etaleResidueFieldNeighborhoodLocalizationToHenselizationHom
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (etaleResidueFieldNeighborhoodLocalizationDiagram R p).obj A ⟶
      CommAlgCat.of (Localization.AtPrime p) Rh :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  CommAlgCat.ofHom <|
    Classical.choose <|
      etaleResidueFieldNeighborhoodLocalization_existsUnique_toHenselization p Rh A

/-- Helper for Chap10 Lemma 10 155 7: the source-to-henselization map is compatible with
the restricted `R`-algebra structures. -/
private theorem etaleResidueFieldNeighborhoodSourceToHenselizationHom_commutes
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    ∀ x : R,
      ((etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A).hom.toRingHom.comp
          (algebraMap A.obj.left
            (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))))
        ((algebraMap R A.obj.left) x) =
        (algebraMap (Localization.AtPrime p) Rh)
          ((algebraMap R (Localization.AtPrime p)) x) := by
  intro x
  -- Proof comment: factor the source element through `R_p`, use `R_p`-linearity of the
  -- localized henselization map, and compute the localization map on generators.
  let _ : Algebra R Rh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rh).comp (algebraMap R (Localization.AtPrime p))
  have hcomm :=
    (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A).hom.commutes
      ((algebraMap R (Localization.AtPrime p)) x)
  have hloc :=
    Localization.localRingHom_to_map
      p
      (residueFieldPointedAlgebraKernel R p A.obj)
      (algebraMap R A.obj.left)
      (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj)
      x
  rw [RingHom.comp_apply]
  have happ := congrArg
    (fun y : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) =>
      (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A).hom.toRingHom y)
    hloc
  have hcomm' :
      (fun y : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) =>
        (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A).hom.toRingHom y)
          ((Localization.localRingHom p
            (residueFieldPointedAlgebraKernel R p A.obj)
            (algebraMap R A.obj.left)
            (residueFieldPointedAlgebraKernel_comap_algebraMap R p A.obj))
            ((algebraMap R (Localization.AtPrime p)) x)) =
        (algebraMap (Localization.AtPrime p) Rh)
          ((algebraMap R (Localization.AtPrime p)) x) := by
    simpa only [etaleResidueFieldNeighborhoodSourceHenselizationPoint,
        etaleResidueFieldNeighborhoodLocalizationDiagram,
        etaleResidueFieldNeighborhoodLocalizationObject,
        etaleResidueFieldNeighborhoodLocalizationAlgebraMap,
        RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hcomm
  exact happ.symm.trans hcomm'

/-- The canonical morphism from the source neighborhood `S` to a chosen henselization `R_p^h`,
obtained by composing `S → S_q` with the canonical localized map `S_q → R_p^h`. -/
private noncomputable def etaleResidueFieldNeighborhoodSourceToHenselizationHom
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    (etaleResidueFieldNeighborhoodSourceDiagram R p).obj A ⟶
      etaleResidueFieldNeighborhoodSourceHenselizationPoint R p Rh :=
  let _ : Algebra R Rh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.ofHom <|
    { toRingHom :=
        (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A).hom.toRingHom.comp
          (algebraMap A.obj.left
            (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)))
      commutes' := etaleResidueFieldNeighborhoodSourceToHenselizationHom_commutes p Rh A }

/-- Helper for Chap10 Lemma 10 155 7: the localized maps to the henselization form a natural
transformation. -/
private theorem etaleResidueFieldNeighborhoodLocalizationToHenselization_naturality
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    ∀ ⦃A B : EtaleResidueFieldNeighborhoodCategory R p⦄ (f : A ⟶ B),
      (etaleResidueFieldNeighborhoodLocalizationDiagram R p).map f ≫
          etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh B =
        etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A ≫
          ((Functor.const (EtaleResidueFieldNeighborhoodCategory R p)).obj
            (CommAlgCat.of (Localization.AtPrime p) Rh)).map f := by
  intro A B f
  apply CommAlgCat.hom_ext
  -- Proof comment: after expanding the two composites, uniqueness of the chosen map from
  -- `A_q` to `Rh` reduces naturality to the maximal-ideal contraction of the transition map.
  have hspecB :=
    Classical.choose_spec
      (etaleResidueFieldNeighborhoodLocalization_existsUnique_toHenselization p Rh B)
  have huniqA :=
    (Classical.choose_spec
      (etaleResidueFieldNeighborhoodLocalization_existsUnique_toHenselization p Rh A)).2
  simp only [CommAlgCat.hom_comp, Functor.const_obj_obj, Functor.const_obj_map,
    Category.comp_id] at hspecB huniqA ⊢
  apply huniqA
  apply Ideal.ext
  intro x
  have hloc := congrArg
    (fun I : Ideal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) =>
      x ∈ I)
    (etaleResidueFieldNeighborhoodLocalizationMorphism_comap_maximalIdeal R p f)
  have hB := congrArg
    (fun I : Ideal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj)) =>
      (Localization.localRingHom
        (residueFieldPointedAlgebraKernel R p A.obj)
        (residueFieldPointedAlgebraKernel R p B.obj)
        (etaleResidueFieldNeighborhoodHom R p f)
        (residueFieldPointedAlgebraKernel_comap R p f.hom) x) ∈ I)
    hspecB.1
  simp only [Ideal.mem_comap] at hloc hB ⊢
  simpa using hloc.symm.trans hB

/-- Helper for Chap10 Lemma 10 155 7: the source maps to the henselization form a natural
transformation. -/
private theorem etaleResidueFieldNeighborhoodSourceToHenselization_naturality
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    ∀ ⦃A B : EtaleResidueFieldNeighborhoodCategory R p⦄ (f : A ⟶ B),
      (etaleResidueFieldNeighborhoodSourceDiagram R p).map f ≫
          etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh B =
        etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh A ≫
          ((Functor.const (EtaleResidueFieldNeighborhoodCategory R p)).obj
            (etaleResidueFieldNeighborhoodSourceHenselizationPoint R p Rh)).map f := by
  intro A B f
  apply CommAlgCat.hom_ext
  -- Proof comment: evaluate the localized naturality equation on the image of a source element
  -- in `A_q`; by definition the source maps are obtained by this precomposition.
  apply DFunLike.ext
  intro x
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj)) :=
    RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p B)
  have hlocnat := congrArg (fun e => CommAlgCat.Hom.hom e)
    (etaleResidueFieldNeighborhoodLocalizationToHenselization_naturality p Rh f)
  simp only [CommAlgCat.hom_comp, Functor.const_obj_obj, Functor.const_obj_map,
    Category.comp_id] at hlocnat
  have hmap := congrArg
    (fun g :
      Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →ₐ[Localization.AtPrime p] Rh =>
        g ((algebraMap A.obj.left
          (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) x))
    hlocnat
  have htoMap := Localization.localRingHom_to_map
    (residueFieldPointedAlgebraKernel R p A.obj)
    (residueFieldPointedAlgebraKernel R p B.obj)
    (etaleResidueFieldNeighborhoodHom R p f)
    (residueFieldPointedAlgebraKernel_comap R p f.hom)
    x
  calc
    (CommAlgCat.Hom.hom
          ((etaleResidueFieldNeighborhoodSourceDiagram R p).map f ≫
            etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh B)) x =
        (CommAlgCat.Hom.hom
          (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh B))
          ((algebraMap B.obj.left
            (Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj)))
            ((etaleResidueFieldNeighborhoodHom R p f) x)) := by
      rfl
    _ = (CommAlgCat.Hom.hom
          (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh B))
          ((Localization.localRingHom
            (residueFieldPointedAlgebraKernel R p A.obj)
            (residueFieldPointedAlgebraKernel R p B.obj)
            (etaleResidueFieldNeighborhoodHom R p f)
            (residueFieldPointedAlgebraKernel_comap R p f.hom))
            ((algebraMap A.obj.left
              (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) x)) := by
      exact congrArg
        (fun y => (CommAlgCat.Hom.hom
          (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh B)) y)
        htoMap.symm
    _ = (CommAlgCat.Hom.hom
          (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A))
          ((algebraMap A.obj.left
            (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))) x) := hmap
    _ = (CommAlgCat.Hom.hom
          (etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh A ≫
            ((Functor.const (EtaleResidueFieldNeighborhoodCategory R p)).obj
              (etaleResidueFieldNeighborhoodSourceHenselizationPoint R p Rh)).map f)) x := by
      rfl

/-- The canonical cocone from the localized neighborhood diagram to a chosen henselization
`R_p^h`. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    Cocone (etaleResidueFieldNeighborhoodLocalizationDiagram R p) where
  pt := CommAlgCat.of (Localization.AtPrime p) Rh
  ι :=
    { app := etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh
      naturality := etaleResidueFieldNeighborhoodLocalizationToHenselization_naturality p Rh }

/-- The canonical cocone from the source neighborhood diagram to a chosen henselization `R_p^h`,
viewed as an `R`-algebra by restriction of scalars. -/
noncomputable def etaleResidueFieldNeighborhoodSourceCoconeToHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    Cocone (etaleResidueFieldNeighborhoodSourceDiagram R p) where
  pt := etaleResidueFieldNeighborhoodSourceHenselizationPoint R p Rh
  ι :=
    { app := etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh
      naturality := etaleResidueFieldNeighborhoodSourceToHenselization_naturality p Rh }

/-!
The next block proves filteredness directly for pointed étale algebras over an arbitrary field
target. This avoids transporting through localized closed-neighborhood categories: tensor products
give common refinements, and the formally unramified equality-locus element gives the equalizer
refinement after a principal localization.
-/

/-- Helper for Chap10 Lemma 10 155 7: the object property selecting generic pointed étale
`R`-algebras over a fixed field `K`. -/
private abbrev etalePointedAlgebraProperty (R : Type u) [CommRing R]
    (K : Type u) [Field K] [Algebra R K] :
    ObjectProperty (Over (CommAlgCat.of R K)) :=
  fun A : Over (CommAlgCat.of R K) ↦ RingHom.Etale (algebraMap R A.left)

/-- Helper for Chap10 Lemma 10 155 7: the generic category of étale `R`-algebras equipped with
an `R`-algebra map to a fixed field `K`. -/
private abbrev EtalePointedAlgebraCategory (R : Type u) [CommRing R]
    (K : Type u) [Field K] [Algebra R K] :=
  (etalePointedAlgebraProperty R K).FullSubcategory

/-- Helper for Chap10 Lemma 10 155 7: the structure map of a generic pointed algebra to its
fixed field target. -/
private noncomputable abbrev pointedAlgebraToTarget
    {K : Type u} [Field K] [Algebra R K] (A : Over (CommAlgCat.of R K)) :
    A.left →+* K :=
  let φ := (forget₂ (CommAlgCat R) CommRingCat).map A.hom
  φ.hom

/-- Helper for Chap10 Lemma 10 155 7: the target map is compatible with the `R`-algebra
structures. -/
private theorem pointedAlgebraToTarget_commutes
    {K : Type u} [Field K] [Algebra R K] (A : Over (CommAlgCat.of R K)) (r : R) :
    pointedAlgebraToTarget A ((algebraMap R A.left) r) = algebraMap R K r := by
  -- Proof comment: this is the commutativity condition stored in the over-category object.
  simp [pointedAlgebraToTarget]

/-- Helper for Chap10 Lemma 10 155 7: the target map as an `R`-algebra homomorphism. -/
private noncomputable def pointedAlgebraToTargetAlgHom
    {K : Type u} [Field K] [Algebra R K] (A : Over (CommAlgCat.of R K)) :
    A.left →ₐ[R] K where
  toRingHom := pointedAlgebraToTarget A
  commutes' := pointedAlgebraToTarget_commutes A

/-- Helper for Chap10 Lemma 10 155 7: the underlying `R`-algebra map of a morphism of pointed
algebras. -/
private abbrev pointedAlgebraHomAlgHom
    {K : Type u} [Field K] [Algebra R K]
    {A B : Over (CommAlgCat.of R K)} (f : A ⟶ B) :
    A.left →ₐ[R] B.left :=
  f.left.hom

/-- Helper for Chap10 Lemma 10 155 7: morphisms in the pointed category commute with the fixed
target maps. -/
private theorem pointedAlgebraHom_target_comp
    {K : Type u} [Field K] [Algebra R K]
    {A B : Over (CommAlgCat.of R K)} (f : A ⟶ B) :
    (pointedAlgebraToTargetAlgHom B).comp (pointedAlgebraHomAlgHom f) =
      pointedAlgebraToTargetAlgHom A := by
  -- Proof comment: forget the over-category triangle to an equality of algebra maps.
  apply AlgHom.coe_ringHom_injective
  simpa [pointedAlgebraToTargetAlgHom, pointedAlgebraToTarget, pointedAlgebraHomAlgHom] using
    (congrArg (fun e : A.left ⟶ CommAlgCat.of R K ↦
      ((forget₂ (CommAlgCat R) CommRingCat).map e).hom) f.w)

/-- Helper for Chap10 Lemma 10 155 7: the target map induces the expected scalar tower. -/
private theorem pointedAlgebraToTarget_isScalarTower
    {K : Type u} [Field K] [Algebra R K] (A : Over (CommAlgCat.of R K)) :
    letI : Algebra A.left K := (pointedAlgebraToTarget A).toAlgebra
    IsScalarTower R A.left K := by
  -- Proof comment: scalar-tower compatibility is the same target-map commutativity, read
  -- pointwise on the image of `R`.
  letI : Algebra A.left K := (pointedAlgebraToTarget A).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (pointedAlgebraToTarget_commutes A r).symm

/-- Helper for Chap10 Lemma 10 155 7: the identity `R`-algebra is étale over `R`. -/
private theorem etalePointedAlgebraBase_etale :
    RingHom.Etale (algebraMap R (CommAlgCat.of R R : Type u)) := by
  -- Proof comment: the base pointed object has the identity structure map, hence a bijective
  -- structure map.
  have hbij : Function.Bijective (algebraMap R (CommAlgCat.of R R : Type u)) := by
    simpa using (Function.bijective_id : Function.Bijective (fun x : R ↦ x))
  exact RingHom.Etale.of_bijective hbij

/-- Helper for Chap10 Lemma 10 155 7: the initial pointed object used for nonemptiness. -/
private noncomputable abbrev etalePointedAlgebraBaseObject
    {K : Type u} [Field K] [Algebra R K] :
    EtalePointedAlgebraCategory R K :=
  ⟨Over.mk (CommAlgCat.ofHom (Algebra.ofId R K)), etalePointedAlgebraBase_etale⟩

/-- Helper for Chap10 Lemma 10 155 7: the tensor-product map to the fixed field target. -/
private noncomputable def etalePointedAlgebraTensorTargetMap
    {K : Type u} [Field K] [Algebra R K]
    (A B : EtalePointedAlgebraCategory R K) :
    ((A.obj.left) ⊗[R] (B.obj.left)) →ₐ[R] K :=
  Algebra.TensorProduct.lift
    (pointedAlgebraToTargetAlgHom A.obj)
    (pointedAlgebraToTargetAlgHom B.obj)
    (fun _ _ ↦ .all _ _)

/-- Helper for Chap10 Lemma 10 155 7: the tensor target map restricts to the first target
map. -/
private theorem etalePointedAlgebraTensorTargetMap_comp_includeLeft
    {K : Type u} [Field K] [Algebra R K]
    (A B : EtalePointedAlgebraCategory R K) :
    (etalePointedAlgebraTensorTargetMap A B).comp
      (Algebra.TensorProduct.includeLeft :
        A.obj.left →ₐ[R] (A.obj.left) ⊗[R] (B.obj.left)) =
      pointedAlgebraToTargetAlgHom A.obj := by
  -- Proof comment: this is the left computation rule for the tensor-product lift.
  simp [etalePointedAlgebraTensorTargetMap]

/-- Helper for Chap10 Lemma 10 155 7: the tensor target map restricts to the second target
map. -/
private theorem etalePointedAlgebraTensorTargetMap_comp_includeRight
    {K : Type u} [Field K] [Algebra R K]
    (A B : EtalePointedAlgebraCategory R K) :
    (etalePointedAlgebraTensorTargetMap A B).comp
      (Algebra.TensorProduct.includeRight :
        B.obj.left →ₐ[R] (A.obj.left) ⊗[R] (B.obj.left)) =
      pointedAlgebraToTargetAlgHom B.obj := by
  -- Proof comment: this is the right computation rule for the tensor-product lift.
  simp [etalePointedAlgebraTensorTargetMap]

/-- Helper for Chap10 Lemma 10 155 7: the tensor product of two generic pointed étale algebras
is étale over the base. -/
private theorem etalePointedAlgebraTensorProduct_etale
    {K : Type u} [Field K] [Algebra R K]
    (A B : EtalePointedAlgebraCategory R K) :
    RingHom.Etale (algebraMap R ((A.obj.left) ⊗[R] (B.obj.left))) := by
  -- Proof comment: view the tensor product as an étale base change of `B`, then compose with
  -- the étale structure map of `A`.
  let _ : Algebra.Etale R A.obj.left :=
    (RingHom.etale_algebraMap (R := R) (S := A.obj.left)).1 A.property
  let _ : Algebra.Etale R B.obj.left :=
    (RingHom.etale_algebraMap (R := R) (S := B.obj.left)).1 B.property
  exact (RingHom.etale_algebraMap (R := R)
    (S := (A.obj.left) ⊗[R] (B.obj.left))).2
      (Algebra.Etale.comp R A.obj.left ((A.obj.left) ⊗[R] (B.obj.left)))

/-- Helper for Chap10 Lemma 10 155 7: tensor products give binary common refinements in the
generic pointed étale category. -/
private theorem etalePointedAlgebra_tensorRefinement
    {K : Type u} [Field K] [Algebra R K]
    (A B : EtalePointedAlgebraCategory R K) :
    ∃ C : EtalePointedAlgebraCategory R K, Nonempty (A ⟶ C) ∧ Nonempty (B ⟶ C) := by
  -- Proof comment: package the tensor product with its induced target map, then use the two
  -- tensor inclusions as morphisms over the fixed field.
  let Cobj : Over (CommAlgCat.of R K) :=
    Over.mk (CommAlgCat.ofHom (etalePointedAlgebraTensorTargetMap A B))
  let C : EtalePointedAlgebraCategory R K :=
    ⟨Cobj, etalePointedAlgebraTensorProduct_etale A B⟩
  refine ⟨C, ?_, ?_⟩
  · refine ⟨ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft :
          A.obj.left →ₐ[R] (A.obj.left) ⊗[R] (B.obj.left))) ?_)⟩
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have h := congrArg (fun e : A.obj.left →ₐ[R] K ↦ e x)
      (etalePointedAlgebraTensorTargetMap_comp_includeLeft A B)
    simpa [Cobj, pointedAlgebraToTargetAlgHom, pointedAlgebraToTarget] using h
  · refine ⟨ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight :
          B.obj.left →ₐ[R] (A.obj.left) ⊗[R] (B.obj.left))) ?_)⟩
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have h := congrArg (fun e : B.obj.left →ₐ[R] K ↦ e x)
      (etalePointedAlgebraTensorTargetMap_comp_includeRight A B)
    simpa [Cobj, pointedAlgebraToTargetAlgHom, pointedAlgebraToTarget] using h

/-- Helper for Chap10 Lemma 10 155 7: the formally unramified equality-locus element for two
parallel morphisms in the generic pointed étale category. -/
private noncomputable def etalePointedAlgebra_equalizerElement
    {K : Type u} [Field K] [Algebra R K]
    {A B : EtalePointedAlgebraCategory R K} (f g : A ⟶ B) :
    B.obj.left :=
  let _ : Algebra.Etale R A.obj.left :=
    (RingHom.etale_algebraMap (R := R) (S := A.obj.left)).1 A.property
  (Algebra.TensorProduct.lift
    (pointedAlgebraHomAlgHom f.hom)
    (pointedAlgebraHomAlgHom g.hom)
    (fun _ _ ↦ .all _ _))
    (Algebra.FormallyUnramified.elem R A.obj.left)

/-- Helper for Chap10 Lemma 10 155 7: applying the same target map on both tensor factors is
the target map after multiplication. -/
private theorem etalePointedAlgebraTensorLift_toTarget_eq_lmul
    {K : Type u} [Field K] [Algebra R K]
    (A : EtalePointedAlgebraCategory R K) :
    Algebra.TensorProduct.lift
        (pointedAlgebraToTargetAlgHom A.obj) (pointedAlgebraToTargetAlgHom A.obj)
        (fun _ _ ↦ .all _ _) =
      (pointedAlgebraToTargetAlgHom A.obj).comp (Algebra.TensorProduct.lmul' R) := by
  -- Proof comment: tensor-product extensionality reduces the comparison to the two generators.
  ext x
  · simp
  · simp

/-- Helper for Chap10 Lemma 10 155 7: the equalizer element maps to `1` in the fixed target
field. -/
private theorem etalePointedAlgebra_equalizerElement_toTarget
    {K : Type u} [Field K] [Algebra R K]
    {A B : EtalePointedAlgebraCategory R K} (f g : A ⟶ B) :
    pointedAlgebraToTarget B.obj (etalePointedAlgebra_equalizerElement f g) = 1 := by
  -- Proof comment: both parallel maps are over `K`, so after applying the target map to both
  -- tensor factors the unramified equality element multiplies to `1`.
  let hB := pointedAlgebraToTargetAlgHom B.obj
  let hA := pointedAlgebraToTargetAlgHom A.obj
  have hcomp :
      hB.comp (Algebra.TensorProduct.lift
          (pointedAlgebraHomAlgHom f.hom) (pointedAlgebraHomAlgHom g.hom)
          (fun _ _ ↦ .all _ _)) =
        Algebra.TensorProduct.lift hA hA (fun _ _ ↦ .all _ _) := by
    ext x
    · simpa [hB, hA, AlgHom.comp_apply] using
        DFunLike.congr_fun (pointedAlgebraHom_target_comp f.hom) x
    · simpa [hB, hA, AlgHom.comp_apply] using
        DFunLike.congr_fun (pointedAlgebraHom_target_comp g.hom) x
  let _ : Algebra.Etale R A.obj.left :=
    (RingHom.etale_algebraMap (R := R) (S := A.obj.left)).1 A.property
  calc
    pointedAlgebraToTarget B.obj (etalePointedAlgebra_equalizerElement f g) =
        hB ((Algebra.TensorProduct.lift
          (pointedAlgebraHomAlgHom f.hom) (pointedAlgebraHomAlgHom g.hom)
          (fun _ _ ↦ .all _ _))
          (Algebra.FormallyUnramified.elem R A.obj.left)) := by
      rfl
    _ = (Algebra.TensorProduct.lift hA hA (fun _ _ ↦ .all _ _))
          (Algebra.FormallyUnramified.elem R A.obj.left) := by
      exact DFunLike.congr_fun hcomp (Algebra.FormallyUnramified.elem R A.obj.left)
    _ = ((pointedAlgebraToTargetAlgHom A.obj).comp (Algebra.TensorProduct.lmul' R))
          (Algebra.FormallyUnramified.elem R A.obj.left) := by
      rw [etalePointedAlgebraTensorLift_toTarget_eq_lmul]
    _ = 1 := by
      simp [Algebra.FormallyUnramified.lmul_elem]

/-- Helper for Chap10 Lemma 10 155 7: multiplying by the equalizer element kills the difference
of two parallel pointed morphisms. -/
private theorem etalePointedAlgebra_map_sub_mul_equalizerElement
    {K : Type u} [Field K] [Algebra R K]
    {A B : EtalePointedAlgebraCategory R K} (f g : A ⟶ B) (a : A.obj.left) :
    (pointedAlgebraHomAlgHom f.hom a - pointedAlgebraHomAlgHom g.hom a) *
      etalePointedAlgebra_equalizerElement f g = 0 := by
  -- Proof comment: push the formally unramified identity through the two maps into `B`.
  let _ : Algebra.Etale R A.obj.left :=
    (RingHom.etale_algebraMap (R := R) (S := A.obj.left)).1 A.property
  let L : ((A.obj.left) ⊗[R] (A.obj.left)) →ₐ[R] B.obj.left :=
    Algebra.TensorProduct.lift
      (pointedAlgebraHomAlgHom f.hom) (pointedAlgebraHomAlgHom g.hom)
      (fun _ _ ↦ .all _ _)
  have h :=
    congrArg L (Algebra.FormallyUnramified.one_tmul_mul_elem
      (R := R) (S := A.obj.left) a)
  simpa [L, etalePointedAlgebra_equalizerElement, Algebra.TensorProduct.lift_tmul, sub_mul] using
    sub_eq_zero.mpr h.symm

/-- Helper for Chap10 Lemma 10 155 7: powers of an equalizer element become units in the fixed
target field. -/
private theorem etalePointedAlgebraEqualizerTargetMap_units
    {K : Type u} [Field K] [Algebra R K]
    (B : EtalePointedAlgebraCategory R K) (s : B.obj.left)
    (hs : pointedAlgebraToTarget B.obj s = 1) :
    ∀ y : Submonoid.powers s, IsUnit ((pointedAlgebraToTargetAlgHom B.obj) y) := by
  -- Proof comment: every denominator is a power of `s`, and `s` maps to the unit `1`.
  intro y
  rcases (Submonoid.mem_powers_iff y.1 s).mp y.2 with ⟨n, hn⟩
  have hsAlg : (pointedAlgebraToTargetAlgHom B.obj) s = 1 := by
    exact hs
  rw [← hn, map_pow, hsAlg, one_pow]
  exact isUnit_one

/-- Helper for Chap10 Lemma 10 155 7: the target map extends over the principal localization
that inverts the equalizer element. -/
private noncomputable def etalePointedAlgebraEqualizerTargetMap
    {K : Type u} [Field K] [Algebra R K]
    (B : EtalePointedAlgebraCategory R K) (s : B.obj.left)
    (hs : pointedAlgebraToTarget B.obj s = 1) :
    Localization.Away s →ₐ[R] K :=
  let _ : Algebra B.obj.left K := (pointedAlgebraToTarget B.obj).toAlgebra
  let _ : IsScalarTower R B.obj.left K := pointedAlgebraToTarget_isScalarTower B.obj
  IsLocalization.liftAlgHom (A := R) (R := B.obj.left)
    (M := Submonoid.powers s) (S := Localization.Away s) (P := K)
    (f := pointedAlgebraToTargetAlgHom B.obj)
    (etalePointedAlgebraEqualizerTargetMap_units B s hs)

/-- Helper for Chap10 Lemma 10 155 7: the canonical map from a pointed algebra to its away
localization is an `R`-algebra map. -/
private noncomputable def etalePointedAlgebraAwayAlgHom
    {K : Type u} [Field K] [Algebra R K]
    (B : EtalePointedAlgebraCategory R K) (s : B.obj.left) :
    B.obj.left →ₐ[R] Localization.Away s where
  toRingHom := algebraMap B.obj.left (Localization.Away s)
  commutes' r := by
    -- Proof comment: the source and target `R`-algebra structures are connected by the usual
    -- scalar tower through `B`.
    simp [IsScalarTower.algebraMap_apply R B.obj.left (Localization.Away s)]

/-- Helper for Chap10 Lemma 10 155 7: the localized target map restricts to the original target
map on the source algebra. -/
private theorem etalePointedAlgebraEqualizerTargetMap_comp_algebraMap
    {K : Type u} [Field K] [Algebra R K]
    (B : EtalePointedAlgebraCategory R K) (s : B.obj.left)
    (hs : pointedAlgebraToTarget B.obj s = 1) :
    (etalePointedAlgebraEqualizerTargetMap B s hs).comp
        (etalePointedAlgebraAwayAlgHom B s) =
      pointedAlgebraToTargetAlgHom B.obj := by
  -- Proof comment: this is the universal-property computation rule for localization.
  apply AlgHom.coe_ringHom_injective
  ext x
  exact IsLocalization.lift_eq (etalePointedAlgebraEqualizerTargetMap_units B s hs) x

/-- Helper for Chap10 Lemma 10 155 7: the principal localization of a generic pointed étale
algebra is still étale over the base. -/
private theorem etalePointedAlgebraEqualizerAway_etale
    {K : Type u} [Field K] [Algebra R K]
    (B : EtalePointedAlgebraCategory R K) (s : B.obj.left) :
    RingHom.Etale (algebraMap R (Localization.Away s)) := by
  -- Proof comment: compose the étale map `R → B` with the étale away localization `B → B[1/s]`.
  let _ : Algebra.Etale R B.obj.left :=
    (RingHom.etale_algebraMap (R := R) (S := B.obj.left)).1 B.property
  exact (RingHom.etale_algebraMap (R := R) (S := Localization.Away s)).2
    (Algebra.Etale.comp R B.obj.left (Localization.Away s))

/-- Helper for Chap10 Lemma 10 155 7: principal localization at the equalizer element equalizes
parallel morphisms in the generic pointed étale category. -/
private theorem etalePointedAlgebra_equalizerRefinement
    {K : Type u} [Field K] [Algebra R K]
    {A B : EtalePointedAlgebraCategory R K} (f g : A ⟶ B) :
    ∃ C : EtalePointedAlgebraCategory R K, ∃ h : B ⟶ C, f ≫ h = g ≫ h := by
  -- Proof comment: invert the unramified equality-locus element, extend the target map over the
  -- localization, and then use the localization zero criterion to equalize the two maps.
  let s : B.obj.left := etalePointedAlgebra_equalizerElement f g
  have hs : pointedAlgebraToTarget B.obj s = 1 :=
    etalePointedAlgebra_equalizerElement_toTarget f g
  let Cobj : Over (CommAlgCat.of R K) :=
    Over.mk (CommAlgCat.ofHom (etalePointedAlgebraEqualizerTargetMap B s hs))
  let C : EtalePointedAlgebraCategory R K :=
    ⟨Cobj, etalePointedAlgebraEqualizerAway_etale B s⟩
  let hOver : B.obj ⟶ C.obj :=
    Over.homMk (CommAlgCat.ofHom (etalePointedAlgebraAwayAlgHom B s)) (by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      have hcomp := congrArg (fun e : B.obj.left →ₐ[R] K ↦ e x)
        (etalePointedAlgebraEqualizerTargetMap_comp_algebraMap B s hs)
      simpa [Cobj, pointedAlgebraToTargetAlgHom, pointedAlgebraToTarget] using hcomp)
  let h : B ⟶ C := ObjectProperty.homMk hOver
  refine ⟨C, h, ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  dsimp [h, hOver, pointedAlgebraHomAlgHom]
  let M : Submonoid B.obj.left := Submonoid.powers s
  have hzero : algebraMap B.obj.left (Localization.Away s)
      (pointedAlgebraHomAlgHom f.hom a - pointedAlgebraHomAlgHom g.hom a) = 0 := by
    rw [IsLocalization.map_eq_zero_iff M (Localization.Away s)]
    have hs_pow : s ∈ M := (Submonoid.mem_powers_iff s s).mpr ⟨1, pow_one s⟩
    refine ⟨⟨s, hs_pow⟩, ?_⟩
    simpa [M, mul_comm] using etalePointedAlgebra_map_sub_mul_equalizerElement f g a
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- Helper for Chap10 Lemma 10 155 7: generic pointed étale algebras over a fixed field form a
filtered category. -/
private theorem etalePointedAlgebraCategory_isFiltered
    {K : Type u} [Field K] [Algebra R K] :
    IsFiltered (EtalePointedAlgebraCategory R K) where
  nonempty := ⟨etalePointedAlgebraBaseObject⟩
  cocone_objs A B := by
    -- Proof comment: tensor products provide common refinements for object pairs.
    obtain ⟨C, hA, hB⟩ := etalePointedAlgebra_tensorRefinement A B
    obtain ⟨f⟩ := hA
    obtain ⟨g⟩ := hB
    exact ⟨C, f, g, trivial⟩
  cocone_maps := by
    -- Proof comment: the equalizer principal localization handles parallel morphisms.
    intro A B f g
    exact etalePointedAlgebra_equalizerRefinement f g

-- Proof sketch: the pair `(R, p)` yields an object of the category, tensor products of étale
-- neighborhoods remain étale and admit a prime over `p` with residue field `κ(p)`, and the usual
-- iterated fiber-product construction over `κ(p)` equalizes parallel morphisms.
/-- Lemma 10.155.7 (1): the category of étale neighborhoods `(S, q)` of `p` with residue field
`κ(q) = κ(p)` is filtered. -/
@[stacks 04GV]
theorem etaleResidueFieldNeighborhoodCategory_isFiltered :
    IsFiltered (EtaleResidueFieldNeighborhoodCategory R p) := by
  -- Route correction: prove filteredness in the generic over-field pointed category and then
  -- specialize the field target to `κ(p)`, avoiding localized closed-neighborhood transport.
  simpa [EtaleResidueFieldNeighborhoodCategory, etaleResidueFieldPointedAlgebraProperty,
    ResidueFieldPointedAlgebraCategory, EtalePointedAlgebraCategory] using
      (etalePointedAlgebraCategory_isFiltered (R := R) (K := p.ResidueField))

/-- Helper for Chap10 Lemma 10 155 7: the canonical source map to a henselization sends every
element outside the chosen prime of a neighborhood to a unit. -/
private theorem etaleResidueFieldNeighborhoodSourceToHenselizationHom_isUnit_of_notMem
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (A : EtaleResidueFieldNeighborhoodCategory R p) {x : A.obj.left}
    (hx : x ∉ residueFieldPointedAlgebraKernel R p A.obj) :
    IsUnit ((etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh A).hom x) := by
  -- Proof comment: first invert `x` in the local ring `S_q`, then map that unit along the
  -- canonical localized morphism `S_q → R_p^h`.
  let q : Ideal A.obj.left := residueFieldPointedAlgebraKernel R p A.obj
  have hxUnit :
      IsUnit ((algebraMap A.obj.left (Localization.AtPrime q)) x) :=
    IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q) ⟨x, hx⟩
  rcases hxUnit with ⟨ux, hux⟩
  let f : Localization.AtPrime q →+* Rh :=
    (etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh A).hom.toRingHom
  refine ⟨Units.map f ux, ?_⟩
  have hmap := congrArg f hux
  simpa [q, f, etaleResidueFieldNeighborhoodSourceToHenselizationHom] using hmap

/-- Helper for Chap10 Lemma 10 155 7: if an element becomes a unit after a refinement of
source neighborhoods, then every source-diagram cocone maps it to a unit. -/
private theorem sourceCocone_map_isUnit_of_refinement
    (s : Cocone (etaleResidueFieldNeighborhoodSourceDiagram R p))
    {A B : EtaleResidueFieldNeighborhoodCategory R p} (f : A ⟶ B) {x : A.obj.left}
    (hx : IsUnit ((etaleResidueFieldNeighborhoodHom R p f) x)) :
    IsUnit ((s.ι.app A).hom x) := by
  -- Proof comment: naturality identifies the `A`-leg with the `B`-leg after the refinement;
  -- units are preserved by the `B`-leg and then transported across that equality.
  have hnat := congrArg (fun e => CommAlgCat.Hom.hom e) (s.w f)
  have hpoint := congrFun (congrArg DFunLike.coe hnat) x
  have hpoint' :
      (s.ι.app B).hom ((etaleResidueFieldNeighborhoodHom R p f) x) =
        (s.ι.app A).hom x := by
    simpa [etaleResidueFieldNeighborhoodSourceDiagram, etaleResidueFieldNeighborhoodHom,
      residueFieldPointedAlgebraHom] using hpoint
  exact hpoint'.symm ▸ (hx.map (s.ι.app B).hom.toRingHom)

/-- Helper for Chap10 Lemma 10 155 7: the localized residue-field neighborhood cocone is
colimiting once the finite-presentation factorization/finality comparison with the henselization
ind-étale presentation has been established. -/
private noncomputable def
    etaleResidueFieldNeighborhoodLocalizationCocone_isColimit_via_factorization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    IsColimit (etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization p Rh) :=
  -- Route correction: the owner property `IsHenselizationOf.isFilteredColimitOfEtale` is not a
  -- concrete diagram to whisker. The remaining proof must show the current localized
  -- residue-field neighborhood stages satisfy the finite-presentation factorization criterion.
  -- TODO: prove every finitely presented `R_p`-algebra over `Rh` factors through a localized
  -- residue-field neighborhood, then transfer the selected-over-target colimit along that final
  -- comparison.
  sorry

/-- Helper for Chap10 Lemma 10 155 7: the source residue-field neighborhood cocone is colimiting
after arbitrary source cocones are shown to invert the chosen denominators and the localized
colimit is applied. -/
private noncomputable def etaleResidueFieldNeighborhoodSourceCocone_isColimit_via_localization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh]
    (hLoc : IsColimit (etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization p Rh)) :
    IsColimit (etaleResidueFieldNeighborhoodSourceCoconeToHenselization p Rh) :=
  -- Route correction: restriction of scalars alone is not the colimit bridge. The missing source
  -- step is a denominator-inversion theorem for arbitrary source cocones, proved by
  -- principal-open refinements inside the residue-field neighborhood category.
  -- TODO: construct the localized cocone associated to an arbitrary source cocone via
  -- `IsLocalization.lift`, use `hLoc` for descent/factorization/uniqueness, and compare back on
  -- the source maps.
  sorry

-- Proof sketch: compare this diagram with the filtered diagram used in the construction of the
-- henselization of `R_p` in Lemma `10.155.1`. Localizing an object `(S, q)` at `q` does not
-- change the corresponding henselian colimit, and every étale neighborhood of `R_p` with residue
-- field `κ(p)` descends from one over `R`.
/-- Lemma 10.155.7 (2): the canonical cocone from the source diagram `(S, q) ↦ S` to a chosen
henselization `R_p^h`, viewed in `CommAlgCat R`, is colimiting. -/
@[stacks 04GV]
noncomputable def etaleResidueFieldNeighborhoodSourceCoconeToHenselizationIsColimit
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    IsColimit (etaleResidueFieldNeighborhoodSourceCoconeToHenselization p Rh) :=
  -- Proof comment: reduce the source colimit to the localized colimit through the explicit
  -- denominator-inversion bridge isolated above.
  etaleResidueFieldNeighborhoodSourceCocone_isColimit_via_localization p Rh
    (etaleResidueFieldNeighborhoodLocalizationCocone_isColimit_via_factorization p Rh)

-- Proof sketch: after replacing each object `(S, q)` by its localization `S_q`, the resulting
-- filtered diagram is the standard étale-neighborhood presentation of the henselization of `R_p`.
-- Apply the construction from Lemma `10.155.1` to identify its colimit with any fixed
-- henselization of `R_p`.
/-- Lemma 10.155.7 (3): the canonical cocone from the localized neighborhood diagram
`(S, q) ↦ S_q` to a chosen henselization `R_p^h` is colimiting. -/
@[stacks 04GV]
noncomputable def etaleResidueFieldNeighborhoodLocalizationCoconeToHenselizationIsColimit
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    IsColimit (etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization p Rh) :=
  -- Proof comment: consume the localized finite-presentation/finality bridge isolated above.
  etaleResidueFieldNeighborhoodLocalizationCocone_isColimit_via_factorization p Rh

end
