import Mathlib
import StacksProject_2024.Chap10.Lemma_10_127_4
import StacksProject_2024.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

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
  sorry

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
  sorry

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
      RingHom.id _ := sorry

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
          (residueFieldPointedAlgebraKernel_comap R p f.hom)) := sorry

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
  sorry

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
      commutes' := by
        intro x
        exact congrArg (fun g : Localization.AtPrime p →+*
            Localization.AtPrime (residueFieldPointedAlgebraKernel R p B.obj) ↦ g x)
          (etaleResidueFieldNeighborhoodLocalization_map_commutes R p f) }

/-- The diagram sending an étale neighborhood `(S, q)` of `p` to the localized `R_p`-algebra
`S_q`. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationDiagram (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    EtaleResidueFieldNeighborhoodCategory R p ⥤ CommAlgCat (Localization.AtPrime p) where
  obj A := etaleResidueFieldNeighborhoodLocalizationObject R p A
  map f := etaleResidueFieldNeighborhoodLocalizationMorphism R p f
  map_id A := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun g : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+*
            Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) ↦ g x)
        (residueFieldPointedAlgebraLocalization_map_id R p A)
  map_comp {A B C} f g := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun h : Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj) →+*
            Localization.AtPrime (residueFieldPointedAlgebraKernel R p C.obj) ↦ h x)
        (residueFieldPointedAlgebraLocalization_map_comp R p f g)

private noncomputable abbrev etaleResidueFieldNeighborhoodSourceHenselizationPoint
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh] :
    CommAlgCat R :=
  let _ : Algebra R Rh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.of R Rh

/-- The localization `S_q` of an étale residue-field neighborhood is étale over `R_p`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_etale
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) := by
  sorry

/-- The maximal ideal of `S_q` lies over the maximal ideal of `R_p`. -/
private theorem etaleResidueFieldNeighborhoodLocalization_maximalIdeal_under
    (A : EtaleResidueFieldNeighborhoodCategory R p) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj)) :=
      RingHom.toAlgebra (etaleResidueFieldNeighborhoodLocalizationAlgebraMap R p A)
    (maximalIdeal (Localization.AtPrime (residueFieldPointedAlgebraKernel R p A.obj))).under
      (Localization.AtPrime p) =
      maximalIdeal (Localization.AtPrime p) := by
  sorry

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
    (by
      sorry)

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
  sorry

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
      commutes' := by
        intro x
        sorry }

/-- The canonical cocone from the localized neighborhood diagram to a chosen henselization
`R_p^h`. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    Cocone (etaleResidueFieldNeighborhoodLocalizationDiagram R p) where
  pt := CommAlgCat.of (Localization.AtPrime p) Rh
  ι :=
    { app := etaleResidueFieldNeighborhoodLocalizationToHenselizationHom p Rh
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

/-- The canonical cocone from the source neighborhood diagram to a chosen henselization `R_p^h`,
viewed as an `R`-algebra by restriction of scalars. -/
noncomputable def etaleResidueFieldNeighborhoodSourceCoconeToHenselization
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    Cocone (etaleResidueFieldNeighborhoodSourceDiagram R p) where
  pt := etaleResidueFieldNeighborhoodSourceHenselizationPoint R p Rh
  ι :=
    { app := etaleResidueFieldNeighborhoodSourceToHenselizationHom p Rh
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

-- Proof sketch: the pair `(R, p)` yields an object of the category, tensor products of étale
-- neighborhoods remain étale and admit a prime over `p` with residue field `κ(p)`, and the usual
-- iterated fiber-product construction over `κ(p)` equalizes parallel morphisms.
/-- Lemma 10.155.7 (1): the category of étale neighborhoods `(S, q)` of `p` with residue field
`κ(q) = κ(p)` is filtered. -/
theorem etaleResidueFieldNeighborhoodCategory_isFiltered :
    IsFiltered (EtaleResidueFieldNeighborhoodCategory R p) := sorry

-- Proof sketch: compare this diagram with the filtered diagram used in the construction of the
-- henselization of `R_p` in Lemma `10.155.1`. Localizing an object `(S, q)` at `q` does not
-- change the corresponding henselian colimit, and every étale neighborhood of `R_p` with residue
-- field `κ(p)` descends from one over `R`.
/-- Lemma 10.155.7 (2): the canonical cocone from the source diagram `(S, q) ↦ S` to a chosen
henselization `R_p^h`, viewed in `CommAlgCat R`, is colimiting. -/
noncomputable def etaleResidueFieldNeighborhoodSourceCoconeToHenselizationIsColimit
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    IsColimit (etaleResidueFieldNeighborhoodSourceCoconeToHenselization p Rh) := by
  sorry

-- Proof sketch: after replacing each object `(S, q)` by its localization `S_q`, the resulting
-- filtered diagram is the standard étale-neighborhood presentation of the henselization of `R_p`.
-- Apply the construction from Lemma `10.155.1` to identify its colimit with any fixed
-- henselization of `R_p`.
/-- Lemma 10.155.7 (3): the canonical cocone from the localized neighborhood diagram
`(S, q) ↦ S_q` to a chosen henselization `R_p^h` is colimiting. -/
noncomputable def etaleResidueFieldNeighborhoodLocalizationCoconeToHenselizationIsColimit
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime p) Rh]
    [IsHenselizationOf (Localization.AtPrime p) Rh] :
    IsColimit (etaleResidueFieldNeighborhoodLocalizationCoconeToHenselization p Rh) := by
  sorry

end
