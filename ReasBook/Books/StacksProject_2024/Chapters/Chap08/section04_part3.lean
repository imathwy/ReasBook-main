import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Small

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_4_3_AmbientIsoClosure (from Chap08) -/
open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)

variable [IsStackOnSite J p]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: the fixed-cover ambient target property asks that every component of
an ambient descent datum over the chosen cover belongs to the corresponding fiberwise
`isoClosure` of `P`. -/
def cover_componentwise_isoClosure_property
    {U : C} (S : J.Cover U) :
    ObjectProperty
      (((canonicalFiberPseudofunctor p).DescentData (fun I : S.Arrow ↦ I.f))) :=
  fun D ↦
    ∀ I : S.Arrow,
      ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure) (D.obj I)

/-- Helper for Lemma 8.4.3: each componentwise `isoClosure` witness in the ambient fixed-cover
target can be strictified to a chosen object of the inverse-image full subcategory. -/
theorem restricted_cover_component_choice_exists
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    ∃ y : (P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).FullSubcategory,
      Nonempty (y.obj ≅ D.obj.obj I) := by
  -- Unpack the `isoClosure` predicate on the `I`-th component and flip the exhibited isomorphism.
  rcases (ObjectProperty.prop_isoClosure_iff
      (P := P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X))
      (X := D.obj.obj I)).1 (D.property I) with ⟨Y, hY, ⟨e⟩⟩
  exact ⟨⟨Y, hY⟩, ⟨e.symm⟩⟩

/-- Helper for Lemma 8.4.3: choose a strict representative for the `I`-th component of an
ambient descent datum in the componentwise `isoClosure` target. -/
noncomputable def restricted_cover_component_choice
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).FullSubcategory :=
  Classical.choose
    (restricted_cover_component_choice_exists (J := J) (p := p) (P := P) S D I)

/-- Helper for Lemma 8.4.3: the chosen strict representative comes equipped with the comparison
isomorphism back to the original ambient descent component. -/
noncomputable def restricted_cover_component_choice_iso
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I).obj ≅ D.obj.obj I := by
  -- The comparison isomorphism is the second component of the chosen existence witness.
  exact Classical.choice
    (Classical.choose_spec
      (restricted_cover_component_choice_exists (J := J) (p := p) (P := P) S D I))

/-- Helper for Lemma 8.4.3: the chosen strict representative still carries the inverse-image
property by construction. -/
theorem restricted_cover_component_choice_property
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X))
      ((restricted_cover_component_choice (J := J) (p := p) (P := P) S D I).obj) := by
  -- The chosen object lives in the inverse-image full subcategory, so its property is immediate.
  exact (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I).property

/-- Helper for Lemma 8.4.3: the chosen strict representative is fixed by the roundtrip through
the restricted fiber, after forgetting back to the ambient fiber. -/
noncomputable def restricted_cover_component_roundtrip_iso
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I))).obj ≅
      (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I).obj :=
  eqToIso <|
    congrArg
      (fun z ↦ z.obj)
      (fullSubcategory_fiber_equiv_inverseImage_functor_inverse_obj
        (p := p) (P := P) I.Y
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I))

/-- Helper for Lemma 8.4.3: the roundtrip component identification composed with the chosen
`isoClosure` witness gives the ambient comparison from the strict component back to `D`. -/
noncomputable def restricted_cover_component_total_iso
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I))).obj ≅
      D.obj.obj I :=
  restricted_cover_component_roundtrip_iso (J := J) (p := p) (P := P) S D I ≪≫
    restricted_cover_component_choice_iso (J := J) (p := p) (P := P) S D I

/-- Helper for Lemma 8.4.3: the component comparison isomorphism is the roundtrip strictification
followed by the chosen `isoClosure` witness. -/
@[simp] theorem restricted_cover_component_total_iso_hom
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I).hom =
      (restricted_cover_component_roundtrip_iso (J := J) (p := p) (P := P) S D I).hom ≫
        (restricted_cover_component_choice_iso (J := J) (p := p) (P := P) S D I).hom := by
  -- Unfold the composite isomorphism once so later shell proofs can isolate the strict part.
  rfl

/-- Helper for Lemma 8.4.3: the inverse component comparison first removes the chosen
`isoClosure` witness and then cancels the roundtrip. -/
@[simp] theorem restricted_cover_component_total_iso_inv
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I).inv =
      (restricted_cover_component_choice_iso (J := J) (p := p) (P := P) S D I).inv ≫
        (restricted_cover_component_roundtrip_iso (J := J) (p := p) (P := P) S D I).inv := by
  -- The inverse of a composite isomorphism reverses the two constituent comparison factors.
  rfl

/-- Helper for Lemma 8.4.3: the strict roundtrip comparison on a chosen component is unchanged
after transporting it into the restricted fiber and back to the inverse-image full subcategory. -/
@[simp] theorem restricted_cover_component_roundtrip_hom_roundtrip_map
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).map
          (ObjectProperty.homMk
            (restricted_cover_component_roundtrip_iso
              (J := J) (p := p) (P := P) S D I).hom)) =
      ObjectProperty.homMk
        (restricted_cover_component_roundtrip_iso
          (J := J) (p := p) (P := P) S D I).hom := by
  -- The strict inverse-image/restricted-fiber roundtrip is exactly the morphism component of the
  -- established fiber equivalence.
  exact
    fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
      (p := p) (P := P) I.Y
      (φ := ObjectProperty.homMk
        (restricted_cover_component_roundtrip_iso
          (J := J) (p := p) (P := P) S D I).hom)

/-- Helper for Lemma 8.4.3: the inverse strict roundtrip comparison on a chosen component is
again unchanged after transporting it into the restricted fiber and back. -/
@[simp] theorem restricted_cover_component_roundtrip_inv_roundtrip_map
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).map
          (ObjectProperty.homMk
            (restricted_cover_component_roundtrip_iso
              (J := J) (p := p) (P := P) S D I).inv)) =
      ObjectProperty.homMk
        (restricted_cover_component_roundtrip_iso
          (J := J) (p := p) (P := P) S D I).inv := by
  -- The same strict roundtrip cancellation applies to the inverse component morphism.
  exact
    fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
      (p := p) (P := P) I.Y
      (φ := ObjectProperty.homMk
        (restricted_cover_component_roundtrip_iso
          (J := J) (p := p) (P := P) S D I).inv)

/-- Helper for Lemma 8.4.3: transporting the strict roundtrip component into the restricted
fiber and back recovers the same inverse-image morphism. -/
@[simp] theorem restricted_cover_component_total_iso_roundtrip_map
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    (I : S.Arrow) :
    (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).map
          (ObjectProperty.homMk
            (restricted_cover_component_roundtrip_iso
              (J := J) (p := p) (P := P) S D I).hom)) =
      ObjectProperty.homMk
        (restricted_cover_component_roundtrip_iso
          (J := J) (p := p) (P := P) S D I).hom := by
  -- This packages the roundtrip cancellation with the source-proof notation used later in the
  -- reverse overlap shell.
  simpa using
    restricted_cover_component_roundtrip_hom_roundtrip_map
      (J := J) (p := p) (P := P) (S := S) (D := D) I

/-- Helper for Lemma 8.4.3: the ambient canonical descent datum of an object already lying in the
inverse-image full subcategory satisfies the componentwise `isoClosure` condition on the cover
legs. -/
lemma ambient_cover_toDescentData_mem_componentwise_isoClosure
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S
      ((((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
          ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f))).obj x) := by
  intro I
  -- Each cover leg is the ambient canonical pullback of the source fiber object, so `hpullback`
  -- supplies the required `isoClosure` witness componentwise.
  simpa [cover_componentwise_isoClosure_property] using hpullback I.f x.1 x.2

/-- Helper for Lemma 8.4.3: restrict the ambient fixed-cover descent functor to the full
subcategory cut out by the componentwise `isoClosure` predicate. -/
noncomputable def ambient_cover_toDescentData_isoClosure
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory ⥤
      (cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S).FullSubcategory :=
  (cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S).lift
    ((((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
        ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f))))
    (ambient_cover_toDescentData_mem_componentwise_isoClosure
      (J := J) (p := p) (P := P) hpullback S)

/-- Helper for Lemma 8.4.3: the ambient fixed-cover descent functor restricted to the
componentwise `isoClosure` target is essentially surjective. -/
lemma ambient_cover_toDescentData_isoClosure_essSurj
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (hlocal : ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
      (hx : ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x)),
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x)
    {U : C} (S : J.Cover U) :
    Functor.EssSurj (ambient_cover_toDescentData_isoClosure
      (J := J) (p := p) (P := P) hpullback S) := by
  let F := ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f))
  have hFEquiv : F.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p).1 inferInstance U S
  letI : F.IsEquivalence := hFEquiv
  refine ⟨fun D ↦ ?_⟩
  -- Descend the ambient componentwise `isoClosure` datum to a single ambient fiber object.
  rcases Functor.EssSurj.mem_essImage (F := F) D.obj with ⟨x, ⟨e⟩⟩
  have hxPullback :
      ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x) := by
    intro I
    -- Each canonical pullback component is isomorphic to the corresponding component of `D`.
    let eI : (F.obj x).obj I ≅ D.obj.obj I :=
      { hom := e.hom.hom I
        inv := e.inv.hom I
        hom_inv_id := by
          calc
            e.hom.hom I ≫ e.inv.hom I = (e.hom ≫ e.inv).hom I := by
              symm
              simpa using Pseudofunctor.DescentData.comp_hom e.hom e.inv I
            _ = Pseudofunctor.DescentData.Hom.hom (𝟙 (F.obj x)) I := by rw [e.hom_inv_id]
            _ = 𝟙 _ := by simp
        inv_hom_id := by
          calc
            e.inv.hom I ≫ e.hom.hom I = (e.inv ≫ e.hom).hom I := by
              symm
              simpa using Pseudofunctor.DescentData.comp_hom e.inv e.hom I
            _ = Pseudofunctor.DescentData.Hom.hom (𝟙 D.obj) I := by rw [e.inv_hom_id]
            _ = 𝟙 _ := by simp }
    have hI :
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          ((F.obj x).obj I) := by
      exact
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure).prop_of_iso
          eI.symm (D.property I)
    simpa [F] using hI
  have hxIsoClosure :
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x :=
    hlocal S x hxPullback
  rw [ObjectProperty.prop_isoClosure_iff] at hxIsoClosure
  rcases hxIsoClosure with ⟨y, hy, ⟨i⟩⟩
  let y' : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory := ⟨y, hy⟩
  -- Move the descended ambient object into the strict inverse-image full subcategory.
  refine ⟨y', ?_⟩
  refine ⟨ObjectProperty.isoMk
    (P := cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S) ?_⟩
  -- The final comparison is the descended ambient isomorphism, whiskered by the iso in the
  -- source fiber that witnesses `x` lies in the `isoClosure`.
  exact (F.mapIso i).symm ≪≫ e

/-- Helper for Lemma 8.4.3: the ambient fixed-cover descent functor restricted to the
componentwise `isoClosure` target is an equivalence. -/
lemma ambient_cover_toDescentData_isoClosure_isEquivalence
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (hlocal : ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
      (hx : ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x)),
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x)
    {U : C} (S : J.Cover U) :
    (ambient_cover_toDescentData_isoClosure
      (J := J) (p := p) (P := P) hpullback S).IsEquivalence := by
  let F := ambient_cover_toDescentData_isoClosure
    (J := J) (p := p) (P := P) hpullback S
  let Fambient := ((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f))
  have hFambient : Fambient.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p).1 inferInstance U S
  letI : Fambient.IsEquivalence := hFambient
  let e : (p.Fiber U) ≌ ((canonicalFiberPseudofunctor p).DescentData fun I : S.Arrow ↦ I.f) :=
    Fambient.asEquivalence
  let Fbase :=
    (((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙ Fambient)
  have hEss : F.EssSurj :=
    ambient_cover_toDescentData_isoClosure_essSurj
      (J := J) (p := p) (P := P) hpullback hlocal S
  letI : F.EssSurj := hEss
  have hFbaseFaithful : Fbase.Faithful := by
    letI : ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι).Faithful := by infer_instance
    letI : e.functor.Faithful := e.faithful_functor
    simpa [Fbase, Fambient] using
      (Functor.Faithful.comp
        (F := (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) (G := e.functor))
  have hFbaseFull : Fbase.Full := by
    letI : ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι).Full := by infer_instance
    letI : e.functor.Full := e.full_functor
    simpa [Fbase, Fambient] using
      (Functor.Full.comp
        (F := (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) (G := e.functor))
  letI : F.Faithful := by
    dsimp [F, ambient_cover_toDescentData_isoClosure]
    letI : Fbase.Faithful := hFbaseFaithful
    infer_instance
  letI : F.Full := by
    dsimp [F, ambient_cover_toDescentData_isoClosure]
    letI : Fbase.Full := hFbaseFull
    infer_instance
  -- The restriction functor inherits full faithfulness from the ambient equivalence, and
  -- essential surjectivity is the local object-descent lemma proved just above.
  exact
    { faithful := by infer_instance
      full := by infer_instance
      essSurj := by infer_instance }

end RestrictedFibered

end

/-! ### Lemma_8_4_3_Core (from Chap08) -/
/-- Compatibility owner for Lemma 8.4.3: the theorem shell now lives directly in
`Chap08.Lemma_8_4_3`, while this file remains as a stable reexport path for any cached imports. -/
import StacksProject_2024.Chap08.Lemma_8_4_3

/-! ### Lemma_8_4_3_Fibered (from Chap08) -/
open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (p : X ⥤ C)
variable (P : ObjectProperty X)
variable [p.IsFibered]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: once the pullback-closure hypothesis provides an ambient strongly
cartesian model over the same base arrow, a strongly cartesian morphism in the restricted
projection is already strongly cartesian in the ambient category. -/
lemma fullSubcategory_hom_isStronglyCartesian_to_ambient
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {R S : C} {a b : P.FullSubcategory} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : (P.ι ⋙ p).IsStronglyCartesian f φ] :
    p.IsStronglyCartesian f φ.hom := by
  have hφLiftRestricted : (P.ι ⋙ p).IsHomLift f φ := hφ.toIsHomLift
  have hφOwnerRestricted : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ := by
    -- Normalize the restricted base arrow to the owner map of `φ` before comparing lifts.
    letI : (P.ι ⋙ p).IsStronglyCartesian f φ := hφ
    letI : (P.ι ⋙ p).IsHomLift f φ := hφLiftRestricted
    have hφDom : (P.ι ⋙ p).obj a = R := IsHomLift.domain_eq (P.ι ⋙ p) f φ
    have hφCod : (P.ι ⋙ p).obj b = S := IsHomLift.codomain_eq (P.ι ⋙ p) f φ
    subst hφDom
    subst hφCod
    have hbase : f = (P.ι ⋙ p).map φ := IsHomLift.eq_of_isHomLift (P.ι ⋙ p) f φ
    subst hbase
    infer_instance
  obtain ⟨y, ψ, hψAmbient⟩ :=
    fullSubcategory_exists_ambient_stronglyCartesian_lift
      (p := p) (P := P) (hpullback := hpullback)
      (x := b) ((P.ι ⋙ p).map φ)
  have hψRestricted : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) ψ :=
    fullSubcategory_hom_isStronglyCartesian_of_ambient
      (p := p) (P := P) (f := (P.ι ⋙ p).map φ) (φ := ψ) (hpφ := hψAmbient)
  let e : y ≅ a :=
    Functor.IsCartesian.domainUniqueUpToIso (P.ι ⋙ p) ((P.ι ⋙ p).map φ) φ ψ
  have hcomp : e.hom ≫ φ = ψ := by
    -- The domain-uniqueness comparison isomorphism is characterized by the Cartesian
    -- factorization through `φ`.
    exact Functor.IsCartesian.fac (P.ι ⋙ p) ((P.ι ⋙ p).map φ) φ ψ
  have hφ_eq : φ = e.inv ≫ ψ := by
    -- Rewrite `φ` as the ambient pullback lift preceded by the vertical comparison isomorphism.
    calc
      φ = (𝟙 a) ≫ φ := by simp
      _ = (e.inv ≫ e.hom) ≫ φ := by rw [e.inv_hom_id]
      _ = e.inv ≫ (e.hom ≫ φ) := by simp
      _ = e.inv ≫ ψ := by rw [hcomp]
  have hφ_eq_hom : φ.hom = e.inv.hom ≫ ψ.hom := by
    exact congrArg (fun k ↦ k.hom) hφ_eq
  have heInvLiftRestricted :
      (P.ι ⋙ p).IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) e.inv := by
    exact Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift
      (P.ι ⋙ p) ((P.ι ⋙ p).map φ) φ ψ
  have heInvLiftAmbient :
      p.IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) e.inv.hom :=
    (fullSubcategory_homLift_iff_ambient (p := p) (P := P)
      (f := 𝟙 ((P.ι ⋙ p).obj a)) (φ := e.inv)).1 heInvLiftRestricted
  have hφOwnerAmbient : p.IsStronglyCartesian ((P.ι ⋙ p).map φ) φ.hom := by
    -- Compose the vertical ambient isomorphism with the chosen ambient strongly cartesian lift.
    letI : p.IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) e.inv.hom := heInvLiftAmbient
    let eAmbient : a.obj ≅ y.obj := P.ι.mapIso e.symm
    letI : p.IsHomLift (𝟙 ((P.ι ⋙ p).obj a)) eAmbient.hom := by
      simpa [eAmbient] using heInvLiftAmbient
    letI : p.IsStronglyCartesian (𝟙 ((P.ι ⋙ p).obj a)) e.inv.hom :=
      IsStronglyCartesian.of_iso (p := p) (f := 𝟙 ((P.ι ⋙ p).obj a)) eAmbient
    have hcompAmbient :
        p.IsStronglyCartesian
          ((𝟙 ((P.ι ⋙ p).obj a)) ≫ ((P.ι ⋙ p).map φ))
          (e.inv.hom ≫ ψ.hom) := by
      infer_instance
    simpa [Functor.comp_map, hφ_eq_hom] using hcompAmbient
  have hφLiftAmbient : p.IsHomLift f φ.hom :=
    (fullSubcategory_homLift_iff_ambient (p := p) (P := P) (f := f) (φ := φ)).1
      hφLiftRestricted
  -- Rebase the owner-level ambient result back to the original external arrow `f`.
  letI : p.IsStronglyCartesian ((P.ι ⋙ p).map φ) φ.hom := hφOwnerAmbient
  letI : p.IsHomLift f φ.hom := hφLiftAmbient
  have ha : p.obj a.obj = R := IsHomLift.domain_eq p f φ.hom
  have hb : p.obj b.obj = S := IsHomLift.codomain_eq p f φ.hom
  subst ha
  subst hb
  have hbase : f = p.map φ.hom := IsHomLift.eq_of_isHomLift p f φ.hom
  subst hbase
  exact hφOwnerAmbient

/-- Helper for Lemma 8.4.3: forgetting the property inside the restricted fiber lands in the
ambient fiber over the same base object. -/
theorem fullSubcategory_restrictedFiber_forget_comp_eq_const (U : C) :
    ((((fiberInclusion : (P.ι ⋙ p).Fiber U ⥤ P.FullSubcategory) ⋙ P.ι) ⋙ p)) =
      (const ((P.ι ⋙ p).Fiber U)).obj U := by
  -- Reassociate the fiber-inclusion identity for `P.ι ⋙ p` to the ambient projection `p`.
  simpa [Functor.assoc] using
    (fiberInclusion_comp_eq_const (p := P.ι ⋙ p) (S := U))

/-- Helper for Lemma 8.4.3: the forgetful functor from the restricted fiber to the ambient fiber
remembers the same underlying ambient object. -/
noncomputable def fullSubcategory_fiber_forget (U : C) :
    (P.ι ⋙ p).Fiber U ⥤ p.Fiber U :=
  inducedFunctor
    (p := p) (S := U)
    (F := ((fiberInclusion : (P.ι ⋙ p).Fiber U ⥤ P.FullSubcategory) ⋙ P.ι))
    (fullSubcategory_restrictedFiber_forget_comp_eq_const (p := p) (P := P) U)

/-- Helper for Lemma 8.4.3: every object of the restricted fiber still satisfies `P` after
forgetting to the ambient fiber. -/
theorem fullSubcategory_fiber_forget_property (U : C) (x : (P.ι ⋙ p).Fiber U) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X))
      ((fullSubcategory_fiber_forget (p := p) (P := P) U).obj x) := by
  -- The induced ambient-fiber object is definitionally the same underlying object.
  simpa [fullSubcategory_fiber_forget, ObjectProperty.inverseImage] using x.1.2

/-- Helper for Lemma 8.4.3: an object of the inverse-image full subcategory of the ambient fiber
determines an object of `P.FullSubcategory` over the same base. -/
noncomputable def inverseImage_fiber_to_fullSubcategory (U : C) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift
    (((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
      (fiberInclusion : p.Fiber U ⥤ X))
    (fun x ↦ x.2)

/-- Helper for Lemma 8.4.3: the inverse-image full subcategory over the ambient fiber projects to
the constant functor at `U` through `P.ι ⋙ p`. -/
theorem inverseImage_fiber_to_fullSubcategory_comp_eq_const (U : C) :
    ((inverseImage_fiber_to_fullSubcategory (p := p) (P := P) U) ⋙ (P.ι ⋙ p)) =
      (const ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory)).obj U := by
  -- After forgetting the `P`-proof, this is the standard fiber-inclusion identity for `p.Fiber U`.
  simpa [inverseImage_fiber_to_fullSubcategory, Functor.assoc] using
    congrArg
      (fun F ↦ ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙ F)
      (fiberInclusion_comp_eq_const (p := p) (S := U))

/-- Helper for Lemma 8.4.3: the inverse-image full subcategory of the ambient fiber maps back to
the restricted fiber over `U`. -/
noncomputable def inverseImage_fiber_to_restrictedFiber (U : C) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory ⥤ (P.ι ⋙ p).Fiber U :=
  inducedFunctor
    (p := P.ι ⋙ p) (S := U)
    (F := inverseImage_fiber_to_fullSubcategory (p := p) (P := P) U)
    (inverseImage_fiber_to_fullSubcategory_comp_eq_const (p := p) (P := P) U)

/-- Helper for Lemma 8.4.3: the restricted fiber maps to the full subcategory of the ambient
fiber cut out by `P`. -/
noncomputable def restrictedFiber_to_inverseImage_fiber (U : C) :
    (P.ι ⋙ p).Fiber U ⥤
      (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory :=
  (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).lift
    (fullSubcategory_fiber_forget (p := p) (P := P) U)
    (fullSubcategory_fiber_forget_property (p := p) (P := P) U)

/-- Helper for Lemma 8.4.3: after forgetting a transport morphism in the restricted fiber all the
way to `X`, only the ambient `eqToHom` remains. -/
lemma restricted_fiber_eqToHom_hom_eq_id (U : C)
    {x y : (P.ι ⋙ p).Fiber U} (h : x = y) :
    (((fiberInclusion : (P.ι ⋙ p).Fiber U ⥤ P.FullSubcategory) ⋙ P.ι).map (eqToHom h)) =
      eqToHom (by subst h; rfl) := by
  -- Substituting the equality removes the nested fiber and full-subcategory transport data.
  subst h
  rfl

/-- Helper for Lemma 8.4.3: after forgetting a transport morphism in the inverse-image full
subcategory all the way to `X`, only the ambient `eqToHom` remains. -/
lemma inverse_image_fullSubcategory_eqToHom_hom_eq_id (U : C)
    {x y : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory} (h : x = y) :
    ((((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
        (fiberInclusion : p.Fiber U ⥤ X)).map (eqToHom h)) =
      eqToHom (by subst h; rfl) := by
  -- The dual nested transport again contracts after substituting the object equality.
  subst h
  rfl

/-- Helper for Lemma 8.4.3: the forward bridge from the restricted fiber to the ambient inverse-
image full subcategory is strictly inverse to the ambient-to-restricted bridge on the restricted
fiber side. -/
theorem restrictedFiber_to_inverseImage_fiber_comp_eq_id (U : C) :
    restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U ⋙
        inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U =
      𝟭 ((P.ι ⋙ p).Fiber U) := by
  -- Route correction: package the roundtrip as a strict functor equality, so the later
  -- equivalence uses `eqToIso` instead of dependent `NatIso.ofComponents`.
  refine CategoryTheory.Functor.hext (h_obj := ?_) (h_map := ?_)
  · intro x
    -- On objects, both bridges return the same nested record once the fiber witness is unfolded.
    cases x
    rfl
  · intro x y φ
    -- Once the object equalities are treated heterogeneously, the map equality is definitional.
    cases x
    cases y
    rfl

/-- Helper for Lemma 8.4.3: the ambient-to-restricted bridge is strictly inverse to the forward
bridge on the inverse-image full-subcategory side. -/
theorem inverseImage_fiber_to_restrictedFiber_comp_eq_id (U : C) :
    inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U ⋙
        restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U =
      𝟭 ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) := by
  -- The dual roundtrip again becomes a strict functor equality once both bridges are explicit.
  refine CategoryTheory.Functor.hext (h_obj := ?_) (h_map := ?_)
  · intro x
    -- The object-level dual roundtrip also unfolds to the original full-subcategory record.
    cases x
    rfl
  · intro x y φ
    -- The dual heterogeneous map equality again collapses after unfolding the nested records.
    cases x
    cases y
    rfl

/-- Helper for Lemma 8.4.3: the restricted fiber is equivalent to the full subcategory of the
ambient fiber cut out by `P`. -/
noncomputable def fullSubcategory_fiber_equiv_inverseImage (U : C) :
    (P.ι ⋙ p).Fiber U ≌
      (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory :=
  CategoryTheory.Equivalence.mk
    (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U)
    (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U)
    (eqToIso (restrictedFiber_to_inverseImage_fiber_comp_eq_id (p := p) (P := P) U).symm)
    (eqToIso (inverseImage_fiber_to_restrictedFiber_comp_eq_id (p := p) (P := P) U))

/-- Helper for Lemma 8.4.3: applying the fiber equivalence and then its inverse returns the
original restricted-fiber object. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_inverse_functor_obj
    (U : C) (x : (P.ι ⋙ p).Fiber U) :
    (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).obj
      ((fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.obj x) = x := by
  -- The object-level roundtrip is exactly the component of the strict composite equality.
  simpa [fullSubcategory_fiber_equiv_inverseImage] using
    Functor.congr_obj
      (restrictedFiber_to_inverseImage_fiber_comp_eq_id (p := p) (P := P) U) x

/-- Helper for Lemma 8.4.3: applying the inverse of the fiber equivalence and then the forward
functor returns the original inverse-image fiber object. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_functor_inverse_obj
    (U : C)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.obj
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).obj x) = x := by
  -- The dual object-level roundtrip is the component of the other strict composite equality.
  simpa [fullSubcategory_fiber_equiv_inverseImage] using
    Functor.congr_obj
      (inverseImage_fiber_to_restrictedFiber_comp_eq_id (p := p) (P := P) U) x

/-- Helper for Lemma 8.4.3: the restricted-to-inverse-image bridge cancels the inverse bridge on
morphisms exactly, not only on objects. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_inverse_functor_map
    (U : C)
    {x y : (P.ι ⋙ p).Fiber U} (φ : x ⟶ y) :
    (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map
        ((fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.map φ) =
      φ := by
  -- Forget to `X`, where the roundtrip functor equality produces only `eqToHom` transports, and
  -- the dedicated transport lemma collapses them to identities.
  change (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ) = φ
  apply Functor.Fiber.hom_ext
  apply ObjectProperty.hom_ext
  cases x
  cases y
  rfl

/-- Helper for Lemma 8.4.3: the inverse-image-to-restricted bridge cancels the forward bridge on
morphisms exactly, mirroring the object-level roundtrip lemma above. -/
@[simp] theorem fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
    (U : C)
    {x y : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory} (φ : x ⟶ y) :
    (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor.map
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map φ) =
      φ := by
  -- Forget to the ambient fiber and then to `X`, so the strict composite equality reduces to the
  -- corresponding ambient `eqToHom` transports.
  change (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map φ) = φ
  apply ObjectProperty.hom_ext
  apply Functor.Fiber.hom_ext
  cases x
  cases y
  rfl

end RestrictedFibered


end

/-! ### Lemma_8_4_3_FiberedBase (from Chap08) -/
open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (p : X ⥤ C)
variable (P : ObjectProperty X)

/- Domain-style sampling:
- primary domain: stacks over a site, fibred categories, and full subcategories cut out by an
  object property.
- inspected owner-level declarations:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.isoClosure`,
  `Functor.Fiber.fiberInclusion`,
  `canonicalPullbackChoice`,
  `IsStackOnSite`.
- best owner abstraction: the restricted projection `P.ι ⋙ p : P.FullSubcategory ⥤ C`.
- primitive data: the object property `P` together with closure of canonical pullback objects up to
  fiberwise isomorphism and a descent-locality hypothesis stated in each fiber.
- derived API: the induced stack structure on the restricted projection.
- layer triage:
  `source-facing`: Lemma 8.4.3, a criterion for the full subcategory to remain a stack;
  `core/canonical`: `p.IsFibered` and the inclusion `P.ι`;
  `bridge/view`: the canonical fiberwise property
  `(P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure` on `p.Fiber U`, together with
  the chosen pullback owner `canonicalPullbackChoice p`.
-/

variable [p.IsFibered]

/-- Helper for Lemma 8.4.3: composing in `C` and then passing to the locally discrete opposite is
the same as composing the corresponding `toLoc` arrows in the owner order used by pullback
transport. -/
theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Cᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.4.3: a morphism in the full subcategory lifts a base arrow for the
restricted projection exactly when its underlying ambient morphism lifts the same arrow. -/
lemma fullSubcategory_homLift_iff_ambient
    {R S : C} {a b : P.FullSubcategory} (f : R ⟶ S) (φ : a ⟶ b) :
    (P.ι ⋙ p).IsHomLift f φ ↔ p.IsHomLift f φ.hom := by
  constructor
  · intro hφ
    -- Forgetting the full-subcategory structure preserves the same base factorization.
    letI : (P.ι ⋙ p).IsHomLift f φ := hφ
    exact
      IsHomLift.of_fac' p f φ.hom
        (IsHomLift.domain_eq (P.ι ⋙ p) f φ)
        (IsHomLift.codomain_eq (P.ι ⋙ p) f φ) <| by
          simpa using (IsHomLift.fac' (P.ι ⋙ p) f φ)
  · intro hφ
    -- The restricted projection has the same object map and morphism map as the ambient one.
    have hφDom : p.obj a.obj = R := by
      letI : p.IsHomLift f φ.hom := hφ
      exact IsHomLift.domain_eq p f φ.hom
    have hφCod : p.obj b.obj = S := by
      letI : p.IsHomLift f φ.hom := hφ
      exact IsHomLift.codomain_eq p f φ.hom
    exact
      IsHomLift.of_fac' (P.ι ⋙ p) f φ hφDom hφCod <| by
        letI : p.IsHomLift f φ.hom := hφ
        simpa using (IsHomLift.fac' p f φ.hom)

/-- Helper for Lemma 8.4.3: a strongly cartesian morphism in the ambient category between objects
of the full subcategory remains strongly cartesian for the restricted projection. -/
lemma fullSubcategory_hom_isStronglyCartesian_of_ambient
    {R S : C} {a b : P.FullSubcategory} (f : R ⟶ S) (φ : a ⟶ b)
    [hpφ : p.IsStronglyCartesian f φ.hom] :
    (P.ι ⋙ p).IsStronglyCartesian f φ := by
  have hφLift : p.IsHomLift f φ.hom := hpφ.toIsHomLift
  have hφDom : p.obj a.obj = R := IsHomLift.domain_eq p f φ.hom
  have hφCod : p.obj b.obj = S := IsHomLift.codomain_eq p f φ.hom
  have hφOwnerAmbient : p.IsStronglyCartesian (p.map φ.hom) φ.hom := by
    -- The lift witness identifies the external base arrow with the owner map `p.map φ.hom`.
    letI : p.IsStronglyCartesian f φ.hom := hpφ
    subst hφDom
    subst hφCod
    have hbase : f = p.map φ.hom := IsHomLift.eq_of_isHomLift p f φ.hom
    subst hbase
    infer_instance
  have hφOwnerRestricted : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ := by
    -- The restricted universal property is the ambient one, transported across the inclusion
    -- bridge for hom lifts.
    letI : p.IsStronglyCartesian (p.map φ.hom) φ.hom := hφOwnerAmbient
    refine
      { toIsHomLift := by infer_instance
        universal_property' := ?_ }
    intro a' g φ' hφ'
    have hφ'Ambient :
        p.IsHomLift (g ≫ p.map φ.hom) φ'.hom := by
      simpa [Functor.comp_map] using
        (fullSubcategory_homLift_iff_ambient (p := p) (P := P)
          (f := g ≫ (P.ι ⋙ p).map φ) (φ := φ')).1 hφ'
    letI : p.IsHomLift (g ≫ p.map φ.hom) φ'.hom := hφ'Ambient
    obtain ⟨χ, hχ, hχuniq⟩ :=
      IsStronglyCartesian.universal_property p (p.map φ.hom) φ.hom g
        (g ≫ p.map φ.hom) rfl φ'.hom
    refine ⟨ObjectProperty.homMk χ, ?_, ?_⟩
    · refine ⟨(fullSubcategory_homLift_iff_ambient (p := p) (P := P)
        (f := g) (φ := ObjectProperty.homMk χ)).2 hχ.1, ?_⟩
      -- The factorization equality is the same after packaging `χ` back into the full
      -- subcategory.
      apply ObjectProperty.hom_ext
      simpa using hχ.2
    · intro ψ hψ
      -- Uniqueness is checked after forgetting to the ambient category.
      apply ObjectProperty.hom_ext
      exact hχuniq ψ.hom ⟨
        (fullSubcategory_homLift_iff_ambient (p := p) (P := P) (f := g) (φ := ψ)).1 hψ.1,
        by simpa using congrArg (fun k ↦ k.hom) hψ.2⟩
  have hφLiftRestricted : (P.ι ⋙ p).IsHomLift f φ :=
    (fullSubcategory_homLift_iff_ambient (p := p) (P := P) (f := f) (φ := φ)).2 hφLift
  -- Finally rebase the restricted owner-map strong-cartesian structure to the external base map
  -- `f`.
  letI : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ := hφOwnerRestricted
  letI : (P.ι ⋙ p).IsHomLift f φ := hφLiftRestricted
  have hφDomRestricted : (P.ι ⋙ p).obj a = R := IsHomLift.domain_eq (P.ι ⋙ p) f φ
  have hφCodRestricted : (P.ι ⋙ p).obj b = S := IsHomLift.codomain_eq (P.ι ⋙ p) f φ
  subst hφDomRestricted
  subst hφCodRestricted
  have hbase : f = (P.ι ⋙ p).map φ := IsHomLift.eq_of_isHomLift (P.ι ⋙ p) f φ
  subst hbase
  infer_instance

/-- Helper for Lemma 8.4.3: the pullback-closure hypothesis produces strongly cartesian pullbacks
inside the full subcategory, before forgetting back to the ambient category. -/
lemma fullSubcategory_exists_ambient_stronglyCartesian_lift
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {V : C} (x : P.FullSubcategory) (f : V ⟶ (P.ι ⋙ p).obj x) :
    ∃ y : P.FullSubcategory, ∃ φ : y ⟶ x, p.IsStronglyCartesian f φ.hom := by
  let xFiber : p.Fiber ((P.ι ⋙ p).obj x) := Functor.Fiber.mk rfl
  have hpb := hpullback f xFiber x.property
  rw [ObjectProperty.prop_isoClosure_iff] at hpb
  rcases hpb with ⟨y, hy, ⟨e⟩⟩
  let y' : P.FullSubcategory := ⟨y.1, hy⟩
  let eX : (f ^*[canonicalPullbackChoice p] xFiber).1 ≅ y.1 :=
    (fiberInclusion : p.Fiber V ⥤ X).mapIso e
  let eX' : y.1 ≅ (f ^*[canonicalPullbackChoice p] xFiber).1 := eX.symm
  let pbMap : y'.obj ⟶ x.obj :=
    eX'.hom ≫ (canonicalPullbackChoice p).map f xFiber
  have hpbStronglyCartesian :
      p.IsStronglyCartesian f pbMap := by
    -- First move from `y` back to the canonical pullback, then use the chosen pullback arrow.
    letI : p.IsHomLift (𝟙 V) eX'.hom := by
      change p.IsHomLift (𝟙 V) ((fiberInclusion : p.Fiber V ⥤ X).map e.inv)
      infer_instance
    letI : p.IsStronglyCartesian (𝟙 V) eX'.hom :=
      IsStronglyCartesian.of_iso (p := p) (f := 𝟙 V) eX'
    letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f xFiber) :=
      (canonicalPullbackChoice p).isStronglyCartesian f xFiber
    simpa [pbMap] using
      (inferInstance : p.IsStronglyCartesian f
        (eX'.hom ≫ (canonicalPullbackChoice p).map f xFiber))
  exact ⟨y', ObjectProperty.homMk pbMap, hpbStronglyCartesian⟩

/-- Helper for Lemma 8.4.3: the pullback-closure hypothesis produces strongly cartesian pullbacks
inside the restricted projection, so the restricted projection is fibered. -/
lemma fullSubcategory_projection_isFibered
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x)) :
    (P.ι ⋙ p).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro x V f
  rcases
      fullSubcategory_exists_ambient_stronglyCartesian_lift
        (p := p) (P := P) (hpullback := hpullback) x f with
    ⟨y, φ, hφ⟩
  -- The restricted strong-cartesian lift is obtained by reusing the ambient one inside the full
  -- subcategory.
  exact
    ⟨y, φ,
      fullSubcategory_hom_isStronglyCartesian_of_ambient
        (p := p) (P := P) (f := f) (φ := φ) (hpφ := hφ)⟩

end

/-! ### Lemma_8_4_3_RestrictedDescent (from Chap08) -/
open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)

variable [IsStackOnSite J p]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: a restricted descent datum over the cover `S` determines an ambient
descent datum whose components land in the corresponding fiberwise `isoClosure` of `P`. -/
noncomputable def restricted_cover_descent_isoClosure_obj
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f))) :
    (cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S).FullSubcategory := by
  refine ⟨?_, ?_⟩
  · refine
      { obj := fun I ↦
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj (D.obj I)).obj
        hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
          restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂
        pullHom_hom := fun Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦ by
          -- The overlap map is already packaged as the comparison-conjugated shell in the forward
          -- helper file, so its pullback law is delegated there unchanged.
          simpa using
            restricted_cover_descent_isoClosure_obj_hom_pullHom_hom
              (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
              (Y' := Y') (Y := Y) (I₁ := I₁) (I₂ := I₂)
              (g := g) (q := q) (q' := q') (hq := hq) (f₁ := f₁) (f₂ := f₂)
              (hf₁ := hf₁) (hf₂ := hf₂) (gf₁ := gf₁) (gf₂ := gf₂)
              (hgf₁ := hgf₁) (hgf₂ := hgf₂)
        hom_self := fun Y q I g hg ↦ by
          -- On equal legs, the comparison shell cancels to the identity in the helper file.
          simpa using
            restricted_cover_descent_isoClosure_obj_hom_self
              (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
              (Y := Y) (I := I) (q := q) (g := g) (hg := hg)
        hom_comp := fun Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦ by
          -- The cocycle law for the comparison-conjugated overlap maps is likewise already
          -- proved in the forward helper file.
          simpa using
            restricted_cover_descent_isoClosure_obj_hom_comp
              (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
              (Y := Y) (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
              (q := q) (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
              (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃) }
  · intro I
    -- Each component is already strict in the inverse-image full subcategory, hence belongs to
    -- the ambient `isoClosure` target via the tautological identity isomorphism.
    exact
      ObjectProperty.le_isoClosure
        (P := P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X))
        (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
          (D.obj I)).obj)
        (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
          (D.obj I)).property)

/-- Helper for Lemma 8.4.3: the source-faithful forward bridge sends restricted fixed-cover
descent data to the ambient componentwise-`isoClosure` target objectwise. -/
noncomputable def restricted_cover_descent_to_isoClosure
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
      (cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S).FullSubcategory where
  obj D :=
    restricted_cover_descent_isoClosure_obj (J := J) (p := p) (P := P) hpullback S D
  map {D₁ D₂} φ :=
    ObjectProperty.homMk
      { hom := fun I ↦
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
            (φ.hom I)).hom
        comm := by
          intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
          -- The morphism compatibility is the corresponding shell naturality from the forward
          -- helper file.
          simpa using
            restricted_cover_descent_to_isoClosure_map_comm_via_pullbackComparison
              (J := J) (p := p) (P := P) hpullback S φ q f₁ f₂ hf₁ hf₂ }
  map_id D := by
    -- The forward bridge functor acts componentwise, so identities are preserved strictly.
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    rfl
  map_comp φ ψ := by
    -- Composition is computed componentwise in each overlap fiber.
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    rfl


-- Route correction: `PullbackComparison.lean` is the canonical owner of the inclusion/pullback
-- comparison API. This file now reuses those declarations instead of rebuilding them in a
-- second elaboration context before the restricted descent-equivalence construction.

/-- Helper for Lemma 8.4.3: the reverse overlap morphism is first defined in the inverse-image
full subcategory, where the chosen component isomorphisms and the pullback-comparison maps live
without extra coercions. -/
noncomputable def restricted_cover_overlap_hom_in_inverseImage_fiber
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.obj
          ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
            (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))) ⟶
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.obj
          ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
            (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))) :=
  ObjectProperty.homMk <|
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₁
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))).hom ≫
      (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_cover_component_total_iso
          (J := J) (p := p) (P := P) S D I₁).hom) ≫
      D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_cover_component_total_iso
          (J := J) (p := p) (P := P) S D I₂).inv) ≫
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₂
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))).inv

/-- Helper for Lemma 8.4.3: the restricted overlap morphism is the image of the inverse-image
overlap morphism under the ambient-to-restricted fiber bridge. -/
noncomputable def restricted_cover_isoClosure_to_descent_obj_hom
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.obj
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))) ⟶
      (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.obj
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))) :=
  (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) Y).map
    (restricted_cover_overlap_hom_in_inverseImage_fiber
      (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)

/-- Helper for Lemma 8.4.3: the reverse overlap morphisms still need the single vertical
pullback-compatibility calculation from the source proof, now isolated in the inverse-image
category. -/
theorem restricted_cover_isoClosure_to_descent_obj_pullHom_hom
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (restricted_cover_isoClosure_to_descent_obj_hom
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  sorry

/-- Helper for Lemma 8.4.3: the reverse overlap map is the identity on equal legs once the
component conjugations are normalized. -/
theorem restricted_cover_isoClosure_to_descent_obj_hom_self
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q g g hg hg =
      𝟙 _ := by
  let E := fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) Y
  let FY := E.functor
  letI : FY.Faithful := E.faithful_functor
  apply FY.map_injective
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q g g hg hg) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q g g hg hg by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q g g hg hg)]
  change restricted_cover_overlap_hom_in_inverseImage_fiber
      (J := J) (p := p) (P := P) hpullback S D q g g hg hg = 𝟙 _
  apply ObjectProperty.hom_ext
  let Fg := ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor
  let c :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback g
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I))
  let t := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  rw [D.obj.hom_self q g hg]
  have ht : Fg.map t.hom ≫ Fg.map t.inv = 𝟙 _ := by
    simpa using (Fg.mapIso t).hom_inv_id
  have hself :
      c.hom ≫ Fg.map t.hom ≫ 𝟙 _ ≫ Fg.map t.inv ≫ c.inv = 𝟙 _ := by
    calc
      c.hom ≫ Fg.map t.hom ≫ 𝟙 _ ≫ Fg.map t.inv ≫ c.inv =
          c.hom ≫ Fg.map t.hom ≫ Fg.map t.inv ≫ c.inv := by
            simp [Category.assoc]
      _ = c.hom ≫ (Fg.map t.hom ≫ Fg.map t.inv) ≫ c.inv := by
            simp [Category.assoc]
      _ = c.hom ≫ 𝟙 _ ≫ c.inv := by
            exact congrArg (fun k ↦ c.hom ≫ k ≫ c.inv) ht
      _ = 𝟙 _ := by
            simp
  simpa only [ObjectProperty.homMk, Fg, c, t, restricted_cover_component_total_iso_hom,
    restricted_cover_component_total_iso_inv, Functor.map_comp] using hself

/-- Helper for Lemma 8.4.3: the reverse overlap maps satisfy the cocycle relation after the same
conjugation normal-form reduction. -/
theorem restricted_cover_isoClosure_to_descent_obj_hom_comp
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
      restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
    restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ := by
  let E := fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) Y
  let FY := E.functor
  letI : FY.Faithful := E.faithful_functor
  apply FY.map_injective
  change
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂) ≫
        FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃) =
      FY.map
        (restricted_cover_isoClosure_to_descent_obj_hom
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃)
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)]
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃)]
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃)]
  change
      restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
      restricted_cover_overlap_hom_in_inverseImage_fiber
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom]
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  let F₁ := ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor
  let F₂ := ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor
  let F₃ := ((canonicalFiberPseudofunctor p).map f₃.op.toLoc).toFunctor
  let c₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))
  let c₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))
  let c₃ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₃
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₃.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₃))
  let t₁ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₁
  let t₂ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₂
  let t₃ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₃
  have ht₂ : F₂.map t₂.inv ≫ F₂.map t₂.hom = 𝟙 _ := by
    simpa using (F₂.mapIso t₂).inv_hom_id
  simpa [ObjectProperty.homMk, F₁, F₂, F₃, c₁, c₂, c₃, t₁, t₂, t₃,
    restricted_cover_component_total_iso_hom, restricted_cover_component_total_iso_inv,
    Functor.map_comp, Category.assoc] using
    calc
      (c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫ F₂.map t₂.inv ≫ c₂.inv) ≫
          (c₂.hom ≫ F₂.map t₂.hom ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv) =
        c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
          (F₂.map t₂.inv ≫ F₂.map t₂.hom) ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫
          F₃.map t₃.inv ≫ c₃.inv := by
            simp [Category.assoc]
      _ =
        c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
          𝟙 _ ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv := by
            exact
              congrArg
                (fun k ↦
                  c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
                    k ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv)
                ht₂
      _ =
        c₁.hom ≫ F₁.map t₁.hom ≫
          (D.obj.hom q f₁ f₂ hf₁ hf₂ ≫ D.obj.hom q f₂ f₃ hf₂ hf₃) ≫
          F₃.map t₃.inv ≫ c₃.inv := by
            simp [Category.assoc]
      _ =
        c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₃ hf₁ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv := by
            exact
              congrArg
                (fun k ↦ c₁.hom ≫ F₁.map t₁.hom ≫ k ≫ F₃.map t₃.inv ≫ c₃.inv)
                (D.obj.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Helper for Lemma 8.4.3: strictify an ambient fixed-cover object in the componentwise
`isoClosure` target to a restricted descent datum by choosing strict representatives of its cover
components. -/
noncomputable def restricted_cover_isoClosure_to_descent_obj
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)) :=
  { obj := fun I ↦
      (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I)
    hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
      restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂
    pullHom_hom := fun Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
      restricted_cover_isoClosure_to_descent_obj_pullHom_hom
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
        (Y' := Y') (Y := Y) (g := g) (q := q) (q' := q') (hq := hq)
        (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
        (hf₁ := hf₁) (hf₂ := hf₂) (gf₁ := gf₁) (gf₂ := gf₂)
        (hgf₁ := hgf₁) (hgf₂ := hgf₂)
    hom_self := fun Y q I g hg ↦
      restricted_cover_isoClosure_to_descent_obj_hom_self
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
        (Y := Y) (q := q) (I := I) (g := g) (hg := hg)
    hom_comp := fun Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
      restricted_cover_isoClosure_to_descent_obj_hom_comp
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
        (Y := Y) (q := q) (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
        (f₁ := f₁) (f₂ := f₂) (f₃ := f₃) (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃) }

end RestrictedFibered

end

/-! ### Lemma_8_4_3_Transport (from Chap08) -/
open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)

variable [IsStackOnSite J p]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: for a fixed source object in the restricted fiber, the componentwise
pullback-comparison isomorphisms satisfy the descent square relating the restricted and ambient
canonical fixed-cover descent data. -/
private theorem restricted_cover_toDescentData_transport_iso_app_comm
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₁.f x).hom) ≫
      (((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)).obj).hom q f₁ f₂ hf₁ hf₂ =
    (((restricted_cover_descent_to_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
              (fun I : S.Arrow ↦ I.f)).obj x)).obj).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₂.f x).hom) := by
  -- TODO: normalize the ambient canonical descent overlap to the comparison-conjugated shell
  -- `restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison`, then finish by the
  -- same fixed-cover transport identity used in the target file.
  sorry

/-- Helper for Lemma 8.4.3: for a fixed source object in the restricted fiber, the legwise
pullback-comparison isomorphisms package to an isomorphism between the restricted and ambient
fixed-cover descent data. -/
private noncomputable def restricted_cover_toDescentData_transport_component_iso
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) :
    ((restricted_cover_descent_to_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)) ≅
      ((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)) := by
  -- Package the legwise pullback-comparison maps into an isomorphism of the two fixed-cover
  -- descent data attached to `x`.
  refine ObjectProperty.isoMk (P := cover_componentwise_isoClosure_property
    (J := J) (p := p) (P := P) S) <|
    Pseudofunctor.DescentData.isoMk
      (fun I ↦ restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback I.f x) ?_
  intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
  -- The componentwise commutativity is exactly the unfolded transport square proved above.
  exact
    restricted_cover_toDescentData_transport_iso_app_comm
      (J := J) (p := p) (P := P) (hpullback := hpullback) S x q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.3: compare the restricted canonical descent functor composed with the
forward bridge to the ambient canonical descent functor on the inverse-image full subcategory. -/
noncomputable def restricted_cover_toDescentData_transport_iso
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙
        restricted_cover_descent_to_isoClosure (J := J) (p := p) (P := P) hpullback S ≅
      (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor ⋙
        ambient_cover_toDescentData_isoClosure (J := J) (p := p) (P := P) hpullback S := by
  let η :
      (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor ⋙
          ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S ≅
        ((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙
          restricted_cover_descent_to_isoClosure
            (J := J) (p := p) (P := P) hpullback S :=
    NatIso.ofComponents
      (fun x ↦
        (restricted_cover_toDescentData_transport_component_iso
          (J := J) (p := p) (P := P) hpullback S x).symm)
      (fun φ ↦ by
        -- TODO: rewrite the objectwise components of the owner comparison to the actual legwise
        -- pullback-comparison maps and close naturality by the specialized inverse-side
        -- pullback-comparison square.
        sorry)
  -- The previous comparison is oriented ambient-to-restricted; invert it to match the theorem.
  exact η.symm

end RestrictedFibered

end
