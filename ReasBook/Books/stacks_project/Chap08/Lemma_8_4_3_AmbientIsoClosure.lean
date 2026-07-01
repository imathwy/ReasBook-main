import stacks_project.Chap08.Lemma_8_4_2
import stacks_project.Chap08.Lemma_8_4_3_Fibered

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
