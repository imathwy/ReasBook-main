import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3

open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

variable (A : FilteredObject C)

-- Internal bridge: transport a filtered object structure across an isomorphism of underlying
-- objects so the public `image` owner can reuse `subobjectFilteredObject` rather than rebuilding
-- its filtration entrywise.
private abbrev ofIso {X : C} (e : A.obj ≅ X) : FilteredObject C where
  obj := X
  filtration := ((Subobject.mapIsoToOrderIso e : Subobject A.obj →o Subobject X)).comp A.filtration

section Pullbacks

variable [HasPullbacks C]
variable (X : Subobject A.obj)

/-- The induced filtered object on a subobject `X ⊆ A`. -/
def subobjectFilteredObject : FilteredObject C where
  obj := X
  filtration := A.filtration.induced X

/-- Helper for Lemma 12.19.4: the induced filtration on a subobject is preserved by the ambient
inclusion. -/
private theorem subobjectInclusion_preserves (i : ℤ) :
    (A.filtration i).Factors
      (((A.subobjectFilteredObject X).filtration i).arrow ≫ X.arrow) := by
  -- Reinterpret the induced stage as a pullback stage of `A.filtration i` along `X.arrow`.
  rw [show (A.subobjectFilteredObject X).filtration i =
      (Subobject.pullback X.arrow).obj (A.filtration i) by
    rfl]
  -- The pullback stage maps into the ambient filtration stage by definition.
  exact (pullback_factors_iff X.arrow (A.filtration i)
      (((A.subobjectFilteredObject X).filtration i).arrow)).1
    (Subobject.factors_self ((A.subobjectFilteredObject X).filtration i))

/-- The inclusion of a filtered subobject into the ambient filtered object. -/
def subobjectInclusion : A.subobjectFilteredObject X ⟶ A where
  hom := X.arrow
  preserves := subobjectInclusion_preserves A X

end Pullbacks

section Quotients

variable [HasPullbacks C] [HasZeroMorphisms C] [HasImages C] [HasCokernels C]
variable (X : Subobject A.obj)

/-- The quotient filtered object `A / X`. -/
def quotientFilteredObject : FilteredObject C where
  obj := cokernel X.arrow
  filtration := A.filtration.quotient (cokernel.π X.arrow)

/-- Helper for Lemma 12.19.4: the quotient filtration is preserved by the canonical quotient map.
-/
private theorem toQuotient_preserves (i : ℤ) :
    ((A.quotientFilteredObject X).filtration i).Factors
      ((A.filtration i).arrow ≫ cokernel.π X.arrow) := by
  let k : (A.filtration i : C) ⟶ cokernel X.arrow :=
    (A.filtration.obj i).arrow ≫ cokernel.π X.arrow
  -- Rewrite the quotient stage as the image of the stage composite into the quotient object.
  rw [show (A.quotientFilteredObject X).filtration i = imageSubobject k by
    simpa [quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (cokernel.π X.arrow) i)]
  -- The image stage contains the defining composite by its universal factorization.
  simpa [k, imageSubobject_arrow_comp] using
    (Subobject.factors_comp_arrow (factorThruImageSubobject k))

/-- The quotient map from a filtered object to the quotient by a subobject. -/
def toQuotient : A ⟶ A.quotientFilteredObject X where
  hom := cokernel.π X.arrow
  preserves := toQuotient_preserves A X

end Quotients

section PullbacksQuotients

variable [HasPullbacks C] [HasZeroMorphisms C] [HasImages C] [HasCokernels C]
variable (X : Subobject A.obj)

/-- The inclusion of a filtered subobject followed by the quotient map is zero. -/
theorem subobjectInclusion_comp_toQuotient :
    A.subobjectInclusion X ≫ A.toQuotient X = 0 := by
  -- This is the ambient cokernel relation for the quotient by `X`.
  apply FilteredObject.forget.map_injective
  change X.arrow ≫ cokernel.π X.arrow = 0
  simpa using cokernel.condition X.arrow

end PullbacksQuotients

section Abelian

variable [Abelian C]

namespace Hom

variable {A B : FilteredObject C}

open FilteredObject

/-
Source/core/bridge triage for Lemma 12.19.4:
- source-facing: strictness of a filtered morphism
- core/canonical owners: `FilteredObject.subobjectFilteredObject`,
  `FilteredObject.quotientFilteredObject`, and `Abelian.coimageImageComparison f.hom`
- bridge/view: the filtered `coimage`, filtered `image`, and their lifted comparison morphism
- primitive data: filtration-preserving morphisms are built from stagewise factorization data
- derived API: the filtered comparison morphism and the strictness/isomorphism criterion
-/

/-- The filtered coimage of a morphism, equipped with the quotient filtration coming from the
source via the canonical projection `Abelian.coimage.π`. -/
abbrev coimage (f : A ⟶ B) : FilteredObject C :=
  { obj := Abelian.coimage f.hom
    filtration := A.filtration.quotient (Abelian.coimage.π f.hom) }

/-- The filtered image of a morphism, equipped with the induced filtration coming from the target.
-/
abbrev image (f : A ⟶ B) : FilteredObject C :=
  (B.subobjectFilteredObject (imageSubobject f.hom)).ofIso
    (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm)

/-- Helper for Lemma 12.19.4: the ambient comparison `coim(f) ⟶ im(f)` viewed with codomain the
literal image subobject of `f.hom`. -/
private abbrev coimageToImageSubobjectHom (f : A ⟶ B) :
    Abelian.coimage f.hom ⟶ imageSubobject f.hom :=
  Abelian.coimageImageComparison f.hom ≫
    (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).inv

/-- Helper for Lemma 12.19.4: the literal image-subobject comparison followed by the inclusion
into `B` is the standard coimage-image factorization. -/
private theorem coimageToImageSubobjectHom_comp_arrow (f : A ⟶ B) :
    coimageToImageSubobjectHom f ≫ (imageSubobject f.hom).arrow =
      Abelian.coimageImageComparison f.hom ≫ Abelian.image.ι f.hom := by
  let e : (imageSubobject f.hom : C) ≅ Abelian.image f.hom :=
    imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
  have he : e.hom ≫ Abelian.image.ι f.hom = (imageSubobject f.hom).arrow := by
    -- The chosen transport identifies the literal image mono with `Abelian.image.ι`.
    have himage :
        (Abelian.imageIsoImage f.hom).inv ≫ Abelian.image.ι f.hom = Limits.image.ι f.hom := by
      -- Rewrite the inverse comparison by the explicit kernel lift formula and simplify.
      rw [Abelian.imageIsoImage_inv]
      simp
    calc
      e.hom ≫ Abelian.image.ι f.hom
          = (imageSubobjectIso f.hom).hom ≫
              ((Abelian.imageIsoImage f.hom).inv ≫ Abelian.image.ι f.hom) := by
                simp [e, Category.assoc]
      _ = (imageSubobjectIso f.hom).hom ≫ Limits.image.ι f.hom := by
            rw [himage]
      _ = (imageSubobject f.hom).arrow := by
            simpa using (Limits.imageSubobject_arrow (f := f.hom))
  have he' : e.inv ≫ (imageSubobject f.hom).arrow = Abelian.image.ι f.hom := by
    -- Compose the forward identification with the inverse transport.
    calc
      e.inv ≫ (imageSubobject f.hom).arrow
          = (Abelian.imageIsoImage f.hom).hom ≫
              ((imageSubobjectIso f.hom).inv ≫ (imageSubobject f.hom).arrow) := by
                simp [e, Category.assoc]
      _ = (Abelian.imageIsoImage f.hom).hom ≫ Limits.image.ι f.hom := by
            rw [Limits.imageSubobject_arrow']
      _ = Abelian.image.ι f.hom := by
            simpa using (Abelian.imageIsoImage_hom_comp_image_ι (f := f.hom))
  -- Precompose that identification with `e.inv` to rewrite the codomain of the comparison.
  calc
    coimageToImageSubobjectHom f ≫ (imageSubobject f.hom).arrow
        = Abelian.coimageImageComparison f.hom ≫ (e.inv ≫ (imageSubobject f.hom).arrow) := by
            simp [coimageToImageSubobjectHom, e, Category.assoc]
    _ = Abelian.coimageImageComparison f.hom ≫ Abelian.image.ι f.hom := by
          simp [he']

/-- Helper for Lemma 12.19.4: the comparison to the literal image subobject composes with the
coimage projection to recover the original map `f.hom`. -/
private theorem coimage_π_comp_coimageToImageSubobjectHom_comp_arrow (f : A ⟶ B) :
    Abelian.coimage.π f.hom ≫ coimageToImageSubobjectHom f ≫ (imageSubobject f.hom).arrow =
      f.hom := by
  -- This is the standard abelian coimage-image factorization, expressed through the chosen image
  -- subobject model.
  rw [coimageToImageSubobjectHom_comp_arrow]
  simpa [Category.assoc] using Abelian.coimage_image_factorisation f.hom

/-- Helper for Lemma 12.19.4: postcomposing an epimorphism does not change the image subobject.
-/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : C} (g : X ⟶ Y) [Epi g] (h : Y ⟶ Z) :
    imageSubobject (g ≫ h) = imageSubobject h := by
  -- Rewrite the composite image through the restriction to `im(g)`, then identify `im(g)` with
  -- the top subobject because `g` is epi.
  calc
    imageSubobject (g ≫ h) = imageSubobject ((imageSubobject g).arrow ≫ h) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction g h]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ h) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ h))
        (Limits.imageSubobject_eq_top_of_epi g)
    _ = imageSubobject h := by
      simpa using Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) h

/-- Helper for Lemma 12.19.4: after mapping the `i`-th coimage stage into `B`, its image is the
strictness subobject `A.filtration.quotient f.hom i`. -/
private theorem coimage_stage_maps_to_strict_subobject (f : A ⟶ B) (i : ℤ) :
    imageSubobject
      ((((coimage f).filtration i).arrow ≫ coimageToImageSubobjectHom f) ≫
        (imageSubobject f.hom).arrow) =
      A.filtration.quotient f.hom i := by
  let k : (A.filtration i : C) ⟶ Abelian.coimage f.hom :=
    (A.filtration i).arrow ≫ Abelian.coimage.π f.hom
  let h : Abelian.coimage f.hom ⟶ B.obj :=
    coimageToImageSubobjectHom f ≫ (imageSubobject f.hom).arrow
  have hstage : (coimage f).filtration i = imageSubobject k := by
    -- Rewrite the coimage filtration stage as the stagewise image of the quotient map.
    simpa [coimage, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (Abelian.coimage.π f.hom) i)
  have hcomp : k ≫ h = (A.filtration i).arrow ≫ f.hom := by
    -- The ambient composite through `coim(f) → im(f) ↪ B` is just `f`.
    calc
      k ≫ h
          = (A.filtration i).arrow ≫
              (Abelian.coimage.π f.hom ≫
                coimageToImageSubobjectHom f ≫ (imageSubobject f.hom).arrow) := by
              simp [k, h, Category.assoc]
      _ = (A.filtration i).arrow ≫ f.hom := by
            rw [coimage_π_comp_coimageToImageSubobjectHom_comp_arrow]
  rw [hstage]
  -- Remove the epimorphic image factor of `k`, then identify the resulting image in `B`.
  calc
    imageSubobject (((imageSubobject k).arrow ≫ coimageToImageSubobjectHom f) ≫
        (imageSubobject f.hom).arrow)
        = imageSubobject ((imageSubobject k).arrow ≫ h) := by
            simp [h, Category.assoc]
    _ = imageSubobject (factorThruImageSubobject k ≫ (imageSubobject k).arrow ≫ h) := by
          symm
          simpa [Category.assoc] using
            (imageSubobject_comp_eq_of_epi (factorThruImageSubobject k)
              ((imageSubobject k).arrow ≫ h))
    _ = imageSubobject ((factorThruImageSubobject k ≫ (imageSubobject k).arrow) ≫ h) := by
          simp
    _ = imageSubobject (k ≫ h) := by
          rw [imageSubobject_arrow_comp]
    _ = imageSubobject ((A.filtration i).arrow ≫ f.hom) := by
          rw [hcomp]
    _ = A.filtration.quotient f.hom i := by
          symm
          simpa using
            (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration f.hom i)

/-- Helper for Lemma 12.19.4: the canonical map from the filtered coimage lands in the induced
filtration on the literal image subobject. -/
private theorem coimage_to_image_subobject_preserves (f : A ⟶ B) (i : ℤ) :
    ((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i).Factors
      (((coimage f).filtration i).arrow ≫ coimageToImageSubobjectHom f) := by
  let u : ((coimage f).filtration i : C) ⟶ B.obj :=
    (((coimage f).filtration i).arrow ≫ coimageToImageSubobjectHom f) ≫
      (imageSubobject f.hom).arrow
  -- Reinterpret the induced target stage as a pullback stage inside `B`.
  rw [show (B.subobjectFilteredObject (imageSubobject f.hom)).filtration i =
      (Subobject.pullback (imageSubobject f.hom).arrow).obj (B.filtration i) by
    rfl]
  apply (pullback_factors_iff (imageSubobject f.hom).arrow (B.filtration i)
      (((coimage f).filtration i).arrow ≫ coimageToImageSubobjectHom f)).2
  rw [Subobject.factors_iff]
  refine ⟨factorThruImageSubobject u ≫ Subobject.ofLE _ _ ?_, ?_⟩
  · -- The image of the stage composite is exactly the quotient stage, which lies in `B.filtration i`.
    rw [coimage_stage_maps_to_strict_subobject]
    rw [show A.filtration.quotient f.hom i = imageSubobject ((A.filtration i).arrow ≫ f.hom) by
      simpa using
        (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration f.hom i)]
    exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ (f.preserves i))
  · -- Unpack the chosen factorization through the image and the inclusion into `B.filtration i`.
    simp [u, Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]

/-- Helper for Lemma 12.19.4: the ambient comparison to the literal image subobject is a morphism
of filtered objects. -/
def coimageToImageSubobject (f : A ⟶ B) :
    coimage f ⟶ B.subobjectFilteredObject (imageSubobject f.hom) where
  hom := coimageToImageSubobjectHom f
  preserves := coimage_to_image_subobject_preserves f

/-- Helper for Lemma 12.19.4: mapping a subobject across an isomorphism agrees with taking the
image of the composed arrow. -/
private theorem mapIso_obj_eq_imageSubobject {X Y : C} (e : X ≅ Y) (S : Subobject X) :
    (Subobject.map e.hom).obj S = imageSubobject (S.arrow ≫ e.hom) := by
  -- The composite `S ↪ X ⟶ Y` is mono, so its image subobject is represented by that arrow.
  calc
    (Subobject.map e.hom).obj S = (Subobject.map e.hom).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ e.hom) := by
      rw [Subobject.map_mk]
    _ = imageSubobject (S.arrow ≫ e.hom) := by
      symm
      simpa using Limits.imageSubobject_mono (S.arrow ≫ e.hom)

/-- Helper for Lemma 12.19.4: mapping a subobject across a monomorphism agrees with the image of
the composed mono. -/
private theorem map_obj_eq_imageSubobject_of_mono {X Y : C} (m : X ⟶ Y) [Mono m]
    (S : Subobject X) :
    (Subobject.map m).obj S = imageSubobject (S.arrow ≫ m) := by
  -- The composite `S ↪ X ⟶ Y` is still mono, so its image subobject is represented by that
  -- composite arrow.
  calc
    (Subobject.map m).obj S = (Subobject.map m).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ m) := by
      rw [Subobject.map_mk]
    _ = imageSubobject (S.arrow ≫ m) := by
      symm
      simpa using Limits.imageSubobject_mono (S.arrow ≫ m)

/-- Helper for Lemma 12.19.4: transport along an isomorphism preserves each stage on the forward
map of `FilteredObject.ofIso`. -/
private theorem ofIso_hom_preserves_stage (A : FilteredObject C) {X : C} (e : A.obj ≅ X)
    (i : ℤ) :
    ((A.ofIso e).filtration i).Factors ((A.filtration i).arrow ≫ e.hom) := by
  -- Rewrite the transported stage as the image of the stage arrow composed with `e.hom`.
  rw [show (A.ofIso e).filtration i = imageSubobject ((A.filtration i).arrow ≫ e.hom) by
    simpa [ofIso] using mapIso_obj_eq_imageSubobject e (A.filtration i)]
  -- The image stage contains its defining composite by construction.
  simpa [imageSubobject_arrow_comp] using
    (Subobject.factors_comp_arrow
      (factorThruImageSubobject ((A.filtration i).arrow ≫ e.hom)))

/-- Helper for Lemma 12.19.4: transport along an isomorphism preserves each stage on the inverse
map of `FilteredObject.ofIso`. -/
private theorem ofIso_inv_preserves_stage (A : FilteredObject C) {X : C} (e : A.obj ≅ X)
    (i : ℤ) :
    (A.filtration i).Factors (((A.ofIso e).filtration i).arrow ≫ e.inv) := by
  let k : (A.filtration i : C) ⟶ X := (A.filtration i).arrow ≫ e.hom
  have hstage : (A.ofIso e).filtration i = imageSubobject k := by
    -- Rewrite the transported stage as the image of the stage map into `X`.
    simpa [ofIso, k] using mapIso_obj_eq_imageSubobject e (A.filtration i)
  rw [hstage]
  rw [Subobject.factors_iff]
  refine ⟨factorThruImageSubobject ((imageSubobject k).arrow ≫ e.inv) ≫ Subobject.ofLE _ _ ?_, ?_⟩
  · -- Pushing the transported stage back along `e.inv` recovers the original stage subobject.
    refine le_of_eq ?_
    calc
      imageSubobject ((imageSubobject k).arrow ≫ e.inv)
          = imageSubobject (factorThruImageSubobject k ≫ (imageSubobject k).arrow ≫ e.inv) := by
              symm
              simpa using
                (imageSubobject_comp_eq_of_epi (factorThruImageSubobject k)
                  ((imageSubobject k).arrow ≫ e.inv))
      _ = imageSubobject ((factorThruImageSubobject k ≫ (imageSubobject k).arrow) ≫ e.inv) := by
            simp
      _ = imageSubobject (k ≫ e.inv) := by
            rw [imageSubobject_arrow_comp]
      _ = imageSubobject (A.filtration i).arrow := by
            simp [k, Category.assoc]
      _ = A.filtration i := by
            simpa using Limits.imageSubobject_mono (A.filtration i).arrow
  · -- Expand the chosen image factorization and the comparison into `A.filtration i`.
    simp [k, Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]

section

omit [Abelian C]
/-- Helper for Lemma 12.19.4: for a filtered morphism whose underlying map is already an ambient
isomorphism, being an isomorphism of filtered objects is equivalent to the ambient inverse
preserving every filtration stage. -/
private theorem isIso_iff_inv_preserves_of_underlying_iso {X Y : FilteredObject C}
    (g : X ⟶ Y) [IsIso g.hom] :
    IsIso g ↔ ∀ i : ℤ, (X.filtration i).Factors ((Y.filtration i).arrow ≫ inv g.hom) := by
  constructor
  · intro hg i
    letI : IsIso g := hg
    -- Read off filtration preservation from the filtered inverse.
    have hhom : (inv g).hom = inv g.hom := by
      apply IsIso.eq_inv_of_hom_inv_id
      exact congrArg FilteredObject.Hom.hom (IsIso.hom_inv_id g)
    rw [← hhom]
    exact (inv g).preserves i
  · intro hinv
    -- Build the filtered inverse from the ambient inverse and the assumed stagewise preservation.
    let gInv : Y ⟶ X :=
      { hom := inv g.hom
        preserves := hinv }
    refine ⟨⟨gInv, ?_, ?_⟩⟩
    · -- The left inverse identity is checked after forgetting to the ambient category.
      apply FilteredObject.forget.map_injective
      change g.hom ≫ inv g.hom = 𝟙 X.obj
      simp
    · -- The right inverse identity is checked similarly.
      apply FilteredObject.forget.map_injective
      change inv g.hom ≫ g.hom = 𝟙 Y.obj
      simp

end

/-- Helper for Lemma 12.19.4: for a filtered morphism with underlying ambient isomorphism,
inverse stage preservation is equivalent to saying that the target stage is the transported image
of the source stage. -/
private theorem map_stage_eq_iff_inv_preserves_of_underlying_iso {X Y : FilteredObject C}
    (g : X ⟶ Y) [IsIso g.hom] (i : ℤ) :
    (Subobject.map g.hom).obj (X.filtration i) = Y.filtration i ↔
      (X.filtration i).Factors ((Y.filtration i).arrow ≫ inv g.hom) := by
  let e : X.obj ≅ Y.obj := asIso g.hom
  letI : Mono g.hom := by infer_instance
  constructor
  · intro hstage
    -- Route correction: once the target stage is identified with the transport of the source
    -- stage along the ambient isomorphism, inverse preservation is exactly `ofIso`.
    rw [← hstage]
    simpa [e] using ofIso_inv_preserves_stage (A := X) (e := e) i
  · intro hinv
    apply le_antisymm
    · -- Forward preservation of `g` gives one inclusion of the transported source stage.
      rw [map_obj_eq_imageSubobject_of_mono g.hom (X.filtration i)]
      exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ (g.preserves i))
    · -- The assumed inverse preservation gives the reverse inclusion after composing back by `g`.
      rw [map_obj_eq_imageSubobject_of_mono g.hom (X.filtration i)]
      let u : (Y.filtration i : C) ⟶ X.filtration i :=
        (X.filtration i).factorThru ((Y.filtration i).arrow ≫ inv g.hom) hinv
      calc
        Y.filtration i = imageSubobject (Y.filtration i).arrow := by
          symm
          simpa using Limits.imageSubobject_mono (Y.filtration i).arrow
        _ ≤ imageSubobject ((X.filtration i).arrow ≫ g.hom) := by
          have hFactors :
              (imageSubobject ((X.filtration i).arrow ≫ g.hom)).Factors
                (Y.filtration i).arrow := by
            rw [Subobject.factors_iff]
            refine ⟨u ≫ factorThruImageSubobject ((X.filtration i).arrow ≫ g.hom), ?_⟩
            calc
              (u ≫ factorThruImageSubobject ((X.filtration i).arrow ≫ g.hom)) ≫
                  (imageSubobject ((X.filtration i).arrow ≫ g.hom)).arrow
                  = u ≫ (X.filtration i).arrow ≫ g.hom := by
                      simp [Category.assoc]
              _ = (Y.filtration i).arrow ≫ inv g.hom ≫ g.hom := by
                    simp [u]
              _ = (Y.filtration i).arrow := by
                    simp
          exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ hFactors)

/-- Helper for Lemma 12.19.4: pushing the image of the coimage stage across the literal image
subobject inclusion recovers the quotient stage of the source filtration. -/
private theorem mapped_coimage_stage_eq_quotient (f : A ⟶ B) (i : ℤ) :
    (Subobject.map (imageSubobject f.hom).arrow).obj
      ((Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i)) =
        A.filtration.quotient f.hom i := by
  let u : ((coimage f).filtration i : C) ⟶ imageSubobject f.hom :=
    ((coimage f).filtration i).arrow ≫ coimageToImageSubobjectHom f
  letI : Mono (coimageToImageSubobjectHom f) := by infer_instance
  -- Rewrite the twice-mapped stage as the image of the composite into `B`, then invoke the
  -- earlier quotient-stage computation.
  calc
    (Subobject.map (imageSubobject f.hom).arrow).obj
        ((Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i))
        =
          imageSubobject
            (((Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i)).arrow ≫
              (imageSubobject f.hom).arrow) := by
              rw [map_obj_eq_imageSubobject_of_mono (imageSubobject f.hom).arrow
                ((Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i))]
    _ = imageSubobject ((imageSubobject u).arrow ≫ (imageSubobject f.hom).arrow) := by
          rw [map_obj_eq_imageSubobject_of_mono (coimageToImageSubobjectHom f)
            ((coimage f).filtration i)]
    _ = imageSubobject (u ≫ (imageSubobject f.hom).arrow) := by
          symm
          simpa [u, Category.assoc] using
            (imageSubobject_comp_eq_of_epi (factorThruImageSubobject u)
              ((imageSubobject u).arrow ≫ (imageSubobject f.hom).arrow))
    _ = A.filtration.quotient f.hom i := by
          simpa [u, Category.assoc] using coimage_stage_maps_to_strict_subobject f i

/-- Helper for Lemma 12.19.4: pushing the induced stage on the literal image object into `B`
recovers the textbook intersection `im(f) ∩ F^i B`. -/
private theorem literal_image_stage_map_eq_inf (f : A ⟶ B) (i : ℤ) :
    (Subobject.map (imageSubobject f.hom).arrow).obj
      ((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i) =
        imageSubobject f.hom ⊓ B.filtration i := by
  -- Unfold the induced filtration stage and rewrite it with the standard `map/pullback = inf`
  -- formula for the ambient mono `im(f) ↪ B`.
  rw [show (B.subobjectFilteredObject (imageSubobject f.hom)).filtration i =
      (Subobject.pullback (imageSubobject f.hom).arrow).obj (B.filtration i) by
    rfl]
  rw [← Subobject.inf_eq_map_pullback (imageSubobject f.hom) (B.filtration i)]

/-- Helper for Lemma 12.19.4: the ambient comparison from `coim(f)` to the literal image
subobject is an isomorphism. -/
private theorem coimageToImageSubobjectHom_isIso (f : A ⟶ B) :
    IsIso (coimageToImageSubobjectHom f) := by
  let e : Abelian.coimage f.hom ≅ imageSubobject f.hom :=
    asIso (Abelian.coimageImageComparison f.hom) ≪≫
      (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).symm
  have he : e.hom = coimageToImageSubobjectHom f := by
    simp [coimageToImageSubobjectHom, e]
  rw [← he]
  infer_instance

/-- Helper for Lemma 12.19.4: the underlying ambient map of the filtered comparison to the literal
image subobject is an isomorphism. -/
private theorem coimageToImageSubobject_hom_isIso (f : A ⟶ B) :
    IsIso (coimageToImageSubobject f).hom := by
  change IsIso (coimageToImageSubobjectHom f)
  exact coimageToImageSubobjectHom_isIso f

/-- Helper for Lemma 12.19.4: the filtered object on the literal image subobject transports to the
chosen `Abelian.image` owner. -/
private theorem imageSubobjectFilteredObjectIsoImage_hom_preserves (f : A ⟶ B) (i : ℤ) :
    ((image f).filtration i).Factors
      (((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i).arrow ≫
        (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).hom) := by
  -- Route correction: keep the literal image-subobject model fixed and read the transported stage
  -- on `image f` directly from the `ofIso` definition.
  simpa [image] using
    ofIso_hom_preserves_stage
      (A := B.subobjectFilteredObject (imageSubobject f.hom))
      (e := imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm) i

/-- Helper for Lemma 12.19.4: the inverse transport from `Abelian.image` back to the literal image
subobject preserves the induced filtration. -/
private theorem imageSubobjectFilteredObjectIsoImage_inv_preserves (f : A ⟶ B) (i : ℤ) :
    ((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i).Factors
      (((image f).filtration i).arrow ≫
        (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).inv) := by
  -- Route correction: the inverse preservation is the companion transport identity for the same
  -- `ofIso`-defined filtration.
  simpa [image] using
    ofIso_inv_preserves_stage
      (A := B.subobjectFilteredObject (imageSubobject f.hom))
      (e := imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm) i

/-- Helper for Lemma 12.19.4: the literal image-subobject model and the chosen `Abelian.image`
model are isomorphic as filtered objects. -/
def imageSubobjectFilteredObjectIsoImage (f : A ⟶ B) :
    B.subobjectFilteredObject (imageSubobject f.hom) ≅ image f where
  hom :=
    { hom := (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).hom
      preserves := imageSubobjectFilteredObjectIsoImage_hom_preserves f }
  inv :=
    { hom := (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).inv
      preserves := imageSubobjectFilteredObjectIsoImage_inv_preserves f }
  hom_inv_id := by
    -- Proof comment: the filtered identity is determined by the underlying ambient identity.
    apply FilteredObject.Hom.ext
    let e : (imageSubobject f.hom : C) ≅ Abelian.image f.hom :=
      imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
    change e.hom ≫ e.inv = 𝟙 (B.subobjectFilteredObject (imageSubobject f.hom)).obj
    exact e.hom_inv_id
  inv_hom_id := by
    -- Proof comment: similarly for the inverse followed by the forward transport.
    apply FilteredObject.Hom.ext
    let e : (imageSubobject f.hom : C) ≅ Abelian.image f.hom :=
      imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
    change e.inv ≫ e.hom = 𝟙 (Abelian.image f.hom)
    exact e.inv_hom_id

/-- Helper for Lemma 12.19.4: the canonical comparison from the filtered coimage to the filtered
image is obtained by transporting the literal image-subobject comparison. -/
def coimageImageComparison (f : A ⟶ B) : coimage f ⟶ image f :=
  coimageToImageSubobject f ≫ (imageSubobjectFilteredObjectIsoImage f).hom

/-- The canonical morphism from the filtered coimage of `f` to the filtered image of `f`. -/
@[simp] theorem coimageImageComparison_hom (f : A ⟶ B) :
    (coimageImageComparison f).hom = Abelian.coimageImageComparison f.hom := by
  -- The transport to `Abelian.image f.hom` cancels with the inverse transport used in the literal
  -- image-subobject comparison.
  let e : (imageSubobject f.hom : C) ≅ Abelian.image f.hom :=
    imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
  apply (cancel_mono (Abelian.image.ι f.hom)).1
  change (((Abelian.coimageImageComparison f.hom ≫ e.inv) ≫ e.hom) ≫
      Abelian.image.ι f.hom) =
    Abelian.coimageImageComparison f.hom ≫ Abelian.image.ι f.hom
  calc
    (((Abelian.coimageImageComparison f.hom ≫ e.inv) ≫ e.hom) ≫
        Abelian.image.ι f.hom)
        =
          Abelian.coimageImageComparison f.hom ≫ (e.inv ≫ e.hom) ≫
            Abelian.image.ι f.hom := by
              simp [Category.assoc]
    _ = Abelian.coimageImageComparison f.hom ≫ Abelian.image.ι f.hom := by
          simp

/-- Helper for Lemma 12.19.4: strictness of `f` is equivalent to saying that the quotient
filtration on `coim(f)` maps isomorphically onto the induced filtration on the literal image
subobject. -/
private theorem strict_iff_stage_map_eq_coimage_to_image_subobject (f : A ⟶ B) :
    Strict f ↔ ∀ i : ℤ,
      (Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i) =
        (B.subobjectFilteredObject (imageSubobject f.hom)).filtration i := by
  letI : IsIso (coimageToImageSubobjectHom f) := coimageToImageSubobjectHom_isIso f
  letI : Mono (coimageToImageSubobjectHom f) := by infer_instance
  constructor
  · intro hf i
    -- Compare the two stages after pushing both of them into the ambient object `B`.
    have hi :
        (Subobject.map (imageSubobject f.hom).arrow).obj
            ((Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i)) =
          (Subobject.map (imageSubobject f.hom).arrow).obj
            ((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i) := by
      calc
      (Subobject.map (imageSubobject f.hom).arrow).obj
          ((Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i))
          = A.filtration.quotient f.hom i := mapped_coimage_stage_eq_quotient f i
      _ = imageSubobject f.hom ⊓ B.filtration i := by
            simpa using (strict_iff_quotient_eq_inf f).1 hf i
      _ = (Subobject.map (imageSubobject f.hom).arrow).obj
            ((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i) := by
            symm
            exact literal_image_stage_map_eq_inf f i
    have hpull := congrArg ((Subobject.pullback (imageSubobject f.hom).arrow).obj) hi
    -- Pullback along the ambient mono is inverse to mapping subobjects into the image object.
    simpa [FilteredObject.subobjectFilteredObject, Subobject.exists_iso_map,
      Subobject.pullback_self] using hpull
  · intro hstage
    refine (strict_iff_quotient_eq_inf f).2 ?_
    intro i
    have hi := congrArg ((Subobject.map (imageSubobject f.hom).arrow).obj) (hstage i)
    calc
      A.filtration.quotient f.hom i
          =
            (Subobject.map (imageSubobject f.hom).arrow).obj
              ((Subobject.map (coimageToImageSubobjectHom f)).obj ((coimage f).filtration i)) := by
                symm
                exact mapped_coimage_stage_eq_quotient f i
      _ =
            (Subobject.map (imageSubobject f.hom).arrow).obj
              ((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i) := by
                simpa using hi
      _ = imageSubobject f.hom ⊓ B.filtration i := literal_image_stage_map_eq_inf f i

/-- Helper for Lemma 12.19.4: the literal image-subobject comparison is an isomorphism of
filtered objects exactly when `f` is strict. -/
private theorem strict_iff_coimage_to_image_subobject_isIso (f : A ⟶ B) :
    Strict f ↔ IsIso (coimageToImageSubobject f) := by
  letI : IsIso (coimageToImageSubobject f).hom := coimageToImageSubobject_hom_isIso f
  constructor
  · intro hf
    have hinv :
        ∀ i : ℤ,
          ((coimage f).filtration i).Factors
            ((((B.subobjectFilteredObject (imageSubobject f.hom)).filtration i).arrow) ≫
              inv (coimageToImageSubobject f).hom) := by
      intro i
      exact (map_stage_eq_iff_inv_preserves_of_underlying_iso (coimageToImageSubobject f) i).1
        ((strict_iff_stage_map_eq_coimage_to_image_subobject f).1 hf i)
    exact (isIso_iff_inv_preserves_of_underlying_iso (coimageToImageSubobject f)).2
      hinv
  · intro hIso
    have hinv := (isIso_iff_inv_preserves_of_underlying_iso (coimageToImageSubobject f)).1 hIso
    refine (strict_iff_stage_map_eq_coimage_to_image_subobject f).2 ?_
    intro i
    exact (map_stage_eq_iff_inv_preserves_of_underlying_iso (coimageToImageSubobject f) i).2
      (hinv i)

-- Proof sketch: the quotient filtration on `coim(f)` and the induced filtration on `im(f)` agree
-- exactly when the stagewise image/intersection equality defining strictness holds. Thus `f` is
-- strict precisely when the canonical comparison is an isomorphism in the filtered category.
/-- Lemma 12.19.4: for a morphism of filtered objects in an abelian category, strictness is
equivalent to the canonical comparison morphism `coim(f) ⟶ im(f)` being an isomorphism of
filtered objects. -/
theorem strict_iff_coimageImageComparison_isIso (f : A ⟶ B) :
    Strict f ↔ IsIso (coimageImageComparison f) := by
  constructor
  · intro hf
    letI : IsIso (coimageToImageSubobject f) :=
      (strict_iff_coimage_to_image_subobject_isIso f).1 hf
    let e₁ : coimage f ≅ B.subobjectFilteredObject (imageSubobject f.hom) :=
      asIso (coimageToImageSubobject f)
    let e₂ : B.subobjectFilteredObject (imageSubobject f.hom) ≅ image f :=
      imageSubobjectFilteredObjectIsoImage f
    -- Compose the literal image-subobject isomorphism with the fixed transport to `Abelian.image`.
    have hcomp : (e₁ ≪≫ e₂).hom = coimageImageComparison f := by
      simp [coimageImageComparison, e₁, e₂]
    rw [← hcomp]
    infer_instance
  · intro hIso
    have htransport :
        coimageToImageSubobject f =
          coimageImageComparison f ≫ (imageSubobjectFilteredObjectIsoImage f).inv := by
      -- Undo the final transport from the literal image subobject to `Abelian.image`.
      apply FilteredObject.Hom.ext
      simp [coimageImageComparison, Category.assoc]
    have hSub : IsIso (coimageToImageSubobject f) := by
      letI : IsIso (coimageImageComparison f) := hIso
      let e₁ : coimage f ≅ image f := asIso (coimageImageComparison f)
      let e₂ : image f ≅ B.subobjectFilteredObject (imageSubobject f.hom) :=
        (imageSubobjectFilteredObjectIsoImage f).symm
      have hcomp : (e₁ ≪≫ e₂).hom = coimageToImageSubobject f := by
        simpa [htransport, e₁, e₂, Category.assoc]
      rw [← hcomp]
      infer_instance
    exact (strict_iff_coimage_to_image_subobject_isIso f).2 hSub

end Hom
end Abelian
end FilteredObject

end CategoryTheory
