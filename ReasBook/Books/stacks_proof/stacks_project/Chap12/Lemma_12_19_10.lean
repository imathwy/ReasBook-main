import StacksProject_2024.Chap12.Lemma_12_19_4
import StacksProject_2024.Chap12.Lemma_12_19_7
import Mathlib.Tactic.StacksAttribute

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

open FilteredObject.Hom

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.10:
- source-facing: strictness of the right map in a filtered pushout square, and the resulting
  existence statement
- core/canonical owner: `IsPushout f g g' f'`, specialized to `HasPushout f g` and `pushout.inr f g`
- bridge/view: the stagewise-image filtration model on the ambient pushout of `f.hom` and `g.hom`
-/

private noncomputable def pushoutStageMap (f : A ⟶ B) (g : A ⟶ C) (p : ℤ) :
    ((B.filtration p : 𝒜) ⊞ (C.filtration p : 𝒜)) ⟶ pushout f.hom g.hom :=
  biprod.desc
    ((B.filtration p).arrow ≫ pushout.inl f.hom g.hom)
    ((C.filtration p).arrow ≫ pushout.inr f.hom g.hom)

private theorem pushoutFiltration_antitone (f : A ⟶ B) (g : A ⟶ C) :
    Antitone fun p ↦ imageSubobject (pushoutStageMap f g p) := by
  intro p q hpq
  let ιB : (B.filtration q : 𝒜) ⟶ B.filtration p :=
    Subobject.ofLE _ _ (B.filtration.antitone_obj hpq)
  let ιC : (C.filtration q : 𝒜) ⟶ C.filtration p :=
    Subobject.ofLE _ _ (C.filtration.antitone_obj hpq)
  let ι :
      ((B.filtration q : 𝒜) ⊞ (C.filtration q : 𝒜)) ⟶
        ((B.filtration p : 𝒜) ⊞ (C.filtration p : 𝒜)) :=
    biprod.map ιB ιC
  have hcomp : pushoutStageMap f g q = ι ≫ pushoutStageMap f g p := by
    -- Compare the two stage maps on the left and right biproduct generators.
    apply biprod.hom_ext'
    · simp [pushoutStageMap, ι, ιB, Category.assoc, Subobject.ofLE_arrow]
    · simp [pushoutStageMap, ι, ιC, Category.assoc, Subobject.ofLE_arrow]
  -- The `q`-stage image lands in the `p`-stage image through the comparison morphism `ι`.
  simpa [hcomp] using imageSubobject_comp_le ι (pushoutStageMap f g p)

private noncomputable def pushoutModel (f : A ⟶ B) (g : A ⟶ C) : FilteredObject 𝒜 where
  obj := pushout f.hom g.hom
  filtration :=
    { toFun := fun p ↦ imageSubobject (pushoutStageMap f g p)
      monotone' := by
        intro p q hpq
        exact pushoutFiltration_antitone f g hpq }

private theorem pushoutModelInl_preserves (f : A ⟶ B) (g : A ⟶ C) :
    ∀ p : ℤ,
      ((pushoutModel f g).filtration p).Factors
        ((B.filtration p).arrow ≫ pushout.inl f.hom g.hom) :=
  by
    intro p
    -- The left generator of the ambient stage biproduct already lands in the stage image.
    simpa [pushoutModel, pushoutStageMap, Category.assoc] using
      (Subobject.factors_comp_arrow
        (biprod.inl ≫ factorThruImageSubobject (pushoutStageMap f g p) :
          (B.filtration p : 𝒜) ⟶ imageSubobject (pushoutStageMap f g p)))

private theorem pushoutModelInr_preserves (f : A ⟶ B) (g : A ⟶ C) :
    ∀ p : ℤ,
      ((pushoutModel f g).filtration p).Factors
        ((C.filtration p).arrow ≫ pushout.inr f.hom g.hom) :=
  by
    intro p
    -- The right generator of the ambient stage biproduct already lands in the stage image.
    simpa [pushoutModel, pushoutStageMap, Category.assoc] using
      (Subobject.factors_comp_arrow
        (biprod.inr ≫ factorThruImageSubobject (pushoutStageMap f g p) :
          (C.filtration p : 𝒜) ⟶ imageSubobject (pushoutStageMap f g p)))

private noncomputable def pushoutModelInl (f : A ⟶ B) (g : A ⟶ C) : B ⟶ pushoutModel f g where
  hom := pushout.inl f.hom g.hom
  preserves := pushoutModelInl_preserves f g

private noncomputable def pushoutModelInr (f : A ⟶ B) (g : A ⟶ C) : C ⟶ pushoutModel f g where
  hom := pushout.inr f.hom g.hom
  preserves := pushoutModelInr_preserves f g

private theorem pushoutModel_isPushout (f : A ⟶ B) (g : A ⟶ C) :
    IsPushout f g (pushoutModelInl f g) (pushoutModelInr f g) := by
  let c : PushoutCocone f g :=
    PushoutCocone.mk (pushoutModelInl f g) (pushoutModelInr f g) <| by
      apply FilteredObject.forget.map_injective
      change f.hom ≫ pushout.inl f.hom g.hom = g.hom ≫ pushout.inr f.hom g.hom
      exact pushout.condition
  refine IsPushout.of_isColimit (c := c) ?_
  refine PushoutCocone.IsColimit.mk c.condition ?_ ?_ ?_ ?_
  · intro s
    refine
      { hom := pushout.desc s.inl.hom s.inr.hom (congrArg FilteredObject.Hom.hom s.condition)
        preserves := ?_ }
    intro p
    let uB :=
      (s.pt.filtration p).factorThru ((B.filtration p).arrow ≫ s.inl.hom) (s.inl.preserves p)
    let uC :=
      (s.pt.filtration p).factorThru ((C.filtration p).arrow ≫ s.inr.hom) (s.inr.preserves p)
    let u :
        ((B.filtration p : 𝒜) ⊞ (C.filtration p : 𝒜)) ⟶ s.pt.filtration p :=
      biprod.desc uB uC
    have hFactorsStage :
        (s.pt.filtration p).Factors
          (pushoutStageMap f g p ≫
            pushout.desc s.inl.hom s.inr.hom (congrArg FilteredObject.Hom.hom s.condition)) := by
      refine ⟨u, ?_⟩
      -- The descended ambient morphism agrees with the cocone maps on the two generators.
      apply biprod.hom_ext'
      · simp [u, uB, pushoutStageMap, Category.assoc]
      · simp [u, uC, pushoutStageMap, Category.assoc]
    have hPullback :
        ((Subobject.pullback
              (pushout.desc s.inl.hom s.inr.hom (congrArg FilteredObject.Hom.hom s.condition))).obj
            (s.pt.filtration p)).Factors (pushoutStageMap f g p) := by
      -- Rephrase the stagewise landing statement as a pullback factorization.
      rw [pullback_factors_iff]
      simpa [Category.assoc] using hFactorsStage
    have hle :
        imageSubobject (pushoutStageMap f g p) ≤
          (Subobject.pullback
              (pushout.desc s.inl.hom s.inr.hom (congrArg FilteredObject.Hom.hom s.condition))).obj
            (s.pt.filtration p) := by
      -- The stage image is the smallest subobject containing the stage generators.
      exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ hPullback)
    -- Convert the pullback inclusion back into the filtration-preservation condition.
    rw [pullback_factors_iff]
    exact
      Subobject.factors_of_le (imageSubobject (pushoutStageMap f g p)).arrow hle
        (Subobject.factors_self _)
  · intro s
    apply FilteredObject.forget.map_injective
    change
      pushout.inl f.hom g.hom ≫
          pushout.desc s.inl.hom s.inr.hom (congrArg FilteredObject.Hom.hom s.condition) =
        s.inl.hom
    simp
  · intro s
    apply FilteredObject.forget.map_injective
    change
      pushout.inr f.hom g.hom ≫
          pushout.desc s.inl.hom s.inr.hom (congrArg FilteredObject.Hom.hom s.condition) =
        s.inr.hom
    simp
  · intro s m hmB hmC
    apply FilteredObject.forget.map_injective
    apply pushout.hom_ext
    · simpa using congrArg FilteredObject.Hom.hom hmB
    · simpa using congrArg FilteredObject.Hom.hom hmC

noncomputable instance hasPushout (f : A ⟶ B) (g : A ⟶ C) : HasPushout f g :=
  (pushoutModel_isPushout f g).hasPushout

/-- Helper for Lemma 12.19.10: mapping the image of a composite through a monomorphism agrees
with the image of the whole composite. -/
private theorem imageSubobject_comp_eq_map_of_mono {X Y Z : 𝒜}
    (u : X ⟶ Y) (v : Y ⟶ Z) [Mono v] :
    imageSubobject (u ≫ v) = (Subobject.map v).obj (imageSubobject u) := by
  calc
    imageSubobject (u ≫ v) = imageSubobject ((imageSubobject u).arrow ≫ v) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction u v]
    _ = Subobject.mk ((imageSubobject u).arrow ≫ v) := by
          simpa using (Limits.imageSubobject_mono ((imageSubobject u).arrow ≫ v))
    _ = (Subobject.map v).obj (Subobject.mk (imageSubobject u).arrow) := by
          rw [Subobject.map_mk]
    _ = (Subobject.map v).obj (imageSubobject u) := by
          rw [Subobject.mk_arrow]

/-- Helper for Lemma 12.19.10: postcomposing an epimorphism does not change the image
subobject. -/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : 𝒜}
    (u : X ⟶ Y) [Epi u] (v : Y ⟶ Z) :
    imageSubobject (u ≫ v) = imageSubobject v := by
  -- Proof comment: rewrite through the restriction to `im(u)`, then identify `im(u)` with `⊤`
  -- because `u` is epi.
  calc
    imageSubobject (u ≫ v) = imageSubobject ((imageSubobject u).arrow ≫ v) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction u v]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ v) := by
          simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ v))
            (Limits.imageSubobject_eq_top_of_epi u)
    _ = imageSubobject v := by
          simpa using Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) v

/-- Helper for Lemma 12.19.10: a filtered isomorphism is strict. -/
private theorem strict_iso_hom {X Y : FilteredObject 𝒜} (e : X ≅ Y) :
    Strict e.hom := by
  letI : Mono e.hom.hom := by infer_instance
  refine (strict_iff_induced_filtration_of_mono e.hom).2 ?_
  refine OrderHom.ext _ _ ?_
  funext i
  refine le_antisymm ?_ ?_
  · -- Proof comment: filtration preservation of `e.hom` gives the easy inclusion into the
    -- pullback filtration.
    simpa using pullback_preserves e.hom i
  · -- Proof comment: factor the pullback stage into `Y.filtration i`, then come back using the
    -- inverse isomorphism and cancel `e.hom ≫ e.inv = 𝟙`.
    refine Subobject.le_of_factors ?_
    let P : Subobject X.obj := (Subobject.pullback e.hom.hom).obj (Y.filtration i)
    have hP :
        (Y.filtration i).Factors (P.arrow ≫ e.hom.hom) := by
      rw [show P = (Subobject.pullback e.hom.hom).obj (Y.filtration i) by rfl]
      rw [pullback_factors_iff]
      exact Subobject.factors_self P
    let u : (P : 𝒜) ⟶ Y.filtration i :=
      (Y.filtration i).factorThru (P.arrow ≫ e.hom.hom) hP
    let v : (Y.filtration i : 𝒜) ⟶ X.filtration i :=
      (X.filtration i).factorThru ((Y.filtration i).arrow ≫ e.inv.hom) (e.inv.preserves i)
    refine ⟨u ≫ v, ?_⟩
    calc
      u ≫ v ≫ (X.filtration i).arrow
          = u ≫ (Y.filtration i).arrow ≫ e.inv.hom := by
              simp [v, Category.assoc]
      _ = P.arrow ≫ e.hom.hom ≫ e.inv.hom := by
            simp [u, Category.assoc]
      _ = P.arrow := by
            simp

/-- Helper for Lemma 12.19.10: a strict monomorphism maps intersections with a stage to the
intersection of the mapped subobject with the target stage. -/
private theorem map_inf_eq_of_strict_mono {X Y : FilteredObject 𝒜} (h : X ⟶ Y)
    [Mono h.hom] (hh : Strict h) (S : Subobject X.obj) (i : ℤ) :
    (Subobject.map h.hom).obj (S ⊓ X.filtration i) =
      (Subobject.map h.hom).obj S ⊓ Y.filtration i := by
  have hi : X.filtration i = (Subobject.pullback h.hom).obj (Y.filtration i) := by
    exact congrArg (fun F ↦ F i) ((strict_iff_induced_filtration_of_mono h).1 hh)
  rw [hi, Subobject.inf_map]
  rw [show (Subobject.map h.hom).obj ((Subobject.pullback h.hom).obj (Y.filtration i)) =
      Subobject.mk h.hom ⊓ Y.filtration i by
        simpa [Subobject.inf_def] using
          (Subobject.inf_eq_map_pullback' (MonoOver.mk h.hom) (Y.filtration i)).symm]
  have hS : (Subobject.map h.hom).obj S ≤ Subobject.mk h.hom := by
    induction S using Subobject.ind
    rename_i W m hm
    simpa [Subobject.map_mk] using
      (Subobject.mk_le_mk_of_comm m (by simp) :
        Subobject.mk (m ≫ h.hom) ≤ Subobject.mk h.hom)
  calc
    (Subobject.map h.hom).obj S ⊓ (Subobject.mk h.hom ⊓ Y.filtration i)
        = ((Subobject.map h.hom).obj S ⊓ Subobject.mk h.hom) ⊓ Y.filtration i := by
            simp [inf_assoc]
    _ = (Subobject.map h.hom).obj S ⊓ Y.filtration i := by
          simp [inf_eq_left.mpr hS]

/-- Helper for Lemma 12.19.10: postcomposing a strict morphism with a filtered isomorphism
preserves strictness. -/
private theorem strict_postcompose_iso {X Y Z : FilteredObject 𝒜}
    (h : X ⟶ Y) (e : Y ≅ Z) (hh : Strict h) :
    Strict (h ≫ e.hom) := by
  -- Proof comment: map the strictness identity for `h` across the strict filtered isomorphism
  -- `e.hom`, using that image subobjects and stage intersections are stable under a mono.
  letI : Mono e.hom.hom := by infer_instance
  refine (strict_iff_quotient_eq_inf (h ≫ e.hom)).2 ?_
  intro i
  calc
    X.filtration.quotient (h.hom ≫ e.hom.hom) i
        = imageSubobject ((X.filtration i).arrow ≫ h.hom ≫ e.hom.hom) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map e.hom.hom).obj (imageSubobject ((X.filtration i).arrow ≫ h.hom)) := by
          simpa [Category.assoc] using
            imageSubobject_comp_eq_map_of_mono ((X.filtration i).arrow ≫ h.hom) e.hom.hom
    _ = (Subobject.map e.hom.hom).obj (X.filtration.quotient h.hom i) := by
          rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map e.hom.hom).obj (imageSubobject h.hom ⊓ Y.filtration i) := by
          rw [(strict_iff_quotient_eq_inf h).1 hh i]
    _ = (Subobject.map e.hom.hom).obj (imageSubobject h.hom) ⊓ Z.filtration i := by
          simpa using map_inf_eq_of_strict_mono e.hom (strict_iso_hom e) (imageSubobject h.hom) i
    _ = imageSubobject (h.hom ≫ e.hom.hom) ⊓ Z.filtration i := by
          rw [← imageSubobject_comp_eq_map_of_mono h.hom e.hom.hom]

/-- Helper for Lemma 12.19.10: the inclusion of a filtered subobject is strict because its
filtration is induced from the ambient object. -/
private theorem strict_subobjectInclusion (X : FilteredObject 𝒜) (S : Subobject X.obj) :
    Strict (X.subobjectInclusion S) := by
  letI : Mono (X.subobjectInclusion S).hom := by
    change Mono S.arrow
    infer_instance
  -- Proof comment: the induced filtration on the subobject is definitionally the pullback
  -- filtration required by the mono-side strictness criterion.
  refine (strict_iff_induced_filtration_of_mono (X.subobjectInclusion S)).2 ?_
  rfl

/-- Helper for Lemma 12.19.10: composing on the right with a strict monomorphism preserves
strictness. -/
private theorem strict_comp_of_mono {X Y Z : FilteredObject 𝒜}
    (h : X ⟶ Y) (k : Y ⟶ Z) [Mono k.hom] (hh : Strict h) (hk : Strict k) :
    Strict (h ≫ k) := by
  -- Proof comment: map the strictness identity for `h` across the strict mono `k`.
  refine (strict_iff_quotient_eq_inf (h ≫ k)).2 ?_
  intro i
  calc
    X.filtration.quotient (h.hom ≫ k.hom) i
        = imageSubobject ((X.filtration i).arrow ≫ h.hom ≫ k.hom) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map k.hom).obj (imageSubobject ((X.filtration i).arrow ≫ h.hom)) := by
          simpa [Category.assoc] using
            imageSubobject_comp_eq_map_of_mono ((X.filtration i).arrow ≫ h.hom) k.hom
    _ = (Subobject.map k.hom).obj (X.filtration.quotient h.hom i) := by
          rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map k.hom).obj (imageSubobject h.hom ⊓ Y.filtration i) := by
          rw [(strict_iff_quotient_eq_inf h).1 hh i]
    _ = (Subobject.map k.hom).obj (imageSubobject h.hom) ⊓ Z.filtration i := by
          simpa using map_inf_eq_of_strict_mono k hk (imageSubobject h.hom) i
    _ = imageSubobject (h.hom ≫ k.hom) ⊓ Z.filtration i := by
          rw [← imageSubobject_comp_eq_map_of_mono h.hom k.hom]

/-- Helper for Lemma 12.19.10: the factor through the ambient image carries the induced filtered
structure coming from the codomain. -/
private theorem filteredImageFactor_preserves {X Y : FilteredObject 𝒜} (h : X ⟶ Y) :
    ∀ i : ℤ,
      ((Y.subobjectFilteredObject (imageSubobject h.hom)).filtration i).Factors
        ((X.filtration i).arrow ≫ factorThruImageSubobject h.hom) := by
  intro i
  -- Proof comment: the induced stage on the image is the pullback of the ambient stage along the
  -- image inclusion, and the defining image factor composes back to `h.hom`.
  change
    ((Subobject.pullback (imageSubobject h.hom).arrow).obj (Y.filtration i)).Factors
      ((X.filtration i).arrow ≫ factorThruImageSubobject h.hom)
  rw [← pullback_factors_iff (f := (imageSubobject h.hom).arrow) (y := Y.filtration i)
    (h := (X.filtration i).arrow ≫ factorThruImageSubobject h.hom)]
  simpa [Category.assoc] using h.preserves i

/-- Helper for Lemma 12.19.10: every filtered morphism factors through the filtered object on its
ambient image subobject. -/
private noncomputable def filteredImageFactor {X Y : FilteredObject 𝒜} (h : X ⟶ Y) :
    X ⟶ Y.subobjectFilteredObject (imageSubobject h.hom) where
  hom := factorThruImageSubobject h.hom
  preserves := filteredImageFactor_preserves h

/-- Helper for Lemma 12.19.10: the filtered image factor followed by the subobject inclusion is
the original morphism. -/
private theorem filteredImageFactor_comp_subobjectInclusion {X Y : FilteredObject 𝒜}
    (h : X ⟶ Y) :
    filteredImageFactor h ≫ Y.subobjectInclusion (imageSubobject h.hom) = h := by
  -- Proof comment: this is the defining factorization of a morphism through its image.
  apply FilteredObject.forget.map_injective
  simpa [filteredImageFactor] using imageSubobject_arrow_comp h.hom

/-- Helper for Lemma 12.19.10: pulling back the induced stage on the filtered image factor
recovers the ambient pullback stage for the original morphism. -/
private theorem pullback_stage_of_filtered_image_factor
    {X Y : FilteredObject 𝒜} (h : X ⟶ Y) (i : ℤ) :
    (Subobject.pullback (filteredImageFactor h).hom).obj
      ((Y.subobjectFilteredObject (imageSubobject h.hom)).filtration i) =
        (Subobject.pullback h.hom).obj (Y.filtration i) := by
  -- Proof comment: unfold the induced filtration on the image object and then compose the two
  -- pullbacks using the defining factorization through the ambient image inclusion.
  change
    (Subobject.pullback (filteredImageFactor h).hom).obj
        ((Subobject.pullback (imageSubobject h.hom).arrow).obj (Y.filtration i)) =
      (Subobject.pullback h.hom).obj (Y.filtration i)
  calc
    (Subobject.pullback (filteredImageFactor h).hom).obj
        ((Subobject.pullback (imageSubobject h.hom).arrow).obj (Y.filtration i))
        =
          (Subobject.pullback
            ((filteredImageFactor h).hom ≫ (imageSubobject h.hom).arrow)).obj
            (Y.filtration i) := by
              symm
              exact Subobject.pullback_comp (filteredImageFactor h).hom
                (imageSubobject h.hom).arrow (Y.filtration i)
    _ = (Subobject.pullback h.hom).obj (Y.filtration i) := by
          rw [show (filteredImageFactor h).hom ≫ (imageSubobject h.hom).arrow = h.hom by
                exact congrArg FilteredObject.Hom.hom
                  (filteredImageFactor_comp_subobjectInclusion h)]

/-- Helper for Lemma 12.19.10: applying `Subobject.exists` to a subobject computes the image of
its arrow followed by the ambient morphism. -/
private theorem exists_obj_eq_imageSubobject_comp {X Y : 𝒜} (u : X ⟶ Y) (S : Subobject X) :
    (Subobject.exists u).obj S = imageSubobject (S.arrow ≫ u) := by
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage u S ≪≫ (imageSubobjectIso _).symm)
  calc
    ((Subobject.existsIsoImage u S).hom ≫ (imageSubobjectIso (S.arrow ≫ u)).inv) ≫
        (imageSubobject (S.arrow ≫ u)).arrow
        = (Subobject.existsIsoImage u S).hom ≫ image.ι (S.arrow ≫ u) := by
            simp [Category.assoc]
    _ = ((Subobject.exists u).obj S).arrow := by
          simpa [Subobject.existsIsoImage] using
            (Over.w ((Subobject.existsCompRepresentativeIso u).app S).hom.hom)

/-- Helper for Lemma 12.19.10: pushing forward a pullback along an epimorphism recovers the
original subobject. -/
private theorem exists_pullback_eq_of_epi {X Y : 𝒜} (u : X ⟶ Y) [Epi u] (P : Subobject Y) :
    (Subobject.exists u).obj ((Subobject.pullback u).obj P) = P := by
  have hImage : imageSubobject (((Subobject.pullback u).obj P).arrow ≫ u) = P := by
    rw [← (Subobject.isPullback u P).w]
    haveI : Epi (Subobject.pullbackπ u P) :=
      Abelian.epi_fst_of_isLimit P.arrow u (Subobject.isPullback u P).isLimit
    have hle :
        imageSubobject (Subobject.pullbackπ u P ≫ P.arrow) ≤ imageSubobject P.arrow :=
      imageSubobject_comp_le (Subobject.pullbackπ u P) P.arrow
    haveI : Epi (Subobject.ofLE _ _ hle) :=
      imageSubobject_comp_le_epi_of_epi (Subobject.pullbackπ u P) P.arrow
    haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
    have hEq :
        imageSubobject (Subobject.pullbackπ u P ≫ P.arrow) = imageSubobject P.arrow :=
      Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)
    simpa [imageSubobject_mono] using hEq
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage u ((Subobject.pullback u).obj P) ≪≫
      (imageSubobjectIso _).symm ≪≫
      Subobject.isoOfEq _ _ hImage)
  calc
    ((Subobject.existsIsoImage u ((Subobject.pullback u).obj P)).hom ≫
        (imageSubobjectIso (((Subobject.pullback u).obj P).arrow ≫ u)).inv ≫
        (Subobject.isoOfEq _ _ hImage).hom) ≫
        P.arrow
        = (Subobject.existsIsoImage u ((Subobject.pullback u).obj P)).hom ≫
            image.ι (((Subobject.pullback u).obj P).arrow ≫ u) := by
              simp [Category.assoc]
    _ = ((Subobject.exists u).obj ((Subobject.pullback u).obj P)).arrow := by
          simpa [Subobject.existsIsoImage] using
            (Over.w ((Subobject.existsCompRepresentativeIso u).app
              ((Subobject.pullback u).obj P)).hom.hom)

/-- Helper for Lemma 12.19.10: the kernel of a composite is the pullback of the later kernel
along the earlier morphism. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : 𝒜} (u : X ⟶ Y) (v : Y ⟶ Z) :
    kernelSubobject (u ≫ v) = (Subobject.pullback u).obj (kernelSubobject v) := by
  -- Proof comment: the universal property of the pullback gives one inclusion, and the kernel
  -- condition gives the reverse inclusion.
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback u).obj (kernelSubobject v)).factorThru
        (kernelSubobject (u ≫ v)).arrow ?_)
      ?_
    · exact
        (pullback_factors_iff u (kernelSubobject v) (kernelSubobject (u ≫ v)).arrow).2 <| by
          rw [kernelSubobject_factors_iff, Category.assoc]
          exact kernelSubobject_arrow_comp (u ≫ v)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback u (kernelSubobject v)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 12.19.10: pulling back the zero subobject along a morphism recovers its
kernel subobject. -/
private theorem pullback_bot_eq_kernel {X Y : 𝒜} (u : X ⟶ Y) :
    (Subobject.pullback u).obj (⊥ : Subobject Y) = kernelSubobject u := by
  -- Proof comment: the pullback of `⊥` consists exactly of those points whose image vanishes.
  apply le_antisymm
  · exact le_kernelSubobject _ _ <| by
      simpa using (Subobject.isPullback u (⊥ : Subobject Y)).w.symm
  · have hFactors :
        ((Subobject.pullback u).obj (⊥ : Subobject Y)).Factors (kernelSubobject u).arrow :=
      (pullback_factors_iff u (⊥ : Subobject Y) (kernelSubobject u).arrow).2 <| by
        rw [Subobject.bot_factors_iff_zero]
        exact kernelSubobject_arrow_comp u
    exact Subobject.le_of_comm
      (((Subobject.pullback u).obj (⊥ : Subobject Y)).factorThru
        (kernelSubobject u).arrow hFactors)
      (((Subobject.pullback u).obj (⊥ : Subobject Y)).factorThru_arrow
        (kernelSubobject u).arrow hFactors)

/-- Helper for Lemma 12.19.10: strictness rewrites each pulled-back stage as the stage joined
with the kernel. -/
private theorem pullback_stage_eq_stage_sup_kernel_of_strict
    {X Y : FilteredObject 𝒜} (h : X ⟶ Y) (hh : Strict h) (i : ℤ) :
    (Subobject.pullback h.hom).obj (Y.filtration i) =
      X.filtration i ⊔ kernelSubobject h.hom := by
  -- Proof comment: pull back the stagewise strictness identity and simplify the image term to the
  -- usual source stage plus kernel preimage.
  have hi := congrArg ((Subobject.pullback h.hom).obj) ((strict_iff_quotient_eq_inf h).1 hh i)
  simpa [DecreasingFiltration.quotient, Subobject.inf_pullback, pullback_bot_eq_kernel] using hi

/-- Helper for Lemma 12.19.10: the ambient pushout map is the cokernel of `(f, -g)`, so its
kernel agrees with the image of that comparison map. -/
private theorem pushout_biprod_image_eq_kernel
    (f : A ⟶ B) (g : A ⟶ C) :
    imageSubobject (biprod.lift f.hom (-g.hom)) =
      kernelSubobject
        (biprod.desc (pushout.inl f.hom g.hom) (pushout.inr f.hom g.hom)) := by
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk
      (biprod.lift f.hom (-g.hom))
      (biprod.desc (pushout.inl f.hom g.hom) (pushout.inr f.hom g.hom))
      (by
        -- Proof comment: this is the defining pushout relation `f ≫ inl = g ≫ inr`.
        simp [biprod.lift_desc, Category.assoc, pushout.condition])
  have hCokernel :
      IsColimit
        (CokernelCofork.ofπ
          (biprod.desc (pushout.inl f.hom g.hom) (pushout.inr f.hom g.hom))
          (by
            -- Proof comment: reuse the same pushout relation in the cokernel-cofork package.
            simp [biprod.lift_desc, Category.assoc, pushout.condition])) := by
    simpa [S] using
      Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout f.hom g.hom
  have hExactEpi : S.Exact ∧ Epi S.g := by
    -- Proof comment: the canonical colimit package turns the ambient pushout map into a cokernel,
    -- hence into an exact short complex with epimorphic right map.
    exact (S.exact_and_epi_g_iff_g_is_cokernel).2 ⟨hCokernel⟩
  -- Proof comment: exactness identifies the image of `(f, -g)` with the kernel of the pushout map.
  simpa [S] using (ShortComplex.exact_iff_image_eq_kernel (S := S)).1 hExactEpi.1

/-- Helper for Lemma 12.19.10: the two obvious stage summands land in the pullback of the
canonical pushout stage along the right leg. -/
private theorem map_pullback_sup_le_pushout_inr_pullback_stage
    (f : A ⟶ B) (g : A ⟶ C) (p : ℤ) :
    (Subobject.map g.hom).obj ((Subobject.pullback f.hom).obj (B.filtration p)) ⊔ C.filtration p ≤
      (Subobject.pullback (pushout.inr f.hom g.hom)).obj ((pushout f g).filtration p) := by
  refine Subobject.sup_le ?_ ?_
  · rw [← Subobject.mk_arrow ((Subobject.pullback f.hom).obj (B.filtration p)), Subobject.map_mk]
    refine imageSubobject_le _ _ ?_
    have hpullback :
        (B.filtration p).Factors
          (((Subobject.pullback f.hom).obj (B.filtration p)).arrow ≫ f.hom) := by
      -- Proof comment: the pullback stage over `F^p B` maps into `F^p B` by definition.
      exact
        (pullback_factors_iff f.hom (B.filtration p)
          (((Subobject.pullback f.hom).obj (B.filtration p)).arrow)).1
          (Subobject.factors_self _)
    let u : (Subobject.pullback f.hom).obj (B.filtration p) ⟶ B.filtration p :=
      (B.filtration p).factorThru
        (((Subobject.pullback f.hom).obj (B.filtration p)).arrow ≫ f.hom) hpullback
    let v : (B.filtration p : 𝒜) ⟶ (pushout f g).filtration p :=
      ((pushout f g).filtration p).factorThru
        ((B.filtration p).arrow ≫ pushout.inl f.hom g.hom)
        ((pushout.inl f g).preserves p)
    have hFactors :
        ((Subobject.pullback (pushout.inr f.hom g.hom)).obj ((pushout f g).filtration p)).Factors
          (((Subobject.pullback f.hom).obj (B.filtration p)).arrow ≫ g.hom) := by
      rw [pullback_factors_iff]
      refine ⟨u ≫ v, ?_⟩
      calc
        u ≫ v ≫ ((pushout f g).filtration p).arrow
            = u ≫ (B.filtration p).arrow ≫ pushout.inl f.hom g.hom := by
                simp [v, Category.assoc]
        _ = ((Subobject.pullback f.hom).obj (B.filtration p)).arrow ≫
              f.hom ≫ pushout.inl f.hom g.hom := by
              simp [u, Category.assoc]
        _ = ((Subobject.pullback f.hom).obj (B.filtration p)).arrow ≫
              g.hom ≫ pushout.inr f.hom g.hom := by
              rw [Category.assoc, Category.assoc,
                show f.hom ≫ pushout.inl f.hom g.hom =
                    g.hom ≫ pushout.inr f.hom g.hom by
                  simpa using pushout.condition (f := f.hom) (g := g.hom)]
    exact Subobject.factorThru_arrow _ _ hFactors
  · -- Proof comment: the right stage generator already lands in the ambient pushout stage.
    refine Subobject.le_of_factors ?_
    exact
      (pullback_factors_iff (pushout.inr f.hom g.hom) ((pushout f g).filtration p)
        ((C.filtration p).arrow)).2
        ((pushout.inr f g).preserves p)

/-- Helper for Lemma 12.19.10: reverse inclusion in the pushout-stage preimage formula. -/
private theorem pushout_inr_pullback_stage_le_map_pullback_sup
    (f : A ⟶ B) (g : A ⟶ C) (p : ℤ) :
    (Subobject.pullback (pushout.inr f.hom g.hom)).obj ((pushout f g).filtration p) ≤
      (Subobject.map g.hom).obj ((Subobject.pullback f.hom).obj (B.filtration p)) ⊔
        C.filtration p := by
  -- Route correction: the source proof produces stage representatives only after passing to an
  -- epi cover, and the `(f,-g)`-image witness only becomes an honest `A`-map after a second epi
  -- cover. We therefore prove the inclusion on that double cover and then descend it by images.
  let P : Subobject A.obj := (Subobject.pullback f.hom).obj (B.filtration p)
  have hmap :
      (Subobject.map g.hom).obj P = imageSubobject (P.arrow ≫ g.hom) := by
    rw [← Subobject.mk_arrow P, Subobject.map_mk]
  rw [hmap]
  let T : Subobject C.obj :=
    (Subobject.pullback (pushout.inr f.hom g.hom)).obj ((pushout f g).filtration p)
  have hT :
      ((pushout f g).filtration p).Factors (T.arrow ≫ pushout.inr f.hom g.hom) := by
    exact
      (pullback_factors_iff (pushout.inr f.hom g.hom) ((pushout f g).filtration p) T.arrow).1
        (Subobject.factors_self T)
  let β : T ⟶ (pushout f g).filtration p :=
    ((pushout f g).filtration p).factorThru (T.arrow ≫ pushout.inr f.hom g.hom) hT
  let R : 𝒜 := pullback (factorThruImageSubobject (pushoutStageMap f g p)) β
  let r : R ⟶ ((B.filtration p : 𝒜) ⊞ (C.filtration p : 𝒜)) :=
    pullback.fst (factorThruImageSubobject (pushoutStageMap f g p)) β
  let πR : R ⟶ T := pullback.snd (factorThruImageSubobject (pushoutStageMap f g p)) β
  letI : Epi πR := by
    simpa [πR, R] using
      (Abelian.epi_snd_of_isLimit (factorThruImageSubobject (pushoutStageMap f g p)) β
        (IsPullback.of_hasPullback (factorThruImageSubobject (pushoutStageMap f g p)) β).isLimit)
  let uB : R ⟶ B.filtration p := r ≫ biprod.fst
  let uC : R ⟶ C.filtration p := r ≫ biprod.snd
  have hr :
      r = biprod.lift uB uC := by
    apply biprod.hom_ext'
    · simp [r, uB]
    · simp [r, uC]
  have hstage_cover :
      uB ≫ (B.filtration p).arrow ≫ pushout.inl f.hom g.hom +
          uC ≫ (C.filtration p).arrow ≫ pushout.inr f.hom g.hom =
        πR ≫ T.arrow ≫ pushout.inr f.hom g.hom := by
    have hcomp :
        r ≫ pushoutStageMap f g p = πR ≫ T.arrow ≫ pushout.inr f.hom g.hom := by
      calc
        r ≫ pushoutStageMap f g p
            =
              r ≫ factorThruImageSubobject (pushoutStageMap f g p) ≫
                ((pushout f g).filtration p).arrow := by
                  simp [pushoutStageMap, Category.assoc]
        _ = πR ≫ β ≫ ((pushout f g).filtration p).arrow := by
              rw [pullback.condition]
        _ = πR ≫ T.arrow ≫ pushout.inr f.hom g.hom := by
              simp [β, Category.assoc]
    calc
      uB ≫ (B.filtration p).arrow ≫ pushout.inl f.hom g.hom +
          uC ≫ (C.filtration p).arrow ≫ pushout.inr f.hom g.hom
          = biprod.lift uB uC ≫ pushoutStageMap f g p := by
              simp [pushoutStageMap, Category.assoc, biprod.lift_desc]
      _ = r ≫ pushoutStageMap f g p := by rw [hr]
      _ = πR ≫ T.arrow ≫ pushout.inr f.hom g.hom := hcomp
  let d : R ⟶ B.obj ⊞ C.obj :=
    biprod.lift
      (uB ≫ (B.filtration p).arrow)
      (uC ≫ (C.filtration p).arrow - πR ≫ T.arrow)
  have hd_zero :
      d ≫ biprod.desc (pushout.inl f.hom g.hom) (pushout.inr f.hom g.hom) = 0 := by
    have hsub :
        uB ≫ (B.filtration p).arrow ≫ pushout.inl f.hom g.hom +
            uC ≫ (C.filtration p).arrow ≫ pushout.inr f.hom g.hom -
              πR ≫ T.arrow ≫ pushout.inr f.hom g.hom =
          0 := by
      exact sub_eq_zero.mpr hstage_cover
    simpa [d, Category.assoc, biprod.lift_desc, Preadditive.sub_comp] using hsub
  have hd_kernel :
      (kernelSubobject
          (biprod.desc (pushout.inl f.hom g.hom) (pushout.inr f.hom g.hom))).Factors d := by
    rw [kernelSubobject_factors_iff, Category.assoc]
    exact hd_zero
  let δ : R ⟶ imageSubobject (biprod.lift f.hom (-g.hom)) :=
    (imageSubobject (biprod.lift f.hom (-g.hom))).factorThru d <| by
      rw [← pushout_biprod_image_eq_kernel f g]
      exact hd_kernel
  let S : 𝒜 := pullback (factorThruImageSubobject (biprod.lift f.hom (-g.hom))) δ
  let a : S ⟶ A.obj := pullback.fst (factorThruImageSubobject (biprod.lift f.hom (-g.hom))) δ
  let σ : S ⟶ R := pullback.snd (factorThruImageSubobject (biprod.lift f.hom (-g.hom))) δ
  letI : Epi σ := by
    simpa [σ, S] using
      (Abelian.epi_snd_of_isLimit (factorThruImageSubobject (biprod.lift f.hom (-g.hom))) δ
        (IsPullback.of_hasPullback (factorThruImageSubobject (biprod.lift f.hom (-g.hom))) δ).isLimit)
  have hsecond_cover :
      a ≫ biprod.lift f.hom (-g.hom) = σ ≫ d := by
    calc
      a ≫ biprod.lift f.hom (-g.hom)
          =
            a ≫ factorThruImageSubobject (biprod.lift f.hom (-g.hom)) ≫
              (imageSubobject (biprod.lift f.hom (-g.hom))).arrow := by
                simp [Category.assoc]
      _ = σ ≫ δ ≫ (imageSubobject (biprod.lift f.hom (-g.hom))).arrow := by
            rw [pullback.condition]
      _ = σ ≫ d := by
            simp [δ, Category.assoc]
  have hf_component :
      a ≫ f.hom = σ ≫ uB ≫ (B.filtration p).arrow := by
    calc
      a ≫ f.hom = a ≫ biprod.lift f.hom (-g.hom) ≫ biprod.fst := by
        simp [Category.assoc]
      _ = σ ≫ d ≫ biprod.fst := by rw [hsecond_cover]
      _ = σ ≫ uB ≫ (B.filtration p).arrow := by
        simp [d, Category.assoc]
  have hg_difference :
      a ≫ (-g.hom) = σ ≫ (uC ≫ (C.filtration p).arrow - πR ≫ T.arrow) := by
    calc
      a ≫ (-g.hom) = a ≫ biprod.lift f.hom (-g.hom) ≫ biprod.snd := by
        simp [Category.assoc]
      _ = σ ≫ d ≫ biprod.snd := by rw [hsecond_cover]
      _ = σ ≫ (uC ≫ (C.filtration p).arrow - πR ≫ T.arrow) := by
        simp [d, Category.assoc, Preadditive.comp_sub]
  have hpullback_factor :
      (B.filtration p).Factors (a ≫ f.hom) := by
    refine ⟨σ ≫ uB, ?_⟩
    simpa [Category.assoc] using hf_component.symm
  let aP : S ⟶ P := P.factorThru (a ≫ f.hom) hpullback_factor
  have hmap_factor :
      (imageSubobject (P.arrow ≫ g.hom)).Factors (a ≫ g.hom) := by
    refine ⟨aP ≫ factorThruImageSubobject (P.arrow ≫ g.hom), ?_⟩
    simp [aP, Category.assoc]
  have hsum_cover :
      a ≫ g.hom + σ ≫ uC ≫ (C.filtration p).arrow = σ ≫ πR ≫ T.arrow := by
    have hneg :
        σ ≫ uC ≫ (C.filtration p).arrow - σ ≫ πR ≫ T.arrow = -(a ≫ g.hom) := by
      simpa [Category.assoc, Preadditive.comp_neg, Preadditive.comp_sub] using
        hg_difference.symm
    apply sub_eq_zero.mp
    calc
      (a ≫ g.hom + σ ≫ uC ≫ (C.filtration p).arrow) - σ ≫ πR ≫ T.arrow
          = a ≫ g.hom + (σ ≫ uC ≫ (C.filtration p).arrow - σ ≫ πR ≫ T.arrow) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = a ≫ g.hom + -(a ≫ g.hom) := by rw [hneg]
      _ = 0 := by simp
  let U : Subobject C.obj := imageSubobject (P.arrow ≫ g.hom) ⊔ C.filtration p
  let ι₁ : imageSubobject (P.arrow ≫ g.hom) ⟶ U := Subobject.ofLE _ _ le_sup_left
  let ι₂ : C.filtration p ⟶ U := Subobject.ofLE _ _ le_sup_right
  have hU :
      U.Factors (σ ≫ πR ≫ T.arrow) := by
    refine
      ⟨aP ≫ factorThruImageSubobject (P.arrow ≫ g.hom) ≫ ι₁ + σ ≫ uC ≫ ι₂, ?_⟩
    calc
      (aP ≫ factorThruImageSubobject (P.arrow ≫ g.hom) ≫ ι₁ + σ ≫ uC ≫ ι₂) ≫ U.arrow
          =
            aP ≫ factorThruImageSubobject (P.arrow ≫ g.hom) ≫ ι₁ ≫ U.arrow +
              σ ≫ uC ≫ ι₂ ≫ U.arrow := by
                simp [Category.assoc, Preadditive.add_comp]
      _ = a ≫ g.hom + σ ≫ uC ≫ (C.filtration p).arrow := by
            simp [aP, ι₁, ι₂, Category.assoc, Subobject.ofLE_arrow]
      _ = σ ≫ πR ≫ T.arrow := hsum_cover
  have himage_cover :
      imageSubobject (σ ≫ πR ≫ T.arrow) ≤ U := by
    exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ hU)
  have hdescend :
      T = imageSubobject (σ ≫ πR ≫ T.arrow) := by
    calc
      T = imageSubobject T.arrow := by
            symm
            simpa using (Limits.imageSubobject_mono T.arrow)
      _ = imageSubobject ((σ ≫ πR) ≫ T.arrow) := by
            symm
            simpa [Category.assoc] using imageSubobject_comp_eq_of_epi (σ ≫ πR) T.arrow
  rw [hdescend]
  exact himage_cover

/-- Helper for Lemma 12.19.10: on the canonical ambient pushout, the pulled-back stage along the
right leg is the sum of the pushed-forward left preimage stage and the ambient stage of `C`. -/
private theorem pushout_inr_pullback_stage_eq_map_pullback_sup
    (f : A ⟶ B) (g : A ⟶ C) (p : ℤ) :
    (Subobject.pullback (pushout.inr f.hom g.hom)).obj ((pushout f g).filtration p) =
      (Subobject.map g.hom).obj ((Subobject.pullback f.hom).obj (B.filtration p)) ⊔
        C.filtration p := by
  -- Proof comment: the source formula is the conjunction of the easy stage-generator inclusion
  -- and the reverse inclusion obtained from the ambient cokernel relation `(f, -g)`.
  exact le_antisymm
    (pushout_inr_pullback_stage_le_map_pullback_sup f g p)
    (map_pullback_sup_le_pushout_inr_pullback_stage f g p)

/-- Helper for Lemma 12.19.10: an epimorphism is strict once every pulled-back stage is the
source stage joined with the kernel. -/
private theorem strict_of_pullback_stage_eq_stage_sup_kernel_of_epi
    {X Y : FilteredObject 𝒜} (h : X ⟶ Y) [Epi h.hom]
    (hh :
      ∀ i : ℤ,
        (Subobject.pullback h.hom).obj (Y.filtration i) =
          X.filtration i ⊔ kernelSubobject h.hom) :
    Strict h := by
  have hkernel :
      (Subobject.exists h.hom).obj (kernelSubobject h.hom) = (⊥ : Subobject Y.obj) := by
    -- Proof comment: the kernel arrow composes to zero, so its pushed-forward image is `⊥`.
    rw [exists_obj_eq_imageSubobject_comp, kernelSubobject_arrow_comp, Limits.imageSubobject_zero]
  refine (strict_iff_quotient_filtration_of_epi h).2 ?_
  refine OrderHom.ext _ _ ?_
  funext i
  -- Proof comment: push the pulled-back stage identity forward along the epi and simplify the
  -- kernel summand to `⊥`.
  calc
    Y.filtration i
        = (Subobject.exists h.hom).obj ((Subobject.pullback h.hom).obj (Y.filtration i)) := by
            symm
            exact exists_pullback_eq_of_epi h.hom (Y.filtration i)
    _ = (Subobject.exists h.hom).obj (X.filtration i ⊔ kernelSubobject h.hom) := by
          rw [hh i]
    _ = (Subobject.exists h.hom).obj (X.filtration i) ⊔
          (Subobject.exists h.hom).obj (kernelSubobject h.hom) := by
          rw [Subobject.exists_sup]
    _ = X.filtration.quotient h.hom i ⊔ (⊥ : Subobject Y.obj) := by
          rw [hkernel]
    _ = X.filtration.quotient h.hom i := by
          simp

/-- In a pushout square of filtered objects, strictness of the left map forces strictness of the
right map. -/
theorem strict_inr_of_isPushout_of_strict
    {P : FilteredObject 𝒜} {g' : B ⟶ P} {f' : C ⟶ P}
    (sq : IsPushout f g g' f') (hf : Strict f) :
    Strict f' := by
  -- Route correction: reduce to the canonical stagewise-image pushout model, prove strictness for
  -- its right leg by the source image formula, and then transport that strictness across
  -- `sq.isoPushout`.
  let e : P ≅ pushout f g := sq.isoPushout
  have hcanonical : Strict (pushout.inr f g : C ⟶ pushout f g) := by
    let I : FilteredObject 𝒜 :=
      (pushout f g).subobjectFilteredObject (imageSubobject (pushout.inr f.hom g.hom))
    let q : C ⟶ I := filteredImageFactor (pushout.inr f g)
    have hq_comp :
        q ≫ (pushout f g).subobjectInclusion (imageSubobject (pushout.inr f.hom g.hom)) =
          (pushout.inr f g : C ⟶ pushout f g) := by
      -- Proof comment: the canonical right leg is the image factor followed by the image
      -- inclusion in the ambient pushout.
      simpa [I, q] using
        filteredImageFactor_comp_subobjectInclusion (pushout.inr f g : C ⟶ pushout f g)
    have himage_inclusion :
        Strict ((pushout f g).subobjectInclusion
          (imageSubobject (pushout.inr f.hom g.hom))) := by
      -- Proof comment: the image inclusion is strict because it carries the induced filtration.
      exact strict_subobjectInclusion (pushout f g)
        (imageSubobject (pushout.inr f.hom g.hom))
    have hq : Strict q := by
      have hq_stage :
          ∀ p : ℤ,
            (Subobject.pullback q.hom).obj (I.filtration p) =
              C.filtration p ⊔ kernelSubobject q.hom := by
        intro p
        have htransport :
            (Subobject.pullback q.hom).obj (I.filtration p) =
              (Subobject.pullback (pushout.inr f.hom g.hom)).obj ((pushout f g).filtration p) := by
          -- Proof comment: normalize the filtration on the image factor back to the ambient
          -- pushout filtration along the defining image-factor factorization.
          simpa [I, q] using
            pullback_stage_of_filtered_image_factor (pushout.inr f g : C ⟶ pushout f g) p
        have hf_stage :
            (Subobject.pullback f.hom).obj (B.filtration p) =
              A.filtration p ⊔ kernelSubobject f.hom := by
          -- Proof comment: strictness of `f` rewrites the pulled-back stage into the source stage
          -- plus the kernel contribution.
          exact pullback_stage_eq_stage_sup_kernel_of_strict f hf p
        have hmap_stage :
            (Subobject.map g.hom).obj (A.filtration p) ≤ C.filtration p := by
          -- Proof comment: the `A`-stage already lands in the `C`-stage because `g` preserves the
          -- filtration.
          exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ (g.preserves p))
        have hmap_kernel :
            (Subobject.map g.hom).obj (kernelSubobject f.hom) ≤ kernelSubobject q.hom := by
          -- Proof comment: a point coming from `ker(f)` maps to zero in the pushout, hence also
          -- in the epi image factor `q`.
          let inc :
              I ⟶ pushout f g :=
            (pushout f g).subobjectInclusion (imageSubobject (pushout.inr f.hom g.hom))
          have hzero_comp :
              (kernelSubobject f.hom).arrow ≫ g.hom ≫ q.hom ≫ inc.hom = 0 := by
            calc
              (kernelSubobject f.hom).arrow ≫ g.hom ≫ q.hom ≫ inc.hom
                  = (kernelSubobject f.hom).arrow ≫ g.hom ≫ pushout.inr f.hom g.hom := by
                      simpa [inc, q, Category.assoc] using
                        congrArg FilteredObject.Hom.hom hq_comp
              _ = (kernelSubobject f.hom).arrow ≫ f.hom ≫ pushout.inl f.hom g.hom := by
                    rw [Category.assoc, Category.assoc,
                      show g.hom ≫ pushout.inr f.hom g.hom =
                          f.hom ≫ pushout.inl f.hom g.hom by
                        simpa using (pushout.condition (f := f.hom) (g := g.hom)).symm]
              _ = 0 := by
                    simp [Category.assoc, kernelSubobject_arrow_comp]
          have hzero :
              (kernelSubobject f.hom).arrow ≫ g.hom ≫ q.hom = 0 := by
            apply cancel_mono inc.hom
            simpa [Category.assoc] using hzero_comp
          have hFactors :
              (kernelSubobject q.hom).Factors ((kernelSubobject f.hom).arrow ≫ g.hom) := by
            rw [kernelSubobject_factors_iff, Category.assoc]
            exact hzero
          have hle_image :
              imageSubobject ((kernelSubobject f.hom).arrow ≫ g.hom) ≤ kernelSubobject q.hom := by
            exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ hFactors)
          calc
            (Subobject.map g.hom).obj (kernelSubobject f.hom)
                = imageSubobject ((kernelSubobject f.hom).arrow ≫ g.hom) := by
                    rw [← Subobject.mk_arrow (kernelSubobject f.hom), Subobject.map_mk]
            _ ≤ kernelSubobject q.hom := hle_image
        have hkernel_in_pullback :
            kernelSubobject q.hom ≤ (Subobject.pullback q.hom).obj (I.filtration p) := by
          -- Proof comment: the kernel is the pullback of the zero subobject, and `⊥` is contained
          -- in every filtration stage.
          rw [← pullback_bot_eq_kernel q.hom]
          exact (Subobject.pullback q.hom).monotone bot_le
        rw [htransport, pushout_inr_pullback_stage_eq_map_pullback_sup f g p, hf_stage,
          Subobject.map_sup]
        refine le_antisymm ?_ ?_
        · rw [sup_assoc]
          refine sup_le (le_sup_of_le_left hmap_stage) ?_
          refine sup_le ?_ le_sup_left
          exact le_sup_of_le_right hmap_kernel
        · refine sup_le ?_ ?_
          · exact le_sup_right
          · simpa [htransport, pushout_inr_pullback_stage_eq_map_pullback_sup f g p, hf_stage,
              Subobject.map_sup] using hkernel_in_pullback
      -- Proof comment: once the source preimage formula is known stagewise for the epi image
      -- factor, the epi-side strictness criterion closes `q`.
      exact strict_of_pullback_stage_eq_stage_sup_kernel_of_epi q hq_stage
    -- Proof comment: compose the strict epi image factor with the strict image inclusion.
    simpa [hq_comp] using
      strict_comp_of_mono q
        ((pushout f g).subobjectInclusion (imageSubobject (pushout.inr f.hom g.hom)))
        hq himage_inclusion
  have htransport :
      Strict ((pushout.inr f g : C ⟶ pushout f g) ≫ e.symm.hom) := by
    simpa using strict_postcompose_iso
      (h := (pushout.inr f g : C ⟶ pushout f g)) (e := e.symm) hcanonical
  -- The universal pushout comparison identifies the transported canonical leg with `f'`.
  simpa [e] using (show Strict ((pushout.inr f g : C ⟶ pushout f g) ≫ e.inv) from htransport)

/-- In the canonical pushout square of filtered objects, strictness of the left map forces
strictness of the induced map on the right. -/
theorem strict_pushout_inr_of_strict (f : A ⟶ B) (g : A ⟶ C) (hf : Strict f) :
    Strict (pushout.inr f g : C ⟶ pushout f g) := by
  exact strict_inr_of_isPushout_of_strict (IsPushout.of_hasPushout f g) hf

end FilteredObject.Hom

-- Proof sketch: first realize the filtered pushout by endowing the ambient pushout of `f.hom` and
-- `g.hom` with the stagewise image filtration coming from `F^p B ⊕ F^p C`; this yields the
-- canonical `HasPushout f g` instance. The strictness statement is proved first for an arbitrary
-- pushout square via `strict_inr_of_isPushout_of_strict`, then specialized to `pushout.inr f g`.
/-- Lemma 12.19.10: for morphisms `f : A ⟶ B` and `g : A ⟶ C` of filtered objects in an abelian
category, there exists a pushout square in the filtered category, and if `f` is strict, then the
induced morphism `f' : C ⟶ C ⨿_A B` is strict. -/
@[stacks 05SM]
theorem exists_filtered_pushout_preserving_strictness
    {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : A ⟶ C) :
    ∃ (P : FilteredObject 𝒜) (g' : B ⟶ P) (f' : C ⟶ P),
      IsPushout f g g' f' ∧ (Strict f → Strict f') := by
  refine ⟨pushout f g, pushout.inl f g, pushout.inr f g, IsPushout.of_hasPushout f g, ?_⟩
  exact strict_pushout_inr_of_strict f g

end CategoryTheory
