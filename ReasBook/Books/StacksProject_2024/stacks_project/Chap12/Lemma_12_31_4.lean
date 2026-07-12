import Mathlib
import StacksProject_2024.Chap10.Lemma_10_86_4
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap12.Definition_12_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open Opposite
open OrderDual (ofDual toDual)

noncomputable section

universe u

namespace CategoryTheory

namespace SequentialInverseSystem

/-- Helper for Lemma 12.31.4: the ambient category of sequential inverse systems of small abelian
groups. -/
private abbrev AbSeq := SequentialInverseSystem AddCommGrpCat.{0}

/-- Helper for Lemma 12.31.4: evaluating a short exact sequence of sequential inverse systems at a
stage gives a short exact sequence of abelian groups. -/
private lemma shortExact_eval {S : ShortComplex AbSeq} {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n))).ShortExact := by
  let ev := (evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)
  have hExactMono : (S.map ev).Exact ∧ Mono (S.map ev).f := by
    -- Evaluation preserves kernels, so left exactness descends immediately to the stagewise row.
    simpa using
      (S.map ev).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  -- Epimorphy of the right map is also checked componentwise.
  exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

/-- Helper for Lemma 12.31.4: in abelian groups, composing on the left with an epimorphism does
not change the image subobject. -/
private lemma imageSubobject_comp_eq_of_epi_left
    {X Y Z : AddCommGrpCat} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g := by
  let h := imageSubobject_comp_le f g
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    -- The comparison map out of the composite image is epi because the left factor is epi.
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  -- An isomorphism of subobjects gives the required equality of image subobjects.
  exact Subobject.eq_of_comm (asIso φ) (by simp [φ])

/-- Helper for Lemma 12.31.4: the concrete range inclusion in `AddCommGrpCat` is a monomorphism.
-/
private instance rangeSubtype_mono {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    Mono (AddCommGrpCat.ofHom f.hom.range.subtype) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Helper for Lemma 12.31.4: the chosen representative of `imageSubobject f` maps to the
concrete range subgroup of `f`. -/
private theorem imageSubobject_to_range_arrow {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    ((imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom) ≫
      AddCommGrpCat.ofHom f.hom.range.subtype = (imageSubobject f).arrow := by
  -- First rewrite the concrete range comparison through the categorical image object.
  rw [Category.assoc]
  change (imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom ≫
      AddCommGrpCat.image.ι f = (imageSubobject f).arrow
  -- Then identify the iso to the concrete range with the universal image comparison map.
  rw [show (AddCommGrpCat.imageIsoRange f).hom ≫ AddCommGrpCat.image.ι f = image.ι f by
    simpa [AddCommGrpCat.imageIsoRange] using
      (IsImage.isoExt_hom_m (hF := Image.isImage f) (hF' := AddCommGrpCat.isImage f))]
  simp

/-- Helper for Lemma 12.31.4: inclusion of image subobjects implies inclusion of the underlying
set-theoretic ranges. -/
private theorem range_subset_of_imageSubobject_le
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f ≤ imageSubobject g) : Set.range f.hom ⊆ Set.range g.hom := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  let φ : X₁ ⟶ AddCommGrpCat.of g.hom.range :=
    factorThruImageSubobject f ≫ Subobject.ofLE _ _ h ≫
      (imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom
  have hφmor : φ ≫ AddCommGrpCat.ofHom g.hom.range.subtype = f := by
    -- Compare the factorization through `imageSubobject g` with the original map `f`.
    dsimp [φ]
    calc
      factorThruImageSubobject f ≫
          Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
            (imageSubobjectIso g).hom ≫
              (AddCommGrpCat.imageIsoRange g).hom ≫
                AddCommGrpCat.ofHom g.hom.range.subtype
          = factorThruImageSubobject f ≫
              Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
                (((imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom) ≫
                  AddCommGrpCat.ofHom g.hom.range.subtype) := by
              simp [Category.assoc]
      _ = factorThruImageSubobject f ≫
            Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
              (imageSubobject g).arrow := by
            rw [imageSubobject_to_range_arrow]
      _ = factorThruImageSubobject f ≫ (imageSubobject f).arrow := by
            rw [Subobject.ofLE_arrow]
      _ = f := by
            rw [imageSubobject_arrow_comp]
  -- Finally, read off an explicit preimage of `y` from the concrete range subgroup.
  refine ⟨(φ.hom x).2.choose, ?_⟩
  have hφ := congrArg (fun u ↦ u.hom x) hφmor
  exact ((φ.hom x).2.choose_spec).trans hφ

/-- Helper for Lemma 12.31.4: reindexing a short exact row along the `OrderDual ℕ`/`ℕᵒᵖ`
comparison preserves short exactness. -/
private lemma orderDual_shortExact_of_shortExact {S : ShortComplex AbSeq}
    (hS : S.ShortExact) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    (S.map W).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  -- Reindexing along the equivalence only precomposes the row, so exactness and mono/epi are
  -- preserved objectwise.
  simpa [W] using hS.map_of_exact W

/-- Helper for Lemma 12.31.4: the source-facing sequential Mittag-Leffler condition gives the
owner `Type`-valued condition after reindexing from `ℕᵒᵖ` to `OrderDual ℕ`. -/
private lemma orderDual_owner_isMittagLeffler_of_source_isMittagLeffler
    (F : AbSeq) (hF : F.IsMittagLeffler) :
    (((CategoryTheory.orderDualEquivalence ℕ).functor ⋙ F) ⋙ forget AddCommGrpCat).IsMittagLeffler := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  refine (Functor.isMittagLeffler_iff_subset_range_comp (((e.functor ⋙ F) ⋙ forget AddCommGrpCat))).2 ?_
  intro i
  obtain ⟨c, hic, hstable⟩ := hF (ofDual i)
  refine ⟨toDual c, ?_, ?_⟩
  · -- The witness map is the chosen stabilized transition morphism `F_c ⟶ F_i`.
    simpa using (homOfLE hic : toDual c ⟶ toDual (ofDual i))
  · intro k g
    have hcg : c ≤ ofDual k := leOfHom g
    have hg : g = (homOfLE hcg : k ⟶ toDual c) := Subsingleton.elim _ _
    let f' : F.obj (op c) ⟶ F.obj (op (ofDual i)) := F.transitionMap hic
    let g' : F.obj (op (ofDual k)) ⟶ F.obj (op (ofDual i)) := F.transitionMap (hic.trans hcg)
    have himage : imageSubobject f' ≤ imageSubobject g' := by
      simpa [f', g'] using (hstable hcg).symm.le
    have hsubset : Set.range f'.hom ⊆ Set.range g'.hom := by
      exact
        @range_subset_of_imageSubobject_le
          (F.obj (op c)) (F.obj (op (ofDual k))) (F.obj (op (ofDual i)))
          f' g' himage
    -- Replace stabilized image equality by inclusion of the underlying set-theoretic ranges.
    simpa [e, hg, SequentialInverseSystem.transitionMap] using
      hsubset

/-- Helper for Lemma 12.31.4: the first square in the reindexed inverse-limit comparison commutes.
-/
private lemma orderDual_limit_map_shortComplex_iso_comm₁₂ (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    i₁.hom ≫ limMap S.f = limMap (e.functor.whiskerLeft S.f) ≫ i₂.hom := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  apply limit.hom_ext
  intro k
  simp_rw [Category.assoc]
  have hleft :
      i₁.hom ≫ limit.π S.X₁ k ≫ S.f.app k =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₁)).inv.app (e.inverse.obj k) ≫
            S.X₁.map (e.counit.app k) ≫ S.f.app k := by
    simpa only [Category.assoc] using
      congrArg (fun φ => φ ≫ S.f.app k)
        (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ S.X₁)) k)
  have hright :
      limMap (e.functor.whiskerLeft S.f) ≫
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.f).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    simpa only [Category.assoc] using
      congrArg
        (fun φ =>
          φ ≫ (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k))
        (Limits.limMap_π (e.functor.whiskerLeft S.f) (e.inverse.obj k))
  have hmiddle :
      limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₁)).inv.app (e.inverse.obj k) ≫
            S.X₁.map (e.counit.app k) ≫ S.f.app k =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.f).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
      congrArg
        (fun φ =>
          limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫ φ)
        (S.f.naturality (e.counit.app k))
  have hfinal :
      i₁.hom ≫ limit.π S.X₁ k ≫ S.f.app k =
        limMap (e.functor.whiskerLeft S.f) ≫
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    exact hleft.trans (hmiddle.trans hright.symm)
  simpa [e, CategoryTheory.orderDualEquivalence, Category.assoc] using hfinal

/-- Helper for Lemma 12.31.4: the second square in the reindexed inverse-limit comparison
commutes. -/
private lemma orderDual_limit_map_shortComplex_iso_comm₂₃ (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    i₂.hom ≫ limMap S.g = limMap (e.functor.whiskerLeft S.g) ≫ i₃.hom := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  apply limit.hom_ext
  intro k
  simp_rw [Category.assoc]
  have hleft :
      i₂.hom ≫ limit.π S.X₂ k ≫ S.g.app k =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k) ≫ S.g.app k := by
    simpa only [Category.assoc] using
      congrArg (fun φ => φ ≫ S.g.app k)
        (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ S.X₂)) k)
  have hright :
      limMap (e.functor.whiskerLeft S.g) ≫
          limit.π (e.functor ⋙ S.X₃) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.g).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    simpa only [Category.assoc] using
      congrArg
        (fun φ =>
          φ ≫ (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
            S.X₃.map (e.counit.app k))
        (Limits.limMap_π (e.functor.whiskerLeft S.g) (e.inverse.obj k))
  have hmiddle :
      limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k) ≫ S.g.app k =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.g).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
      congrArg
        (fun φ =>
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫ φ)
        (S.g.naturality (e.counit.app k))
  have hfinal :
      i₂.hom ≫ limit.π S.X₂ k ≫ S.g.app k =
        limMap (e.functor.whiskerLeft S.g) ≫
          limit.π (e.functor ⋙ S.X₃) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    exact hleft.trans (hmiddle.trans hright.symm)
  simpa [e, CategoryTheory.orderDualEquivalence, Category.assoc] using hfinal

/-- Helper for Lemma 12.31.4: after applying `lim`, the reindexed short complex is canonically
isomorphic to the original one. -/
private noncomputable def orderDual_limit_map_shortComplex_iso (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    ((S.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)) ≅
      S.map (lim : (ℕᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat) :=
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  -- Package the three objectwise limit comparisons into a short-complex isomorphism.
  ShortComplex.isoMk i₁ i₂ i₃
    (orderDual_limit_map_shortComplex_iso_comm₁₂ S)
    (orderDual_limit_map_shortComplex_iso_comm₂₃ S)

/-- Helper for Lemma 12.31.4: if the middle term of a short exact sequence of sequential inverse
systems of abelian groups is Mittag-Leffler, then the quotient inverse system is also
Mittag-Leffler. -/
private theorem isMittagLeffler_right_of_shortExact {S : ShortComplex AbSeq}
    (hS : S.ShortExact)
    (hML : S.X₂.IsMittagLeffler) :
    S.X₃.IsMittagLeffler := by
  intro i
  obtain ⟨c, hic, hstable⟩ := hML i
  refine ⟨c, hic, ?_⟩
  intro k hck
  have hnat_k :
      S.X₂.transitionMap (hic.trans hck) ≫ S.g.app (op i) =
        S.g.app (op k) ≫ S.X₃.transitionMap (hic.trans hck) := by
    -- Rewrite the transition map through naturality of the right morphism in the short complex.
    simpa [transitionMap] using S.g.naturality ((homOfLE (hic.trans hck)).op)
  have hnat_c :
      S.X₂.transitionMap hic ≫ S.g.app (op i) =
        S.g.app (op c) ≫ S.X₃.transitionMap hic := by
    -- The same naturality identity at the stabilizing stage `c`.
    simpa [transitionMap] using S.g.naturality ((homOfLE hic).op)
  letI : Epi (S.g.app (op k)) := (shortExact_eval hS).epi_g
  letI : Epi (S.g.app (op c)) := (shortExact_eval hS).epi_g
  -- Transport stabilized images in the middle row across the stagewise quotient maps.
  calc
    imageSubobject (S.X₃.transitionMap (hic.trans hck))
        = imageSubobject (S.g.app (op k) ≫ S.X₃.transitionMap (hic.trans hck)) := by
            symm
            simpa using
              imageSubobject_comp_eq_of_epi_left
                (S.g.app (op k)) (S.X₃.transitionMap (hic.trans hck))
    _ = imageSubobject (S.X₂.transitionMap (hic.trans hck) ≫ S.g.app (op i)) := by
          rw [← hnat_k]
    _ = imageSubobject
          ((imageSubobject (S.X₂.transitionMap (hic.trans hck))).arrow ≫ S.g.app (op i)) := by
          rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction]
    _ = imageSubobject ((imageSubobject (S.X₂.transitionMap hic)).arrow ≫ S.g.app (op i)) := by
          rw [hstable hck]
    _ = imageSubobject (S.X₂.transitionMap hic ≫ S.g.app (op i)) := by
          rw [← Limits.imageSubobject_comp_eq_imageSubobject_restriction]
    _ = imageSubobject (S.g.app (op c) ≫ S.X₃.transitionMap hic) := by
          rw [hnat_c]
    _ = imageSubobject (S.X₃.transitionMap hic) := by
          simpa using
            imageSubobject_comp_eq_of_epi_left
              (S.g.app (op c)) (S.X₃.transitionMap hic)

/-- Helper for Lemma 12.31.4: if the left term of a short exact sequence of sequential inverse
systems of abelian groups is Mittag-Leffler, then the induced sequence on inverse limits is short
exact. -/
private theorem inverseLimit_shortExact_of_isMittagLeffler_left {S : ShortComplex AbSeq}
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler) :
    (S.map lim).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  let hReindexed :
      ((S.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)).ShortExact :=
    inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
      (S := S.map W)
      (orderDual_shortExact_of_shortExact hS)
      (orderDual_owner_isMittagLeffler_of_source_isMittagLeffler (F := S.X₁) hML)
  -- Transport the Chapter 10 short exactness statement back across the limit comparison isomorphism.
  exact ShortComplex.shortExact_of_iso
    (orderDual_limit_map_shortComplex_iso S)
    hReindexed

/- Domain-style sampling for Lemma 12.31.4 in the sequential inverse-system exactness domain:
- `source-facing`: a four-term exact sequence of sequential inverse systems and the induced exact
  tail sequence on inverse limits
- `core/canonical`: the finite exact-sequence owner `ComposableArrows.Exact` together with the
  chapter theorems `inverseLimit_shortExact_of_isMittagLeffler_left` and
  `inverseLimit_exact_and_mono_of_shortExact`
- `bridge/view`: the present theorem, which passes from an exact four-term composable-arrow object
  of towers to exactness of the tail sequence after applying inverse limit

Primitive data are the exact composable-arrow object `S : ComposableArrows AbSeq 3` and the
Mittag-Leffler condition on its leftmost term `S.left`. The tail inverse-limit sequence is
derived canonically as `δ₀ (S ⋙ lim)`, so the statement should use that owner-level
construction directly rather than reintroducing separate primitive morphism binders. -/

-- Proof sketch: let `Z_i = ker(C_i ⟶ D_i)` and `I_i = im(A_i ⟶ B_i)`. The short exact sequence
-- `0 ⟶ I_i ⟶ B_i ⟶ Z_i ⟶ 0` together with Lemma 12.31.3 yields surjectivity of
-- `\varprojlim B_i ⟶ \varprojlim Z_i`, and `\varprojlim Z_i` identifies with the kernel of
-- `\varprojlim C_i ⟶ \varprojlim D_i`.
/-- Helper for Lemma 12.31.4: the canonical factorization through an image subobject fits into a
short exact sequence. -/
lemma factor_thru_image_subobject_short_exact
    {X Y : AbSeq} (f : X ⟶ Y) :
    (ShortComplex.mk (kernel.ι (factorThruImageSubobject f))
      (factorThruImageSubobject f) (kernel.condition _)).ShortExact := by
  -- The canonical kernel-image row is exact, with mono kernel inclusion and epi image factor map.
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- Helper for Lemma 12.31.4: the image tower of the first map in an exact four-term row is
Mittag-Leffler when the leftmost tower is Mittag-Leffler. -/
lemma first_image_is_mittag_leffler
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact)
    (hML : S.left.IsMittagLeffler) :
    (imageSubobject (S.sc hS.toIsComplex 0).f : AbSeq).IsMittagLeffler := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let T : ShortComplex AbSeq :=
    ShortComplex.mk (kernel.ι (factorThruImageSubobject S₀.f))
      (factorThruImageSubobject S₀.f) (kernel.condition _)
  have hT : T.ShortExact := by
    -- Apply the generic image-factor short exact sequence to the first map in the row.
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  -- Mittag-Leffler passes across a short exact sequence with surjective right map.
  simpa [T, S₀] using isMittagLeffler_right_of_shortExact (S := T) hT hML

/-- Helper for Lemma 12.31.4: the composite
`image(A ⟶ B) ⟶ B ⟶ kernel(C ⟶ D)` vanishes. -/
lemma middle_to_tail_kernel_comp_zero
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact) :
    let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
    let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
    (imageSubobject S₀.f).arrow ≫ factorThruKernelSubobject S₁.g S₁.f S₁.zero = 0 := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have hzero_image : (imageSubobject S₀.f).arrow ≫ S₁.f = 0 := by
    -- Exactness at `B` says the image of `A ⟶ B` lands in the kernel of `B ⟶ C`.
    apply (cancel_epi (factorThruImageSubobject S₀.f)).1
    simpa [S₀, S₁] using S₀.zero
  -- The lift to the kernel object has the same composite into `C`.
  apply (cancel_mono (kernelSubobject S₁.g).arrow).1
  rw [Category.assoc, factorThruKernelSubobject_comp_arrow, zero_comp]
  simpa [S₁] using hzero_image

/-- Helper for Lemma 12.31.4: the source-proof row
`image(A ⟶ B) ⟶ B ⟶ kernel(C ⟶ D)` is short exact. -/
lemma middle_to_tail_kernel_short_exact
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact) :
    let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
    let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
    (ShortComplex.mk (imageSubobject S₀.f).arrow
      (factorThruKernelSubobject S₁.g S₁.f S₁.zero)
      (middle_to_tail_kernel_comp_zero S hS)).ShortExact := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have hzero_image : (imageSubobject S₀.f).arrow ≫ S₁.f = 0 := by
    -- Exactness at `B` says the image of `A ⟶ B` lands in the kernel of `B ⟶ C`.
    apply (cancel_epi (factorThruImageSubobject S₀.f)).1
    simpa [S₀, S₁] using S₀.zero
  have hzero_kernel :
      (imageSubobject S₀.f).arrow ≫ factorThruKernelSubobject S₁.g S₁.f S₁.zero = 0 := by
    -- The lift to the kernel object has the same composite into `C`.
    apply (cancel_mono (kernelSubobject S₁.g).arrow).1
    rw [Category.assoc, factorThruKernelSubobject_comp_arrow, zero_comp]
    simpa using hzero_image
  let T : ShortComplex AbSeq :=
    ShortComplex.mk (imageSubobject S₀.f).arrow
      (factorThruKernelSubobject S₁.g S₁.f S₁.zero) hzero_kernel
  let U : ShortComplex AbSeq := ShortComplex.mk (imageSubobject S₀.f).arrow S₁.f hzero_image
  have hU : U.Exact := by
    -- Rewrite exactness of `A ⟶ B ⟶ C` as the image-kernel equality for the image inclusion.
    rw [ShortComplex.exact_iff_image_eq_kernel]
    rw [Limits.imageSubobject_mono]
    simpa [U, S₀, S₁] using
      (ShortComplex.exact_iff_image_eq_kernel (S := S₀)).1 (hS.exact 0)
  let hcomm₁₂ : (𝟙 _) ≫ U.f = T.f ≫ (𝟙 _) := by
    simp [T, U]
  let hcomm₂₃ : (𝟙 _) ≫ U.g = T.g ≫ (kernelSubobject S₁.g).arrow := by
    simp [T, U]
  let φ : T ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (kernelSubobject S₁.g).arrow
      comm₁₂ := hcomm₁₂
      comm₂₃ := hcomm₂₃ }
  have hTExact : T.Exact := by
    -- Transport exactness from `B ⟶ C` to `B ⟶ kernel(C ⟶ D)` through the mono kernel inclusion.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hU
  have hTepi : Epi T.g := by
    -- Exactness of `B ⟶ C ⟶ D` identifies `kernel(C ⟶ D)` with the image of `B ⟶ C`,
    -- so the canonical map `B ⟶ kernel(C ⟶ D)` is epi.
    have hImageToKernel : Epi (imageToKernel S₁.f S₁.g S₁.zero) := by
      exact (ShortComplex.exact_iff_epi_imageToKernel (S := S₁)).1 (hS.exact 1)
    letI : Epi (factorThruImageSubobject S₁.f ≫ imageToKernel S₁.f S₁.g S₁.zero) := by
      infer_instance
    have hfactor :
        factorThruImageSubobject S₁.f ≫ imageToKernel S₁.f S₁.g S₁.zero =
          factorThruKernelSubobject S₁.g S₁.f S₁.zero := by
      simpa using factorThruImageSubobject_comp_imageToKernel (f := S₁.f) (g := S₁.g) S₁.zero
    simpa [T, hfactor] using
      (inferInstance : Epi
        (factorThruImageSubobject S₁.f ≫ imageToKernel S₁.f S₁.g S₁.zero))
  -- Assemble the exactness, monomorphism, and epimorphism into the desired short exact row.
  simpa [T, S₀, S₁] using ShortComplex.ShortExact.mk' hTExact inferInstance hTepi

/-- Helper for Lemma 12.31.4: after passing to inverse limits, the image of the first tail map is
the kernel of the second tail map. -/
lemma inverse_limit_tail_kernel_image_eq_kernel
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact)
    (hML : S.left.IsMittagLeffler) :
    let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
    imageSubobject (lim.map S₁.f) = kernelSubobject (lim.map S₁.g) := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have hImageML : (imageSubobject S₀.f : AbSeq).IsMittagLeffler :=
    first_image_is_mittag_leffler S hS hML
  let hzero_middle :
      (imageSubobject S₀.f).arrow ≫ factorThruKernelSubobject S₁.g S₁.f S₁.zero = 0 := by
    simpa [S₀, S₁] using middle_to_tail_kernel_comp_zero S hS
  let T : ShortComplex AbSeq :=
    ShortComplex.mk (imageSubobject S₀.f).arrow
      (factorThruKernelSubobject S₁.g S₁.f S₁.zero) hzero_middle
  have hT : T.ShortExact := by
    -- This is the short exact row `0 ⟶ image(A ⟶ B) ⟶ B ⟶ kernel(C ⟶ D) ⟶ 0`.
    simpa [T, S₀, S₁] using middle_to_tail_kernel_short_exact S hS
  have hTlim : (T.map lim).ShortExact :=
    inverseLimit_shortExact_of_isMittagLeffler_left (S := T) hT hImageML
  let hzero_kernel : (kernelSubobject S₁.g).arrow ≫ S₁.g = 0 := kernelSubobject_arrow_comp S₁.g
  let K : ShortComplex AbSeq := ShortComplex.mk (kernelSubobject S₁.g).arrow S₁.g hzero_kernel
  let K' : ShortComplex AbSeq := ShortComplex.mk (kernel.ι S₁.g) S₁.g (kernel.condition _)
  have hK' : K'.Exact := by
    -- The kernel row is exact by the universal property of the kernel.
    simpa [K'] using (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S₁.g))
  let hkernel_comm₁₂ : (kernelSubobjectIso S₁.g).hom ≫ K'.f = K.f ≫ (𝟙 _) := by
    simp [K, K']
  let hkernel_comm₂₃ : (𝟙 _) ≫ K'.g = K.g ≫ (𝟙 _) := by
    simp [K, K']
  let ψ : K ⟶ K' :=
    { τ₁ := (kernelSubobjectIso S₁.g).hom
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := hkernel_comm₁₂
      comm₂₃ := hkernel_comm₂₃ }
  have hK : K.Exact := by
    -- Replace the chosen kernel object by the canonically equivalent kernel subobject object.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hK'
  have hKlim : (K.map lim).Exact := by
    -- Inverse limit preserves kernels, so the kernel row stays exact after applying `lim`.
    exact
      (show (K.map lim).Exact ∧ Mono (K.map lim).f from by
        simpa using
          (K.map lim).exact_and_mono_f_iff_f_is_kernel.2
            ⟨KernelFork.mapIsLimit _ hK.fIsKernel lim⟩).1
  have htail_fac : (T.map lim).g ≫ (K.map lim).f = lim.map S₁.f := by
    -- The tail map factors through the inverse limit of the kernel tower.
    calc
      (T.map lim).g ≫ (K.map lim).f
          = lim.map
              (factorThruKernelSubobject S₁.g S₁.f S₁.zero ≫ (kernelSubobject S₁.g).arrow) := by
                simpa [T, K] using
                  (Functor.map_comp lim
                    (factorThruKernelSubobject S₁.g S₁.f S₁.zero)
                    ((kernelSubobject S₁.g).arrow)).symm
      _ = lim.map S₁.f := by
            simp
  letI : Epi (T.map lim).g := hTlim.epi_g
  -- Surjectivity onto `lim Z` and left exactness on the kernel row identify the target kernel.
  have hkernel_eq : imageSubobject (lim.map S₁.f) = kernelSubobject ((K.map lim).g) := by
    calc
    imageSubobject (lim.map S₁.f)
        = imageSubobject ((T.map lim).g ≫ (K.map lim).f) := by
            rw [htail_fac]
            rfl
    _ = imageSubobject ((K.map lim).f) := by
          simpa using imageSubobject_comp_eq_of_epi_left ((T.map lim).g) ((K.map lim).f)
    _ = kernelSubobject ((K.map lim).g) := by
          simpa using (ShortComplex.exact_iff_image_eq_kernel (S := K.map lim)).1 hKlim
  simpa [K, S₁] using hkernel_eq

/-- Lemma 12.31.4: let `A ⟶ B ⟶ C ⟶ D` be an exact sequence of sequential inverse systems of
abelian groups. If `A` is Mittag-Leffler, then the induced sequence on inverse limits
`\varprojlim B ⟶ \varprojlim C ⟶ \varprojlim D` is exact. -/
theorem inverseLimit_exact_of_four_term_exact_of_isMittagLeffler_left
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact)
    (hML : S.left.IsMittagLeffler) :
    (δ₀ (S ⋙ lim)).Exact := by
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have himage_kernel : imageSubobject (lim.map S₁.f) = kernelSubobject (lim.map S₁.g) := by
    simpa [S₁] using inverse_limit_tail_kernel_image_eq_kernel S hS hML
  have hzero : (δ₀ (S ⋙ lim)).map' 0 1 ≫ (δ₀ (S ⋙ lim)).map' 1 2 = 0 := by
    -- The tail inverse-limit row is still a complex.
    simpa [S₁] using (S₁.map lim).zero
  have hExact : (S₁.map lim).Exact := by
    -- The source proof identifies the tail kernel with the inverse limit of the kernel tower `Z`.
    rw [ShortComplex.exact_iff_image_eq_kernel]
    simpa [S₁] using himage_kernel
  exact exact₂_mk (δ₀ (S ⋙ lim)) hzero hExact

end SequentialInverseSystem

end CategoryTheory
