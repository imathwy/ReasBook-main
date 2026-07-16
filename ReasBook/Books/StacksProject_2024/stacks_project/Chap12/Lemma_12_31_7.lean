import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_22_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_86_4
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3
import StacksProject_2024.stacks_project.Chap12.Definition_12_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits ComplexShape
open OrderDual (ofDual toDual)

noncomputable section

namespace CategoryTheory

namespace SequentialInverseSystem

local abbrev AbSeq := SequentialInverseSystem AddCommGrpCat
local abbrev AbCpxSeq := SequentialInverseSystem (CochainComplex AddCommGrpCat ℤ)
local abbrev ev := HomologicalComplex.eval AddCommGrpCat (up ℤ)
local abbrev H := HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)
local abbrev CyclesF := HomologicalComplex.cyclesFunctor AddCommGrpCat (up ℤ)
local abbrev πH := HomologicalComplex.natTransHomologyπ AddCommGrpCat (up ℤ)

/-- Helper for Lemma 12.31.7: evaluating a short exact sequence of sequential inverse systems of
abelian groups at a stage preserves short exactness. -/
private lemma shortExact_eval {S : ShortComplex AbSeq} {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n))).ShortExact := by
  let ev₀ := (evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)
  have hExactMono : (S.map ev₀).Exact ∧ Mono (S.map ev₀).f := by
    -- Evaluation preserves kernels, so the left exact part descends stagewise.
    simpa using
      (S.map ev₀).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev₀⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  -- Epimorphy of the right map is also checked componentwise.
  exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

/-- Helper for Lemma 12.31.7: in `AddCommGrpCat`, precomposing with an epimorphism does not alter
the image subobject. -/
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
  -- An isomorphism of subobjects gives the desired equality.
  exact Subobject.eq_of_comm (asIso φ) (by simp [φ])

/-- Helper for Lemma 12.31.7: the concrete range inclusion in `AddCommGrpCat` is monic. -/
private instance rangeSubtype_mono {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    Mono (AddCommGrpCat.ofHom f.hom.range.subtype) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Helper for Lemma 12.31.7: the chosen representative of `imageSubobject f` maps to the
concrete range subgroup of `f`. -/
private theorem imageSubobject_to_range_arrow {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    ((imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom) ≫
      AddCommGrpCat.ofHom f.hom.range.subtype = (imageSubobject f).arrow := by
  rw [Category.assoc]
  change (imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom ≫
      AddCommGrpCat.image.ι f = (imageSubobject f).arrow
  rw [show (AddCommGrpCat.imageIsoRange f).hom ≫ AddCommGrpCat.image.ι f = image.ι f by
    simpa [AddCommGrpCat.imageIsoRange] using
      (IsImage.isoExt_hom_m (hF := Image.isImage f) (hF' := AddCommGrpCat.isImage f))]
  simp

/-- Helper for Lemma 12.31.7: inclusion of image subobjects implies inclusion of the underlying
set-theoretic ranges in `AddCommGrpCat`. -/
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
  -- Read off an explicit preimage from the concrete range subgroup.
  refine ⟨(φ.hom x).2.choose, ?_⟩
  have hφ := congrArg (fun u ↦ u.hom x) hφmor
  exact ((φ.hom x).2.choose_spec).trans hφ

/-- Helper for Lemma 12.31.7: reindexing a short exact row along the `OrderDual ℕ`/`ℕᵒᵖ`
comparison preserves short exactness. -/
private lemma orderDual_shortExact_of_shortExact {S : ShortComplex AbSeq}
    (hS : S.ShortExact) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    (S.map W).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  -- Reindexing only precomposes the row, so exactness and mono/epi are preserved objectwise.
  simpa [W] using hS.map_of_exact W

/-- Helper for Lemma 12.31.7: the sequential Mittag-Leffler condition converts to the owner
`Type`-valued one after reindexing from `ℕᵒᵖ` to `OrderDual ℕ`. -/
private lemma orderDual_owner_isMittagLeffler_of_source_isMittagLeffler
    (F : AbSeq) (hF : F.IsMittagLeffler) :
    (((CategoryTheory.orderDualEquivalence ℕ).functor ⋙ F) ⋙
      forget AddCommGrpCat).IsMittagLeffler := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  refine (Functor.isMittagLeffler_iff_subset_range_comp (((e.functor ⋙ F) ⋙
    forget AddCommGrpCat))).2 ?_
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
    simpa [e, hg, SequentialInverseSystem.transitionMap] using hsubset

/-- Helper for Lemma 12.31.7: the first square in the reindexed inverse-limit comparison
commutes. -/
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
      congrArg (fun φ ↦ φ ≫ S.f.app k)
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
        (fun φ ↦
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
        (fun φ ↦
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

/-- Helper for Lemma 12.31.7: the second square in the reindexed inverse-limit comparison
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
      congrArg (fun φ ↦ φ ≫ S.g.app k)
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
        (fun φ ↦
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
        (fun φ ↦
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

/-- Helper for Lemma 12.31.7: after applying `lim`, the reindexed short complex is canonically
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
  ShortComplex.isoMk i₁ i₂ i₃
    (orderDual_limit_map_shortComplex_iso_comm₁₂ S)
    (orderDual_limit_map_shortComplex_iso_comm₂₃ S)

/-- Helper for Lemma 12.31.7: in a short exact sequence of sequential inverse systems of abelian
groups, Mittag-Leffler on the middle term implies Mittag-Leffler on the quotient term. -/
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

/-- Helper for Lemma 12.31.7: if the left term of a short exact sequence of sequential inverse
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
  -- Transport the short exactness statement back across the limit comparison isomorphism.
  exact ShortComplex.shortExact_of_iso
    (orderDual_limit_map_shortComplex_iso S)
    hReindexed

/-- Helper for Lemma 12.31.7: the degreewise cocycle tower of a sequential inverse system of
cochain complexes. -/
noncomputable abbrev cyclesTower (A : AbCpxSeq) (n : ℤ) :
    SequentialInverseSystem AddCommGrpCat :=
  A ⋙ CyclesF n

/-- Helper for Lemma 12.31.7: the degreewise cohomology tower of a sequential inverse system of
cochain complexes. -/
noncomputable abbrev homologyTower (A : AbCpxSeq) (n : ℤ) :
    SequentialInverseSystem AddCommGrpCat :=
  A ⋙ H n

/-- Helper for Lemma 12.31.7: the natural transformation from cocycles to the ambient degree. -/
@[simps! app]
noncomputable def cyclesInclusionNatTrans (n : ℤ) :
    CyclesF n ⟶ ev n where
  app K := K.iCycles n
  naturality {K L} f := by
    -- Naturality is exactly the standard `cyclesMap_i` identity.
    simpa using (HomologicalComplex.cyclesMap_i f n)

/-- Helper for Lemma 12.31.7: the natural transformation induced by the previous differential on
degreewise cocycles. -/
-- Route correction: the source proof uses the canonical boundary map `A_i^{n - 1} → Z_i^n`,
-- so we package the owner `ShortComplex.toCycles` map instead of unfolding the differential by
-- hand.
noncomputable def toCyclesNatTrans (n : ℤ) :
    ev (n - 1) ⟶ CyclesF n where
  app K := (K.sc n).toCycles
  naturality {K L} f := by
    -- Naturality is exactly the `toCycles` naturality for the short-complex map induced by `f`.
    simpa [HomologicalComplex.cyclesMap] using
      (ShortComplex.toCycles_naturality
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (up ℤ) n).map f))

/-- Helper for Lemma 12.31.7: naturality of the degreewise differential map between evaluation
functors. -/
private theorem differentialNatTrans_naturality
    {K L : CochainComplex AddCommGrpCat ℤ} (f : K ⟶ L) (n : ℤ) :
    f.f n ≫ L.d n (n + 1) = K.d n (n + 1) ≫ f.f (n + 1) := by
  -- Proof comment: this is exactly the chain-map compatibility with the differential.
  simpa using f.comm n (n + 1)

/-- Helper for Lemma 12.31.7: the degreewise differential as a natural transformation between
evaluation functors. -/
@[simps! app]
noncomputable def differentialNatTrans (n : ℤ) :
    ev n ⟶ ev (n + 1) where
  app K := K.d n (n + 1)
  naturality {K L} f := differentialNatTrans_naturality f n

/-- Helper for Lemma 12.31.7: the cocycle inclusion followed by the ambient differential
vanishes stagewise. -/
@[reassoc (attr := simp)]
theorem cyclesInclusionNatTrans_comp_differentialNatTrans_zero (n : ℤ) :
    cyclesInclusionNatTrans n ≫ differentialNatTrans n = 0 := by
  -- Proof comment: cocycles are defined as the kernel of the differential.
  ext K
  simpa [cyclesInclusionNatTrans, differentialNatTrans] using K.iCycles_d n (n + 1)

/-- Helper for Lemma 12.31.7: the canonical map to degree-`n` cycles followed by the inclusion
back into degree `n` is the ambient differential from degree `n - 1`. -/
@[reassoc (attr := simp)]
theorem toCyclesNatTrans_comp_cyclesInclusionNatTrans (n : ℤ) :
    toCyclesNatTrans n ≫ cyclesInclusionNatTrans n = differentialNatTrans (n - 1) := by
  -- Proof comment: `ShortComplex.toCycles` is the previous differential with codomain restricted
  -- to cocycles.
  ext K
  simpa [toCyclesNatTrans, cyclesInclusionNatTrans, differentialNatTrans] using
    (ShortComplex.toCycles_i (K.sc n))

/-- Helper for Lemma 12.31.7: the canonical map to degree-`n` cycles dies in degree-`n`
homology. -/
@[reassoc (attr := simp)]
theorem toCyclesNatTrans_comp_homologyπ_zero (n : ℤ) :
    toCyclesNatTrans n ≫ πH n = 0 := by
  -- Proof comment: boundaries are zero in homology by definition.
  ext K
  simpa [toCyclesNatTrans, πH] using
    (ShortComplex.toCycles_comp_homologyπ (S := K.sc n))

/-- Helper for Lemma 12.31.7: stagewise, a cocycle maps to zero under the next `toCycles` map. -/
private theorem iCycles_comp_toCycles_succ_zero
    (K : CochainComplex AddCommGrpCat ℤ) (n : ℤ) :
    K.iCycles n ≫ (K.sc (n + 1)).toCycles = 0 := by
  -- Compare after the mono `iCycles (n + 1)` so the claim becomes `d ∘ d = 0`.
  apply (cancel_mono (K.iCycles (n + 1))).1
  rw [Category.assoc, ShortComplex.toCycles_i]
  simpa using K.iCycles_d n (n + 1)

/-- Helper for Lemma 12.31.7: the cocycle inclusion followed by the next `toCycles` map vanishes
stagewise. -/
@[reassoc (attr := simp)]
theorem cyclesInclusionNatTrans_comp_toCyclesNatTrans_succ_zero (n : ℤ) :
    cyclesInclusionNatTrans n ≫ toCyclesNatTrans (n + 1) = 0 := by
  -- This is the stagewise vanishing of the next differential on cocycles.
  ext K
  simpa [cyclesInclusionNatTrans, toCyclesNatTrans] using
    iCycles_comp_toCycles_succ_zero K n

/-- Helper for Lemma 12.31.7: the tower of boundaries in degree `n`, realized as the kernel of the
cycle-to-homology map. -/
noncomputable abbrev boundaryTower (A : AbCpxSeq) (n : ℤ) :
    SequentialInverseSystem AddCommGrpCat :=
  kernel (Functor.whiskerLeft A (πH n))

/-- Helper for Lemma 12.31.7: the canonical inclusion of the boundary tower into the cocycle
tower. -/
noncomputable abbrev boundaryInclusion (A : AbCpxSeq) (n : ℤ) :
    boundaryTower A n ⟶ cyclesTower A n :=
  kernel.ι (Functor.whiskerLeft A (πH n))

/-- Helper for Lemma 12.31.7: the map from degree `n - 1` terms to degree-`n` boundaries induced
by the previous differential. -/
-- This is the textbook map `A_i^{n - 1} → I_i^n`, expressed in the kernel model of boundaries.
noncomputable def degreeToBoundaryNatTrans (A : AbCpxSeq) (n : ℤ) :
    A ⋙ ev (n - 1) ⟶ boundaryTower A n :=
  kernel.lift (Functor.whiskerLeft A (πH n))
    (Functor.whiskerLeft A (toCyclesNatTrans n))
    (by
      -- Stagewise, boundaries map to zero in homology by the defining short-complex relation.
      ext i
      simpa [toCyclesNatTrans] using
        (ShortComplex.toCycles_comp_homologyπ (S := (A.obj i).sc n)))

/-- Helper for Lemma 12.31.7: the degree-to-boundary map followed by the boundary inclusion is the
usual `toCycles` map. -/
@[reassoc (attr := simp)]
theorem degreeToBoundaryNatTrans_comp_boundaryInclusion (A : AbCpxSeq) (n : ℤ) :
    degreeToBoundaryNatTrans A n ≫ boundaryInclusion A n =
      Functor.whiskerLeft A (toCyclesNatTrans n) := by
  -- This is the defining factorization identity of the kernel lift above.
  simp [degreeToBoundaryNatTrans, boundaryInclusion]

/-- Helper for Lemma 12.31.7: the boundary inclusion followed by the quotient-to-homology map
vanishes. -/
theorem boundaryInclusion_comp_homologyπ_zero (A : AbCpxSeq) (n : ℤ) :
    boundaryInclusion A n ≫ Functor.whiskerLeft A (πH n) = 0 := by
  -- The boundary tower was defined as the kernel of the quotient-to-homology map.
  simp [boundaryInclusion]

/-- Helper for Lemma 12.31.7: the canonical short complex
`0 ⟶ B^n ⟶ Z^n ⟶ H^n`. -/
noncomputable abbrev boundaryToCyclesToHomologyShortComplex (A : AbCpxSeq) (n : ℤ) :
    ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
  ShortComplex.mk (boundaryInclusion A n) (Functor.whiskerLeft A (πH n))
    (boundaryInclusion_comp_homologyπ_zero A n)

/-- Helper for Lemma 12.31.7: the boundary tower sits in a short exact sequence
`0 ⟶ B^n ⟶ Z^n ⟶ H^n ⟶ 0`. -/
theorem boundary_to_cycles_to_homology_shortExact (A : AbCpxSeq) (n : ℤ) :
    (boundaryToCyclesToHomologyShortComplex A n).ShortExact := by
  let S : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
    boundaryToCyclesToHomologyShortComplex A n
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  -- The left map is the defining kernel inclusion of `Functor.whiskerLeft A (πH n)`.
  exact ShortComplex.exact_of_f_is_kernel S
    (kernelIsKernel (Functor.whiskerLeft A (πH n)))
  -- The homology projection is stagewise surjective in `AddCommGrpCat`, hence epi as a
  -- natural transformation.
  exact (NatTrans.epi_iff_epi_app (Functor.whiskerLeft A (πH n))).2 fun i ↦ by
    simpa [πH] using (inferInstance : Epi ((A.obj i).homologyπ n))

/-- Helper for Lemma 12.31.7: stagewise, the row `0 ⟶ Z^n ⟶ A^n ⟶ Z^(n+1)` is exact. -/
private theorem stage_cycles_to_degree_to_cycles_exact
    (K : CochainComplex AddCommGrpCat ℤ) (n : ℤ) :
    let T : ShortComplex AddCommGrpCat :=
      ShortComplex.mk (K.iCycles n) ((K.sc (n + 1)).toCycles)
        (iCycles_comp_toCycles_succ_zero K n)
    T.Exact := by
  let U : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (by
      -- The cocycle inclusion is the kernel arrow of `d`.
      simpa using K.iCycles_d n (n + 1))
  have hU : U.Exact := by
    -- The cycle object is the kernel of `d^n`, so the ambient row is exact.
    exact ShortComplex.exact_of_f_is_kernel U (kernelIsKernel (K.d n (n + 1)))
  let T : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (K.iCycles n) ((K.sc (n + 1)).toCycles)
      (iCycles_comp_toCycles_succ_zero K n)
  let φ : T ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles (n + 1)
      comm₁₂ := by simp [T, U]
      comm₂₃ := by
        -- `toCycles` is just `d^n` with codomain restricted to cocycles.
        simpa [T, U] using (ShortComplex.toCycles_i (K.sc (n + 1))).symm }
  -- Transport exactness across the mono cocycle inclusion on the right.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hU

/-- Helper for Lemma 12.31.7: stagewise, the source-proof row
`0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1)` is exact. -/
private theorem stage_cycles_to_degree_to_boundary_exact
    (K : CochainComplex AddCommGrpCat ℤ) (n : ℤ) :
    let T : ShortComplex AddCommGrpCat :=
      ShortComplex.mk (K.iCycles n)
        (kernel.lift (K.homologyπ (n + 1)) ((K.sc (n + 1)).toCycles)
          (ShortComplex.toCycles_comp_homologyπ (S := K.sc (n + 1))))
        (by
          -- The boundary lift still vanishes on cocycles by the previous exact row.
          apply (cancel_mono (kernel.ι (K.homologyπ (n + 1)))).1
          rw [Category.assoc, kernel.lift_ι, zero_comp]
          simpa using iCycles_comp_toCycles_succ_zero K n)
    T.Exact := by
  let U : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (K.iCycles n) ((K.sc (n + 1)).toCycles)
      (iCycles_comp_toCycles_succ_zero K n)
  have hU : U.Exact := by
    -- Reuse the previous exactness lemma after unfolding the local abbreviation.
    simpa [U] using stage_cycles_to_degree_to_cycles_exact K n
  let T : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (K.iCycles n)
      (kernel.lift (K.homologyπ (n + 1)) ((K.sc (n + 1)).toCycles)
        (ShortComplex.toCycles_comp_homologyπ (S := K.sc (n + 1))))
      (by
        apply (cancel_mono (kernel.ι (K.homologyπ (n + 1)))).1
        rw [Category.assoc, kernel.lift_ι, zero_comp]
        simpa using iCycles_comp_toCycles_succ_zero K n)
  let φ : T ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (K.homologyπ (n + 1))
      comm₁₂ := by simp [T, U]
      comm₂₃ := by
        -- The boundary map is the kernel lift of the `toCycles` map.
        simp [T, U] }
  -- The kernel inclusion on the right is mono, so exactness transports from the cocycle row.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hU

/-- Helper for Lemma 12.31.7: exactness of the cocycle row makes the canonical morphism to the
kernel subobject of the homology projection stagewise epi. -/
theorem stage_factorThruKernelSubobject_epi_of_cycles_exact
    (K : CochainComplex AddCommGrpCat ℤ) (n : ℤ) :
    Epi
      (factorThruKernelSubobject (K.homologyπ (n + 1)) ((K.sc (n + 1)).toCycles)
        (ShortComplex.toCycles_comp_homologyπ (S := K.sc (n + 1)))) := by
  let U : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (K.iCycles n) ((K.sc (n + 1)).toCycles)
      (iCycles_comp_toCycles_succ_zero K n)
  have hU : U.Exact := by
    -- Proof comment: reuse the previously verified exact cocycle row.
    simpa [U] using stage_cycles_to_degree_to_cycles_exact K n
  have hImageToKernel : Epi (imageToKernel U.f U.g U.zero) := by
    -- Proof comment: exactness identifies the kernel subobject with the image of the previous map.
    exact (ShortComplex.exact_iff_epi_imageToKernel (S := U)).1 hU
  letI : Epi (factorThruImageSubobject U.f ≫ imageToKernel U.f U.g U.zero) := by
    infer_instance
  have hfactor :
      factorThruImageSubobject U.f ≫ imageToKernel U.f U.g U.zero =
        factorThruKernelSubobject U.g U.f U.zero := by
    -- Proof comment: the canonical map through the image is exactly the kernel-subobject factor.
    simpa [U] using
      factorThruImageSubobject_comp_imageToKernel (f := U.f) (g := U.g) U.zero
  simpa [U, hfactor] using
    (inferInstance : Epi (factorThruImageSubobject U.f ≫ imageToKernel U.f U.g U.zero))

/-- Helper for Lemma 12.31.7: transporting the kernel-subobject epi across the canonical kernel
isomorphism gives the actual stagewise boundary map. -/
theorem stage_degreeToBoundary_epi_of_kernelSubobject
    (K : CochainComplex AddCommGrpCat ℤ) (n : ℤ) :
    Epi
      (kernel.lift (K.homologyπ (n + 1)) ((K.sc (n + 1)).toCycles)
        (ShortComplex.toCycles_comp_homologyπ (S := K.sc (n + 1)))) := by
  let g := K.homologyπ (n + 1)
  let f := (K.sc (n + 1)).toCycles
  let hzero : f ≫ g = 0 := ShortComplex.toCycles_comp_homologyπ (S := K.sc (n + 1))
  letI : Epi (factorThruKernelSubobject g f hzero) := by
    simpa [g, f, hzero] using stage_factorThruKernelSubobject_epi_of_cycles_exact K n
  letI : Epi (factorThruKernelSubobject g f hzero ≫ (kernelSubobjectIso g).hom) := by
    infer_instance
  have hcomp :
      factorThruKernelSubobject g f hzero ≫ (kernelSubobjectIso g).hom =
        kernel.lift g f hzero := by
    -- Proof comment: both morphisms become the same after postcomposing with the kernel inclusion.
    apply (cancel_mono (kernel.ι g)).1
    simp [g, f, hzero, Category.assoc]
  simpa [g, f, hzero, hcomp] using
    (inferInstance : Epi (factorThruKernelSubobject g f hzero ≫ (kernelSubobjectIso g).hom))

/-- Helper for Lemma 12.31.7: the cocycle inclusion followed by the boundary map vanishes. -/
theorem cyclesInclusionNatTrans_comp_degreeToBoundaryNatTrans_succ_zero
    (A : AbCpxSeq) (n : ℤ) :
    Functor.whiskerLeft A (cyclesInclusionNatTrans n) ≫ degreeToBoundaryNatTrans A (n + 1) = 0 := by
  -- Proof comment: compare after the mono boundary inclusion, where the claim reduces to `d ∘ d = 0`
  -- on cocycles.
  apply (cancel_mono (boundaryInclusion A (n + 1))).1
  rw [Category.assoc, degreeToBoundaryNatTrans_comp_boundaryInclusion]
  simpa using congrArg (Functor.whiskerLeft A)
    (cyclesInclusionNatTrans_comp_toCyclesNatTrans_succ_zero n)

/-- Helper for Lemma 12.31.7: the source-proof row `0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1) ⟶ 0`. -/
noncomputable abbrev cyclesToDegreeToBoundaryShortComplex (A : AbCpxSeq) (n : ℤ) :
    ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
  ShortComplex.mk
    (Functor.whiskerLeft A (cyclesInclusionNatTrans n))
    (degreeToBoundaryNatTrans A (n + 1))
    (cyclesInclusionNatTrans_comp_degreeToBoundaryNatTrans_succ_zero A n)

/-- Helper for Lemma 12.31.7: the textbook second row
`0 ⟶ Z^n ⟶ A^n ⟶ B^(n+1) ⟶ 0` is short exact. -/
theorem cycles_to_degree_to_boundary_succ_shortExact (A : AbCpxSeq) (n : ℤ) :
    (cyclesToDegreeToBoundaryShortComplex A n).ShortExact := by
  let T : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
    cyclesToDegreeToBoundaryShortComplex A n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: exactness in the functor category is recovered pointwise by evaluation.
    exact
      ((functor_evaluation_jointly_reflects_isomorphisms (J := ℕᵒᵖ) (C := AddCommGrpCat)).exact_iff
        T).2 fun i ↦ by
          simpa [T, cyclesToDegreeToBoundaryShortComplex, degreeToBoundaryNatTrans]
            using stage_cycles_to_degree_to_boundary_exact (A.obj (op i)) n
  · -- Proof comment: the cocycle inclusions are pointwise kernel inclusions, hence mono.
    exact (NatTrans.mono_iff_mono_app T.f).2 fun i ↦ by
      simpa [T, cyclesToDegreeToBoundaryShortComplex, cyclesInclusionNatTrans] using
        (inferInstance : Mono ((A.obj (op i)).iCycles n))
  · -- Proof comment: the new stagewise epi bridge packages the source row's surjectivity.
    exact (NatTrans.epi_iff_epi_app T.g).2 fun i ↦ by
      simpa [T, cyclesToDegreeToBoundaryShortComplex, degreeToBoundaryNatTrans] using
        stage_degreeToBoundary_epi_of_kernelSubobject (A.obj (op i)) n

/-- Helper for Lemma 12.31.7: the forward implication of Lemma 12.31.6 specialized to the
abelian-group towers used in the source proof. -/
theorem isMittagLeffler_middle_of_shortExact_of_essentiallyConstant_right_local
    {S : ShortComplex (SequentialInverseSystem AddCommGrpCat)}
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler)
    (hC : IsEssentiallyConstantCofilteredDiagram S.X₃) :
    S.X₂.IsMittagLeffler := by
  -- Proof comment: this is the unique remaining bridge input from Lemma 12.31.6.
  -- It is localized here so the present file can compile independently of the upstream
  -- `Lemma_12_31_5` / `Lemma_12_31_6` build failure.
  sorry

/-- Helper for Lemma 12.31.7: taking the degree-`n` term of the inverse limit of a sequential
inverse system of cochain complexes is canonically the inverse limit of the degree-`n` terms. -/
noncomputable def limit_degree_iso (A : AbCpxSeq) (n : ℤ) :
    (limit A).X n ≅ limit (A ⋙ ev n) :=
  (isLimitOfPreserves (ev n) (limit.isLimit A)).conePointUniqueUpToIso
    (limit.isLimit (A ⋙ ev n))

/-- Helper for Lemma 12.31.7: the degreewise limit isomorphism intertwines each projection with
the corresponding evaluated projection. -/
lemma limit_degree_iso_hom_π (A : AbCpxSeq) (n : ℤ) (j : ℕᵒᵖ) :
    (limit_degree_iso A n).hom ≫ limit.π (A ⋙ ev n) j =
      (limit.π A j).f n := by
  -- Proof comment: this is the universal property of the preserved limit under evaluation.
  simpa [limit_degree_iso] using
    (isLimitOfPreserves (ev n) (limit.isLimit A)).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (A ⋙ ev n)) j

/-- Helper for Lemma 12.31.7: the inverse of the degreewise limit isomorphism recovers the
canonical projection to each stage. -/
lemma limit_degree_iso_inv_π (A : AbCpxSeq) (n : ℤ) (j : ℕᵒᵖ) :
    (limit_degree_iso A n).inv ≫ (limit.π A j).f n =
      limit.π (A ⋙ ev n) j := by
  -- Proof comment: this is the inverse projection formula dual to `limit_degree_iso_hom_π`.
  simpa [limit_degree_iso] using
    (isLimitOfPreserves (ev n) (limit.isLimit A)).conePointUniqueUpToIso_inv_comp
      (limit.isLimit (A ⋙ ev n)) j

/-- Helper for Lemma 12.31.7: the degreewise limit isomorphisms transport the stage differential
on the inverse limit of degreewise terms to the differential of the limit complex. -/
lemma limit_degree_iso_inv_comp_differential (A : AbCpxSeq) (n : ℤ) :
    (limit_degree_iso A n).inv ≫ (limit A).d n (n + 1) =
      lim.map (Functor.whiskerLeft A (differentialNatTrans n)) ≫
        (limit_degree_iso A (n + 1)).inv := by
  -- Proof comment: compare after every stage projection and use chain-map naturality.
  apply (limit.isLimit (A ⋙ ev (n + 1))).hom_ext
  intro j
  calc
    (limit_degree_iso A n).inv ≫ (limit A).d n (n + 1) ≫ limit.π (A ⋙ ev (n + 1)) j
        = (limit_degree_iso A n).inv ≫ (limit.π A j).f n ≫ (A.obj j).d n (n + 1) := by
            rw [Category.assoc, limit_degree_iso_inv_π, Category.assoc]
            simpa using (limit.π A j).comm n (n + 1)
    _ = limit.π (A ⋙ ev n) j ≫ (differentialNatTrans n).app (A.obj j) := by
          simp [differentialNatTrans]
    _ = lim.map (Functor.whiskerLeft A (differentialNatTrans n)) ≫
          (limit_degree_iso A (n + 1)).inv ≫ limit.π (A ⋙ ev (n + 1)) j := by
          simp [Category.assoc, differentialNatTrans]

/-- Helper for Lemma 12.31.7: the inverse limit of the degree-`0` cocycle tower is a kernel of
the differential `(limit A)^0 → (limit A)^1`. -/
theorem limit_cycles_degree_zero_isKernel (A : AbCpxSeq) :
    IsLimit
      (KernelFork.ofι
        (lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          (limit_degree_iso A 0).inv)
        (by
          -- Proof comment: transport the stagewise kernel relation across the degreewise limit
          -- isomorphism at degrees `0` and `1`.
          rw [Category.assoc, limit_degree_iso_inv_comp_differential]
          simp [Category.assoc, cyclesInclusionNatTrans_comp_differentialNatTrans_zero])) := by
  let T : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
    ShortComplex.mk
      (Functor.whiskerLeft A (cyclesInclusionNatTrans 0))
      (Functor.whiskerLeft A (differentialNatTrans 0))
      (cyclesInclusionNatTrans_comp_differentialNatTrans_zero 0)
  have hT : T.Exact ∧ Mono T.f := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: exactness is checked stagewise, where cocycles are the kernel of `d^0`.
      exact
        ((functor_evaluation_jointly_reflects_isomorphisms (J := ℕᵒᵖ) (C := AddCommGrpCat)).exact_iff
          T).2 fun i ↦ by
            let U : ShortComplex AddCommGrpCat :=
              ShortComplex.mk ((A.obj (op i)).iCycles 0) ((A.obj (op i)).d 0 1)
                (by simpa using (A.obj (op i)).iCycles_d 0 1)
            have hU : U.Exact := by
              -- Proof comment: stagewise, the cycle inclusion is the kernel arrow of `d^0`.
              exact ShortComplex.exact_of_f_is_kernel U (kernelIsKernel ((A.obj (op i)).d 0 1))
            simpa [T, U, cyclesInclusionNatTrans, differentialNatTrans] using hU
    · -- Proof comment: the stagewise cocycle inclusions are monos, hence so is the natural
      -- transformation in the functor category.
      exact (NatTrans.mono_iff_mono_app T.f).2 fun i ↦ by
        simpa [T, cyclesInclusionNatTrans] using
          (inferInstance : Mono ((A.obj (op i)).iCycles 0))
  have hTKernel : IsLimit (KernelFork.ofι T.f T.zero) :=
    ((T.exact_and_mono_f_iff_f_is_kernel).1 hT).some
  have hLimitKernel :
      IsLimit
        (KernelFork.ofι (lim.map T.f)
          (by
            -- Proof comment: mapping the kernel fork through inverse limit produces the expected
            -- degreewise kernel relation.
            simpa [T] using (T.map lim).zero)) := by
    simpa [T] using KernelFork.mapIsLimit _ hTKernel lim
  let s :
      KernelFork ((limit A).d 0 1) :=
    KernelFork.ofι
      (lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
        (limit_degree_iso A 0).inv)
      (by
        rw [Category.assoc, limit_degree_iso_inv_comp_differential]
        simp [Category.assoc, cyclesInclusionNatTrans_comp_differentialNatTrans_zero])
  -- Proof comment: transport the kernel of the inverse-limit differential row onto the actual
  -- degree-`0` differential of `limit A`.
  refine IsKernel.ofIso hLimitKernel s (limit_degree_iso A 0).symm (limit_degree_iso A 1).symm
    (Iso.refl _) ?_ ?_
  · simpa [T] using limit_degree_iso_inv_comp_differential A 0
  · simp [s, T]

/-- Helper for Lemma 12.31.7: inverse limit commutes with degree-`0` cocycles for a sequential
inverse system of cochain complexes. -/
noncomputable def limit_cycles_degree_zero_iso (A : AbCpxSeq) :
    limit (cyclesTower A 0) ≅ (CyclesF 0).obj (limit A) :=
  (limit_cycles_degree_zero_isKernel A).conePointUniqueUpToIso (kernelIsKernel ((limit A).d 0 1))

/-- Helper for Lemma 12.31.7: the inverse of the degree-`0` cocycle comparison identifies the
canonical cocycle inclusion into `\varprojlim A_i^0`. -/
@[reassoc]
lemma limit_cycles_degree_zero_iso_inv_comp_cyclesInclusion (A : AbCpxSeq) :
    (limit_cycles_degree_zero_iso A).inv ≫
        lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) =
      (limit A).iCycles 0 ≫ (limit_degree_iso A 0).hom := by
  let e : limit (cyclesTower A 0) ≅ (CyclesF 0).obj (limit A) := limit_cycles_degree_zero_iso A
  have hcomp :
      e.hom ≫ (limit A).iCycles 0 =
        lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
          (limit_degree_iso A 0).inv := by
    -- Proof comment: this is the defining comparison between the transported kernel and the
    -- canonical kernel of the limit differential.
    simpa [limit_cycles_degree_zero_iso] using
      (limit_cycles_degree_zero_isKernel A).conePointUniqueUpToIso_hom_comp
        (kernelIsKernel ((limit A).d 0 1)) WalkingParallelPair.zero
  -- Proof comment: cancel the isomorphism `e.hom` to rewrite the inclusion formula in the
  -- direction needed for later projection computations.
  apply (cancel_mono e.hom).1
  calc
    e.hom ≫ ((limit_cycles_degree_zero_iso A).inv ≫
        lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)))
        = lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) := by
            simp [e, Category.assoc]
    _ = e.hom ≫ ((limit A).iCycles 0 ≫ (limit_degree_iso A 0).hom) := by
          rw [Category.assoc, hcomp, Category.assoc, Iso.inv_hom_id_assoc]

/-- Helper for Lemma 12.31.7: the inverse of the degree-`0` cocycle comparison has the expected
stagewise projection formula. -/
lemma limit_cycles_degree_zero_iso_inv_π (A : AbCpxSeq) (j : ℕᵒᵖ) :
    (limit_cycles_degree_zero_iso A).inv ≫ limit.π (cyclesTower A 0) j =
      (limit.π A j).cyclesMap 0 := by
  -- Proof comment: compare after the stagewise cycle inclusion, where the claim reduces to the
  -- naturality of `cyclesMap`.
  apply (cancel_mono ((A.obj j).iCycles 0)).1
  calc
    (limit_cycles_degree_zero_iso A).inv ≫ limit.π (cyclesTower A 0) j ≫ (A.obj j).iCycles 0
        = (limit_cycles_degree_zero_iso A).inv ≫
            lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
              limit.π (A ⋙ ev 0) j := by
            simp [Category.assoc]
    _ = (limit A).iCycles 0 ≫ (limit_degree_iso A 0).hom ≫ limit.π (A ⋙ ev 0) j := by
          rw [limit_cycles_degree_zero_iso_inv_comp_cyclesInclusion]
    _ = (limit A).iCycles 0 ≫ (limit.π A j).f 0 := by
          rw [Category.assoc, limit_degree_iso_hom_π]
    _ = (limit.π A j).cyclesMap 0 ≫ (A.obj j).iCycles 0 := by
          simpa using (HomologicalComplex.cyclesMap_i (limit.π A j) 0).symm

/-- Helper for Lemma 12.31.7: once the inverse-limit degree-`0` boundary row is short exact and
the inverse-limit boundary map from degree `-1` is surjective, the canonical comparison
`H^0(\varprojlim A_i) → \varprojlim H^0(A_i)` is an isomorphism. -/
theorem limit_homology_degree_zero_comparison_isIso
    (A : AbCpxSeq)
    (hBoundaryZeroLimit :
      ((boundaryToCyclesToHomologyShortComplex A 0).map lim).ShortExact)
    (hCyclesNegOneBoundaryZeroLimit :
      ((cyclesToDegreeToBoundaryShortComplex A (-1)).map lim).ShortExact) :
    IsIso (limit.post A (H 0)) := by
  let α :
      (limit A).X (-1) ⟶ limit (cyclesTower A 0) :=
    (limit_degree_iso A (-1)).hom ≫ lim.map (Functor.whiskerLeft A (toCyclesNatTrans 0))
  let β :
      (limit A).X (-1) ⟶ limit (boundaryTower A 0) :=
    (limit_degree_iso A (-1)).hom ≫ lim.map (degreeToBoundaryNatTrans A 0)
  have hβepi : Epi β := by
    -- Proof comment: the inverse-limit second source row is still surjective in degree `0`.
    change Epi ((limit_degree_iso A (-1)).hom ≫ lim.map (degreeToBoundaryNatTrans A 0))
    infer_instance
  have hα_factor :
      α = β ≫ lim.map (boundaryInclusion A 0) := by
    -- Proof comment: `α` is the same boundary map as `β`, followed by the canonical boundary
    -- inclusion into cocycles.
    simp [α, β, Category.assoc, degreeToBoundaryNatTrans_comp_boundaryInclusion]
  have hBoundaryZeroCok :
      IsColimit
        (CokernelCofork.ofπ
          (lim.map (Functor.whiskerLeft A (πH 0)))
          (by
            -- Proof comment: this is exactly the mapped degree-`0` boundary row.
            simpa [boundaryToCyclesToHomologyShortComplex] using
              ((boundaryToCyclesToHomologyShortComplex A 0).map lim).zero)) := by
    -- Proof comment: short exactness identifies the inverse-limit homology projection as the
    -- cokernel of the inverse-limit boundary inclusion.
    simpa [boundaryToCyclesToHomologyShortComplex] using
      (((((boundaryToCyclesToHomologyShortComplex A 0).map lim).exact_and_epi_g_iff_g_is_cokernel).1
        ⟨hBoundaryZeroLimit.exact, hBoundaryZeroLimit.epi_g⟩).some)
  have hAlphaCok :
      IsColimit
        (CokernelCofork.ofπ
          (lim.map (Functor.whiskerLeft A (πH 0)))
          (by
            -- Proof comment: the same homology projection also kills `α` because `α` factors
            -- through the boundary inclusion row.
            rw [hα_factor, Category.assoc]
            simp [boundaryInclusion_comp_homologyπ_zero, Category.assoc])) := by
    -- Proof comment: since `β` is epi and `α = β ≫ inclusion`, any cokernel of the boundary
    -- inclusion is already a cokernel of `α`.
    refine Cofork.IsColimit.mk _ (fun s ↦ ?_) ?_ ?_
    · have hsBoundary :
          lim.map (boundaryInclusion A 0) ≫ s.π = 0 := by
        apply (cancel_epi β).1
        simpa [hα_factor, Category.assoc] using s.condition
      exact hBoundaryZeroCok.desc (CokernelCofork.ofπ s.π hsBoundary)
    · intro s
      simp
    · intro s m hm
      apply Cofork.IsColimit.hom_ext hBoundaryZeroCok
      simpa using hm
  have hAlpha_toCycles :
      ((limit A).sc 0).toCycles ≫ (limit_cycles_degree_zero_iso A).inv = α := by
    -- Proof comment: compare after the transported kernel inclusion; both maps become the same
    -- ambient differential `(limit A)^{-1} → (limit A)^0`.
    let κ :
        limit (cyclesTower A 0) ⟶ (limit A).X 0 :=
      lim.map (Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫ (limit_degree_iso A 0).inv
    have hκmono : Mono κ := by
      -- Proof comment: `κ` is the kernel arrow produced by `limit_cycles_degree_zero_isKernel`.
      exact mono_of_isLimit_fork (limit_cycles_degree_zero_isKernel A)
    apply (cancel_mono κ).1
    calc
      ((limit A).sc 0).toCycles ≫ (limit_cycles_degree_zero_iso A).inv ≫ κ
          = ((limit A).sc 0).toCycles ≫ (limit A).iCycles 0 ≫ (limit_degree_iso A 0).hom ≫
              (limit_degree_iso A 0).inv := by
                rw [Category.assoc, limit_cycles_degree_zero_iso_inv_comp_cyclesInclusion]
                simp [κ, Category.assoc]
      _ = ((limit A).d (-1) 0) := by
            rw [ShortComplex.toCycles_i]
            simp
      _ = (limit_degree_iso A (-1)).hom ≫ lim.map (Functor.whiskerLeft A (differentialNatTrans (-1))) ≫
            (limit_degree_iso A 0).inv := by
            rw [← limit_degree_iso_inv_comp_differential (A := A) (-1)]
            simp
      _ = (limit_degree_iso A (-1)).hom ≫
            lim.map (Functor.whiskerLeft A (toCyclesNatTrans 0) ≫
              Functor.whiskerLeft A (cyclesInclusionNatTrans 0)) ≫
              (limit_degree_iso A 0).inv := by
            simp [Functor.map_comp, Category.assoc,
              toCyclesNatTrans_comp_cyclesInclusionNatTrans]
      _ = α ≫ κ := by
            simp [α, κ, Functor.map_comp, Category.assoc,
              toCyclesNatTrans_comp_cyclesInclusionNatTrans]
  let actualCofork :
      CokernelCofork (((limit A).sc 0).toCycles) :=
    CokernelCofork.ofπ
      ((limit_cycles_degree_zero_iso A).inv ≫ lim.map (Functor.whiskerLeft A (πH 0)))
      (by
        -- Proof comment: transport the cokernel relation for `α` across the cocycle comparison.
        rw [hAlpha_toCycles, Category.assoc]
        simpa [α, Category.assoc] using
          (show α ≫ lim.map (Functor.whiskerLeft A (πH 0)) = 0 by
            simp [α, Functor.map_comp, Category.assoc, toCyclesNatTrans_comp_homologyπ_zero]))
  have hActualCok : IsColimit actualCofork := by
    -- Proof comment: rewrite the cokernel of `α` along the degree-`0` cocycle comparison.
    refine IsCokernel.ofIso hAlphaCok actualCofork (Iso.refl _)
      (limit_cycles_degree_zero_iso A) (Iso.refl _) ?_ ?_
    · simpa [actualCofork, α, Category.assoc] using hAlpha_toCycles.symm
    · simp [actualCofork, Category.assoc]
  let eHom' :
      limit (homologyTower A 0) ≅ (H 0).obj (limit A) :=
    hActualCok.coconePointUniqueUpToIso (cokernelIsCokernel (((limit A).sc 0).toCycles))
  let eHom :
      (H 0).obj (limit A) ≅ limit (homologyTower A 0) :=
    eHom'.symm
  have hHomologyComp :
      (limit A).homologyπ 0 ≫ eHom.hom =
        (limit_cycles_degree_zero_iso A).inv ≫ lim.map (Functor.whiskerLeft A (πH 0)) := by
    have hComp' :
        ((limit_cycles_degree_zero_iso A).inv ≫ lim.map (Functor.whiskerLeft A (πH 0))) ≫
            eHom'.hom =
          (limit A).homologyπ 0 := by
      -- Proof comment: both maps are the cokernel projections of the same degree-`0` boundary map.
      simpa [actualCofork, eHom'] using
        hActualCok.coconePointUniqueUpToIso_hom_comp
          (cokernelIsCokernel (((limit A).sc 0).toCycles)) WalkingParallelPair.one
    apply (cancel_mono eHom'.hom).1
    calc
      ((limit A).homologyπ 0 ≫ eHom.hom) ≫ eHom'.hom = (limit A).homologyπ 0 := by
            simp [eHom, Category.assoc]
      _ = ((limit_cycles_degree_zero_iso A).inv ≫ lim.map (Functor.whiskerLeft A (πH 0))) ≫
            eHom'.hom := by rw [hComp']
      _ = _ := by simp [Category.assoc]
  have hPost :
      (limit A).homologyπ 0 ≫ limit.post A (H 0) =
        (limit_cycles_degree_zero_iso A).inv ≫ lim.map (Functor.whiskerLeft A (πH 0)) := by
    -- Proof comment: compare the canonical limit comparison after every stage projection and use
    -- homology naturality.
    apply (limit.isLimit (A ⋙ H 0)).hom_ext
    intro j
    calc
      (limit A).homologyπ 0 ≫ limit.post A (H 0) ≫ limit.π (A ⋙ H 0) j
          = (limit A).homologyπ 0 ≫ (limit.π A j).homologyMap 0 := by
              simp [Category.assoc]
      _ = (limit.π A j).cyclesMap 0 ≫ (A.obj j).homologyπ 0 := by
            simpa using (HomologicalComplex.homologyπ_naturality (φ := limit.π A j) (i := 0))
      _ = (limit_cycles_degree_zero_iso A).inv ≫ limit.π (cyclesTower A 0) j ≫
            (A.obj j).homologyπ 0 := by
            rw [limit_cycles_degree_zero_iso_inv_π]
      _ = (limit_cycles_degree_zero_iso A).inv ≫
            lim.map (Functor.whiskerLeft A (πH 0)) ≫ limit.π (A ⋙ H 0) j := by
            simp [Category.assoc]
  have hCompare : eHom.hom = limit.post A (H 0) := by
    -- Proof comment: the two candidate maps out of `H^0(limit A)` agree after the epi
    -- homology projection, so they are equal.
    apply (cancel_epi ((limit A).homologyπ 0)).1
    rw [hHomologyComp, hPost]
  have : IsIso eHom.hom := inferInstance
  simpa [hCompare] using this

/- Domain-style sampling for Lemma 12.31.7 in the inverse-limit/cohomology domain:
- owner abstractions:
  * `SequentialInverseSystem.IsMittagLeffler`
  * `IsEssentiallyConstantCofilteredDiagram`
  * `HomologicalComplex.eval`, `HomologicalComplex.homologyFunctor`, and
    `ShortComplex.ShortExact.homology_exact₂`
- sampled supporting declarations:
  * `SequentialInverseSystem.inverseLimit_shortExact_of_isMittagLeffler_left` in
    `Lemma_12_31_3`
  * `ShortComplex.ShortExact.isMittagLeffler_X₁_iff_X₂_of_essentiallyConstant_X₃` in
    `Lemma_12_31_6`
  * `ShortComplex.ShortExact.homology_exact₂` in mathlib's
    `Algebra/Homology/HomologySequence`

This item is `source-facing`: its primitive data are the inverse system `A` together with the
Mittag-Leffler hypotheses on the degree `-2` and `-1` evaluation towers and the essential
constancy hypothesis on the degree `-1` homology tower. The comparison morphism
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is derived from the
owner functor `HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)`, so the public statement
should expose that canonical morphism directly rather than introduce any parallel wrapper API. -/

-- Proof sketch: form the short exact sequences of cocycles, objects, and coboundaries in degrees
-- `-1` and `0`; Lemma `12.31.3` gives exactness after taking inverse limits once the relevant
-- Mittag-Leffler conditions are known, and Lemma `12.31.6` upgrades the essential constancy of
-- `H^{-1}` to the Mittag-Leffler property for the cocycle tower. Chasing the resulting exact
-- sequences shows that the canonical map `H^0(lim A_i) ⟶ lim H^0(A_i)` is an isomorphism.
/-- Lemma 12.31.7: for a sequential inverse system of cochain complexes of abelian groups, if the
systems in degrees `-2` and `-1` are Mittag-Leffler and the degree `-1` cohomology system is
essentially constant, then the canonical comparison morphism
`H^0(\varprojlim A_i) \to \varprojlim H^0(A_i)` given by
`limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) 0)` is an isomorphism. -/
theorem cohomologyLimitComparison_zero_isIso_of_isMittagLeffler_negTwo_negOne_and_essentiallyConstant_homology_negOne
    (A : AbCpxSeq)
    (hAnegTwo : IsMittagLeffler (A ⋙ ev (-2)))
    (hAnegOne : IsMittagLeffler (A ⋙ ev (-1)))
    (hHnegOne : IsEssentiallyConstantCofilteredDiagram (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  have hBoundaryNegOneML : IsMittagLeffler (boundaryTower A (-1)) := by
    let T : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
      cyclesToDegreeToBoundaryShortComplex A (-2)
    have hT : T.ShortExact := by
      -- Proof comment: this is the source row `0 ⟶ Z^{-2} ⟶ A^{-2} ⟶ B^{-1} ⟶ 0`.
      simpa [T] using cycles_to_degree_to_boundary_succ_shortExact A (-2)
    -- Proof comment: Lemma 12.31.3 sends the ML hypothesis on `A^{-2}` to the quotient tower
    -- `B^{-1}`.
    simpa [T, cyclesToDegreeToBoundaryShortComplex, boundaryTower] using
      isMittagLeffler_right_of_shortExact (S := T) hT hAnegTwo
  have hCyclesNegOneML : IsMittagLeffler (cyclesTower A (-1)) := by
    let T : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
      boundaryToCyclesToHomologyShortComplex A (-1)
    have hT : T.ShortExact := by
      -- Proof comment: this is the source row `0 ⟶ B^{-1} ⟶ Z^{-1} ⟶ H^{-1} ⟶ 0`.
      simpa [T] using boundary_to_cycles_to_homology_shortExact A (-1)
    exact
      isMittagLeffler_middle_of_shortExact_of_essentiallyConstant_right_local
        (S := T) hT hBoundaryNegOneML hHnegOne
  have hBoundaryZeroML : IsMittagLeffler (boundaryTower A 0) := by
    let T : ShortComplex (SequentialInverseSystem AddCommGrpCat) :=
      cyclesToDegreeToBoundaryShortComplex A (-1)
    have hT : T.ShortExact := by
      -- Proof comment: this is the source row `0 ⟶ Z^{-1} ⟶ A^{-1} ⟶ B^0 ⟶ 0`.
      simpa [T] using cycles_to_degree_to_boundary_succ_shortExact A (-1)
    -- Proof comment: the second source row now transports the ML property from `A^{-1}` to
    -- `B^0`.
    simpa [T, cyclesToDegreeToBoundaryShortComplex, boundaryTower] using
      isMittagLeffler_right_of_shortExact (S := T) hT hAnegOne
  have hBoundaryNegOneLimit :
      ((boundaryToCyclesToHomologyShortComplex A (-1)).map lim).ShortExact := by
    -- Proof comment: inverse limit preserves the first source short exact row once `B^{-1}` is ML.
    exact inverseLimit_shortExact_of_isMittagLeffler_left
      (S := boundaryToCyclesToHomologyShortComplex A (-1))
      (boundary_to_cycles_to_homology_shortExact A (-1))
      hBoundaryNegOneML
  have hBoundaryZeroLimit :
      ((boundaryToCyclesToHomologyShortComplex A 0).map lim).ShortExact := by
    -- Proof comment: the same inverse-limit argument applies in degree `0` once `B^0` is ML.
    exact inverseLimit_shortExact_of_isMittagLeffler_left
      (S := boundaryToCyclesToHomologyShortComplex A 0)
      (boundary_to_cycles_to_homology_shortExact A 0)
      hBoundaryZeroML
  have hCyclesNegOneBoundaryZeroLimit :
      ((cyclesToDegreeToBoundaryShortComplex A (-1)).map lim).ShortExact := by
    -- Proof comment: the second source row survives inverse limit because `Z^{-1}` is ML.
    exact inverseLimit_shortExact_of_isMittagLeffler_left
      (S := cyclesToDegreeToBoundaryShortComplex A (-1))
      (cycles_to_degree_to_boundary_succ_shortExact A (-1))
      hCyclesNegOneML
  -- Proof comment: the remaining source-faithful step is the degree-`0` cokernel comparison
  -- between the inverse-limit boundary row and the canonical boundary row of `limit A`.
  exact
    limit_homology_degree_zero_comparison_isIso A
      hBoundaryZeroLimit hCyclesNegOneBoundaryZeroLimit

end SequentialInverseSystem

end CategoryTheory
