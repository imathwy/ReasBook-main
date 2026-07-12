import Mathlib
import StacksProject_2024.Chap10.Lemma_10_86_4
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap12.Definition_12_31_2

open CategoryTheory.Limits
open Opposite
open OrderDual (ofDual toDual)

noncomputable section

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 12.31.3 in the inverse-limit / Mittag-Leffler domain:
- owner abstractions:
  * `SequentialInverseSystem` and `SequentialInverseSystem.IsMittagLeffler` from
    `Definition_12_31_2`
  * `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`
  * `ShortComplex.ShortExact.mk'`
  * `ShortComplex.exact_and_mono_f_iff_f_is_kernel`
- primitive data: a short exact sequence `S` of sequential inverse systems together with, for (2)
  and (3), the owner Mittag-Leffler hypothesis on one term
- derived API: the induced short complex `S.map lim` on inverse limits and its exactness,
  monomorphism, and short-exactness consequences
- source/core/bridge triage:
  * `source-facing`: the textbook statements about inverse limits and Mittag-Leffler towers
  * `core/canonical`: the owner exactness criteria for `ShortComplex` under `lim`
  * `bridge/view`: the abelian-group specialization from a short exact sequence of towers to the
    induced exactness properties on inverse limits

These lemmas should therefore live under the chapter owner `SequentialInverseSystem`; the short
complex on inverse limits is derived from `lim`, not packaged as a separate public wrapper. -/

variable (S : ShortComplex AbSeq)

/-- Helper for Lemma 12.31.3: evaluating a short exact sequence of sequential inverse systems at a
stage gives a short exact sequence of abelian groups. -/
lemma shortExact_eval {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n))).ShortExact := by
  let ev := (evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)
  have hExactMono : (S.map ev).Exact ∧ Mono (S.map ev).f := by
    -- Evaluation preserves kernels, so left exactness descends immediately to the stagewise row.
    simpa using
      (S.map ev).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  · -- Epimorphy of the right map is also checked componentwise.
    exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

/-- Helper for Lemma 12.31.3: in abelian groups, composing on the left with an epimorphism does
not change the image subobject. -/
lemma imageSubobject_comp_eq_of_epi_left
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

/-- Helper for Lemma 12.31.3: the concrete range inclusion in `AddCommGrpCat` is a monomorphism.
-/
private instance rangeSubtype_mono {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    Mono (AddCommGrpCat.ofHom f.hom.range.subtype) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Helper for Lemma 12.31.3: the chosen representative of `imageSubobject f` maps to the
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

/-- Helper for Lemma 12.31.3: inclusion of image subobjects implies inclusion of the underlying
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

/-- Helper for Lemma 12.31.3: reindexing a short exact row along the `OrderDual ℕ`/`ℕᵒᵖ`
comparison preserves short exactness. -/
private lemma orderDual_shortExact_of_shortExact
    (hS : S.ShortExact) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    (S.map W).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  -- Reindexing along the equivalence only precomposes the row, so exactness and mono/epi are
  -- preserved objectwise.
  simpa [W] using hS.map_of_exact W

/-- Helper for Lemma 12.31.3: the source-facing sequential Mittag-Leffler condition gives the
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
      -- The source Mittag-Leffler equality already identifies these two image subobjects.
      simpa [f', g'] using (hstable hcg).symm.le
    have hsubset : Set.range f'.hom ⊆ Set.range g'.hom := by
      -- Move from subobject inclusion to the concrete range inclusion requested by the owner API.
      exact
        @range_subset_of_imageSubobject_le
          (F.obj (op c)) (F.obj (op (ofDual k))) (F.obj (op (ofDual i)))
          f' g' himage
    -- Replace stabilized image equality by inclusion of the underlying set-theoretic ranges.
    simpa [e, hg, SequentialInverseSystem.transitionMap] using hsubset

/-- Helper for Lemma 12.31.3: the first square in the reindexed inverse-limit comparison
commutes. -/
private lemma orderDual_limit_map_shortComplex_iso_comm₁₂ :
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
  -- Compare the two ways of applying `S.f` after reindexing by checking each limit projection.
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

/-- Helper for Lemma 12.31.3: the second square in the reindexed inverse-limit comparison
commutes. -/
private lemma orderDual_limit_map_shortComplex_iso_comm₂₃ :
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
  -- The same projectionwise comparison handles the second square in the short complex.
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

/-- Helper for Lemma 12.31.3: after applying `lim`, the reindexed short complex is canonically
isomorphic to the original one. -/
private noncomputable def orderDual_limit_map_shortComplex_iso :
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
    (orderDual_limit_map_shortComplex_iso_comm₁₂ (S := S))
    (orderDual_limit_map_shortComplex_iso_comm₂₃ (S := S))

/-- Helper for Lemma 12.31.3: after reindexing from `ℕᵒᵖ` to `OrderDual ℕ`, Chapter 10 gives the
short exact inverse-limit row once the left term is Mittag-Leffler. -/
private lemma orderDual_inverseLimit_shortExact_of_isMittagLeffler_left
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    ((S.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  -- Apply the Chapter 10 countable inverse-limit theorem to the reindexed short exact row.
  exact inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
    (S := S.map W)
    (orderDual_shortExact_of_shortExact (S := S) hS)
    (orderDual_owner_isMittagLeffler_of_source_isMittagLeffler (F := S.X₁) hML)

-- Proof sketch: inverse limits of abelian groups are left exact. Apply the owner exact-functor
-- criterion for `lim` preserving finite limits to the given short exact sequence of sequential
-- inverse systems.
/-- Lemma 12.31.3 (1): for a short exact sequence of sequential inverse systems of abelian groups,
the induced sequence on inverse limits is left exact; equivalently, the map
`\varprojlim A_i \to \varprojlim B_i` is monic and the short complex
`\varprojlim A_i \to \varprojlim B_i \to \varprojlim C_i` is exact. -/
@[stacks 02N1]
theorem inverseLimit_exact_and_mono_of_shortExact
    (hS : S.ShortExact)
    : (S.map lim).Exact ∧ Mono (S.map lim).f := by
  simpa using
    (S.map lim).exact_and_mono_f_iff_f_is_kernel.2
      ⟨KernelFork.mapIsLimit _ hS.fIsKernel lim⟩

-- Proof sketch: evaluate the short exact sequence at each stage, where the right map is
-- surjective. The image-stabilization condition for the middle inverse system then passes to the
-- quotient inverse system, so the right term is again Mittag-Leffler.
/-- Lemma 12.31.3 (2): if the middle term of a short exact sequence of sequential inverse systems
of abelian groups is Mittag-Leffler, then the quotient inverse system is also Mittag-Leffler. -/
@[stacks 02N1]
theorem isMittagLeffler_right_of_shortExact
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
  letI : Epi (S.g.app (op k)) := (shortExact_eval (S := S) hS).epi_g
  letI : Epi (S.g.app (op c)) := (shortExact_eval (S := S) hS).epi_g
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

-- Proof sketch: this is the abelian-group specialization of the inverse-limit short-exactness
-- theorem for short exact sequences of sequential inverse systems with Mittag-Leffler left term.
/-- Lemma 12.31.3 (3): if the left term of a short exact sequence of sequential inverse systems of
abelian groups is Mittag-Leffler, then the induced sequence on inverse limits is short exact. -/
-- Route correction: the source proof should pass through the earlier countable inverse-limit
-- theorem from Chapter 10 after a thin `OrderDual ℕ`/`ℕᵒᵖ` reindexing bridge, rather than
-- replacing it with an ad hoc recursive lifting argument here.
theorem inverseLimit_shortExact_of_isMittagLeffler_left
    (hS : S.ShortExact)
    (hML : S.X₁.IsMittagLeffler) :
    (S.map lim).ShortExact := by
  let hReindexed := orderDual_inverseLimit_shortExact_of_isMittagLeffler_left
    (S := S) hS hML
  -- Transport the Chapter 10 short exactness statement back across the limit comparison isomorphism.
  exact ShortComplex.shortExact_of_iso
    (orderDual_limit_map_shortComplex_iso (S := S))
    hReindexed

end SequentialInverseSystem

end CategoryTheory
