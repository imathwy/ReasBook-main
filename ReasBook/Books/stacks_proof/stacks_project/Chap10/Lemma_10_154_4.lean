import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty Limits
open CommRingCat
open CommRingCat.Hom

universe u v

namespace RingHom

section

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- Helper for Chap10 Lemma 10 154 4: the categorical étale morphism property is stable under
cobase change in the universe used by the arrow-colimit system. -/
private instance etale_isStableUnderCobaseChange_for_colimitSystem :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}).IsStableUnderCobaseChange := by
  -- Translate the ring-hom base-change theorem through the morphism-property bridge.
  simpa [CommRingCat.etale, RingHom.toMorphismProperty] using
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2
      RingHom.Etale.isStableUnderBaseChange

/-- Helper for Chap10 Lemma 10 154 4: a source-facing filtered-colimit-of-étale ring map gives
the raw categorical `ind CommRingCat.etale` witness in the same universe. -/
private lemma raw_ind_etale_of_isFilteredColimitOfEtale
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (hf : RingHom.IsFilteredColimitOfEtale.{u, u, v} f) :
    MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale (CommRingCat.ofHom f) := by
  -- Install the algebra structure defined by `f` so that `algebraMap` reduces back to `f`.
  let _ : Algebra R A := f.toAlgebra
  have hraw :
      MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale
        (CommRingCat.ofHom (algebraMap R A)) := by
    exact raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale.2 hf
  simpa [RingHom.toAlgebra] using hraw

/-- Helper for Chap10 Lemma 10 154 4: pushing an ind-étale arrow forward in an under category
preserves the raw ind-étale witness. -/
private lemma raw_ind_etale_underPushout_of_isFilteredColimitOfEtale
    {X Y X' : CommRingCat.{u}} (f : X ⟶ Y) (g : X ⟶ X')
    (hf : RingHom.IsFilteredColimitOfEtale.{u, u, v} (hom f)) :
    MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale
      (((Under.pushout g).obj (Under.mk f)).hom) := by
  -- Convert to the under-category `ind` owner, apply pushout stability, and convert back.
  have hraw :
      MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale f :=
    raw_ind_etale_of_isFilteredColimitOfEtale (hom f) hf
  rw [MorphismProperty.ind_iff_ind_underMk] at hraw ⊢
  exact MorphismProperty.ind_underObj_pushout g hraw

/-- Helper for Chap10 Lemma 10 154 4: the transition map between pointwise pushouts respects the
defining pushout square. -/
private theorem pointwisePushoutFunctor_mapW
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) {j j' : J} (α : j ⟶ j') :
    f.app j ≫ (X₂.map α ≫ pushout.inl (f.app j') (c₁.ι.app j')) =
      c₁.ι.app j ≫ pushout.inr (f.app j') (c₁.ι.app j') := by
  -- The naturality square for `f` and the cocone square for `c₁` put both composites in the
  -- canonical pushout relation.
  rw [← Category.assoc, ← f.naturality]
  rw [Category.assoc, pushout.condition]
  exact c₁.w α =≫ pushout.inr (f.app j') (c₁.ι.app j')

/-- Helper for Chap10 Lemma 10 154 4: the transition morphism between pointwise pushouts
associated to a natural transformation and a source cocone. -/
private noncomputable def pointwisePushoutMap
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) {j j' : J} (α : j ⟶ j') :
    pushout (f.app j) (c₁.ι.app j) ⟶ pushout (f.app j') (c₁.ι.app j') :=
  pushout.desc
    (X₂.map α ≫ pushout.inl (f.app j') (c₁.ι.app j'))
    (pushout.inr (f.app j') (c₁.ι.app j'))
    (pointwisePushoutFunctor_mapW c₁ f α)

/-- Helper for Chap10 Lemma 10 154 4: the pointwise pushout transition carries the target
generator to the next target generator. -/
@[reassoc (attr := simp)]
private theorem pointwisePushoutMap_inl
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) {j j' : J} (α : j ⟶ j') :
    pushout.inl (f.app j) (c₁.ι.app j) ≫ pointwisePushoutMap c₁ f α =
      X₂.map α ≫ pushout.inl (f.app j') (c₁.ι.app j') := by
  -- Reduce the transition map to its first pushout generator.
  rw [pointwisePushoutMap, pushout.inl_desc]

/-- Helper for Chap10 Lemma 10 154 4: the pointwise pushout transition fixes the common
source-colimit generator. -/
@[reassoc (attr := simp)]
private theorem pointwisePushoutMap_inr
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) {j j' : J} (α : j ⟶ j') :
    pushout.inr (f.app j) (c₁.ι.app j) ≫ pointwisePushoutMap c₁ f α =
      pushout.inr (f.app j') (c₁.ι.app j') := by
  -- Reduce the transition map to its second pushout generator.
  rw [pointwisePushoutMap, pushout.inr_desc]

/-- Helper for Chap10 Lemma 10 154 4: the pointwise pushout transition for an identity morphism
is the identity map. -/
private theorem pointwisePushoutMap_id
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) (j : J) :
    pointwisePushoutMap c₁ f (𝟙 j) =
      𝟙 (pushout (f.app j) (c₁.ι.app j)) := by
  -- Both maps agree on the two pushout generators.
  apply pushout.hom_ext
  · rw [pointwisePushoutMap_inl]
    simp
  · rw [pointwisePushoutMap_inr]
    simp

/-- Helper for Chap10 Lemma 10 154 4: pointwise pushout transitions compose functorially. -/
private theorem pointwisePushoutMap_comp
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) {j j' j'' : J}
    (α : j ⟶ j') (β : j' ⟶ j'') :
    pointwisePushoutMap c₁ f (α ≫ β) =
      pointwisePushoutMap c₁ f α ≫ pointwisePushoutMap c₁ f β := by
  -- Both sides are determined by the target and common-base generators.
  apply pushout.hom_ext
  · simp only [pointwisePushoutMap, pushout.inl_desc, pushout.inl_desc_assoc,
      Functor.map_comp_assoc]
    rw [Category.assoc, pushout.inl_desc]
  · simp only [pointwisePushoutMap, pushout.inr_desc, pushout.inr_desc_assoc]
    exact (pushout.inr_desc
      (X₂.map β ≫ pushout.inl (f.app j'') (c₁.ι.app j''))
      (pushout.inr (f.app j'') (c₁.ι.app j'')) _).symm

/-- Helper for Chap10 Lemma 10 154 4: pointwise pushouts of a natural transformation along a
source colimit cocone form a functor. -/
private noncomputable def pointwisePushoutFunctor
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) : J ⥤ CommRingCat.{u} where
  obj j := pushout (f.app j) (c₁.ι.app j)
  map α := pointwisePushoutMap c₁ f α
  map_id j := pointwisePushoutMap_id c₁ f j
  map_comp α β := pointwisePushoutMap_comp c₁ f α β

/-- Helper for Chap10 Lemma 10 154 4: the common source-colimit generator is natural for the
pointwise pushout functor. -/
private theorem pointwisePushoutSourceNat_naturality
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) {j j' : J} (α : j ⟶ j') :
    ((Functor.const J).obj c₁.pt).map α ≫
        pushout.inr (f.app j') (c₁.ι.app j') =
      pushout.inr (f.app j) (c₁.ι.app j) ≫
        (pointwisePushoutFunctor c₁ f).map α := by
  -- Put the naturality equation in the exact orientation required by `NatTrans`.
  simpa [pointwisePushoutFunctor] using (pointwisePushoutMap_inr c₁ f α).symm

/-- Helper for Chap10 Lemma 10 154 4: the source colimit point maps naturally to the pointwise
pushout diagram. -/
private noncomputable def pointwisePushoutSourceNat
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
  (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) :
    (Functor.const J).obj c₁.pt ⟶ pointwisePushoutFunctor c₁ f where
  app j := pushout.inr (f.app j) (c₁.ι.app j)
  naturality _ _ α := pointwisePushoutSourceNat_naturality c₁ f α

/-- Helper for Chap10 Lemma 10 154 4: the comparison morphism of source and target colimits
induces a cocone on the pointwise pushout diagram. -/
private theorem pointwisePushoutForgetCocone_w
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {j j' : J} (α : j ⟶ j') :
    (pointwisePushoutFunctor c₁ f).map α ≫
        pushout.desc (c₂.ι.app j') φ ((hφ j').symm) =
      pushout.desc (c₂.ι.app j) φ ((hφ j).symm) := by
  -- Naturality is checked on the two pushout generators.
  apply pushout.hom_ext
  · simp only [pointwisePushoutFunctor, pointwisePushoutMap, pushout.inl_desc_assoc]
    rw [Category.assoc, pushout.inl_desc]
    exact (c₂.w α).trans
      (pushout.inl_desc (c₂.ι.app j) φ ((hφ j).symm)).symm
  · simp only [pointwisePushoutFunctor, pointwisePushoutMap, pushout.inr_desc_assoc]
    exact (pushout.inr_desc (c₂.ι.app j') φ ((hφ j').symm)).trans
      (pushout.inr_desc (c₂.ι.app j) φ ((hφ j).symm)).symm

/-- Helper for Chap10 Lemma 10 154 4: the pointwise pushout comparison maps satisfy the
`NatTrans` naturality equation. -/
private theorem pointwisePushoutForgetCocone_naturality
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {j j' : J} (α : j ⟶ j') :
    (pointwisePushoutFunctor c₁ f).map α ≫
        pushout.desc (c₂.ι.app j') φ ((hφ j').symm) =
      pushout.desc (c₂.ι.app j) φ ((hφ j).symm) ≫
        ((Functor.const J).obj c₂.pt).map α := by
  -- Remove the identity map from the constant functor and use the cocone compatibility lemma.
  simpa using pointwisePushoutForgetCocone_w c₁ c₂ f φ hφ α

/-- Helper for Chap10 Lemma 10 154 4: the comparison morphism of source and target colimits
induces the underlying cocone on pointwise pushouts. -/
private noncomputable def pointwisePushoutForgetCocone
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    Cocone (pointwisePushoutFunctor c₁ f) where
  pt := c₂.pt
  ι.app j := pushout.desc (c₂.ι.app j) φ ((hφ j).symm)
  ι.naturality _ _ α := pointwisePushoutForgetCocone_naturality c₁ c₂ f φ hφ α

/-- Helper for Chap10 Lemma 10 154 4: any cocone on the pointwise pushout diagram restricts
along the target generators to a cocone on the target diagram. -/
private theorem pointwisePushoutTargetCocone_naturality
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) (s : Cocone (pointwisePushoutFunctor c₁ f))
    {j j' : J} (α : j ⟶ j') :
    X₂.map α ≫ (pushout.inl (f.app j') (c₁.ι.app j') ≫ s.ι.app j') =
      (pushout.inl (f.app j) (c₁.ι.app j) ≫ s.ι.app j) ≫
        ((Functor.const J).obj s.pt).map α := by
  -- Route correction: the previous route tried to discover this under associativity inside the
  -- target cocone; we first normalize to the pointwise transition map and then use `s.w`.
  -- Rewrite the target generator through the pointwise transition, then use the cocone
  -- identity for `s`; the constant-functor map is an identity.
  rw [Category.assoc, ← pointwisePushoutMap_inl_assoc c₁ f α]
  simpa [pointwisePushoutFunctor] using
    congrArg (fun q ↦ pushout.inl (f.app j) (c₁.ι.app j) ≫ q) (s.w α)

/-- Helper for Chap10 Lemma 10 154 4: the target-generator part of a pointwise-pushout cocone
as a cocone on the target diagram. -/
private noncomputable def pointwisePushoutTargetCocone
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂)
    (s : Cocone (pointwisePushoutFunctor c₁ f)) : Cocone X₂ where
  pt := s.pt
  ι.app j := pushout.inl (f.app j) (c₁.ι.app j) ≫ s.ι.app j
  ι.naturality _ _ α := pointwisePushoutTargetCocone_naturality c₁ f s α

/-- Helper for Chap10 Lemma 10 154 4: along one transition, the common-base generator has the
same composite with a cocone leg. -/
private theorem pointwisePushoutMap_inr_comp_cocone
    {J : Type v} [SmallCategory J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) (s : Cocone (pointwisePushoutFunctor c₁ f))
    {j j' : J} (α : j ⟶ j') :
    pushout.inr (f.app j) (c₁.ι.app j) ≫ s.ι.app j =
      pushout.inr (f.app j') (c₁.ι.app j') ≫ s.ι.app j' := by
  -- Rewrite the common-base generator through the transition map and then use the cocone
  -- identity for `s`.
  rw [← s.w α]
  simpa [pointwisePushoutFunctor] using
    pointwisePushoutMap_inr_assoc c₁ f α (s.ι.app j')

/-- Helper for Chap10 Lemma 10 154 4: over a filtered index, the common-base generator of a
pointwise-pushout cocone is independent of the chosen stage. -/
private theorem pointwisePushoutMap_inr_comp_cocone_const
    {J : Type v} [SmallCategory J] [IsFiltered J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (f : X₁ ⟶ X₂) (s : Cocone (pointwisePushoutFunctor c₁ f))
    (j j' : J) :
    pushout.inr (f.app j) (c₁.ι.app j) ≫ s.ι.app j =
      pushout.inr (f.app j') (c₁.ι.app j') ≫ s.ι.app j' := by
  -- Filtered categories are connected, so one-arrow preservation globalizes to all stages.
  letI : IsConnected J := CategoryTheory.IsFiltered.isConnected J
  exact constant_of_preserves_morphisms
    (fun k ↦ pushout.inr (f.app k) (c₁.ι.app k) ≫ s.ι.app k)
    (fun _ _ α ↦ pointwisePushoutMap_inr_comp_cocone c₁ f s α) j j'

/-- Helper for Chap10 Lemma 10 154 4: the common-base generator of any cocone on the pointwise
pushout diagram factors through the target-colimit descent map. -/
private theorem pointwisePushoutForgetCocone_base_fac
    {J : Type v} [SmallCategory J] [IsFiltered J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    (s : Cocone (pointwisePushoutFunctor c₁ f)) (j : J) :
    pushout.inr (f.app j) (c₁.ι.app j) ≫ s.ι.app j =
      φ ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s) := by
  -- Compare the two maps out of the source colimit on every source generator.
  apply hc₁.hom_ext
  intro k
  have hTargetFac :
      pushout.inl (f.app k) (c₁.ι.app k) ≫ s.ι.app k =
        c₂.ι.app k ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s) := by
    -- The target colimit descent agrees with the restricted target-generator cocone.
    exact (hc₂.fac (pointwisePushoutTargetCocone c₁ f s) k).symm
  have hPushout :
      c₁.ι.app k ≫ (pushout.inr (f.app k) (c₁.ι.app k) ≫ s.ι.app k) =
        f.app k ≫ (pushout.inl (f.app k) (c₁.ι.app k) ≫ s.ι.app k) := by
    -- The defining pushout square identifies the two generator composites at stage `k`.
    calc
      c₁.ι.app k ≫ (pushout.inr (f.app k) (c₁.ι.app k) ≫ s.ι.app k)
          = (c₁.ι.app k ≫ pushout.inr (f.app k) (c₁.ι.app k)) ≫ s.ι.app k := by
            rw [Category.assoc]
      _ = (f.app k ≫ pushout.inl (f.app k) (c₁.ι.app k)) ≫ s.ι.app k := by
            rw [← pushout.condition]
      _ = f.app k ≫ (pushout.inl (f.app k) (c₁.ι.app k) ≫ s.ι.app k) := by
            rw [Category.assoc]
  have hCompare :
      f.app k ≫ (pushout.inl (f.app k) (c₁.ι.app k) ≫ s.ι.app k) =
        c₁.ι.app k ≫ (φ ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s)) := by
    -- Replace the target-generator cocone leg by the target colimit descent and use `hφ`.
    calc
      f.app k ≫ (pushout.inl (f.app k) (c₁.ι.app k) ≫ s.ι.app k)
          = f.app k ≫
              (c₂.ι.app k ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s)) := by
            rw [hTargetFac]
            rfl
      _ = (f.app k ≫ c₂.ι.app k) ≫
            hc₂.desc (pointwisePushoutTargetCocone c₁ f s) := by
            rw [Category.assoc]
      _ = (c₁.ι.app k ≫ φ) ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s) := by
            rw [← hφ k]
            rfl
      _ = c₁.ι.app k ≫
            (φ ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s)) := by
            rw [Category.assoc]
  -- At generator `k`, replace the chosen common-base leg by the `k`-indexed one, then use the
  -- pushout square, the comparison equation, and the target-colimit facet.
  have hConst :=
    congrArg (fun q ↦ c₁.ι.app k ≫ q)
      (pointwisePushoutMap_inr_comp_cocone_const c₁ f s j k)
  exact hConst.trans (hPushout.trans hCompare)

/-- Helper for Chap10 Lemma 10 154 4: the underlying pointwise-pushout cocone induced by the
comparison map is colimiting. -/
private noncomputable def pointwisePushoutForgetCocone_isColimit
    {J : Type v} [SmallCategory J] [IsFiltered J] {X₁ X₂ : J ⥤ CommRingCat.{u}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    IsColimit (pointwisePushoutForgetCocone c₁ c₂ f φ hφ) := by
  -- A cocone over pointwise pushouts descends through the target colimit after restricting
  -- along the target generators.
  refine
    { desc := fun s ↦ hc₂.desc (pointwisePushoutTargetCocone c₁ f s)
      fac := ?_
      uniq := ?_ }
  · intro s j
    have hInlFac :
        pushout.inl (f.app j) (c₁.ι.app j) ≫
            (pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j =
          c₂.ι.app j := by
      -- The comparison cocone restricts to the target-colimit leg on the target generator.
      exact pushout.inl_desc (c₂.ι.app j) φ ((hφ j).symm)
    have hInrFac :
        pushout.inr (f.app j) (c₁.ι.app j) ≫
            (pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j =
          φ := by
      -- The comparison cocone restricts to the colimit-source map on the common-base generator.
      exact pushout.inr_desc (c₂.ι.app j) φ ((hφ j).symm)
    -- The facet is checked on the two pushout generators.
    apply pushout.hom_ext
    · calc
        pushout.inl (f.app j) (c₁.ι.app j) ≫
              ((pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j ≫
                hc₂.desc (pointwisePushoutTargetCocone c₁ f s))
            = (pushout.inl (f.app j) (c₁.ι.app j) ≫
                (pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j) ≫
                hc₂.desc (pointwisePushoutTargetCocone c₁ f s) := by
              rw [Category.assoc]
        _ = c₂.ι.app j ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s) := by
              rw [hInlFac]
              rfl
        _ = pushout.inl (f.app j) (c₁.ι.app j) ≫ s.ι.app j := by
              exact hc₂.fac (pointwisePushoutTargetCocone c₁ f s) j
    · have hAssoc :
          pushout.inr (f.app j) (c₁.ι.app j) ≫
              ((pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j ≫
                hc₂.desc (pointwisePushoutTargetCocone c₁ f s)) =
            (pushout.inr (f.app j) (c₁.ι.app j) ≫
                (pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j) ≫
                hc₂.desc (pointwisePushoutTargetCocone c₁ f s) := by
        rw [Category.assoc]
      have hMid :=
        congrArg (fun q ↦ q ≫ hc₂.desc (pointwisePushoutTargetCocone c₁ f s)) hInrFac
      exact hAssoc.trans
        (hMid.trans (pointwisePushoutForgetCocone_base_fac c₁ c₂ hc₁ hc₂ f φ hφ s j).symm)
  · intro s m hm
    -- Uniqueness follows because the target-colimit descent is determined on target generators.
    apply hc₂.hom_ext
    intro j
    have hInlFac :
        pushout.inl (f.app j) (c₁.ι.app j) ≫
            (pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j =
          c₂.ι.app j := by
      -- The target generator of the comparison cocone is the target-colimit cocone leg.
      exact pushout.inl_desc (c₂.ι.app j) φ ((hφ j).symm)
    have hStart :
        c₂.ι.app j ≫ m =
          (pushout.inl (f.app j) (c₁.ι.app j) ≫
            (pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j) ≫ m := by
      rw [hInlFac]
      rfl
    have hAssoc :
        (pushout.inl (f.app j) (c₁.ι.app j) ≫
            (pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j) ≫ m =
          pushout.inl (f.app j) (c₁.ι.app j) ≫
            ((pointwisePushoutForgetCocone c₁ c₂ f φ hφ).ι.app j ≫ m) := by
      rw [Category.assoc]
    have hUseFac :=
      congrArg (fun q ↦ pushout.inl (f.app j) (c₁.ι.app j) ≫ q) (hm j)
    exact hStart.trans
      (hAssoc.trans
        (hUseFac.trans (hc₂.fac (pointwisePushoutTargetCocone c₁ f s) j).symm))

/-- Helper for Chap10 Lemma 10 154 4: an arrow-category colimit gives a colimit of source
objects without requiring a global preservation instance for `Arrow.leftFunc`. -/
private noncomputable def arrowLeftFunc_mapCocone_isColimit_of_isColimit
    {J : Type v} [SmallCategory J] {F : J ⥤ Arrow CommRingCat.{u}} {c : Cocone F}
    (hc : IsColimit c) :
    IsColimit (Arrow.leftFunc.mapCocone c) := by
  -- Extend a source cocone to an arrow cocone whose target is terminal, then read off the
  -- left component of the arrow-colimit universal morphism.
  let mkCocone (s : Cocone (F ⋙ Arrow.leftFunc)) : Cocone F :=
    { pt := Arrow.mk (terminal.from s.pt)
      ι :=
        { app := fun j ↦ Arrow.homMk (s.ι.app j) (terminal.from (F.obj j).right)
          naturality := by
            intro j j' α
            apply Arrow.hom_ext
            · simpa using s.w α
            · apply terminal.hom_ext } }
  refine
    { desc := fun s ↦ (hc.desc (mkCocone s)).left
      fac := ?_
      uniq := ?_ }
  · intro s j
    -- The arrow-colimit facet, projected to the left component, is the source-cocone facet.
    have h := congrArg Arrow.Hom.left (hc.fac (mkCocone s) j)
    simpa [mkCocone] using h
  · intro s m hm
    -- A competing source descent extends uniquely to the same terminal-arrow test cocone.
    have huniq := congrArg Arrow.Hom.left (hc.uniq (mkCocone s)
      (Arrow.homMk m (terminal.from c.pt.right))
      (by
        intro j
        apply Arrow.hom_ext
        · simpa using hm j
        · apply terminal.hom_ext))
    simpa [mkCocone] using huniq

/-- Helper for Chap10 Lemma 10 154 4: an arrow-category colimit gives a colimit of target
objects without requiring a global preservation instance for `Arrow.rightFunc`. -/
private noncomputable def arrowRightFunc_mapCocone_isColimit_of_isColimit
    {J : Type v} [SmallCategory J] {F : J ⥤ Arrow CommRingCat.{u}} {c : Cocone F}
    (hc : IsColimit c) :
    IsColimit (Arrow.rightFunc.mapCocone c) := by
  -- Extend a target cocone to an arrow cocone landing in the identity arrow on the target point.
  let mkCocone (s : Cocone (F ⋙ Arrow.rightFunc)) : Cocone F :=
    { pt := Arrow.mk (𝟙 s.pt)
      ι :=
        { app := fun j ↦ Arrow.homMk ((F.obj j).hom ≫ s.ι.app j) (s.ι.app j)
          naturality := by
            intro j j' α
            apply Arrow.hom_ext
            · have hs := s.w α
              calc
                (F.map α).left ≫ ((F.obj j').hom ≫ s.ι.app j')
                    = ((F.map α).left ≫ (F.obj j').hom) ≫ s.ι.app j' := by
                      rw [Category.assoc]
                _ = ((F.obj j).hom ≫ (F.map α).right) ≫ s.ι.app j' := by
                      rw [(F.map α).w]
                _ = (F.obj j).hom ≫ ((F.map α).right ≫ s.ι.app j') := by
                      rw [Category.assoc]
                _ = (F.obj j).hom ≫ s.ι.app j := by
                      simpa using congrArg (fun q ↦ (F.obj j).hom ≫ q) hs
            · simpa using s.w α } }
  refine
    { desc := fun s ↦ (hc.desc (mkCocone s)).right
      fac := ?_
      uniq := ?_ }
  · intro s j
    -- The arrow-colimit facet, projected to the right component, is the target-cocone facet.
    have h := congrArg Arrow.Hom.right (hc.fac (mkCocone s) j)
    simpa [mkCocone] using h
  · intro s m hm
    -- A competing target descent extends to the identity-arrow test cocone by composing through
    -- the colimit arrow on the left.
    have hLeft : ∀ j,
        (c.ι.app j).left ≫ (c.pt.hom ≫ m) = (F.obj j).hom ≫ s.ι.app j := by
      intro j
      have hmj := hm j
      calc
        (c.ι.app j).left ≫ (c.pt.hom ≫ m)
            = ((c.ι.app j).left ≫ c.pt.hom) ≫ m := by
              rw [Category.assoc]
        _ = ((F.obj j).hom ≫ (c.ι.app j).right) ≫ m := by
              simpa using congrArg (fun q ↦ q ≫ m) (c.ι.app j).w
        _ = (F.obj j).hom ≫ ((c.ι.app j).right ≫ m) := by
              rw [Category.assoc]
        _ = (F.obj j).hom ≫ s.ι.app j := by
              simpa using congrArg (fun q ↦ (F.obj j).hom ≫ q) hmj
    have huniq := congrArg Arrow.Hom.right (hc.uniq (mkCocone s)
      (Arrow.homMk (c.pt.hom ≫ m) m (by simp [mkCocone]))
      (by
        intro j
        apply Arrow.hom_ext
        · exact hLeft j
        · simpa using hm j))
    simpa [mkCocone] using huniq

/- Domain-style sampling for Lemma 10.154.4:
* primary domain: filtered-colimit closure of ind-étale morphisms in the arrow category of
  commutative rings;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner for ind-étale ring maps;
  - `RingHom.filteredColimitOfEtale_baseChange`, the owner-level base-change theorem;
  - `RingHom.isFilteredColimitOfEtale_of_isColimit_filtered_system`, the fixed-source colimit
    theorem;
  - `CategoryTheory.MorphismProperty.ind`, the core filtered-colimit owner behind the wrapper.
* owner decision:
  - `source-facing`: `RingHom.isFilteredColimitOfEtale_colimit_of_directed_ringMap_system`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the wrapper `RingHom.IsFilteredColimitOfEtale`, which hides the same-universe
    `ULift` presentation of the core owner.
* primitive data: a directed diagram of ring maps in `Arrow CommRingCat` and the owner-level
  ind-étale hypothesis on each stage map;
* derived API: the induced owner-level ind-étale statement for the colimit map.

Since Lemma `10.154.3` already introduced `RingHom.IsFilteredColimitOfEtale` as the source-facing
owner, this file should use that owner directly instead of repeating the raw
`ind CommRingCat.etale` presentation in its public theorem surface.
-/

-- Proof sketch: view the directed system of ring maps as a diagram in `Arrow CommRingCat`. For
-- each stage, base change its étale presentation along the map from the source ring to the colimit
-- source using Lemma `10.154.1`. These base-changed presentations assemble into a filtered diagram
-- over the colimit source, and Lemma `10.154.3` upgrades the resulting filtered colimit
-- decomposition of the colimit target map to one by étale algebras.
/-- Chap10 Lemma 10 154 4: if a directed system of commutative ring maps has the property that
each stage map is a filtered colimit of étale algebras over its source, then the colimit map from
the colimit of the source rings to the colimit of the target rings is also a filtered colimit of
étale algebras. -/
@[stacks 0GIM]
theorem isFilteredColimitOfEtale_colimit_of_directed_ringMap_system
    (F : I ⥤ Arrow CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, RingHom.IsFilteredColimitOfEtale.{u, u, v} (hom (F.obj i).hom)) :
    RingHom.IsFilteredColimitOfEtale.{u, u, v} (hom c.pt.hom) := by
  -- First base-change each stage along its map to the colimit source; this is the verified
  -- stagewise part of the fixed-source reduction.
  have hStageBaseChange : ∀ i,
      MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale
        (((Under.pushout (c.ι.app i).left).obj (Under.mk (F.obj i).hom)).hom) := by
    intro i
    exact raw_ind_etale_underPushout_of_isFilteredColimitOfEtale
      (F.obj i).hom (c.ι.app i).left (hF i)
  let c₁ : Cocone (F ⋙ Arrow.leftFunc) := Arrow.leftFunc.mapCocone c
  let c₂ : Cocone (F ⋙ Arrow.rightFunc) := Arrow.rightFunc.mapCocone c
  let f : (F ⋙ Arrow.leftFunc) ⟶ (F ⋙ Arrow.rightFunc) :=
    Functor.whiskerLeft F Arrow.leftToRight
  let φ : c₁.pt ⟶ c₂.pt := c.pt.hom
  have hφ : ∀ i, c₁.ι.app i ≫ φ = f.app i ≫ c₂.ι.app i := by
    intro i
    -- Project the original arrow-cocone square into the pointwise source/target notation.
    simpa [c₁, c₂, f, φ] using (c.ι.app i).w
  let D : I ⥤ Under c₁.pt :=
    Under.lift (pointwisePushoutFunctor c₁ f) (pointwisePushoutSourceNat c₁ f)
  let cD : Cocone (pointwisePushoutFunctor c₁ f) :=
    pointwisePushoutForgetCocone c₁ c₂ f φ hφ
  have hp : ∀ i, (pointwisePushoutSourceNat c₁ f).app i ≫ cD.ι.app i = φ := by
    intro i
    -- The lifted under-cocone is based on the common source-colimit generator.
    simpa [cD, pointwisePushoutSourceNat, pointwisePushoutForgetCocone] using
      pushout.inr_desc (c₂.ι.app i) φ ((hφ i).symm)
  let cUnder : Cocone D :=
    Under.liftCocone (pointwisePushoutFunctor c₁ f) (pointwisePushoutSourceNat c₁ f)
      cD φ hp
  have hcD : IsColimit cD :=
    pointwisePushoutForgetCocone_isColimit c₁ c₂
      (arrowLeftFunc_mapCocone_isColimit_of_isColimit hc)
      (arrowRightFunc_mapCocone_isColimit_of_isColimit hc) f φ hφ
  have hcUnder : IsColimit cUnder :=
    Under.isColimitLiftCocone (pointwisePushoutFunctor c₁ f)
      (pointwisePushoutSourceNat c₁ f) cD φ hp hcD
  have hStages : ∀ i,
      MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale (D.obj i).hom := by
    intro i
    -- Each pointwise-pushout stage is exactly the under-category pushout used in the
    -- stagewise base-change witness.
    simpa [D, c₁, f, pointwisePushoutSourceNat] using hStageBaseChange i
  have hraw :
      MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale cUnder.pt.hom :=
    isFilteredColimitOfEtale_of_isColimit_filtered_system D cUnder hcUnder hStages
  -- Convert the raw owner on the lifted cocone point back to the source-facing ring-hom wrapper.
  let _ : Algebra c.pt.left c.pt.right := (hom c.pt.hom).toAlgebra
  have hrawAlg :
      MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale
        (CommRingCat.ofHom (algebraMap c.pt.left c.pt.right)) := by
    simpa [RingHom.toAlgebra, cUnder, φ] using hraw
  simpa [RingHom.toAlgebra] using
    (raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale.mp hrawAlg)

end

end RingHom
