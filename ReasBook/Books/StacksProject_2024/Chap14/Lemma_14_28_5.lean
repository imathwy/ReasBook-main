import Mathlib
import stacks_project.Chap14.Lemma_14_26_9
import stacks_project.Chap14.Lemma_14_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)
variable [∀ n : ℕ, HasWidePushout (Arrow.mk f).left
  (fun _ : Fin (n + 1) ↦ (Arrow.mk f).right) (fun _ ↦ (Arrow.mk f).hom)]
variable (s : Y ⟶ X) (hs : f ≫ s = 𝟙 X)

/- Domain-style sampling for Lemma 14.28.5:
- primary domain: Čech conerves of split monomorphisms, organized through the augmented
  Čech-conerve owner and the source-facing cosimplicial homotopy owner;
- sampled same-kind owner declarations:
  `Arrow.augmentedCechConerve`,
  `Arrow.mapCechConerve`,
  `Arrow.mapAugmentedCechConerve`,
  `CosimplicialObject.DeltaOneHomotopy`,
  `cechNerveSectionEndomorphism_homotopic_id`,
  `NatTrans.op`;
- best owner abstraction: the ambient owner is the augmented Čech conerve of `Arrow.mk f`, while
  the source-facing directed homotopy owner in this chapter is
  `CosimplicialObject.DeltaOneHomotopy`, and the public relation-level owner is
  `CosimplicialObject.DeltaOneHomotopic`; the opposite simplicial homotopy statement is a bridge
  obtained from Lemma 14.28.3;
- primitive data: the split-monomorphism witness `s : Y ⟶ X` with `f ≫ s = 𝟙 X`;
- derived API: the induced conerve endomorphism, the conerve retraction, and the resulting
  `Δ[1]`-homotopy zigzag relations and their opposite-simplicial reformulations.

Source/core/bridge triage:
- `source-facing`: the conerve retraction of a split monomorphism and the induced homotopy to the
  identity in `CosimplicialObject.DeltaOneHomotopic`;
- `core/canonical`: `Arrow.augmentedCechConerve`, `Arrow.mapAugmentedCechConerve`, and the split
  epimorphism homotopy owner `cechNerveSectionEndomorphism_homotopic_id` on the Čech-nerve side;
- `bridge/view`: passage from the split-epi Čech nerve in `Cᵒᵖ` to the opposite simplicial object
  of the Čech conerve in `C`, expressed by `NatTrans.op` together with
  `CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`. -/

private def cechConerveSectionEndomorphismArrowHom (hs : f ≫ s = 𝟙 X) :
    Arrow.mk f ⟶ Arrow.mk f :=
  Arrow.homMk (𝟙 X) (s ≫ f)
    (by simpa [Category.assoc] using (congrArg (fun k ↦ k ≫ f) hs).symm)

/-- The endomorphism of the Čech conerve of `f` induced by the retraction idempotent `s ≫ f`. -/
def cechConerveSectionEndomorphism (hs : f ≫ s = 𝟙 X) :
    (Arrow.mk f).cechConerve ⟶ (Arrow.mk f).cechConerve :=
  Arrow.mapCechConerve (cechConerveSectionEndomorphismArrowHom f s hs)

/-- The degreewise map from the Čech conerve of `f` to the constant cosimplicial object on `X`
induced by the chosen section `s`. -/
private def cechConerveRetractionApp (hs : f ≫ s = 𝟙 X) (n : SimplexCategory) :
    ((Arrow.mk f).cechConerve.obj n) ⟶ X :=
  WidePushout.desc (𝟙 X) (fun _ : Fin (n.len + 1) ↦ s) (fun _ ↦ hs)

-- Proof sketch: both composites out of the degree-`n` wide pushout agree on the head component
-- and on every `Y`-factor, so the universal property of the target wide pushout identifies them.
/-- The degreewise retraction maps assemble into a morphism of cosimplicial objects. -/
private theorem cechConerveRetraction_naturality (hs : f ≫ s = 𝟙 X)
    {n m : SimplexCategory} (α : n ⟶ m) :
    ((Arrow.mk f).cechConerve).map α ≫ cechConerveRetractionApp f s hs m =
      cechConerveRetractionApp f s hs n ≫ ((CosimplicialObject.const C).obj X).map α := sorry

/-- The canonical retraction from the Čech conerve of `f` to the constant cosimplicial object on
`X`, induced by the chosen section `s`. -/
def cechConerveRetraction (hs : f ≫ s = 𝟙 X) :
    (Arrow.mk f).cechConerve ⟶ (CosimplicialObject.const C).obj X :=
  { app := cechConerveRetractionApp f s hs
    naturality := fun _ _ α ↦ cechConerveRetraction_naturality f s hs α }

private def cechConerveRetractionAugmented (hs : f ≫ s = 𝟙 X) :
    (Arrow.mk f).augmentedCechConerve ⟶ (CosimplicialObject.Augmented.const).obj X where
  left := 𝟙 X
  right := cechConerveRetraction f s hs
  w := by
    ext n
    let _ : HasWidePushout (Arrow.mk f).left (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).right)
        (fun _ ↦ (Arrow.mk f).hom) := inferInstance
    simpa [cechConerveRetraction, cechConerveRetractionApp] using
      (WidePushout.head_desc (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom)
        (𝟙 X) (fun _ ↦ s) (fun _ ↦ hs)).symm

omit [∀ n : ℕ, HasWidePushout (Arrow.mk f).left
  (fun _ : Fin (n + 1) ↦ (Arrow.mk f).right) (fun _ ↦ (Arrow.mk f).hom)] in
private theorem cechConerveSectionEndomorphism_opposite_splitEpi (hs : f ≫ s = 𝟙 X) :
    s.op ≫ f.op = 𝟙 (op X) := by
  simpa using congrArg Quiver.Hom.op hs

private def oppositeCechNerveSectionEndomorphism
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (hs : f ≫ s = 𝟙 X) :
    (Arrow.mk f.op).cechNerve ⟶ (Arrow.mk f.op).cechNerve :=
  Arrow.mapCechNerve
    (Arrow.homMk (f.op ≫ s.op) (𝟙 (op X))
      (by
        simpa [Category.assoc] using
          congrArg (fun k ↦ f.op ≫ k)
            (cechConerveSectionEndomorphism_opposite_splitEpi f s hs)))

private theorem cechConerve_opposite_hasWidePullback (n : ℕ) :
    HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom) := by
  let F : WidePullbackShape (Fin (n + 1)) ⥤ Cᵒᵖ :=
    WidePullbackShape.wideCospan (op X) (fun _ : Fin (n + 1) ↦ op Y) (fun _ ↦ f.op)
  let G : WidePushoutShape (Fin (n + 1)) ⥤ C :=
    (widePullbackShapeOpEquiv (Fin (n + 1))).symm.functor ⋙ F.leftOp
  letI : HasColimit (WidePushoutShape.wideSpan X (fun _ : Fin (n + 1) ↦ Y) (fun _ ↦ f)) := by
    change HasWidePushout (Arrow.mk f).left
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f).right) (fun _ ↦ (Arrow.mk f).hom)
    infer_instance
  letI : HasColimit G := by
    let e : G ≅ WidePushoutShape.wideSpan X (fun _ : Fin (n + 1) ↦ Y) (fun _ ↦ f) := by
      simpa [G, F] using WidePushoutShape.diagramIsoWideSpan G
    exact hasColimit_of_iso e
  letI : HasColimit F.leftOp :=
    hasColimit_of_equivalence_comp (widePullbackShapeOpEquiv (Fin (n + 1))).symm
  exact hasLimit_of_hasColimit_leftOp F

private theorem cechConerveSectionEndomorphism_homotopic_id_type
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (hs : f ≫ s = 𝟙 X) :
    CosimplicialObject.DeltaOneHomotopy
      (NatTrans.unop (oppositeCechNerveSectionEndomorphism f s hs))
      (NatTrans.unop (𝟙 ((Arrow.mk f.op).cechNerve))) =
    CosimplicialObject.DeltaOneHomotopy
      (cechConerveSectionEndomorphism f s hs)
      (𝟙 ((Arrow.mk f).cechConerve)) := by
  sorry

/-- Lemma 14.28.5: if `f : X ⟶ Y` admits a section `s`, then the endomorphism of the Čech
conerve of `f` induced by the idempotent `s ≫ f` is connected to the identity by actual
`Δ[1]`-homotopy data. -/
def cechConerveSectionEndomorphism_homotopic_id (hs : f ≫ s = 𝟙 X) :
    CosimplicialObject.DeltaOneHomotopy
      (cechConerveSectionEndomorphism f s hs)
      (𝟙 ((Arrow.mk f).cechConerve)) := by
  letI (n : ℕ) : HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom) :=
    cechConerve_opposite_hasWidePullback f n
  let H :
      SimplicialObject.Homotopy
        (oppositeCechNerveSectionEndomorphism f s hs)
        (𝟙 ((Arrow.mk f.op).cechNerve)) := by
    simpa [oppositeCechNerveSectionEndomorphism] using
      cechNerveSectionEndomorphism_homotopic_id f.op s.op
        (cechConerveSectionEndomorphism_opposite_splitEpi f s hs)
  let K :=
    (CosimplicialObject.DeltaOneHomotopy.equivOppositeSimplicialHomotopy
      (NatTrans.unop (oppositeCechNerveSectionEndomorphism f s hs))
      (NatTrans.unop (𝟙 ((Arrow.mk f.op).cechNerve)))).symm H
  exact cast (cechConerveSectionEndomorphism_homotopic_id_type f s hs) K

/-- Companion reformulation of Lemma 14.28.5 in the source-facing zigzag relation. -/
theorem cechConerveSectionEndomorphism_deltaOneHomotopic_id (hs : f ≫ s = 𝟙 X) :
    CosimplicialObject.DeltaOneHomotopic
      (cechConerveSectionEndomorphism f s hs)
      (𝟙 ((Arrow.mk f).cechConerve)) :=
  CosimplicialObject.DeltaOneHomotopic.of_homotopy
    (cechConerveSectionEndomorphism_homotopic_id f s hs)

/-- Companion reformulation of Lemma 14.28.5 on the opposite simplicial zigzag relation. -/
theorem cechConerveSectionEndomorphism_opposite_homotopic_id (hs : f ≫ s = 𝟙 X) :
    SimplicialObject.Homotopic
      (NatTrans.op (cechConerveSectionEndomorphism f s hs))
      (NatTrans.op (𝟙 ((Arrow.mk f).cechConerve))) := by
  exact
    (CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
      (cechConerveSectionEndomorphism f s hs)
      (𝟙 ((Arrow.mk f).cechConerve))).1
      (cechConerveSectionEndomorphism_deltaOneHomotopic_id f s hs)

-- Proof sketch: the retraction is the right component of an augmented morphism to the constant
-- augmented cosimplicial object whose left component is `𝟙 X`, so the compatibility square gives
-- the desired identity after forgetting the augmentation.
/-- The canonical retraction induced by a section of `f` is a left inverse to the coaugmentation
of the Čech conerve. -/
theorem cechConerveCoaugmentation_comp_retraction (hs : f ≫ s = 𝟙 X) :
    (Arrow.mk f).augmentedCechConerve.hom ≫ cechConerveRetraction f s hs =
      𝟙 ((CosimplicialObject.const C).obj X) := by
  simpa using (cechConerveRetractionAugmented f s hs).w.symm

-- Proof sketch: first identify the composite
-- `cechConerveRetraction f s hs ≫ (Arrow.mk f).augmentedCechConerve.hom` with the canonical
-- `cechConerveSectionEndomorphism f s hs`; then apply
-- `cechConerveSectionEndomorphism_homotopic_id`.
theorem cechConerveRetraction_comp_coaugmentation_eq_sectionEndomorphism
    (hs : f ≫ s = 𝟙 X) :
    cechConerveRetraction f s hs ≫ (Arrow.mk f).augmentedCechConerve.hom =
      cechConerveSectionEndomorphism f s hs := sorry

/-- The Čech conerve of a split monomorphism is a cosimplicial retract of the constant
cosimplicial object on the source, so the resulting endomorphism carries actual `Δ[1]`-homotopy
data to the identity. -/
def cechConerveRetraction_comp_coaugmentation_homotopic_id
    (hs : f ≫ s = 𝟙 X) :
    CosimplicialObject.DeltaOneHomotopy
      (cechConerveRetraction f s hs ≫ (Arrow.mk f).augmentedCechConerve.hom)
      (𝟙 ((Arrow.mk f).cechConerve)) := by
  exact
    (cechConerveRetraction_comp_coaugmentation_eq_sectionEndomorphism f s hs) ▸
      cechConerveSectionEndomorphism_homotopic_id f s hs

/-- Companion reformulation of the preceding result in the source-facing zigzag relation. -/
theorem cechConerveRetraction_comp_coaugmentation_deltaOneHomotopic_id
    (hs : f ≫ s = 𝟙 X) :
    CosimplicialObject.DeltaOneHomotopic
      (cechConerveRetraction f s hs ≫ (Arrow.mk f).augmentedCechConerve.hom)
      (𝟙 ((Arrow.mk f).cechConerve)) :=
  CosimplicialObject.DeltaOneHomotopic.of_homotopy
    (cechConerveRetraction_comp_coaugmentation_homotopic_id f s hs)

/-- Companion reformulation of the preceding result on the opposite simplicial homotopy owner. -/
theorem cechConerveRetraction_comp_coaugmentation_opposite_homotopic_id
    (hs : f ≫ s = 𝟙 X) :
    SimplicialObject.Homotopic
      (NatTrans.op
        (cechConerveRetraction f s hs ≫ (Arrow.mk f).augmentedCechConerve.hom))
      (NatTrans.op (𝟙 ((Arrow.mk f).cechConerve))) := by
  exact
    (CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
      (cechConerveRetraction f s hs ≫ (Arrow.mk f).augmentedCechConerve.hom)
      (𝟙 ((Arrow.mk f).cechConerve))).1
      (cechConerveRetraction_comp_coaugmentation_deltaOneHomotopic_id f s hs)

end CategoryTheory
