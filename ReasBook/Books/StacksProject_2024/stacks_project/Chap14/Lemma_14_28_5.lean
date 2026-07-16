import Mathlib
import StacksProject_2024.stacks_project.Chap14.Lemma_14_26_9
import StacksProject_2024.stacks_project.Chap14.Lemma_14_28_3

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

/-- Helper for Lemma 14.28.5: every structure map of the constant cosimplicial object on `X` is
the identity on `X`. -/
private theorem constCosimplicial_map_eq_id {n m : SimplexCategory} (α : n ⟶ m) :
    ((CosimplicialObject.const C).obj X).map α = 𝟙 X :=
  rfl

-- Proof sketch: both composites out of the degree-`n` wide pushout agree on the head component
-- and on every `Y`-factor, so the universal property of the target wide pushout identifies them.
/-- The degreewise retraction maps assemble into a morphism of cosimplicial objects. -/
private theorem cechConerveRetraction_naturality (hs : f ≫ s = 𝟙 X)
    {n m : SimplexCategory} (α : n ⟶ m) :
    ((Arrow.mk f).cechConerve).map α ≫ cechConerveRetractionApp f s hs m =
      cechConerveRetractionApp f s hs n ≫ ((CosimplicialObject.const C).obj X).map α := by
  -- TODO: precompose with each coprojection and the head map; both sides reduce to `s` and `𝟙 X`
  -- respectively after one use of `Arrow.cechConerve_map`.
  sorry

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

/-- Helper for Lemma 14.28.5: the degree-`n` comparison map from the chosen Čech-conerve term to
the unopposed opposite Čech-nerve term is the wide-pushout map determined by the opposite
wide-pullback legs. -/
private noncomputable def unop_opposite_cechNerve_component_hom
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) :
    ((Arrow.mk f).cechConerve.obj n) ⟶ (Functor.unop ((Arrow.mk f.op).cechNerve)).obj n :=
  WidePushout.desc
    (Quiver.Hom.unop
      (WidePullback.base (B := (Arrow.mk f.op).right)
        (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
        (arrows := fun _ ↦ (Arrow.mk f.op).hom)))
    (fun j ↦
      Quiver.Hom.unop
        (WidePullback.π (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom) j))
    (fun j ↦ by
      -- Proof comment: unop the opposite wide-pullback relation `π_j ≫ f.op = base`.
      exact congrArg Quiver.Hom.unop
        (WidePullback.π_arrow (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom) (j := j)))

/-- Helper for Lemma 14.28.5: the inverse degree-`n` comparison map is obtained by op-ing the
Čech-conerve coprojections into a wide-pullback lift on the opposite side. -/
private noncomputable def unop_opposite_cechNerve_component_inv
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) :
    (Functor.unop ((Arrow.mk f.op).cechNerve)).obj n ⟶ ((Arrow.mk f).cechConerve.obj n) :=
  Quiver.Hom.unop <|
    WidePullback.lift
      (B := (Arrow.mk f.op).right)
      (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
      (arrows := fun _ ↦ (Arrow.mk f.op).hom)
      (WidePushout.head (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom)).op
      (fun j ↦ (WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) j).op)
      (fun j ↦ by
        -- Proof comment: op the Čech-conerve relation `f ≫ ι_j = head`.
        simpa using
          congrArg Quiver.Hom.op
            (WidePushout.arrow_ι (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) j))

/-- Helper for Lemma 14.28.5: the forward comparison map sends each branch coprojection to the
corresponding opposite Čech-nerve projection. -/
private theorem unop_opposite_cechNerve_component_hom_ι
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) j ≫
        unop_opposite_cechNerve_component_hom f n =
      Quiver.Hom.unop
        (WidePullback.π (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom) j) := by
  -- TODO: unfold `unop_opposite_cechNerve_component_hom` and read off the branch formula of
  -- `WidePushout.desc`.
  sorry

/-- Helper for Lemma 14.28.5: the forward comparison map sends the head coprojection to the
opposite Čech-nerve base morphism. -/
private theorem unop_opposite_cechNerve_component_hom_head
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) :
    WidePushout.head (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) ≫
        unop_opposite_cechNerve_component_hom f n =
      Quiver.Hom.unop
        (WidePullback.base (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom)) := by
  -- TODO: unfold `unop_opposite_cechNerve_component_hom` and read off the head formula of
  -- `WidePushout.desc`.
  sorry

/-- Helper for Lemma 14.28.5: precomposing the inverse comparison map with the opposite base leg
recovers the Čech-conerve head coprojection. -/
private theorem unop_opposite_cechNerve_component_inv_head
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) :
    Quiver.Hom.unop
        (WidePullback.base (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom)) ≫
        unop_opposite_cechNerve_component_inv f n =
      WidePushout.head (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) := by
  -- Proof comment: after op-ing the goal, this is `WidePullback.lift_base`.
  apply Quiver.Hom.op_inj
  simp [unop_opposite_cechNerve_component_inv, WidePullback.lift_base]

/-- Helper for Lemma 14.28.5: precomposing the inverse comparison map with the opposite branch
leg recovers the corresponding Čech-conerve coprojection. -/
private theorem unop_opposite_cechNerve_component_inv_ι
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    Quiver.Hom.unop
        (WidePullback.π (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom) j) ≫
        unop_opposite_cechNerve_component_inv f n =
      WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) j := by
  -- Proof comment: after op-ing the goal, this is `WidePullback.lift_π`.
  apply Quiver.Hom.op_inj
  simp [unop_opposite_cechNerve_component_inv, WidePullback.lift_π]

/-- Helper for Lemma 14.28.5: the forward and inverse degree-`n` comparison maps are mutually
inverse because they agree with the identity on the universal legs. -/
private theorem unop_opposite_cechNerve_component_hom_inv_id
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) :
    unop_opposite_cechNerve_component_hom f n ≫
        unop_opposite_cechNerve_component_inv f n =
      𝟙 ((Arrow.mk f).cechConerve.obj n) := by
  -- TODO: use `WidePushout.hom_ext`; after precomposing with each branch/head map, compose the
  -- already-proved formulas for `hom` and `inv`.
  sorry

/-- Helper for Lemma 14.28.5: the inverse and forward degree-`n` comparison maps are mutually
inverse; after op-ing, both endomorphisms of the opposite Čech-nerve term have the same
wide-pullback projections and base map. -/
private theorem unop_opposite_cechNerve_component_inv_hom_id
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) :
    unop_opposite_cechNerve_component_inv f n ≫
        unop_opposite_cechNerve_component_hom f n =
      𝟙 ((Functor.unop ((Arrow.mk f.op).cechNerve)).obj n) := by
  -- TODO: op the equality and use `WidePullback.hom_ext`; the projection and base checks are the
  -- opposites of the already-isolated `inv_*` and `hom_*` formulas.
  sorry

/-- Helper for Lemma 14.28.5: degreewise, the chosen Čech-conerve owner is canonically
isomorphic to the unopposed opposite Čech-nerve owner. -/
private noncomputable def unop_opposite_cechNerve_component_iso
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (n : SimplexCategory) :
    ((Arrow.mk f).cechConerve.obj n) ≅ (Functor.unop ((Arrow.mk f.op).cechNerve)).obj n :=
  { hom := unop_opposite_cechNerve_component_hom f n
    inv := unop_opposite_cechNerve_component_inv f n
    hom_inv_id := unop_opposite_cechNerve_component_hom_inv_id f n
    inv_hom_id := unop_opposite_cechNerve_component_inv_hom_id f n }

/-- Helper for Lemma 14.28.5: the degreewise comparison maps commute with every simplex
operator, so the objectwise bridge upgrades to a natural isomorphism of cosimplicial owners. -/
private theorem unop_opposite_cechNerve_component_hom_naturality
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    {n m : SimplexCategory} (α : n ⟶ m) :
    ((Arrow.mk f).cechConerve).map α ≫ (unop_opposite_cechNerve_component_iso f m).hom =
      (unop_opposite_cechNerve_component_iso f n).hom ≫
        (Functor.unop ((Arrow.mk f.op).cechNerve)).map α := by
  -- TODO: precompose with each `WidePushout.ι j` and `WidePushout.head`, then pass to opposites so
  -- the right-hand side becomes the explicit `Arrow.cechNerve_map α.op` formulas
  -- `WidePullback.lift_π` and `WidePullback.lift_base`.
  sorry

/-- Helper for Lemma 14.28.5: the degreewise comparison isomorphisms assemble into a natural
isomorphism from the Čech conerve to the unopposed opposite Čech nerve. -/
private noncomputable def unop_opposite_cechNerve_iso_cechConerve
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)] :
    (Arrow.mk f).cechConerve ≅ Functor.unop ((Arrow.mk f.op).cechNerve) :=
  NatIso.ofComponents
    (fun n ↦ unop_opposite_cechNerve_component_iso f n)
    (fun {_ _} α ↦ unop_opposite_cechNerve_component_hom_naturality (f := f) α)

/-- Helper for Lemma 14.28.5: the Čech-conerve section endomorphism carries each branch
coprojection by precomposing with `s ≫ f`. -/
@[reassoc]
private theorem cechConerveSectionEndomorphism_app_ι
    (hs : f ≫ s = 𝟙 X) (n : SimplexCategory) (j : Fin (n.len + 1)) :
    WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) j ≫
        (cechConerveSectionEndomorphism f s hs).app n =
      s ≫ f ≫ WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) j := by
  -- TODO: unfold `Arrow.mapCechConerve`; the `j`-th branch of its `WidePushout.desc` is exactly
  -- the right component `s ≫ f`.
  sorry

/-- Helper for Lemma 14.28.5: the Čech-conerve section endomorphism fixes the head map. -/
@[reassoc]
private theorem cechConerveSectionEndomorphism_app_head
    (hs : f ≫ s = 𝟙 X) (n : SimplexCategory) :
    WidePushout.head (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) ≫
        (cechConerveSectionEndomorphism f s hs).app n =
      WidePushout.head (fun _ : Fin (n.len + 1) ↦ (Arrow.mk f).hom) := by
  -- TODO: unfold `Arrow.mapCechConerve`; the head branch of its `WidePushout.desc` is the left
  -- component `𝟙 X`.
  sorry

/-- Helper for Lemma 14.28.5: after unop, the opposite Čech-nerve section endomorphism acts on
each projection by precomposing with `s ≫ f`. -/
@[reassoc]
private theorem unop_oppositeCechNerveSectionEndomorphism_app_π
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (hs : f ≫ s = 𝟙 X) (n : SimplexCategory) (j : Fin (n.len + 1)) :
    Quiver.Hom.unop
        (WidePullback.π (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom) j) ≫
        (NatTrans.unop (oppositeCechNerveSectionEndomorphism f s hs)).app n =
      s ≫ f ≫
        Quiver.Hom.unop
          (WidePullback.π (B := (Arrow.mk f.op).right)
            (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
            (arrows := fun _ ↦ (Arrow.mk f.op).hom) j) := by
  -- TODO: after applying `Quiver.Hom.op_inj`, unfold `Arrow.mapCechNerve` and read off the
  -- `WidePullback.lift_π` branch formula for the arrow endomorphism `(f.op ≫ s.op, 𝟙)`.
  sorry

/-- Helper for Lemma 14.28.5: after unop, the opposite Čech-nerve section endomorphism fixes the
base map. -/
@[reassoc]
private theorem unop_oppositeCechNerveSectionEndomorphism_app_base
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (hs : f ≫ s = 𝟙 X) (n : SimplexCategory) :
    Quiver.Hom.unop
        (WidePullback.base (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom)) ≫
        (NatTrans.unop (oppositeCechNerveSectionEndomorphism f s hs)).app n =
      Quiver.Hom.unop
        (WidePullback.base (B := (Arrow.mk f.op).right)
          (objs := fun _ : Fin (n.len + 1) ↦ (Arrow.mk f.op).left)
          (arrows := fun _ ↦ (Arrow.mk f.op).hom)) := by
  -- TODO: after applying `Quiver.Hom.op_inj`, unfold `Arrow.mapCechNerve` and read off the
  -- `WidePullback.lift_base` formula for the same arrow endomorphism.
  sorry

/-- Helper for Lemma 14.28.5: conjugating the transported opposite Čech-nerve section
endomorphism by the comparison isomorphism recovers the literal Čech-conerve section
endomorphism. -/
private theorem unop_oppositeCechNerveSectionEndomorphism_conj_eq_cechConerveSectionEndomorphism
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (hs : f ≫ s = 𝟙 X) :
    let e := unop_opposite_cechNerve_iso_cechConerve (f := f)
    e.hom ≫ NatTrans.unop (oppositeCechNerveSectionEndomorphism f s hs) ≫ e.inv =
      cechConerveSectionEndomorphism f s hs := by
  -- TODO: ext on degrees, then use `WidePushout.hom_ext`; the branch computation should use
  -- `unop_opposite_cechNerve_component_hom_ι`, `unop_oppositeCechNerveSectionEndomorphism_app_π`,
  -- `unop_opposite_cechNerve_component_inv_ι`, and `cechConerveSectionEndomorphism_app_ι`, while
  -- the head computation should use the corresponding base/head lemmas.
  sorry

/-- Helper for Lemma 14.28.5: transport the opposite Čech-nerve homotopy across the canonical
comparison between the opposite owner and the Čech conerve. -/
private def cechConerveSectionEndomorphism_homotopic_id_transport
    [∀ n : ℕ, HasWidePullback (Arrow.mk f.op).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f.op).left) (fun _ ↦ (Arrow.mk f.op).hom)]
    (hs : f ≫ s = 𝟙 X) :
    CosimplicialObject.DeltaOneHomotopy
      (NatTrans.unop (oppositeCechNerveSectionEndomorphism f s hs))
      (NatTrans.unop (𝟙 ((Arrow.mk f.op).cechNerve))) →
    CosimplicialObject.DeltaOneHomotopy
      (cechConerveSectionEndomorphism f s hs)
      (𝟙 ((Arrow.mk f).cechConerve)) :=
  -- Route correction: `Functor.unop ((Arrow.mk f.op).cechNerve)` and `(Arrow.mk f).cechConerve`
  -- are not definitionally equal. The objectwise comparison is now isolated in
  -- `unop_opposite_cechNerve_component_iso`; the remaining work is to package its naturality into
  -- a `NatIso`, conjugate the endpoints, and transport the `Δ[1]`-components across that `NatIso`.
  -- TODO: conjugate each `H.hom i` by `unop_opposite_cechNerve_iso_cechConerve`; the endpoint
  -- proofs should use `unop_oppositeCechNerveSectionEndomorphism_conj_eq_cechConerveSectionEndomorphism`
  -- and the `NatIso` identities, and the naturality proof should be the short `calc` built from
  -- `e.hom.naturality`, `(H.naturality σ i).w`, and `e.inv.naturality`.
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
  exact cechConerveSectionEndomorphism_homotopic_id_transport f s hs K

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
      cechConerveSectionEndomorphism f s hs := by
  -- TODO: work degreewise and use `WidePushout.hom_ext`; on the `Y`-branches both composites are
  -- `s ≫ head`, while the head branch is fixed.
  sorry

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
