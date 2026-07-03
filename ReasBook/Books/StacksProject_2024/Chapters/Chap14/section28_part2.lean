import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_28_5 (from Chap14) -/
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

/-! ### Lemma_14_28_6 (from Chap14) -/
open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 14.28.6:
- primary domain: simplicial/cosimplicial homotopy and the Dold-Kan comparison functors
  `alternatingCofaceMapComplex` and `normalizedCochainComplexFunctor`;
- sampled same-kind declarations:
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`,
  `CategoryTheory.CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`,
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`,
  `AlgebraicTopology.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
  `CategoryTheory.CosimplicialObject.normalizedCochainComplexFunctor`;
- best owner abstraction: the source-facing relation in this file is
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`; the opposite simplicial zigzag relation
  is only the bridge from Lemma 14.28.3, and the normalized complex owner in this chapter is
  `normalizedCochainComplexFunctor`;
- primitive data: directed `Δ[1]`-indexed cosimplicial homotopies and the canonical Moore-complex
  inclusion and retraction on the opposite simplicial side;
- derived API: the resulting existence of chain/cochain homotopies on the alternating and
  normalized complexes after passage through the opposite/unop bridges.

Source/core/bridge triage:
- `source-facing`: the two Stacks statements about homotopic cosimplicial maps inducing homotopic
  maps on `s(U)` and `Q(U)`;
- `core/canonical`: `DeltaOneHomotopic`, `toChainHomotopy`, and the Chapter 14 owner
  `normalizedCochainComplexFunctor`;
- `bridge/view`: `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, passage to opposite
  simplicial objects, and transport of chain homotopies through `HomologicalComplex.unopFunctor`.
  -/

section HomotopyTransport

variable [Preadditive A]
variable {K L : ChainComplex Aᵒᵖ ℕ} {f g : K ⟶ L}

/-- Transport a chain homotopy in `Aᵒᵖ` across `HomologicalComplex.unopFunctor` to the
corresponding cochain homotopy in `A`. This is the only local bridge theorem needed below. -/
private theorem unopFunctor_map_homotopy
    (h : _root_.Homotopy f g) :
    Nonempty
      (_root_.Homotopy
        ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map f.op)
        ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map g.op)) := by
  sorry

end HomotopyTransport

section AlternatingCofaceMapComplex

variable [Preadditive A]
variable {U V : CosimplicialObject A} {a b : U ⟶ V}

-- Proof sketch: transport the given `DeltaOneHomotopic` relation across
-- `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, apply
-- `SimplicialObject.alternatingFaceMapComplex_map_homotopic`, and identify the resulting chain
-- homotopy in `Aᵒᵖ` with the desired cochain homotopy on `alternatingCofaceMapComplex`.
/-- Lemma 14.28.6 (1): if two morphisms of cosimplicial objects in an additive category are
`Δ[1]`-homotopic, then the induced morphisms on the alternating coface map complexes
`s(U) ⟶ s(V)` are homotopic as maps of cochain complexes. -/
theorem alternatingCofaceMapComplex_map_homotopic
    (h : DeltaOneHomotopic a b) :
    Nonempty
      (_root_.Homotopy
        ((alternatingCofaceMapComplex A).map a)
        ((alternatingCofaceMapComplex A).map b)) := by
  rcases SimplicialObject.alternatingFaceMapComplex_map_homotopic
      ((deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag a b).1 h) with
    ⟨h'⟩
  have hunop :
      Nonempty
        (_root_.Homotopy
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((alternatingFaceMapComplex Aᵒᵖ).map (NatTrans.op a)).op)
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((alternatingFaceMapComplex Aᵒᵖ).map (NatTrans.op b)).op)) :=
    unopFunctor_map_homotopy h'
  sorry

end AlternatingCofaceMapComplex

section NormalizedCochainComplex

variable [Abelian A]
local instance : CategoryTheory.Limits.HasZeroObject Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasBinaryCoproducts Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasImages Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasCokernels (CochainComplex A ℕ) := inferInstance

variable {U V : CosimplicialObject A} {a b : U ⟶ V}

-- Proof sketch: transport the given `DeltaOneHomotopic` relation across
-- `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, apply
-- `SimplicialObject.normalizedMooreComplex_map_homotopic` in `Aᵒᵖ`, and transport the resulting
-- chain homotopy back to a cochain homotopy using `HomologicalComplex.unopFunctor`.
/-- Lemma 14.28.6 (2): if `A` is abelian and two morphisms of cosimplicial objects are homotopic,
then the induced morphisms on the normalized cochain complexes `Q(U) ⟶ Q(V)` are homotopic as
maps of cochain complexes. -/
theorem normalizedCochainComplex_map_homotopic
    (h : DeltaOneHomotopic a b) :
    Nonempty
      (_root_.Homotopy
        (normalizedCochainComplexFunctor.map a)
        (normalizedCochainComplexFunctor.map b)) := by
  rcases SimplicialObject.normalizedMooreComplex_map_homotopic
      ((deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag a b).1 h) with
    ⟨h'⟩
  have hunop :
      Nonempty
        (_root_.Homotopy
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((normalizedMooreComplex Aᵒᵖ).map (NatTrans.op a)).op)
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((normalizedMooreComplex Aᵒᵖ).map (NatTrans.op b)).op)) :=
    unopFunctor_map_homotopy h'
  sorry

end NormalizedCochainComplex

end CategoryTheory.CosimplicialObject

/-! ### Lemma_14_28_7 (from Chap14) -/
open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open scoped DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 14.28.7:
- primary domain: cosimplicial homotopy equivalences and the induced homotopy-equivalence
  property on the canonical cochain-complex functors `s` and `Q`;
- sampled same-kind owner declarations:
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`,
  `CategoryTheory.CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `HomologicalComplex.homotopyEquivalences`;
- best owner abstraction: the source-facing owner in this file should be the cosimplicial analogue
  of `SimplicialObject.HomotopyEquiv`, with primitive data given directly by a morphism, a chosen
  inverse, and two `DeltaOneHomotopic` witnesses; `NatTrans.op` is only the bridge/view to the
  already-canonical simplicial owner, while the target-side owner remains
  `HomologicalComplex.homotopyEquivalences`;
- primitive-vs-derived split:
  primitive data are the forward map, inverse map, and the two `DeltaOneHomotopic` witnesses on
  the cosimplicial side;
  derived API is the morphism property `IsHomotopyEquivalence`, its bridge to the opposite
  simplicial owner, and the induced cochain-level homotopy-equivalence property.

Source/core/bridge triage:
- `source-facing`: the two Stacks lemmas on cosimplicial homotopy equivalences;
- `core/canonical`: `CosimplicialObject.HomotopyEquiv`, `CosimplicialObject.IsHomotopyEquivalence`,
  `SimplicialObject.IsHomotopyEquivalence`, and
  `HomologicalComplex.homotopyEquivalences`;
- `bridge/view`: `NatTrans.op` between cosimplicial and simplicial morphisms. -/

/-- A homotopy equivalence between cosimplicial objects consists of a morphism, a chosen inverse,
and zigzag `Δ[1]`-homotopies from the two composites to the corresponding identities. -/
@[ext]
structure HomotopyEquiv (U V : CosimplicialObject A) where
  hom : U ⟶ V
  inv : V ⟶ U
  homotopyHomInvId : DeltaOneHomotopic (hom ≫ inv) (𝟙 U)
  homotopyInvHomId : DeltaOneHomotopic (inv ≫ hom) (𝟙 V)

variable (A) in
/-- The morphism property on cosimplicial objects given by cosimplicial homotopy equivalences. -/
def homotopyEquivalences : MorphismProperty (CosimplicialObject A) :=
  fun U V a ↦ ∃ e : HomotopyEquiv U V, e.hom = a

/-- A morphism of cosimplicial objects is a homotopy equivalence if it is the forward map of a
cosimplicial homotopy equivalence. -/
abbrev IsHomotopyEquivalence {U V : CosimplicialObject A} (a : U ⟶ V) : Prop :=
  homotopyEquivalences A a

namespace HomotopyEquiv

variable {U V : CosimplicialObject A}

/-- The forward morphism of a cosimplicial homotopy equivalence is a morphism-level homotopy
equivalence. -/
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    IsHomotopyEquivalence e.hom :=
  ⟨e, rfl⟩

end HomotopyEquiv

/-- A morphism of cosimplicial objects is a homotopy equivalence exactly when its opposite
simplicial morphism is one. -/
theorem isHomotopyEquivalence_iff_op
    {U V : CosimplicialObject A} (a : U ⟶ V) :
    IsHomotopyEquivalence a ↔
      SimplicialObject.IsHomotopyEquivalence (NatTrans.op a) := by
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨{
      hom := NatTrans.op e.hom
      inv := NatTrans.op e.inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_
    }, rfl⟩
    · simpa using
        (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
          (e.inv ≫ e.hom) (𝟙 V)).1 e.homotopyInvHomId
    · simpa using
        (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
          (e.hom ≫ e.inv) (𝟙 U)).1 e.homotopyHomInvId
  · rintro ⟨e, he⟩
    refine ⟨{
      hom := a
      inv := NatTrans.unop e.inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_
    }, rfl⟩
    · apply (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
        (a ≫ NatTrans.unop e.inv) (𝟙 U)).2
      simpa [he] using e.homotopyInvHomId
    · apply (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
        (NatTrans.unop e.inv ≫ a) (𝟙 V)).2
      simpa [he] using e.homotopyHomInvId

section AlternatingCofaceMapComplex

variable [Preadditive A]
variable {U V : CosimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

/-- A cosimplicial homotopy equivalence induces a homotopy equivalence on alternating coface map
complexes. -/
theorem alternatingCofaceMapComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      ((alternatingCofaceMapComplex A).map e.hom) := by
  classical
  let h :
      _root_.HomotopyEquiv
        ((alternatingCofaceMapComplex A).obj U)
        ((alternatingCofaceMapComplex A).obj V) := {
      hom := (alternatingCofaceMapComplex A).map e.hom
      inv := (alternatingCofaceMapComplex A).map e.inv
      homotopyHomInvId := by
        simpa using Classical.choice (alternatingCofaceMapComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        simpa using Classical.choice (alternatingCofaceMapComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a source-facing cosimplicial homotopy equivalence whose forward morphism is
-- `a`, then apply Lemma 14.28.6 (1) to the two `DeltaOneHomotopic` fields in that witness.
/-- Lemma 14.28.7 (1): if `a` is a homotopy equivalence of cosimplicial objects, then the induced
morphism on alternating coface map complexes `s(a) : s(U) ⟶ s(V)` is a homotopy equivalence of
cochain complexes. -/
theorem alternatingCofaceMapComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      ((alternatingCofaceMapComplex A).map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.alternatingCofaceMapComplex_map_isHomotopyEquivalence

end AlternatingCofaceMapComplex

section NormalizedCochainComplex

variable [Abelian A]
local instance : CategoryTheory.Limits.HasZeroObject Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasBinaryCoproducts Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasImages Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasCokernels (CochainComplex A ℕ) := inferInstance
variable {U V : CosimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

/-- In an abelian category, a cosimplicial homotopy equivalence induces a homotopy equivalence on
normalized cochain complexes. -/
theorem normalizedCochainComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      (normalizedCochainComplexFunctor.map e.hom) := by
  classical
  let h :
      _root_.HomotopyEquiv (Q(U)) (Q(V)) := {
      hom := normalizedCochainComplexFunctor.map e.hom
      inv := normalizedCochainComplexFunctor.map e.inv
      homotopyHomInvId := by
        simpa only [Functor.map_comp, Functor.map_id] using
          Classical.choice (normalizedCochainComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        simpa only [Functor.map_comp, Functor.map_id] using
          Classical.choice (normalizedCochainComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a source-facing cosimplicial homotopy equivalence whose forward morphism is
-- `a`, then apply Lemma 14.28.6 (2) to the two `DeltaOneHomotopic` fields in that witness.
/-- Lemma 14.28.7 (2): if `A` is abelian and `a` is a homotopy equivalence of cosimplicial
objects, then the induced morphism `Q(a) : Q(U) ⟶ Q(V)` is a homotopy equivalence of cochain
complexes. -/
theorem normalizedCochainComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      (normalizedCochainComplexFunctor.map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.normalizedCochainComplex_map_isHomotopyEquivalence

end NormalizedCochainComplex

end CategoryTheory.CosimplicialObject
