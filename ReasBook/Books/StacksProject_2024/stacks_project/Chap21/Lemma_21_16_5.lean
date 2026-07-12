import StacksProject_2024.Chap07.Lemma_7_18_4
import StacksProject_2024.Chap19.Theorem_19_7_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe uI uC vC

namespace CategoryTheory

open CofilteredSiteDiagram

/- Domain-style sampling for Lemma 21.16.5:
- primary domain: compatible inverse systems of abelian sheaves on a cofiltered inverse system of
  sites, together with a stagewise monomorphism into an injective inverse system;
- sampled owner declarations:
  `CofilteredSiteDiagram.StageFamily`,
  `CofilteredSiteDiagram.StageFamily.Hom`,
  `Injective`,
  `Mono`;
- best owner abstraction: `CofilteredSiteDiagram.StageFamily S A`;
- primitive data: the stage sheaves and pullback transition morphisms;
- derived API: morphisms of stage families together with the stagewise mono/injective predicates.

Source/core/bridge triage:
- `source-facing`: Lemma 21.16.5, asserting existence of a stagewise monomorphism into an
  injective inverse system of abelian sheaves;
- `core/canonical`: the generic compatible-family owner `CofilteredSiteDiagram.StageFamily`;
- `bridge/view`: a morphism `StageFamily.Hom F G` together with stagewise `Injective` and `Mono`
  predicates on its target and components.
-/

-- Proof sketch: choose for each stage an injective embedding `F.obj i ⟶ A_i`, then form the
-- product over all arrows `b : k ⟶ i` of the pushforwards `f_{b,*} A_k`. The adjoints of the
-- composites `f_b^{-1} F_i ⟶ F_k ⟶ A_k` give a componentwise monomorphism into this product, and
-- the canonical pullback-pushforward comparison maps make the targets into a compatible inverse
-- system. Exactness of stage pushforwards preserves injectives, so each stage of the target system
-- is injective.
/-- Helper for Lemma 21.16.5: the hom part of the stage pullback composition isomorphism is
natural in assoc-normal form. -/
private theorem stageSheafPullbackCompIso_hom_naturality_assoc
    (S : CofilteredSiteDiagram.{uI, uC, vC}) {A : Type*} [Category A]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    [HasWeakSheafify (S.stageTopology j) A]
    [HasWeakSheafify (S.stageTopology k) A]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ F : (S.stage j)ᵒᵖ ⥤ A, (S.stageFunctor b).op.HasLeftKanExtension F]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor (b ≫ a)).op.HasLeftKanExtension F]
    {X Y : Sheaf (S.stageTopology i) A} (e : X ⟶ Y) :
    ((S.stageFunctor b).sheafPullback A
        (S.stageTopology j) (S.stageTopology k)).map
        (((S.stageFunctor a).sheafPullback A
          (S.stageTopology i) (S.stageTopology j)).map e) ≫
      (S.stageSheafPullbackCompIso A a b).hom.app Y =
        (S.stageSheafPullbackCompIso A a b).hom.app X ≫
          ((S.stageFunctor (b ≫ a)).sheafPullback A
            (S.stageTopology i) (S.stageTopology k)).map e := by
  -- This is the ordinary naturality square, rewritten to expose the composite pullback map.
  simpa [Functor.comp_map] using
    ((S.stageSheafPullbackCompIso A a b).hom.naturality e)

/-- Helper for Lemma 21.16.5: the chosen injective envelope map on each stage sheaf. -/
private abbrev stageInjectiveEmbedding
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) (i : S.I) :
    F.obj i ⟶ HasFunctorialInjectiveEmbeddings.under (F.obj i) :=
  HasFunctorialInjectiveEmbeddings.ι (F.obj i)

/-- Helper for Lemma 21.16.5: the stage functor on an identity arrow is definitionally the
identity functor. -/
private theorem stageFunctor_id_eq
    (S : CofilteredSiteDiagram.{uI, uC, vC}) (i : S.I) :
    S.stageFunctor (𝟙 i) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (S.diagram.map_id (op i))

/-- Helper for Lemma 21.16.5: the stage functor of a composite arrow is the corresponding
composite of stage functors. -/
private theorem stageFunctor_comp_eq
    (S : CofilteredSiteDiagram.{uI, uC, vC})
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor (b ≫ a) = S.stageFunctor a ⋙ S.stageFunctor b :=
  congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op)

/-- Helper for Lemma 21.16.5: every stage pullback functor on abelian sheaves preserves
monomorphisms. -/
private theorem stagePullbackPreservesMonomorphisms
    (S : CofilteredSiteDiagram.{uI, uC, vC}) {i j : S.I} (a : j ⟶ i)
    [HasWeakSheafify (S.stageTopology j) AddCommGrpCat.{max uC vC}]
    [∀ H : (S.stage i)ᵒᵖ ⥤ AddCommGrpCat.{max uC vC},
      (S.stageFunctor a).op.HasLeftKanExtension H] :
    (((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j))).PreservesMonomorphisms := by
  -- Proof comment: finite-limit preservation of the pullback functor is the owner bridge;
  -- preservation of pullbacks then gives preservation of monomorphisms.
  let _ :
      PreservesFiniteLimits
        ((S.stageFunctor a).op.lan :
          ((S.stage i)ᵒᵖ ⥤ AddCommGrpCat.{max uC vC}) ⥤
            (S.stage j)ᵒᵖ ⥤ AddCommGrpCat.{max uC vC}) :=
    inferInstance
  let _ :
      PreservesFiniteLimits
        ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
          (S.stageTopology i) (S.stageTopology j)) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits
      (S.stageFunctor a) AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)
  let _ :
      PreservesLimitsOfShape WalkingCospan
        ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
          (S.stageTopology i) (S.stageTopology j)) :=
    inferInstance
  infer_instance

/-- Helper for Lemma 21.16.5: each stage pushforward functor on abelian sheaves preserves
injective objects. -/
private theorem stagePushforwardPreservesInjectiveObjects
    (S : CofilteredSiteDiagram.{uI, uC, vC}) {i j : S.I} (a : j ⟶ i)
    [HasWeakSheafify (S.stageTopology j) AddCommGrpCat.{max uC vC}]
    [∀ H : (S.stage i)ᵒᵖ ⥤ AddCommGrpCat.{max uC vC},
      (S.stageFunctor a).op.HasLeftKanExtension H] :
    (((S.stageFunctor a).sheafPushforwardContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j))).PreservesInjectiveObjects := by
  let P :=
    (S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)
  let _ : P.PreservesMonomorphisms :=
    stagePullbackPreservesMonomorphisms (S := S) a
  -- The stage pushforward is right adjoint to pullback, so it inherits injective preservation
  -- from the monomorphism-preserving left adjoint.
  simpa [P] using
    (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      ((S.stageFunctor a).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
        (S.stageTopology i) (S.stageTopology j)))

/-- Helper for Lemma 21.16.5: the identity transition pushforward is canonically the identity
functor on stagewise abelian sheaves. -/
private noncomputable def stagePushforwardIdIso
    (S : CofilteredSiteDiagram.{uI, uC, vC}) (i : S.I) :
    ((S.stageFunctor (𝟙 i)).sheafPushforwardContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology i)) ≅ 𝟭 _ := by
  let e := eqToIso (stageFunctor_id_eq S i)
  -- Proof comment: specialize the owner-level identity comparison to the stage functor.
  simpa using
    (Functor.sheafPushforwardContinuousId' e
      AddCommGrpCat.{max uC vC} (S.stageTopology i))

/-- Helper for Lemma 21.16.5: stage pushforwards compose canonically along composable transition
arrows. -/
private noncomputable def stagePushforwardCompIso
    (S : CofilteredSiteDiagram.{uI, uC, vC})
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    ((S.stageFunctor b).sheafPushforwardContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology j) (S.stageTopology k)) ⋙
        ((S.stageFunctor a).sheafPushforwardContinuous AddCommGrpCat.{max uC vC}
          (S.stageTopology i) (S.stageTopology j)) ≅
      ((S.stageFunctor (b ≫ a)).sheafPushforwardContinuous AddCommGrpCat.{max uC vC}
        (S.stageTopology i) (S.stageTopology k)) := by
  let e := eqToIso (stageFunctor_comp_eq S a b)
  -- Proof comment: this is the stagewise specialization of the generic pushforward-composition
  -- comparison for continuous functors.
  simpa using
    (Functor.sheafPushforwardContinuousComp' e.symm
      AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j) (S.stageTopology k))

/-- Helper for Lemma 21.16.5: the `B`-indexed factor of the target product at stage `i`. -/
private noncomputable abbrev stageInjectiveProductFactor
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) {i : S.I} (B : Over i) :
    Sheaf (S.stageTopology i) AddCommGrpCat.{max uC vC} :=
  ((S.stageFunctor B.hom).sheafPushforwardContinuous AddCommGrpCat.{max uC vC}
    (S.stageTopology i) (S.stageTopology B.left)).obj
      (HasFunctorialInjectiveEmbeddings.under (F.obj B.left))

/-- Helper for Lemma 21.16.5: each `B`-indexed pushforward factor is injective. -/
private theorem stageInjectiveProductFactor_injective
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) {i : S.I} (B : Over i) :
    Injective (stageInjectiveProductFactor F B) := by
  let u :=
    (S.stageFunctor B.hom).sheafPushforwardContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology B.left)
  let _ : u.PreservesInjectiveObjects :=
    stagePushforwardPreservesInjectiveObjects (S := S) B.hom
  -- Proof comment: push forward the chosen injective envelope on `B.left`.
  simpa [stageInjectiveProductFactor, u] using
    (u.injective_obj_of_injective
      (HasFunctorialInjectiveEmbeddings.under_injective (F.obj B.left)))

/-- Helper for Lemma 21.16.5: the stagewise target object is the product of all injective
pushforward factors over `Over i`. -/
private noncomputable abbrev stageInjectiveProductObject
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) (i : S.I) :
    Sheaf (S.stageTopology i) AddCommGrpCat.{max uC vC} :=
  ∏ᶜ fun B : Over i ↦ stageInjectiveProductFactor F B

/-- Helper for Lemma 21.16.5: each stagewise target product is injective. -/
private theorem stageInjectiveProductObject_injective
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) (i : S.I) :
    Injective (stageInjectiveProductObject F i) := by
  let _ : ∀ B : Over i, Injective (stageInjectiveProductFactor F B) :=
    fun B ↦ stageInjectiveProductFactor_injective F B
  -- Proof comment: products of injective objects are injective in the sheaf category.
  simpa [stageInjectiveProductObject] using
    (inferInstance :
      Injective (∏ᶜ fun B : Over i ↦ stageInjectiveProductFactor F B))

/-- Helper for Lemma 21.16.5: a mate of `Adjunction.leftAdjointIdIso` written in morphism form. -/
private theorem mateLeftAdjointIdIso_hom
    {C : Type*} [Category C] {L R : C ⥤ C} (adj : L ⊣ R) (e : R ≅ 𝟭 C)
    {X Y : C} (h : X ⟶ Y) :
    (adj.homEquiv X Y).symm (h ≫ e.inv.app Y) =
      (adj.leftAdjointIdIso e).hom.app X ≫ h := by
  -- Proof comment: move the statement across the adjunction, identify the mate of the identity
  -- comparison by `unit_conjugateEquiv`, and finish with the naturality of `e.inv`.
  apply (adj.homEquiv X Y).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
  have hmate :
      (adj.homEquiv X ((𝟭 C).obj X)) ((adj.leftAdjointIdIso e).hom.app X) = e.inv.app X := by
    let α : L ⟶ 𝟭 C := (adj.leftAdjointIdIso e).hom
    have hunit : adj.unit.app X ≫ R.map (α.app X) = e.inv.app X := by
      simpa [α] using (CategoryTheory.unit_conjugateEquiv Adjunction.id adj α X).symm
    have hhom :
        (adj.homEquiv X ((𝟭 C).obj X)) (α.app X) =
          adj.unit.app X ≫ R.map (α.app X) := by
      exact CategoryTheory.Adjunction.homEquiv_unit adj X ((𝟭 C).obj X) (α.app X)
    simpa [α] using hhom.trans hunit
  rw [hmate]
  simpa using NatTrans.naturality e.inv h

/-- Helper for Lemma 21.16.5: transporting an adjunction across a right natural isomorphism
postcomposes the transpose by that comparison map. -/
private theorem ofNatIsoRight_homEquiv_apply
    {C : Type*} [Category C] {D : Type*} [Category D]
    {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (e : R ≅ R')
    {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    ((adj.ofNatIsoRight e).homEquiv X Y) f =
      adj.homEquiv X Y f ≫ e.hom.app Y := by
  -- Proof comment: `ofNatIsoRight` changes only the right adjoint, so the transpose is the
  -- original one followed by the new right-side comparison.
  simp [Adjunction.homEquiv, Adjunction.ofNatIsoRight, Category.assoc]

/-- Helper for Lemma 21.16.5: the `B`-component of the canonical transition on the injective
product target. -/
private noncomputable def stageInjectiveProductTransitionComponent
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC})
    {i j : S.I} (a : j ⟶ i) (B : Over j) :
    ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)).obj
        (stageInjectiveProductObject F i) ⟶
      stageInjectiveProductFactor F B := by
  let adj :=
    (S.stageFunctor a).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)
  let B' : Over i := Over.mk (B.hom ≫ a)
  -- Proof comment: project to the composite-index factor and transport the target through the
  -- canonical pushforward-composition comparison before taking the adjoint mate.
  exact (adj.homEquiv _ _).symm
    (Pi.π (fun C : Over i ↦ stageInjectiveProductFactor F C) B' ≫
      (stagePushforwardCompIso S a B.hom).inv.app
        (HasFunctorialInjectiveEmbeddings.under (F.obj B.left)))

/-- Helper for Lemma 21.16.5: the canonical transition component is defined by the displayed
pushforward-side projection formula. -/
private theorem stageInjectiveProductTransitionComponent_homEquiv
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC})
    {i j : S.I} (a : j ⟶ i) (B : Over j) :
    let adj :=
      (S.stageFunctor a).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
        (S.stageTopology i) (S.stageTopology j)
    let B' : Over i := Over.mk (B.hom ≫ a)
    (adj.homEquiv _ _) (stageInjectiveProductTransitionComponent F a B) =
      Pi.π (fun C : Over i ↦ stageInjectiveProductFactor F C) B' ≫
        (stagePushforwardCompIso S a B.hom).inv.app
          (HasFunctorialInjectiveEmbeddings.under (F.obj B.left)) := by
  -- Proof comment: unfold the component definition and cancel the `homEquiv`/`symm` pair.
  dsimp [stageInjectiveProductTransitionComponent]
  rw [Equiv.apply_symm_apply]

/-- Helper for Lemma 21.16.5: under the composite stage adjunction, precomposing with the
canonical pullback-composition comparison becomes postcomposition with the pushforward
comparison. -/
private theorem stageSheafPullbackCompIso_inv_homEquiv
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    {X : Sheaf (S.stageTopology i) AddCommGrpCat.{max uC vC}}
    {Y : Sheaf (S.stageTopology k) AddCommGrpCat.{max uC vC}}
    (m :
      ((S.stageFunctor b).sheafPullback AddCommGrpCat.{max uC vC}
        (S.stageTopology j) (S.stageTopology k)).obj
          (((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
            (S.stageTopology i) (S.stageTopology j)).obj X) ⟶
        Y) :
    (((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
        (S.stageTopology i) (S.stageTopology k)).homEquiv _ _)
      (((S.stageSheafPullbackCompIso AddCommGrpCat.{max uC vC} a b).inv.app X) ≫ m) =
      ((((Adjunction.comp
          ((S.stageFunctor a).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
            (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor b).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
            (S.stageTopology j) (S.stageTopology k))).ofNatIsoRight
          (stagePushforwardCompIso S a b)).homEquiv _ _) m := by
  -- Proof comment: `stageSheafPullbackCompIso` is the owner-level `leftAdjointCompIso`, so its
  -- inverse component is characterized by agreement of the corresponding Hom-equivalences.
  simp [CofilteredSiteDiagram.stageSheafPullbackCompIso]

/-- Helper for Lemma 21.16.5: the inverse pullback-composition comparison rewrites direct
transposes to composite-adjunction transposes with the pushforward comparison explicit. -/
private theorem stageSheafPullbackCompIso_inv_homEquiv_apply
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    {X : Sheaf (S.stageTopology i) AddCommGrpCat.{max uC vC}}
    {Y : Sheaf (S.stageTopology k) AddCommGrpCat.{max uC vC}}
    (m :
      ((S.stageFunctor b).sheafPullback AddCommGrpCat.{max uC vC}
        (S.stageTopology j) (S.stageTopology k)).obj
          (((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
            (S.stageTopology i) (S.stageTopology j)).obj X) ⟶
        Y) :
    (((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
        (S.stageTopology i) (S.stageTopology k)).homEquiv _ _)
      (((S.stageSheafPullbackCompIso AddCommGrpCat.{max uC vC} a b).inv.app X) ≫ m) =
      (((Adjunction.comp
          ((S.stageFunctor a).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
            (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor b).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
            (S.stageTopology j) (S.stageTopology k))).homEquiv _ _) m) ≫
        (stagePushforwardCompIso S a b).hom.app Y := by
  -- Proof comment: rewrite the transported adjunction statement so the right-side comparison map
  -- appears as an explicit postcomposition.
  rw [stageSheafPullbackCompIso_inv_homEquiv]
  simpa using
    (ofNatIsoRight_homEquiv_apply
      (Adjunction.comp
        ((S.stageFunctor a).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
          (S.stageTopology i) (S.stageTopology j))
        ((S.stageFunctor b).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
          (S.stageTopology j) (S.stageTopology k)))
      (stagePushforwardCompIso S a b)
      m)

/-- Helper for Lemma 21.16.5: the canonical transition on the injective product target. -/
private noncomputable def stageInjectiveProductTransition
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC})
    {i j : S.I} (a : j ⟶ i) :
    ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)).obj
        (stageInjectiveProductObject F i) ⟶
      stageInjectiveProductObject F j :=
  Pi.lift (fun B : Over j ↦ stageInjectiveProductTransitionComponent F a B)

/-- Helper for Lemma 21.16.5: on an identity arrow, the canonical transition on the injective
product target is the standard pullback identity comparison. -/
private theorem stageInjectiveProductTransition_id
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) (i : S.I) :
    stageInjectiveProductTransition F (𝟙 i) =
      (S.stageSheafPullbackIdIso AddCommGrpCat.{max uC vC} i).hom.app
        (stageInjectiveProductObject F i) := by
  -- Proof comment: compare the two candidate transitions after projecting to an arbitrary
  -- `B`-factor, then transpose the right side through the identity pullback-pushforward
  -- adjunction.
  apply Pi.hom_ext
  intro B
  let adj :=
    (S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology i)
  have hmate :
      (S.stageSheafPullbackIdIso AddCommGrpCat.{max uC vC} i).hom.app
          (stageInjectiveProductObject F i) ≫
        Pi.π (fun C : Over i ↦ stageInjectiveProductFactor F C) B =
      (adj.homEquiv _ _).symm
        (Pi.π (fun C : Over i ↦ stageInjectiveProductFactor F C) B ≫
          (stagePushforwardIdIso S i).inv.app (stageInjectiveProductFactor F B)) := by
    -- Proof comment: this is the standard mate formula for the identity adjunction comparison.
    simpa [adj, stagePushforwardIdIso, CofilteredSiteDiagram.stageSheafPullbackIdIso] using
      (mateLeftAdjointIdIso_hom
        (adj := adj)
        (e := stagePushforwardIdIso S i)
        (X := stageInjectiveProductObject F i)
        (Y := stageInjectiveProductFactor F B)
        (h := Pi.π (fun C : Over i ↦ stageInjectiveProductFactor F C) B)).symm
  apply (adj.homEquiv _ _).injective
  rw [Pi.lift_π, stageInjectiveProductTransitionComponent_homEquiv, hmate]
  rw [Equiv.apply_symm_apply]
  -- Proof comment: after moving both sides to the pushforward side, the identity comparison
  -- specializes to the identity factor indexed by `B`.
  simpa only [stagePushforwardCompIso, stagePushforwardIdIso, B, Category.assoc]

/-- Helper for Lemma 21.16.5: the stagewise embedding into the injective product target. -/
private noncomputable def stageInjectiveProductEmbedding
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) (i : S.I) :
    F.obj i ⟶ stageInjectiveProductObject F i :=
  Pi.lift fun B : Over i ↦
    ((S.stageFunctor B.hom).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology B.left)).homEquiv _ _
      (F.transition B.hom ≫ stageInjectiveEmbedding F B.left)

/-- Helper for Lemma 21.16.5: the stagewise embedding into the injective product target is
monic. -/
private theorem stageInjectiveProductEmbedding_mono
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) (i : S.I) :
    Mono (stageInjectiveProductEmbedding F i) := by
  let B : Over i := Over.mk (𝟙 i)
  let adj :=
    (S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology i)
  have hcomp :
      stageInjectiveProductEmbedding F i ≫
          Pi.π (fun C : Over i ↦ stageInjectiveProductFactor F C) B =
        stageInjectiveEmbedding F i ≫
          (stagePushforwardIdIso S i).inv.app
            (HasFunctorialInjectiveEmbeddings.under (F.obj i)) := by
    -- Proof comment: the identity factor of the product records exactly the chosen injective
    -- embedding, up to the canonical identity pushforward comparison.
    rw [stageInjectiveProductEmbedding, Pi.lift_π]
    have hmate :=
      mateLeftAdjointIdIso_hom
        (adj := adj) (e := stagePushforwardIdIso S i)
        (X := F.obj i)
        (Y := HasFunctorialInjectiveEmbeddings.under (F.obj i))
        (h := stageInjectiveEmbedding F i)
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply]
    simpa [B, stagePushforwardIdIso, CofilteredSiteDiagram.stageSheafPullbackIdIso] using
      (show F.transition (𝟙 i) ≫ stageInjectiveEmbedding F i =
          (adj.homEquiv _ _).symm
            (stageInjectiveEmbedding F i ≫
              (stagePushforwardIdIso S i).inv.app
                (HasFunctorialInjectiveEmbeddings.under (F.obj i))) from by
        rw [hmate, F.transition_id])
  haveI : Mono
      (stageInjectiveEmbedding F i ≫
        (stagePushforwardIdIso S i).inv.app
          (HasFunctorialInjectiveEmbeddings.under (F.obj i))) := by
    infer_instance
  haveI : Mono
      (stageInjectiveProductEmbedding F i ≫
        Pi.π (fun C : Over i ↦ stageInjectiveProductFactor F C) B) := by
    simpa [hcomp]
  -- Proof comment: a morphism with monic composite against a projection is itself monic.
  exact mono_of_mono_fac hcomp

/-- Helper for Lemma 21.16.5: each `B`-component of the composite transition is the iterated
transition component obtained from the canonical pullback-composition comparison. -/
private theorem stageInjectiveProductTransitionComponent_comp
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC})
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) (B : Over k) :
    stageInjectiveProductTransitionComponent F (b ≫ a) B =
      (S.stageSheafPullbackCompIso AddCommGrpCat.{max uC vC} a b).inv.app
          (stageInjectiveProductObject F i) ≫
        (((S.stageFunctor b).sheafPullback AddCommGrpCat.{max uC vC}
          (S.stageTopology j) (S.stageTopology k)).map
          (stageInjectiveProductTransition F a)) ≫
        stageInjectiveProductTransitionComponent F b B := by
  -- TODO: transpose through the adjunction for `b ≫ a`, then replace the remaining broad
  -- `simp` normalization by a dedicated pushforward-associativity bridge for the three-step
  -- composite `B.hom`, `b`, `a`.
  sorry

/-- Helper for Lemma 21.16.5: each projected embedding component commutes with the canonical
transition on the injective product target. -/
private theorem stageInjectiveProductEmbedding_comm_component
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC})
    {i j : S.I} (a : j ⟶ i) (B : Over j) :
    ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)).map
        (stageInjectiveProductEmbedding F i) ≫
      stageInjectiveProductTransitionComponent F a B =
        F.transition a ≫
          stageInjectiveProductEmbedding F j ≫
            Pi.π (fun C : Over j ↦ stageInjectiveProductFactor F C) B := by
  -- TODO: compare both sides on the pushforward side of the adjunction for `a`; the remaining
  -- blocker is the same normal-form bridge relating the direct `B.hom ≫ a` component to the
  -- nested `B.hom`-then-`a` transpose used by `F.transition_comp`.
  sorry

/-- Lemma 21.16.5: every inverse system of abelian sheaves on a cofiltered inverse system of sites
admits a morphism into another inverse system whose stagewise maps are monomorphisms and whose
stagewise targets are injective abelian sheaves. -/
@[stacks 0EXZ]
theorem exists_mono_to_injective_inverse_system_of_abelian_sheaves
    (S : CofilteredSiteDiagram.{uI, uC, vC})
    (F : StageFamily S AddCommGrpCat.{max uC vC}) :
    ∃ (G : StageFamily S AddCommGrpCat.{max uC vC}) (ι : StageFamily.Hom F G),
      (∀ i : S.I, Injective (G.obj i)) ∧ ∀ i : S.I, Mono (ι.app i) := by
  classical
  let G : StageFamily S AddCommGrpCat.{max uC vC} where
    obj := stageInjectiveProductObject F
    transition := stageInjectiveProductTransition F
    transition_id := stageInjectiveProductTransition_id F
    transition_comp := by
      intro i j k a b
      -- Proof comment: the cocycle law is checked componentwise on each `B : Over k`.
      apply Pi.hom_ext
      intro B
      rw [stageInjectiveProductTransition, Pi.lift_π, Category.assoc]
      simpa [Category.assoc] using
        stageInjectiveProductTransitionComponent_comp (F := F) a b B
  let ι : StageFamily.Hom F G where
    app := stageInjectiveProductEmbedding F
    comm := by
      intro i j a
      -- Proof comment: compatibility with transitions is likewise detected on each product
      -- projection.
      apply Pi.hom_ext
      intro B
      rw [stageInjectiveProductTransition, Pi.lift_π, Category.assoc]
      simpa [Category.assoc] using
        stageInjectiveProductEmbedding_comm_component (F := F) a B
  refine ⟨G, ι, ?_, ?_⟩
  · intro i
    -- Proof comment: each stage of `G` is the product of pushforwards of injective envelopes.
    simpa [G] using stageInjectiveProductObject_injective (F := F) i
  · intro i
    -- Proof comment: the identity-factor projection detects the stagewise embedding as monic.
    simpa [ι] using stageInjectiveProductEmbedding_mono (F := F) i

/-- Source-facing repacking of Lemma 21.16.5 with the injective target family exposed first. -/
theorem exists_injective_inverse_system_of_abelian_sheaves_with_stagewise_mono
    (S : CofilteredSiteDiagram.{uI, uC, vC})
    (F : StageFamily S AddCommGrpCat.{max uC vC}) :
    ∃ G : StageFamily S AddCommGrpCat.{max uC vC},
      (∀ i : S.I, Injective (G.obj i)) ∧
        ∃ ι : StageFamily.Hom F G, ∀ i : S.I, Mono (ι.app i) := by
  obtain ⟨G, ι, hG, hι⟩ := exists_mono_to_injective_inverse_system_of_abelian_sheaves S F
  exact ⟨G, hG, ι, hι⟩

end CategoryTheory
