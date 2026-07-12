import Mathlib
import StacksProject_2024.Chap07.Definition_7_14_1
import StacksProject_2024.Chap07.Lemma_7_18_2
import StacksProject_2024.Chap07.Situation_7_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe uI uC vC u w

namespace CategoryTheory

open CofilteredSiteDiagram

/- Domain-style sampling for Lemma 7.18.3:
- primary domain: pullback of sheaves along the stage and cocone functors in a cofiltered diagram
  of sites, together with the slice indexing category `(Over i)ᵒᵖ`;
- sampled owner API:
  `CofilteredSiteDiagram.stageFunctor`,
  `CofilteredSiteDiagram.stageCoconeFunctor`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPushforwardContinuousComp'`,
  `Adjunction.leftAdjointCompIso`;
- source/core/bridge triage:
  `source-facing`: the filtered colimit comparison on section sets indexed by arrows `a : j ⟶ i`;
  `core/canonical`: the owner pullback functors attached to `S.stageFunctor a` and
    `S.stageCoconeFunctor i`;
  `bridge/view`: the private over-category section diagram used to express equation `(7.18.3.1)`.

Primitive data are the stage and cocone functors already packaged by
`CofilteredSiteDiagram`. The pullback-composition isomorphisms are derived API and should reuse the
owner-level stage and cocone functors rather than raw `diagram.map` and `colimit.ι` spellings.
-/

private noncomputable abbrev stageSheafPullbackAlong
    (S : CofilteredSiteDiagram.{u, u, u})
    {i j : S.I} (a : j ⟶ i) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf (S.stageTopology j) (Type u) :=
  let _ : Functor.IsContinuous (S.stageFunctor a)
      (S.stageTopology i) (S.stageTopology j) :=
    S.stageFunctor_isContinuous a
  (S.stageFunctor a).sheafPullback (Type u) (S.stageTopology i) (S.stageTopology j)

private noncomputable abbrev overStageSheafPullback
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (A : (Over i)ᵒᵖ) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf (S.stageTopology A.unop.left) (Type u) :=
  stageSheafPullbackAlong S A.unop.hom

private abbrev overLeftHom
    {C : Type*} [Category C] {i : C} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    B.unop.left ⟶ A.unop.left :=
  u.unop.left

private abbrev colimitSiteStagePullbackSectionValue
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) : Type u :=
  ((overStageSheafPullback S A).obj ℱ).obj.obj
    (op (S.overImage X A))

private noncomputable def colimitSiteStagePullbackSectionTransition
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u))
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    let a := overLeftHom u
    (overStageSheafPullback S A).obj ℱ ⟶
      ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
      ((overStageSheafPullback S B).obj ℱ) :=
  let _ : Functor.IsContinuous (S.stageFunctor (overLeftHom u))
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left) :=
    S.stageFunctor_isContinuous (overLeftHom u)
  let e :=
    (((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
      ((overStageSheafPullback S A).obj ℱ)
      ((overStageSheafPullback S B).obj ℱ))
  e <|
    show ((S.stageFunctor (overLeftHom u)).sheafPullback (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
          ((overStageSheafPullback S A).obj ℱ) ⟶
        (overStageSheafPullback S B).obj ℱ from by
      have h : overLeftHom u ≫ A.unop.hom = B.unop.hom := by
        simpa using Over.w u.unop
      let _ : Functor.IsContinuous (S.stageFunctor (overLeftHom u ≫ A.unop.hom))
          (S.stageTopology i) (S.stageTopology B.unop.left) :=
        S.stageFunctor_isContinuous (overLeftHom u ≫ A.unop.hom)
      have h' :
          (stageSheafPullbackAlong S (overLeftHom u ≫ A.unop.hom)).obj ℱ =
            (overStageSheafPullback S B).obj ℱ := by
        simpa [stageSheafPullbackAlong, overStageSheafPullback] using
          congrArg (fun a : B.unop.left ⟶ i ↦ (stageSheafPullbackAlong S a).obj ℱ) h
      exact
        (S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ ≫
          eqToHom h'

private theorem colimitSiteStagePullbackSectionMap_target_eq
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    let a := overLeftHom u
    ((((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
        ((overStageSheafPullback S B).obj ℱ)).obj.obj
      (op (S.overImage X A))) =
      colimitSiteStagePullbackSectionValue S ℱ X B := by
  sorry

private noncomputable def colimitSiteStagePullbackSectionMap
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    colimitSiteStagePullbackSectionValue S ℱ X A ⟶
      colimitSiteStagePullbackSectionValue S ℱ X B :=
  (colimitSiteStagePullbackSectionTransition S ℱ u).1.app
      (op (S.overImage X A)) ≫
    eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)

private theorem colimitSiteStagePullbackSectionMap_id
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    colimitSiteStagePullbackSectionMap S ℱ X (𝟙 A) = 𝟙 _ := by
  sorry

private theorem colimitSiteStagePullbackSectionMap_comp
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B C : (Over i)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ C) :
    colimitSiteStagePullbackSectionMap S ℱ X (u ≫ v) =
      colimitSiteStagePullbackSectionMap S ℱ X u ≫
        colimitSiteStagePullbackSectionMap S ℱ X v := by
  sorry

/-- Lemma 7.18.3, equation `(7.18.3.1)`: the filtered diagram on `(Over i)ᵒᵖ` sending an arrow
`a : j ⟶ i` to the section set `f_a⁻¹ ℱ (u_a(X))`. -/
noncomputable def colimitSiteStagePullbackSectionDiagram
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := colimitSiteStagePullbackSectionValue S ℱ X A
  map u := colimitSiteStagePullbackSectionMap S ℱ X u
  map_id A := colimitSiteStagePullbackSectionMap_id S ℱ X A
  map_comp u v := colimitSiteStagePullbackSectionMap_comp S ℱ X u v

private theorem colimitSiteStagePullbackSectionsComparisonTarget_eq
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (((S.stageCoconeFunctor i).sheafPullback
            (Type u)
            (S.stageTopology i)
            S.colimitTopology).obj
          ℱ)).obj.obj
      (op (S.overImage X A))) =
      ((((S.stageCoconeFunctor i).sheafPullback
            (Type u)
            (S.stageTopology i)
            S.colimitTopology).obj
          ℱ).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) := by
  sorry

private noncomputable def colimitSiteStagePullbackSectionsComparisonCocone
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Cocone (colimitSiteStagePullbackSectionDiagram S ℱ X) where
  pt :=
    ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj
      (op ((S.stageCoconeFunctor i).obj X)))
  ι :=
    { app := fun A ↦
        (((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
            (S.stageTopology A.unop.left) S.colimitTopology).unit.app
            ((overStageSheafPullback S A).obj ℱ)).1.app
            (op (S.overImage X A)) ≫
          eqToHom (by rfl) ≫
          ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous
                (Type u) (S.stageTopology A.unop.left)
                  S.colimitTopology).map
              ((S.colimitStageSheafPullbackCompIso (Type u) A.unop.hom).hom.app ℱ)).1.app
              (op (S.overImage X A))) ≫
          eqToHom (by
            simpa using colimitSiteStagePullbackSectionsComparisonTarget_eq S ℱ X A)
      naturality := by
        intro A B u
        sorry }

/-- Lemma 7.18.3, equation `(7.18.3.1)`: for a sheaf `ℱ` on the stage site `i` and an object
`X` of `\mathcal C_i`, the canonical map from the filtered colimit over arrows `a : j ⟶ i` of
the section sets `f_a⁻¹ ℱ (u_a(X))` to the section set `f_i⁻¹ ℱ (u_i(X))` is bijective. In Lean
the indexing category is `(Over i)ᵒᵖ`. -/
noncomputable def colimitSiteStagePullbackSectionsComparison
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    colimit (colimitSiteStagePullbackSectionDiagram S ℱ X) ⟶
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) :=
  colimit.desc _ (colimitSiteStagePullbackSectionsComparisonCocone S ℱ X) ≫
    eqToHom (by simp [colimitSiteStagePullbackSectionsComparisonCocone])

/-- Lemma 7.18.3, equation `(7.18.3.1)`, as an isomorphism in `Type`. -/
private theorem colimitSiteStagePullbackSectionsComparison_isIso
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    IsIso (colimitSiteStagePullbackSectionsComparison S ℱ X) := by
  rw [isIso_iff_bijective]
  sorry

/-- Lemma 7.18.3, equation `(7.18.3.1)`, in the source-text bijectivity form. -/
theorem colimitSiteStagePullbackSectionsComparison_bijective
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Function.Bijective (colimitSiteStagePullbackSectionsComparison S ℱ X) := by
  simpa [isIso_iff_bijective] using
    (colimitSiteStagePullbackSectionsComparison_isIso S ℱ X)

/-- Lemma 7.18.3: in Situation 7.18.1, the cocone functor
`u_i : \mathcal C_i \to \mathop{\mathrm{colim}} \mathcal C_j`
defines a morphism of sites
`(\mathop{\mathrm{colim}} \mathcal C_j, J_{\mathrm{colim}}) \to (\mathcal C_i, J_i)`. -/
instance colimit_site_cocone_isMorphismOfSites
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I) :
    IsMorphismOfSites (S.stageTopology i) S.colimitTopology
      (S.stageCoconeFunctor i) := by
  refine
    { toIsContinuous := by
        infer_instance
      toRepresentablyFlat := ?_ }
  sorry

end CategoryTheory
