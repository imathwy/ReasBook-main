import Mathlib
import stacks_project.Chap07.Lemma_7_18_3
import stacks_project.Chap21.Lemma_21_16_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory

open CofilteredSiteDiagram

/-- The transition morphism between the pullbacks of an inverse system of abelian sheaves to the
colimit site. -/
noncomputable def inverseSystemColimitAbelianSheafTransition
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S)
    {i j : S.I} (a : j ⟶ i) :
    (((S.stageCoconeFunctor i).sheafPullback AddCommGrpCat
        (S.stageTopology i) S.colimitTopology).obj (F.obj i)) ⟶
      (((S.stageCoconeFunctor j).sheafPullback AddCommGrpCat
        (S.stageTopology j) S.colimitTopology).obj (F.obj j)) :=
  (S.colimitStageSheafPullbackCompIso AddCommGrpCat a).inv.app (F.obj i) ≫
    (((S.stageCoconeFunctor j).sheafPullback AddCommGrpCat
      (S.stageTopology j) S.colimitTopology)).map (F.transition a)

-- Proof sketch: unfold `inverseSystemColimitAbelianSheafTransition`; for the identity arrow the
-- pullback-comparison isomorphism reduces to the identity, and `F.transition_id i` identifies the
-- remaining stagewise transition with the identity morphism.
/-- The colimit-site transition attached to the identity arrow is the identity morphism. -/
private theorem inverseSystemColimitAbelianSheafTransition_id
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S) (i : S.I) :
    inverseSystemColimitAbelianSheafTransition S F (𝟙 i) =
      𝟙 (((S.stageCoconeFunctor i).sheafPullback AddCommGrpCat
        (S.stageTopology i) S.colimitTopology).obj (F.obj i)) := sorry

-- Proof sketch: compare the two pullback routes from stage `i` to stage `k` through stage `j`,
-- use the coherence isomorphism for the two left-adjoint comparison maps, and finish with
-- `F.transition_comp a b`.
/-- The colimit-site transitions of an inverse system compose canonically. -/
private theorem inverseSystemColimitAbelianSheafTransition_comp
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    inverseSystemColimitAbelianSheafTransition S F (b ≫ a) =
      inverseSystemColimitAbelianSheafTransition S F a ≫
        inverseSystemColimitAbelianSheafTransition S F b := sorry

/-- The inverse system `F` pulled back to the colimit site along the stage cocone functors. -/
noncomputable def inverseSystemColimitAbelianSheafDiagram
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S) :
    S.Iᵒᵖ ⥤ Sheaf S.colimitTopology AddCommGrpCat where
  obj i := (((S.stageCoconeFunctor i.unop).sheafPullback AddCommGrpCat
    (S.stageTopology i.unop) S.colimitTopology).obj (F.obj i.unop))
  map a := inverseSystemColimitAbelianSheafTransition S F a.unop
  map_id := fun i ↦ inverseSystemColimitAbelianSheafTransition_id S F i.unop
  map_comp := fun a b ↦ inverseSystemColimitAbelianSheafTransition_comp S F a.unop b.unop

/-- The colimit abelian sheaf `\mathcal F = \operatorname{colim}_i u_i^{-1} \mathcal F_i`
attached to an inverse system of abelian sheaves on the stage sites of `S`. -/
noncomputable abbrev inverseSystemColimitAbelianSheaf
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat)]
    (F : InverseSystemOfAbelianSheaves S) :
    Sheaf S.colimitTopology AddCommGrpCat :=
  colimit (inverseSystemColimitAbelianSheafDiagram S F)

/-- The image of a stage object `X_i` in the colimit category of the site diagram `S`. -/
abbrev colimitStageObject
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram] {i : S.I} (X : S.diagram.obj (op i)) :
    (colimit S.diagram : Cat) :=
  (S.stageCoconeFunctor i).obj X

/-- The canonical map from the filtered colimit of the stagewise cohomology objects over the image
of `X_i` to the cohomology of the colimit sheaf over `u_i(X_i)`. This is the Lean model of the
source comparison `\operatorname{colim}_{a : j \to i} H^p(u_a(X_i), \mathcal F_j) \to
H^p(u_i(X_i), \mathcal F)`. -/
noncomputable def inverseSystemStageObjectCohomologyColimitComparison
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    [HasSheafify S.colimitTopology AddCommGrpCat]
    [HasExt (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (((colimit S.diagram : Cat)ᵒᵖ) ⥤ AddCommGrpCat)]
    (F : InverseSystemOfAbelianSheaves S) (p : ℕ) {i : S.I} (X : S.diagram.obj (op i)) :
    (colimit
        (inverseSystemColimitAbelianSheafDiagram S F ⋙
          Sheaf.cohomologyPresheafFunctor S.colimitTopology p)).obj
      (op (colimitStageObject S X)) ⟶
    (((Sheaf.cohomologyPresheafFunctor S.colimitTopology p).obj
        (inverseSystemColimitAbelianSheaf S F)).obj
      (op (colimitStageObject S X))) :=
  (colimit.post (inverseSystemColimitAbelianSheafDiagram S F)
      (Sheaf.cohomologyPresheafFunctor S.colimitTopology p)).app
    (op (colimitStageObject S X))

-- Proof sketch: the case `p = 0` is the stagewise section comparison of Lemma `7.18.4`. For
-- `p > 0`, choose a stagewise monomorphism into a stagewise injective system as in Lemma
-- `21.16.5`, pass to the colimit sheaf on the colimit site, and apply the same injective
-- resolution argument as in Lemma `21.16.1`. The remaining acyclicity statement is reduced to
-- Čech cohomology vanishing by Lemmas `21.10.9` and `21.10.2`.
/-- Lemma 21.16.6: for an inverse system of abelian sheaves on a cofiltered inverse system of
sites with colimit sheaf `\mathcal F = \operatorname{colim}_i u_i^{-1}\mathcal F_i`, the
canonical map from the filtered colimit of the cohomology objects over the images `u_a(X_i)` to
the cohomology of `\mathcal F` over `u_i(X_i)` is an isomorphism. This is the canonical Lean form
of the source identity `\operatorname{colim}_{a : j \to i} H^p(u_a(X_i), \mathcal F_j) =
H^p(u_i(X_i), \mathcal F)`. -/
theorem inverseSystemStageObjectCohomologyColimitComparison_isIso
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    [HasSheafify S.colimitTopology AddCommGrpCat]
    [HasExt (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (((colimit S.diagram : Cat)ᵒᵖ) ⥤ AddCommGrpCat)]
    (F : InverseSystemOfAbelianSheaves S) {i : S.I} (X : S.diagram.obj (op i)) (p : ℕ) :
    IsIso (inverseSystemStageObjectCohomologyColimitComparison S F p X) := sorry

end CategoryTheory
