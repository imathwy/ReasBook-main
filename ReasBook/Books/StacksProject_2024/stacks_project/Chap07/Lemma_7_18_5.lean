import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_18_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace CategoryTheory

open CofilteredSiteDiagram

/- Domain-style sampling for Lemma 7.18.5:
- primary domain: stagewise inverse-image/pushforward comparison for sheaves on the colimit site
  of a cofiltered diagram of sites;
- sampled owner API:
  `ColimitSiteStageFamily`,
  `ColimitSiteStageFamily.diagram`,
  `ColimitSiteStageFamily.colimitSheaf`,
  `CofilteredSiteDiagram.colimitStageSheafPullbackCompIso`;
- best owner abstraction: `ColimitSiteStageFamily S`;
- primitive data: the stage sheaves `f_{i,*} ℱ` and the comparison maps
  `f_a⁻¹ f_{i,*} ℱ ⟶ f_{j,*} ℱ`;
- derived API: the pulled-back colimit-site diagram, its colimit sheaf, and the canonical colimit
  comparison to `ℱ`.

This file should therefore build the stage family once and reuse the owner-level diagram and
colimit sheaf from `Lemma_7_18_4`, rather than keeping a parallel local diagram/cocone package.
-/

section

variable (S : CofilteredSiteDiagram.{u, u, u})
variable [HasWeakSheafify S.colimitTopology (Type u)]

/-- The direct-image functor `f_{i,*}` from the colimit site to the stage site `i`. -/
private abbrev stageDirectImage (i : S.I) :
    Sheaf S.colimitTopology (Type u) ⥤ Sheaf (S.stageTopology i) (Type u) :=
  (S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
    (S.stageTopology i) S.colimitTopology

/-- The inverse-image functor `f_i⁻¹` from the stage site `i` to the colimit site. -/
private abbrev stageInverseImage (i : S.I) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf S.colimitTopology (Type u) :=
  (S.stageCoconeFunctor i).sheafPullback (Type u) (S.stageTopology i) S.colimitTopology

private instance stageMap_isContinuous {i j : S.I} (a : j ⟶ i) :
    Functor.IsContinuous (S.diagram.map a.op).toFunctor (S.stageTopology i) (S.stageTopology j) :=
  by
    simpa [CofilteredSiteDiagram.stageFunctor] using S.stageFunctor_isContinuous a

/-- The direct-image functors `f_{i,*}` compose along a transition map as expected. -/
private noncomputable def stageDirectImageCompIso
    {i j : S.I} (a : j ⟶ i) :
    stageDirectImage S j ⋙
        (S.stageFunctor a).sheafPushforwardContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j) ≅
      stageDirectImage S i := by
  let F := (S.diagram.map a.op).toFunctor
  let G := S.stageCoconeFunctor j
  let FG := S.stageCoconeFunctor i
  letI : Functor.IsContinuous F (S.stageTopology i) (S.stageTopology j) :=
    stageMap_isContinuous S a
  have h :
      G.sheafPushforwardContinuous (Type u) (S.stageTopology j) S.colimitTopology ⋙
          F.sheafPushforwardContinuous (Type u) (S.stageTopology i) (S.stageTopology j) ≅
        FG.sheafPushforwardContinuous (Type u) (S.stageTopology i) S.colimitTopology :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ F G FG
      (eqToIso (congrArg Cat.Hom.toFunctor (colimit.w S.diagram a.op)))
      (Type u) inferInstance (S.stageTopology i) (S.stageTopology j) S.colimitTopology
      inferInstance inferInstance inferInstance
  simpa [CofilteredSiteDiagram.stageFunctor] using h

/-- The canonical stagewise comparison map
`f_a⁻¹ f_{i,*} ℱ ⟶ f_{j,*} ℱ` for a transition `a : j ⟶ i`. -/
private noncomputable def stagePushforwardComparison
    (ℱ : Sheaf S.colimitTopology (Type u)) {i j : S.I} (a : j ⟶ i) :
    ((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).obj
        ((stageDirectImage S i).obj ℱ) ⟶
      (stageDirectImage S j).obj ℱ :=
  (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).homEquiv
      ((stageDirectImage S i).obj ℱ)
      ((stageDirectImage S j).obj ℱ)).symm
    ((stageDirectImageCompIso S a).inv.app ℱ)

/-- The identity stage-comparison map is the canonical identity pullback map. -/
private theorem stagePushforwardComparison_id
    (ℱ : Sheaf S.colimitTopology (Type u)) (i : S.I) :
    stagePushforwardComparison S ℱ (𝟙 i) =
      (S.stageSheafPullbackIdIso (Type u) i).hom.app ((stageDirectImage S i).obj ℱ) := sorry

/-- The stage-comparison maps satisfy the cocycle condition. -/
private theorem stagePushforwardComparison_comp
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    (S.stageSheafPullbackCompIso (Type u) a b).hom.app ((stageDirectImage S i).obj ℱ) ≫
        stagePushforwardComparison S ℱ (b ≫ a) =
      (((S.stageFunctor b).sheafPullback (Type u)
          (S.stageTopology j) (S.stageTopology k)).map
          (stagePushforwardComparison S ℱ a)) ≫
        stagePushforwardComparison S ℱ b := sorry

/-- The compatible stage family `i ↦ f_{i,*} ℱ` from Lemma 7.18.5. -/
private noncomputable def stagePullbackPushforwardFamily
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    ColimitSiteStageFamily S where
  obj i := (stageDirectImage S i).obj ℱ
  transition a := stagePushforwardComparison S ℱ a
  transition_id := stagePushforwardComparison_id S ℱ
  transition_comp := stagePushforwardComparison_comp S ℱ

/-- The counit map `f_i⁻¹ f_{i,*} ℱ ⟶ ℱ` at a single stage. -/
private abbrev stagePullbackPushforwardCounit
    (ℱ : Sheaf S.colimitTopology (Type u)) (i : S.I) :
    (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj
        ((stageDirectImage S i).obj ℱ)) ⟶
      ℱ :=
  ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
    (S.stageTopology i) S.colimitTopology).counit.app ℱ

/-- The stage counits assemble into a cocone over the owner-level pulled-back diagram attached to
`i ↦ f_{i,*} ℱ`. -/
private theorem stagePullbackPushforwardCounit_naturality
    (ℱ : Sheaf S.colimitTopology (Type u)) {i j : S.I} (a : j ⟶ i) :
    (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)).map a.op ≫
      stagePullbackPushforwardCounit S ℱ j =
        stagePullbackPushforwardCounit S ℱ i := sorry

/-- The canonical cocone from the owner-level diagram `i ↦ f_i⁻¹ f_{i,*} ℱ` to `ℱ`. -/
private noncomputable def stagePullbackPushforwardCocone
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    Cocone (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)) where
  pt := ℱ
  ι :=
    { app := fun i ↦ stagePullbackPushforwardCounit S ℱ (unop i)
      naturality := by
        intro i j a
        simpa using stagePullbackPushforwardCounit_naturality S ℱ a.unop }

/-- The filtered colimit object `colim_i f_i⁻¹ f_{i,*} ℱ` in the colimit site. -/
abbrev colimitSiteStagePullbackPushforward
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    Sheaf S.colimitTopology (Type u) :=
  ColimitSiteStageFamily.colimitSheaf (stagePullbackPushforwardFamily S ℱ)

/-- The canonical comparison morphism from the colimit of the diagram
`i ↦ f_i⁻¹ f_{i,*} ℱ` to `ℱ`. -/
abbrev colimitSiteStagePullbackPushforwardComparison
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    colimitSiteStagePullbackPushforward S ℱ ⟶ ℱ :=
  colimit.desc (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ))
    (stagePullbackPushforwardCocone S ℱ)

-- Proof sketch: evaluate the comparison map at an object `U` of the colimit site, choose a stage
-- object `U_i` mapping to `U`, and identify the source with the filtered colimit of the sections
-- `f_{j,*} ℱ(u_a(U_i))`. Lemma `7.18.4` computes this colimit, and each term is canonically
-- `ℱ(U)`, so the comparison map is bijective on every object and hence an isomorphism.
/-- Lemma 7.18.5: in Situation 7.18.1, for a sheaf `ℱ` on the colimit site, the canonical map
from the filtered colimit of the canonical diagram `i ↦ f_i⁻¹ f_{i,*} ℱ` to `ℱ` is an
isomorphism. In Lean this filtered colimit is indexed by `S.Iᵒᵖ` via the owner-level diagram
coming from the compatible stage family `i ↦ f_{i,*} ℱ`. -/
theorem colimitSiteStagePullbackPushforwardComparison_isIso
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    IsIso (colimitSiteStagePullbackPushforwardComparison S ℱ) := sorry

attribute [instance] colimitSiteStagePullbackPushforwardComparison_isIso

end

end CategoryTheory
