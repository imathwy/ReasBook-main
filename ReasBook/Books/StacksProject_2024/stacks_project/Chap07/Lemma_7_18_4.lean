import Mathlib
import StacksProject_2024.Chap07.Lemma_7_17_7
import StacksProject_2024.Chap07.Lemma_7_18_3
import StacksProject_2024.Chap07.Situation_7_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe uI uC vC u w

namespace CategoryTheory

open CofilteredSiteDiagram

/- Source/core/bridge triage for Lemma 7.18.4:
- source-facing owner: `ColimitSiteStageFamily S`, a family of stage sheaves with the transition
  maps `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` from the source text, together with its colimit sheaf on the colimit site
  and the explicit comparison indexed by arrows `a : j ⟶ i`, i.e. by `(Over i)ᵒᵖ`
- core/canonical owner: the filtered-diagram comparison map
  `((colimit.post F (sheafToPresheaf _ _)).app (op U))` from `Lemma_7_17_7`
- bridge/view layer in this file: the private pulled-back colimit-site diagram obtained by pulling
  each stage sheaf back to the colimit site and transporting the transition maps through
  `colimitStageSheafPullbackCompIso`
- primitive data: the stage sheaves and their pullback transition morphisms
- derived API: the source-facing colimit sheaf and the over-category comparison map
-/

namespace CofilteredSiteDiagram

/-- A compatible inverse system of `A`-valued sheaves on the stage sites of `S`, with the
source-text transition maps `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` for arrows `a : j ⟶ i`. -/
structure StageFamily
    (S : CofilteredSiteDiagram.{uI, uC, vC}) (A : Type w) [Category A] where
  /-- The sheaf on the stage site `i`. -/
  obj (i : S.I) : Sheaf (S.stageTopology i) A
  /-- The transition morphism `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` for `a : j ⟶ i`. -/
  transition {i j : S.I} (a : j ⟶ i)
      [HasWeakSheafify (S.stageTopology j) A]
      [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F] :
      ((S.stageFunctor a).sheafPullback A
        (S.stageTopology i) (S.stageTopology j)).obj (obj i) ⟶
        obj j
  /-- The identity transition is the canonical identity pullback map. -/
  transition_id (i : S.I)
      [HasWeakSheafify (S.stageTopology i) A]
      [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor (𝟙 i)).op.HasLeftKanExtension F] :
      transition (𝟙 i) = (S.stageSheafPullbackIdIso A i).hom.app (obj i)
  /-- The transition morphisms satisfy the usual cocycle condition. -/
  transition_comp {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
      [HasWeakSheafify (S.stageTopology j) A]
      [HasWeakSheafify (S.stageTopology k) A]
      [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
      [∀ F : (S.stage j)ᵒᵖ ⥤ A, (S.stageFunctor b).op.HasLeftKanExtension F]
      [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor (b ≫ a)).op.HasLeftKanExtension F] :
      (S.stageSheafPullbackCompIso A a b).hom.app (obj i) ≫ transition (b ≫ a) =
        ((S.stageFunctor b).sheafPullback A
          (S.stageTopology j) (S.stageTopology k)).map (transition a) ≫
          transition b

namespace StageFamily

/-- A morphism of compatible stage families is a componentwise morphism commuting with the
transition maps. -/
@[ext] structure Hom
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F G : StageFamily S A) where
  /-- The component morphism on stage `i`. -/
  app (i : S.I) : F.obj i ⟶ G.obj i
  /-- Compatibility of the component maps with the transition morphisms. -/
  comm {i j : S.I} (a : j ⟶ i)
      [HasWeakSheafify (S.stageTopology j) A]
      [∀ H : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension H] :
      ((S.stageFunctor a).sheafPullback A
        (S.stageTopology i) (S.stageTopology j)).map (app i) ≫
          G.transition a =
        F.transition a ≫
          app j

/-- The transition morphism between the pullbacks of a compatible stage family to the colimit
site. -/
private noncomputable def transitionOnColimit
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [HasColimit S.diagram]
    [∀ i : S.I, HasWeakSheafify (S.stageTopology i) A]
    [HasWeakSheafify S.colimitTopology A]
    [∀ {i j : S.I} (a : j ⟶ i),
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ i : S.I,
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageCoconeFunctor i).op.HasLeftKanExtension F]
    (family : StageFamily S A)
    {i j : S.I} (a : j ⟶ i) :
    ((S.stageCoconeFunctor i).sheafPullback A
      (S.stageTopology i) S.colimitTopology).obj (family.obj i) ⟶
      ((S.stageCoconeFunctor j).sheafPullback A
        (S.stageTopology j) S.colimitTopology).obj (family.obj j) :=
  (S.colimitStageSheafPullbackCompIso A a).inv.app (family.obj i) ≫
    (((S.stageCoconeFunctor j).sheafPullback A
      (S.stageTopology j) S.colimitTopology)).map (family.transition a)

/-- The colimit-site transition attached to the identity arrow is the identity morphism. -/
private theorem transitionOnColimit_id
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [HasColimit S.diagram]
    [∀ i : S.I, HasWeakSheafify (S.stageTopology i) A]
    [HasWeakSheafify S.colimitTopology A]
    [∀ {i j : S.I} (a : j ⟶ i),
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ i : S.I,
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageCoconeFunctor i).op.HasLeftKanExtension F]
    (family : StageFamily S A) (i : S.I) :
    transitionOnColimit family (𝟙 i) =
      𝟙 (((S.stageCoconeFunctor i).sheafPullback A
        (S.stageTopology i) S.colimitTopology).obj (family.obj i)) := sorry

/-- The colimit-site transitions attached to a compatible stage family compose canonically. -/
private theorem transitionOnColimit_comp
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [HasColimit S.diagram]
    [∀ i : S.I, HasWeakSheafify (S.stageTopology i) A]
    [HasWeakSheafify S.colimitTopology A]
    [∀ {i j : S.I} (a : j ⟶ i),
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ i : S.I,
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageCoconeFunctor i).op.HasLeftKanExtension F]
    (family : StageFamily S A)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    transitionOnColimit family (b ≫ a) =
      transitionOnColimit family a ≫ transitionOnColimit family b := sorry

/-- The compatible family `family` determines a filtered diagram on the colimit site by pulling
each stage sheaf back along the cocone functor `u_i : \mathcal C_i \to \mathcal C`. This is the
owner-level colimit-site diagram attached to a compatible stage family. -/
noncomputable def diagram
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [HasColimit S.diagram]
    [∀ i : S.I, HasWeakSheafify (S.stageTopology i) A]
    [HasWeakSheafify S.colimitTopology A]
    [∀ {i j : S.I} (a : j ⟶ i),
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ i : S.I,
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageCoconeFunctor i).op.HasLeftKanExtension F]
    (family : StageFamily S A) :
    S.Iᵒᵖ ⥤ Sheaf S.colimitTopology A where
  obj i :=
    (((S.stageCoconeFunctor i.unop).sheafPullback A
      (S.stageTopology i.unop) S.colimitTopology).obj (family.obj i.unop))
  map a := transitionOnColimit family a.unop
  map_id i := by
    simpa using transitionOnColimit_id family i.unop
  map_comp a b := by
    simpa using transitionOnColimit_comp family a.unop b.unop

/-- The colimit sheaf on the colimit site attached to a compatible stage family. -/
noncomputable def colimitSheaf
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [HasColimit S.diagram]
    [∀ i : S.I, HasWeakSheafify (S.stageTopology i) A]
    [HasWeakSheafify S.colimitTopology A]
    [∀ {i j : S.I} (a : j ⟶ i),
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ i : S.I,
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageCoconeFunctor i).op.HasLeftKanExtension F]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology A)]
    (family : StageFamily S A) :
    Sheaf S.colimitTopology A :=
  colimit (diagram family)

end StageFamily

end CofilteredSiteDiagram

/-- A compatible inverse system of sheaves on the stage sites of `S`, with the source-text
transition maps `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` for arrows `a : j ⟶ i`. -/
structure ColimitSiteStageFamily (S : CofilteredSiteDiagram.{u, u, u}) where
  /-- The sheaf on the stage site `i`. -/
  obj (i : S.I) : Sheaf (S.stageTopology i) (Type u)
  /-- The transition morphism `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` for `a : j ⟶ i`. -/
  transition {i j : S.I} (a : j ⟶ i) :
      ((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj (obj i) ⟶
        obj j
  /-- The identity transition is the canonical identity pullback map. -/
  transition_id (i : S.I) :
      transition (𝟙 i) = (S.stageSheafPullbackIdIso (Type u) i).hom.app (obj i)
  /-- The transition morphisms satisfy the usual cocycle condition. -/
  transition_comp {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
      (S.stageSheafPullbackCompIso (Type u) a b).hom.app (obj i) ≫ transition (b ≫ a) =
        ((S.stageFunctor b).sheafPullback (Type u)
          (S.stageTopology j) (S.stageTopology k)).map (transition a) ≫
          transition b

namespace ColimitSiteStageFamily

/-- The transition morphism between the pullbacks of a compatible stage family to the colimit
site. -/
private noncomputable def transitionOnColimit
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i j : S.I} (a : j ⟶ i) :
    ((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj (family.obj i) ⟶
      ((S.stageCoconeFunctor j).sheafPullback (Type u)
        (S.stageTopology j) S.colimitTopology).obj (family.obj j) :=
  (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app (family.obj i) ≫
    (((S.stageCoconeFunctor j).sheafPullback (Type u)
      (S.stageTopology j) S.colimitTopology)).map (family.transition a)

/-- The colimit-site transition attached to the identity arrow is the identity morphism. -/
private theorem transitionOnColimit_id
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S) (i : S.I) :
    transitionOnColimit family (𝟙 i) =
      𝟙 (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj (family.obj i)) := sorry

/-- The colimit-site transitions attached to a compatible stage family compose canonically. -/
private theorem transitionOnColimit_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    transitionOnColimit family (b ≫ a) =
      transitionOnColimit family a ≫ transitionOnColimit family b := sorry

/-- The compatible family `family` determines a filtered diagram on the colimit site by pulling
each stage sheaf back along the cocone functor `u_i : \mathcal C_i \to \mathcal C`. This diagram
is only an implementation device for the filtered-colimit comparison theorem. -/
noncomputable def diagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S) :
    S.Iᵒᵖ ⥤ Sheaf S.colimitTopology (Type u) where
  obj i :=
    (((S.stageCoconeFunctor i.unop).sheafPullback (Type u)
      (S.stageTopology i.unop) S.colimitTopology).obj (family.obj i.unop))
  map a := transitionOnColimit family a.unop
  map_id := by
    intro i
    simpa using transitionOnColimit_id family i.unop
  map_comp := by
    intro i j k a b
    simpa using transitionOnColimit_comp family a.unop b.unop

/-- The colimit sheaf on the colimit site attached to a compatible stage family. -/
noncomputable def colimitSheaf
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S) :
    Sheaf S.colimitTopology (Type u) :=
  colimit (diagram family)

/- The source colimit in Lemma 7.18.4 is indexed by arrows `a : j ⟶ i`, represented in Lean by
`(Over i)ᵒᵖ`, and sends `a` to the section set `𝒜_j(u_a(X))`. -/
private abbrev sectionValue
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) : Type u :=
  (family.obj A.unop.left).obj.obj
    (op (S.overImage X A))

private theorem sectionMap_target_eq
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    sectionValue family X A =
      ((((S.stageFunctor u.unop.left).sheafPullback (Type u)
          (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
          (family.obj A.unop.left)).obj.obj
        (op (S.overImage X B))) := by
  sorry

private noncomputable def sectionMap
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    sectionValue family X A ⟶ sectionValue family X B :=
  eqToHom (sectionMap_target_eq family X u) ≫
    (family.transition u.unop.left).1.app
      (op (S.overImage X B))

private theorem sectionMap_id
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    sectionMap family X (𝟙 A) = 𝟙 _ := by
  sorry

private theorem sectionMap_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    {A B C : (Over i)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ C) :
    sectionMap family X (u ≫ v) =
      sectionMap family X u ≫ sectionMap family X v := by
  sorry

/-- The source-text indexing diagram `a : j ⟶ i ↦ 𝒜_j(u_a(X))`. -/
noncomputable def sectionDiagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := sectionValue family X A
  map u := sectionMap family X u
  map_id A := sectionMap_id family X A
  map_comp u v := sectionMap_comp family X u v

private noncomputable abbrev pulledBackSectionDiagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
  (family : ColimitSiteStageFamily S)
  {i : S.I} (X : S.stage i) :
  (Over i)ᵒᵖ ⥤ Type u :=
  (Over.forget i).op ⋙ family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u) ⋙
    (evaluation _ (Type u)).obj (op ((S.stageCoconeFunctor i).obj X))

private theorem sourceToPulledBackTarget_eq
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    (((((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
            (S.stageTopology A.unop.left) S.colimitTopology) ⋙
          (S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous (Type u)
            (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj)
      (op (S.overImage X A)) =
      (pulledBackSectionDiagram family X).obj A := by
  sorry

private noncomputable def sourceToPulledBack
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    sectionDiagram family X ⟶ pulledBackSectionDiagram family X where
  app A :=
    (((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).unit.app
        (family.obj A.unop.left)).1.app
        (op (S.overImage X A)) ≫
      eqToHom (sourceToPulledBackTarget_eq family X A)
  naturality := by
    intro A B u
    sorry

private noncomputable abbrev globalSectionDiagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
  (family : ColimitSiteStageFamily S)
  {i : S.I} (X : S.stage i) :
  S.Iᵒᵖ ⥤ Type u :=
  family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u) ⋙
    (evaluation _ (Type u)).obj (op ((S.stageCoconeFunctor i).obj X))

end ColimitSiteStageFamily

/-- Every stage image object in the colimit site satisfies the cofinal finite overlap hypothesis
needed for Lemma `7.17.7 (4)`. -/
private theorem colimitSiteStage_hasCofinalFiniteQuasiCompactOverlapCoverings
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (X : S.stage i) :
    GrothendieckTopology.HasCofinalFiniteQuasiCompactOverlapCoverings S.colimitTopology
      ((S.stageCoconeFunctor i).obj X) := sorry

-- Proof sketch: map the source-text diagram `a : j ⟶ i ↦ 𝒜_j(u_a(X))` into the restriction of
-- the private pulled-back colimit-site diagram along `(Over i)ᵒᵖ ⥤ S.Iᵒᵖ`, use finality of
-- `(Over.forget i).op` to pass from arrows into `i` to the ambient filtered index category, and
-- then apply Lemma `7.17.7 (4)` to that derived diagram.
/-- Lemma 7.18.4: let `S` be a cofiltered inverse system of sites with finite covering families.
For a compatible family of stage sheaves `family : ColimitSiteStageFamily S`, the canonical map
from the source colimit
`\operatorname{colim}_{a : j \to i} \mathcal A_j(u_a(X))`
over arrows into the fixed stage `i` to the sections of the colimit sheaf at `u_i(X)` is
bijective. In Lean the indexing category is `(Over i)ᵒᵖ`. -/
noncomputable def colimitSiteStageFamilySectionsComparison
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    colimit (family.sectionDiagram X) ⟶
      (family.colimitSheaf).obj.obj (op ((S.stageCoconeFunctor i).obj X)) :=
  colimMap (family.sourceToPulledBack X) ≫
    (Functor.Final.colimitIso ((Over.forget i).op) (family.globalSectionDiagram X)).hom ≫
      (colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).inv ≫
      ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
        (op ((S.stageCoconeFunctor i).obj X)))

/-- Lemma 7.18.4, in the source-text bijectivity form. -/
theorem colimitSiteStageFamilySectionsComparison_bijective
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    Function.Bijective (colimitSiteStageFamilySectionsComparison S family X) := by
  sorry

end CategoryTheory
