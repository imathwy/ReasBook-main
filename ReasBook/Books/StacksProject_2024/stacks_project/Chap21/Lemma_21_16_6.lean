import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import StacksProject_2024.Chap21.Lemma_21_7_2
import StacksProject_2024.Chap21.Lemma_21_16_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory

open CofilteredSiteDiagram Sheaf

/- Domain-style sampling for Lemma 21.16.6:
- primary domain: cohomology comparison for a compatible inverse system of abelian sheaves on a
  cofiltered inverse system of sites;
- sampled owner declarations:
  `CofilteredSiteDiagram.StageFamily`,
  `CofilteredSiteDiagram.StageFamily.diagram`,
  `CofilteredSiteDiagram.StageFamily.colimitSheaf`,
  `Sheaf.cohomologyOverColimitComparison_isIso_of_cofinal_finite_coverings`,
  `Functor.Final.colimitIso`,
  `colimit.post`;
- best owner abstraction: `CofilteredSiteDiagram.StageFamily S AddCommGrpCat`;
- primitive data: the stagewise abelian sheaves and their pullback transition morphisms;
- derived API: the ambient fixed-object cohomology diagram on `S.Iᵒᵖ`, its restriction to
  `(Over i)ᵒᵖ`, and the canonical colimit comparison obtained from finality and `colimit.post`.

Source/core/bridge triage:
- `source-facing`: Lemma 21.16.6, whose source colimit is indexed by arrows `a : j ⟶ i`;
- `core/canonical`: `StageFamily.diagram` together with the ambient colimit comparison
  `colimit.post`;
- `bridge/view`: restricting the ambient `S.Iᵒᵖ`-indexed cohomology diagram along
  `(Over.forget i).op`.
-/

variable (S : CofilteredSiteDiagram.{u, u, u})

section ColimitComparison

variable [HasColimit S.diagram]
variable [∀ i : S.I, HasWeakSheafify (S.stageTopology i) AddCommGrpCat]
variable [∀ i : S.I, HasSheafify (S.stageTopology i) AddCommGrpCat]
variable [∀ i : S.I, HasExt (Sheaf (S.stageTopology i) AddCommGrpCat)]
variable [HasWeakSheafify S.colimitTopology AddCommGrpCat]
variable [HasSheafify S.colimitTopology AddCommGrpCat]
variable [HasExt (Sheaf S.colimitTopology AddCommGrpCat)]
variable [∀ {i j : S.I} (a : j ⟶ i),
  ∀ G : (S.stage i)ᵒᵖ ⥤ AddCommGrpCat, (S.stageFunctor a).op.HasLeftKanExtension G]
variable [∀ i : S.I,
  ∀ G : (S.stage i)ᵒᵖ ⥤ AddCommGrpCat, (S.stageCoconeFunctor i).op.HasLeftKanExtension G]
variable [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat)]

/-- The fixed-object cohomology functor on the colimit site at `u_i(X)`. -/
abbrev stageObjectCohomologyAt
    (p : ℕ) {i : S.I} (X : S.stage i) :
    Sheaf S.colimitTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  cohomologyPresheafFunctor S.colimitTopology p ⋙
    (evaluation _ AddCommGrpCat.{u}).obj (op ((S.stageCoconeFunctor i).obj X))

/-- The ambient `S.Iᵒᵖ`-indexed cohomology diagram on the colimit site attached to `F`. -/
abbrev stageObjectCohomologyDiagram
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i) :
    S.Iᵒᵖ ⥤ AddCommGrpCat.{u} :=
  F.diagram ⋙ stageObjectCohomologyAt S p X

/-- The `(Over i)ᵒᵖ`-indexed source diagram of Lemma 21.16.6, realized canonically as the
restriction of the ambient colimit-site cohomology diagram along `(Over.forget i).op`. -/
abbrev inverseSystemStageObjectCohomologyDiagram
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Over.forget i).op ⋙ stageObjectCohomologyDiagram S F p X

/-- Objectwise, the restricted ambient diagram recovers the source-text term
`H^p(u_a(X), 𝓕_j)` for `a : j ⟶ i`. -/
theorem inverseSystemStageObjectCohomologyDiagram_obj_isomorphic
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    IsIsomorphic
      ((inverseSystemStageObjectCohomologyDiagram S F p X).obj A)
      ((F.obj A.unop.left).H' p (S.overImage X A)) := by
  sorry

-- Proof sketch: apply Lemma `21.16.1` to the ambient filtered diagram
-- `CofilteredSiteDiagram.StageFamily.diagram F` on the colimit site, then restrict along
-- `(Over.forget i).op` and use finality to identify the restricted colimit with the ambient one.
/-- The canonical comparison morphism in Lemma 21.16.6 from the over-category colimit to the
cohomology of the colimit sheaf at `u_i(X)`. This is the finality comparison followed by the
ambient canonical comparison `colimit.post F.diagram (stageObjectCohomologyAt S p X)`. -/
noncomputable def inverseSystemStageObjectCohomologyColimitComparison
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i) :
    colimit (inverseSystemStageObjectCohomologyDiagram S F p X) ⟶
      F.colimitSheaf.H' p ((S.stageCoconeFunctor i).obj X) :=
  (Functor.Final.colimitIso ((Over.forget i).op) (stageObjectCohomologyDiagram S F p X)).hom ≫
    colimit.post F.diagram (stageObjectCohomologyAt S p X)

/-- The canonical comparison morphism of Lemma 21.16.6 is an isomorphism. -/
theorem inverseSystemStageObjectCohomologyColimitComparison_isIso
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i) :
    IsIso
      ((inverseSystemStageObjectCohomologyColimitComparison S F p X) :
        colimit (inverseSystemStageObjectCohomologyDiagram S F p X) ⟶
          F.colimitSheaf.H' p ((S.stageCoconeFunctor i).obj X)) := by
  sorry

/-- Lemma 21.16.6: for an inverse system of abelian sheaves on a cofiltered inverse system of
sites with colimit sheaf `𝓕 = colim_i u_i⁻¹ 𝓕_i`, the filtered colimit over arrows `a : j ⟶ i` of
the source-text terms `H^p(u_a(X), 𝓕_j)` is canonically isomorphic to the cohomology of `𝓕` over
`u_i(X)`. In Lean the source colimit is represented by the canonical restricted diagram
`inverseSystemStageObjectCohomologyDiagram`, and
`inverseSystemStageObjectCohomologyDiagram_obj_isomorphic` records its objectwise identification
with the source-text terms. -/
@[stacks 09YP]
theorem inverseSystemStageObjectCohomologyColimit_isomorphic
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i) :
    IsIsomorphic
      (colimit (inverseSystemStageObjectCohomologyDiagram S F p X))
      (F.colimitSheaf.H' p ((S.stageCoconeFunctor i).obj X)) := by
  let φ := inverseSystemStageObjectCohomologyColimitComparison S F p X
  haveI : IsIso φ := inverseSystemStageObjectCohomologyColimitComparison_isIso S F p X
  exact ⟨asIso φ⟩

end ColimitComparison

end CategoryTheory
