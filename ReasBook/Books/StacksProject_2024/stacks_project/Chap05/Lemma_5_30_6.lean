import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.MonCat.Colimits
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.Topology.Algebra.Group.GroupTopology
import StacksProject_2024.stacks_project.Chap05.Lemma_5_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Monoidal MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/- Domain-style sampling for topological groups:
- primary domain: category-theoretic colimits of topological groups, organized canonically as
  group objects in `TopCat`
- sampled declarations in the same owner layer:
  `Grp TopCat`,
  `GroupTopology.coinduced`,
  `MonCat.Colimits.colimitCocone`,
  `MonCat.Colimits.colimitIsColimit`,
  `preservesColimit_of_preserves_colimit_cocone`
- best owner abstraction: `Grp TopCat`, with the underlying `GrpCat` colimit as primitive algebraic
  data and the coarsest compatible group topology as the topological bridge

Layer triage:
- `source-facing`: Lemma 5.30.6 asserts that `Grp TopCat` has colimits and that the forgetful
  functor to `GrpCat` preserves them
- `core/canonical`: the owner `Grp TopCat` and the forgetful bridge `forget₂ (Grp TopCat) GrpCat`
- `bridge/view`: the underlying `MonCat` colimit equipped first with its induced group structure and
  then with the infimum of the coinduced group topologies from the cocone maps

Primitive-vs-derived split:
- primitive data: the `MonCat` colimit carrier for the underlying group diagram, the induced
  inversion, and the resulting coinduced `GroupTopology` on that carrier
- derived API: the owner instances `HasColimits (Grp TopCat)` and
  `PreservesColimits (forget₂ (Grp TopCat) GrpCat)`
- the public surface should therefore install those owner instances directly, with the conjunction
  theorem kept only as a secondary summary
-/

namespace TopologicalGroupCat

noncomputable section

open MonCat.Colimits

variable {J : Type u} [Category.{u} J]

private abbrev underlyingMonoidDiagram (F : J ⥤ Grp TopCat.{u}) :=
  F ⋙ forget₂ (Grp TopCat.{u}) GrpCat.{u} ⋙ forget₂ GrpCat.{u} MonCat.{u}

private abbrev underlyingGrpDiagram (F : J ⥤ Grp TopCat.{u}) :=
  F ⋙ forget₂ (Grp TopCat.{u}) GrpCat.{u}

private def prequotientInv {F : J ⥤ Grp TopCat.{u}} :
    Prequotient (underlyingMonoidDiagram F) → Prequotient (underlyingMonoidDiagram F)
  | .of j x =>
      letI : Group ((underlyingMonoidDiagram F).obj j) := by
        change Group ((underlyingGrpDiagram F).obj j)
        infer_instance
      .of j x⁻¹
  | .one => .one
  | .mul x y => .mul (prequotientInv y) (prequotientInv x)

private theorem prequotientInv_rel {F : J ⥤ Grp TopCat.{u}}
    {x y : Prequotient (underlyingMonoidDiagram F)}
    (h : Relation (underlyingMonoidDiagram F) x y) :
    Relation (underlyingMonoidDiagram F) (prequotientInv x) (prequotientInv y) := by
  sorry

private instance colimitInv (F : J ⥤ Grp TopCat.{u}) :
    Inv (ColimitType (underlyingMonoidDiagram F)) where
  inv x :=
    Quotient.liftOn x
      (fun a ↦ Quotient.mk _ (prequotientInv a))
      (fun _ _ h ↦ by
        apply Quotient.sound
        exact prequotientInv_rel h)

private noncomputable instance colimitGroup (F : J ⥤ Grp TopCat.{u}) :
    Group (ColimitType (underlyingMonoidDiagram F)) where
  inv := (colimitInv F).inv
  inv_mul_cancel := by
    intro x
    sorry

private noncomputable def grpColimit (F : J ⥤ Grp TopCat.{u}) : GrpCat.{u} :=
  GrpCat.of (ColimitType (underlyingMonoidDiagram F))

private noncomputable def grpColimitCocone (F : J ⥤ Grp TopCat.{u}) :
    Cocone (underlyingGrpDiagram F) where
  pt := grpColimit F
  ι.app j := GrpCat.ofHom ((MonCat.Colimits.colimitCocone (underlyingMonoidDiagram F)).ι.app j).hom
  ι.naturality i j f := by
    apply (forget₂ GrpCat MonCat).map_injective
    simpa [underlyingGrpDiagram, underlyingMonoidDiagram] using
      (MonCat.Colimits.colimitCocone (underlyingMonoidDiagram F)).ι.naturality f

private def grpColimitIsColimit (F : J ⥤ Grp TopCat.{u}) :
    IsColimit (grpColimitCocone F) := by
  sorry

private def admissibleGroupTopologies {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : Set (GroupTopology c.pt) :=
  { t | ∀ j,
      letI : TopologicalSpace ((underlyingGrpDiagram F).obj j) := (F.obj j).X.str
      GroupTopology.coinduced (c.ι.app j).hom ≤ t }

private def coinducedGroupTopology {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : GroupTopology c.pt :=
  sInf (admissibleGroupTopologies c)

private def topologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : Grp TopCat.{u} :=
  let t := coinducedGroupTopology c
  letI : TopologicalSpace c.pt := t.toTopologicalSpace
  letI : IsTopologicalGroup c.pt := t.toIsTopologicalGroup
  letI : GrpObj (TopCat.of c.pt) :=
    { one := TopCat.ofHom ⟨fun _ ↦ 1, continuous_const⟩
      mul := TopCat.ofHom ⟨fun p ↦ p.1 * p.2, continuous_mul⟩
      one_mul := by
        sorry
      mul_one := by
        sorry
      mul_assoc := by
        sorry
      inv := TopCat.ofHom ⟨fun x ↦ x⁻¹, continuous_inv⟩
      left_inv := by
        sorry
      right_inv := by
        sorry }
  { X := TopCat.of c.pt }

private def toTopologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    F.obj j ⟶ topologicalColimit c := by
  let t := coinducedGroupTopology c
  letI : TopologicalSpace c.pt := t.toTopologicalSpace
  letI : IsTopologicalGroup c.pt := t.toIsTopologicalGroup
  let f : (F.obj j).X →ₜ* (topologicalColimit c).X :=
    { toFun := (c.ι.app j).hom
      map_one' := by
        sorry
      map_mul' := by
        sorry
      continuous_toFun := by
        sorry }
  haveI : IsMonHom (show (F.obj j).X ⟶ (topologicalColimit c).X from TopCat.ofHom f.toContinuousMap) := by
    sorry
  exact Grp.homMk (show (F.obj j).X ⟶ (topologicalColimit c).X from TopCat.ofHom f.toContinuousMap)

private def topologicalColimitCocone (F : J ⥤ Grp TopCat.{u}) : Cocone F where
  pt := topologicalColimit (grpColimitCocone F)
  ι.app j := toTopologicalColimit (grpColimitCocone F) j
  ι.naturality i j f := by
    sorry

private def topologicalColimitIsColimit (F : J ⥤ Grp TopCat.{u}) :
    IsColimit (topologicalColimitCocone F) := by
  sorry

instance hasColimitsOfShape (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (Grp TopCat.{u}) where
  has_colimit F := ⟨⟨topologicalColimitCocone F, topologicalColimitIsColimit F⟩⟩

/-- Lemma 5.30.6 (1): the category of topological groups has colimits of every small shape. -/
instance hasColimits : HasColimits (Grp TopCat.{u}) where
  has_colimits_of_shape K _ := by
    infer_instance

instance forgetToGrpCat_preservesColimitsOfShape (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesColimit := fun {F} ↦ by
    sorry

/-- Lemma 5.30.6 (2): the forgetful functor from topological groups to groups preserves colimits. -/
instance forgetToGrpCat_preservesColimits :
    PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesColimitsOfShape {J} := by
    infer_instance

end

end TopologicalGroupCat

/-- Summary theorem collecting the colimit existence and preservation instances for
`Grp TopCat`. -/
theorem topologicalGroupCat_hasColimits_and_forgetToGrpCat_preservesColimits :
    HasColimits (Grp TopCat.{u}) ∧
      PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) := by
  exact ⟨TopologicalGroupCat.hasColimits, TopologicalGroupCat.forgetToGrpCat_preservesColimits⟩
