import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.stacks_project.Chap07.HasEnoughObjectsWithProperty
import StacksProject_2024.stacks_project.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
local notation "ModX" => SheafOfModules X.structureSheaf

/- Domain-style sampling for Situation 21.25.5:
- primary domain: Grothendieck-topology covering families on the target site together with
  cohomology of `𝒪_X`-modules evaluated on the pulled-back source objects `f⁻¹(V')`;
- sampled owner declarations:
  `GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `GrothendieckTopology.CoversTop`,
  `CategoryTheory.Limits.FormalCoproduct`,
  `Sheaf.H'`;
- best owner abstraction for the source-facing item: the present structure
  `BoundedCohomologyBasis`, because the source adds cohomological bounds, cofinal systems of
  coverings in the slice topology, and the basiswise vanishing condition after pulling objects
  back along `f.base` on top of the canonical cover-existence owner
  `Y.siteTopology.HasEnoughObjectsWithProperty (· ∈ B')`;
- primitive data: the basis set on `Y`, the canonical enough-objects witness for that basis, the
  bound attached to each basis object, the cofinal covering systems, and the pulled-back
  cohomology-vanishing condition;
- derived API: the coercion to the underlying subset of target-site objects together with the
  canonical membership bridge.

Source/core/bridge triage:
- source-facing: `BoundedCohomologyBasis`;
- core/canonical pieces reused internally: `HasEnoughObjectsWithProperty`, `CoversTop`,
  `FormalCoproduct`, and the cohomology functors `H'`;
- bridge/view: the coercion from a bounded-cohomology basis to its underlying subset of objects.

The weak-Serre closure assumptions on `A` are not primitive data for this situation and do not
appear in the fields below, so they should not be kept in the public owner signature. -/

/-- Situation 21.25.5: for a morphism of ringed sites `f : X ⟶ Y` with underlying continuous
functor `f.base : Y ⥤ X`, and for a weak Serre subcategory `A ⊆ ModX`, there is a subset `B'` of
objects of `Y` covering every object of `Y` such that for each `V' ∈ B'` there is a bound `d_V'`
and a cofinal system of coverings of `V'` whose members `V'_i` satisfy
`H^p(f.base.obj V'_i, ℱ) = 0` for every `ℱ ∈ A` and every `p > d_V'`. -/
@[stacks 0D6V]
structure BoundedCohomologyBasis (A : ObjectProperty ModX) where
  /-- The chosen subset `B'` of objects of the target site. -/
  basis : Set Y
  /-- Every object of the target site admits a covering by objects in the subset `B'`. -/
  hasEnoughObjectsWithProperty :
    Y.siteTopology.HasEnoughObjectsWithProperty (· ∈ basis)
  /-- The integer cohomological bound `d_V'` attached to a basis object `V'`. -/
  cohomology_bound {V' : Y} (hV' : V' ∈ basis) : ℤ
  /-- The chosen cofinal system of coverings of a basis object `V'`. -/
  covering_system {V' : Y} (hV' : V' ∈ basis) : Set (FormalCoproduct.{w} (Over V'))
  /-- Each selected element of the cofinal system is an actual covering of `V'`. -/
  covering_system_isCover {V' : Y} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{w} (Over V')} (hcover : cover ∈ covering_system hV') :
      (Y.siteTopology.over V').CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object `V'`. -/
  covering_system_cofinal {V' : Y} (hV' : V' ∈ basis) {ι : Type w} (family : ι → Over V')
      (hfamily : (Y.siteTopology.over V').CoversTop family) :
        ∃ cover : FormalCoproduct.{w} (Over V'),
          cover ∈ covering_system hV' ∧
            Nonempty (cover ⟶ FormalCoproduct.mk ι family)
  /-- Every member of every selected covering of a basis object `V'` has vanishing cohomology in
  degrees strictly larger than the chosen bound `d_V'` for all modules belonging to `A`. -/
  higher_cohomology_isZero {V' : Y} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{w} (Over V')} (hcover : cover ∈ covering_system hV')
      (i : cover.I) (p : ℕ) (hp : cohomology_bound hV' < p) {ℱ : ModX} (hℱ : A ℱ) :
      IsZero
        (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H' p
          (f.base.obj (cover.obj i).left))

/-- A bounded-cohomology basis on the target ringed site can be used as its underlying subset of
objects. -/
instance (A : ObjectProperty ModX) :
    CoeOut (BoundedCohomologyBasis f A) (Set Y) where
  coe h := h.basis

instance (A : ObjectProperty ModX) :
    Membership Y (BoundedCohomologyBasis f A) where
  mem basis V := V ∈ basis.basis

end RingedSite.Hom
