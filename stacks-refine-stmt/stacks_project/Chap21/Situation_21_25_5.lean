import Mathlib
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import stacks_project.Chap07.Definition_7_40_2
import stacks_project.Chap18.Definition_18_6_1

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
  cohomology of `\mathcal O_X`-modules evaluated on the pulled-back source objects `f^{-1}(V')`;
- sampled owner declarations:
  `GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `GrothendieckTopology.CoversTop`,
  `CategoryTheory.Limits.FormalCoproduct`,
  `Sheaf.H'`;
- best owner abstraction for the source-facing item: the present structure
  `bounded_cohomology_basis`, because the source packages extra data beyond the canonical
  cover-existence owner `Y.siteTopology.HasEnoughObjectsWithProperty (· ∈ B')`, namely chosen
  covering families on `Y`, chosen cohomological bounds, chosen cofinal systems of coverings in
  the slice topology, and the basiswise vanishing condition after pulling objects back along
  `f.base`;
- primitive data: the basis set on `Y`, chosen covering families by basis objects, the bound
  attached to each basis object, the cofinal covering systems, and the pulled-back
  cohomology-vanishing condition;
- derived API: the canonical cover-existence owner
  `Y.siteTopology.HasEnoughObjectsWithProperty (· ∈ basis)` and the coercion to the underlying
  subset of target-site objects.

Source/core/bridge triage:
- source-facing: `bounded_cohomology_basis`;
- core/canonical pieces reused internally: `HasEnoughObjectsWithProperty`, `CoversTop`,
  `FormalCoproduct`, and the cohomology functors `H'`;
- bridge/view: the coercion from a bounded-cohomology basis to its underlying subset of objects.

The weak-Serre closure assumptions on `A` are not primitive data for this situation and do not
appear in the fields below, so they should not be kept in the public owner signature. -/

/-- Situation 21.25.5: for a morphism of ringed sites `f : X ⟶ Y` with underlying continuous
functor `f.base : Y ⥤ X`, and for a weak Serre subcategory `A ⊆ Mod(\mathcal O_X)`, there is a
subset `B'` of objects of `Y` covering every object of `Y` such that for each `V' ∈ B'` there is
a bound `d_{V'}` and a cofinal system of coverings of `V'` whose members `V'_i` satisfy
`H^p(f.base.obj V'_i, ℱ) = 0` for every `ℱ ∈ A` and every `p > d_{V'}`. -/
structure bounded_cohomology_basis (A : ObjectProperty ModX) where
  /-- The chosen subset `B'` of objects of the target site. -/
  basis : Set Y
  /-- Every object of the target site admits a chosen covering by objects in the subset `B'`. -/
  cover_by_basis :
    ∀ V' : Y, ∃ cover : FormalCoproduct.{w} (Over V'),
      (Y.siteTopology.over V').CoversTop cover.obj ∧
        ∀ i : cover.I, (cover.obj i).left ∈ basis
  /-- The integer cohomological bound `d_{V'}` attached to a basis object `V'`. -/
  cohomology_bound {V' : Y} (hV' : V' ∈ basis) : ℤ
  /-- The chosen cofinal system of coverings of a basis object `V'`. -/
  covering_system {V' : Y} (hV' : V' ∈ basis) : Set (FormalCoproduct.{w} (Over V'))
  /-- Each selected element of the cofinal system is an actual covering of `V'`. -/
  covering_system_isCover {V' : Y} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{w} (Over V')} :
      cover ∈ covering_system hV' → (Y.siteTopology.over V').CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object `V'`. -/
  covering_system_cofinal {V' : Y} (hV' : V' ∈ basis) {ι : Type w} (family : ι → Over V') :
      (Y.siteTopology.over V').CoversTop family →
        ∃ cover : FormalCoproduct.{w} (Over V'),
          cover ∈ covering_system hV' ∧
            Nonempty (cover ⟶ FormalCoproduct.mk ι family)
  /-- Every member of every selected covering of a basis object `V'` has vanishing cohomology in
  degrees strictly larger than the chosen bound `d_{V'}` for all modules belonging to `A`. -/
  higher_cohomology_isZero {V' : Y} (hV' : V' ∈ basis)
      {cover : FormalCoproduct.{w} (Over V')} :
      cover ∈ covering_system hV' →
        ∀ i : cover.I, ∀ p : ℕ, cohomology_bound hV' < p →
          ∀ ⦃ℱ : ModX⦄, A ℱ →
            IsZero
              (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H' p
                (f.base.obj (cover.obj i).left))

namespace bounded_cohomology_basis

/-- The chosen covering families in a bounded-cohomology basis induce the canonical owner
`HasEnoughObjectsWithProperty` for the underlying subset of target-site objects. -/
theorem hasEnoughObjectsWithProperty
    {A : ObjectProperty ModX} (hB : bounded_cohomology_basis f A) :
    Y.siteTopology.HasEnoughObjectsWithProperty (· ∈ hB.basis) := by
  intro V'
  rcases hB.cover_by_basis V' with ⟨cover, hcover, hbasis⟩
  refine ⟨?_, ?_⟩
  · exact ⟨cover.I, cover.obj, hcover⟩
  · intro i
    exact hbasis i

end bounded_cohomology_basis

/-- A bounded-cohomology basis on the target ringed site can be used as its underlying subset of
objects. -/
instance bounded_cohomology_basis_coeSet
    (A : ObjectProperty ModX) :
    CoeOut (bounded_cohomology_basis f A) (Set Y) where
  coe h := h.basis

end RingedSite.Hom
