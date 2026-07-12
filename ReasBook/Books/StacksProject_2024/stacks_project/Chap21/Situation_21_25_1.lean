import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.Chap07.HasEnoughObjectsWithProperty

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe wι w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat] [HasExt (Sheaf J AddCommGrpCat)]

/- Domain-style sampling for Situation 21.25.1:
- primary domain: Grothendieck-topology covering families in slice sites together with sheaf
  cohomology on those basis objects;
- sampled owner declarations:
  `GrothendieckTopology.CoversTop`,
  `GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `CategoryTheory.Limits.FormalCoproduct`,
  `Sheaf.H'`;
- best owner abstraction for the source-facing item: the present structure
  `BoundedCohomologyBasis`, because the source packages extra data beyond the canonical
  cover-existence owner `J.HasEnoughObjectsWithProperty (· ∈ B)`, namely chosen cohomological
  bounds, chosen cofinal systems of coverings in the slice topology, and the basiswise vanishing
  hypothesis on those coverings;
- primitive data: the basis set, cover-existence on the site, the bound attached to each basis
  object, the cofinal covering systems, and the vanishing condition;
- derived API: only the coercion to the underlying set of basis objects.

Source/core/bridge triage:
- source-facing: `BoundedCohomologyBasis`;
- core/canonical pieces reused internally: `CoversTop`, `FormalCoproduct`, and the cohomology
  functors `H'`;
- bridge/view: the coercion from a bounded-cohomology basis to its underlying subset of objects.

The weak-Serre closure assumptions on `A` are not primitive data for this situation and do not
appear in the fields below, so they should not be kept in the public owner signature. -/

/-- Situation 21.25.1: for a site `(𝒞, J)`, a sheaf of rings `𝒪`, and a weak Serre subcategory
`𝒜 ⊂ Mod(𝒪)`, a choice of basis objects `B ⊂ C` covering every object together with, for each
`V ∈ B`, an integer bound `d_V` and a cofinal family of coverings of `V` whose members have
vanishing cohomology `H^p(V_i, 𝓕)` for every `𝓕 ∈ 𝒜` and every `p > d_V`. -/
@[stacks 0D6R]
structure BoundedCohomologyBasis
    (𝒪 : Sheaf J RingCat.{w}) (A : ObjectProperty (SheafOfModules 𝒪)) where
  /-- The chosen subset `B` of objects of the site. -/
  basis : Set C
  /-- Every object of the site admits a covering by objects in the chosen subset `B`. -/
  hasEnoughObjectsWithProperty :
    J.HasEnoughObjectsWithProperty (· ∈ basis)
  /-- The integer cohomological bound `d_V` attached to a basis object `V`. -/
  cohomology_bound {V : C} (hV : V ∈ basis) : ℤ
  /-- The chosen cofinal system of coverings of a basis object `V`. -/
  covering_system {V : C} (hV : V ∈ basis) : Set (FormalCoproduct.{wι} (Over V))
  /-- Each selected element of the cofinal system is an actual covering of `V`. -/
  covering_system_isCover {V : C} (hV : V ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ covering_system hV) :
      (J.over V).CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object `V`. -/
  covering_system_cofinal {V : C} (hV : V ∈ basis) {ι : Type wι} (family : ι → Over V)
      (hfamily : (J.over V).CoversTop family) :
      ∃ cover : FormalCoproduct.{wι} (Over V),
        cover ∈ covering_system hV ∧
          Nonempty (cover ⟶ FormalCoproduct.mk ι family)
  /-- Every member of every selected covering of a basis object `V` has vanishing cohomology in
  degrees strictly larger than the chosen bound `d_V` for all modules belonging to `A`. -/
  higher_cohomology_isZero {V : C} (hV : V ∈ basis)
      {cover : FormalCoproduct.{wι} (Over V)} (hcover : cover ∈ covering_system hV)
      (i : cover.I) (p : ℕ) (hp : cohomology_bound hV < p) {ℱ : SheafOfModules 𝒪} (hℱ : A ℱ) :
      IsZero (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p (cover.obj i).left)

/-- A bounded-cohomology basis can be used as its underlying subset of site objects. -/
instance (𝒪 : Sheaf J RingCat.{w}) (A : ObjectProperty (SheafOfModules 𝒪)) :
    CoeOut (BoundedCohomologyBasis 𝒪 A) (Set C) where
  coe h := h.basis

instance (𝒪 : Sheaf J RingCat.{w}) (A : ObjectProperty (SheafOfModules 𝒪)) :
    Membership C (BoundedCohomologyBasis 𝒪 A) where
  mem basis V := V ∈ basis.basis

namespace BoundedCohomologyBasis

variable {𝒪 : Sheaf J RingCat.{w}} {A : ObjectProperty (SheafOfModules 𝒪)}

/-- Helper for Situation 21.25.1: the coercion from a bounded-cohomology basis to a set is its
underlying subset of objects. -/
@[simp]
theorem coeSet_eq_basis (basis : BoundedCohomologyBasis 𝒪 A) :
    (basis : Set C) = basis.basis := by
  -- This coercion is definitionally the stored subset.
  rfl

/-- Helper for Situation 21.25.1: membership in a bounded-cohomology basis is membership in its
underlying subset of objects. -/
@[simp]
theorem mem_basis_iff (basis : BoundedCohomologyBasis 𝒪 A) {V : C} :
    V ∈ basis ↔ V ∈ basis.basis := by
  -- The membership instance is defined directly from the underlying subset.
  rfl

/-- Helper for Situation 21.25.1: the underlying subset of a bounded-cohomology basis covers every
object of the site. -/
theorem hasEnoughObjects (basis : BoundedCohomologyBasis 𝒪 A) :
    J.HasEnoughObjectsWithProperty (· ∈ basis) := by
  -- This is exactly the stored cover-existence field, viewed through the membership bridge.
  exact basis.hasEnoughObjectsWithProperty

/-- Helper for Situation 21.25.1: a selected element of the covering system is a covering in the
slice topology. -/
theorem coveringSystem_isCover (basis : BoundedCohomologyBasis 𝒪 A)
    {V : C} (hV : V ∈ basis) {cover : FormalCoproduct.{wι} (Over V)}
    (hcover : cover ∈ basis.covering_system hV) :
    (J.over V).CoversTop cover.obj := by
  -- This accessor just exposes the structure field at the requested basis object.
  exact basis.covering_system_isCover hV hcover

/-- Helper for Situation 21.25.1: selected covering systems are cofinal among all coverings of a
basis object. -/
theorem exists_coveringSystem_refinement (basis : BoundedCohomologyBasis 𝒪 A)
    {V : C} (hV : V ∈ basis) {ι : Type wι} (family : ι → Over V)
    (hfamily : (J.over V).CoversTop family) :
    ∃ cover : FormalCoproduct.{wι} (Over V),
      cover ∈ basis.covering_system hV ∧
        Nonempty (cover ⟶ FormalCoproduct.mk ι family) := by
  -- Cofinality is already one of the chosen pieces of structure.
  exact basis.covering_system_cofinal hV family hfamily

/-- Helper for Situation 21.25.1: each member of a selected covering satisfies the prescribed
higher-cohomology vanishing bound. -/
theorem higherCohomology_isZero (basis : BoundedCohomologyBasis 𝒪 A)
    {V : C} (hV : V ∈ basis) {cover : FormalCoproduct.{wι} (Over V)}
    (hcover : cover ∈ basis.covering_system hV) (i : cover.I) (p : ℕ)
    (hp : basis.cohomology_bound hV < p) {ℱ : SheafOfModules 𝒪} (hℱ : A ℱ) :
    IsZero (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p (cover.obj i).left) := by
  -- This is the source-facing vanishing hypothesis recorded in the basis data.
  exact basis.higher_cohomology_isZero hV hcover i p hp hℱ

end BoundedCohomologyBasis

end CategoryTheory.GrothendieckTopology
