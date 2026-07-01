import Mathlib

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
  `bounded_cohomology_basis`, because the source packages extra data beyond the canonical
  cover-existence owner `J.HasEnoughObjectsWithProperty (· ∈ B)`, namely chosen cohomological
  bounds, chosen cofinal systems of coverings in the slice topology, and the basiswise vanishing
  hypothesis on those coverings;
- primitive data: the basis set, cover-existence on the site, the bound attached to each basis
  object, the cofinal covering systems, and the vanishing condition;
- derived API: only the coercion to the underlying set of basis objects.

Source/core/bridge triage:
- source-facing: `bounded_cohomology_basis`;
- core/canonical pieces reused internally: `CoversTop`, `FormalCoproduct`, and the cohomology
  functors `H'`;
- bridge/view: the coercion from a bounded-cohomology basis to its underlying subset of objects.

The weak-Serre closure assumptions on `A` are not primitive data for this situation and do not
appear in the fields below, so they should not be kept in the public owner signature. -/

/-- Situation 21.25.1: for a site `(\mathcal C, J)`, a sheaf of rings `\mathcal O`, and a weak
Serre subcategory `\mathcal A \subset \mathrm{Mod}(\mathcal O)`, a choice of basis objects
`B ⊂ \mathrm{Ob}(\mathcal C)` covering every object together with, for each `V ∈ B`, an integer
bound `d_V` and a cofinal family of coverings of `V` whose members have vanishing cohomology
`H^p(V_i, \mathcal F)` for every `\mathcal F ∈ \mathcal A` and every `p > d_V`. -/
structure bounded_cohomology_basis
    (𝒪 : Sheaf J RingCat.{w}) (A : ObjectProperty (SheafOfModules 𝒪)) where
  /-- The chosen subset `B` of objects of the site. -/
  basis : Set C
  /-- Every object of the site admits a covering by objects in the chosen subset `B`. -/
  cover_by_basis :
    ∀ U : C, ∃ cover : FormalCoproduct.{wι} (Over U),
      (J.over U).CoversTop cover.obj ∧
        ∀ i : cover.I, (cover.obj i).left ∈ basis
  /-- The integer cohomological bound `d_V` attached to a basis object `V`. -/
  cohomology_bound : ∀ ⦃V : C⦄, V ∈ basis → ℤ
  /-- The chosen cofinal system of coverings of a basis object `V`. -/
  covering_system : ∀ ⦃V : C⦄, V ∈ basis → Set (FormalCoproduct.{wι} (Over V))
  /-- Each selected element of the cofinal system is an actual covering of `V`. -/
  covering_system_isCover :
    ∀ ⦃V : C⦄ (hV : V ∈ basis) ⦃cover : FormalCoproduct.{wι} (Over V)⦄,
      cover ∈ covering_system hV → (J.over V).CoversTop cover.obj
  /-- The selected coverings are cofinal among all coverings of a basis object `V`. -/
  covering_system_cofinal :
    ∀ ⦃V : C⦄ (hV : V ∈ basis) {ι : Type wι} (family : ι → Over V),
      (J.over V).CoversTop family →
        ∃ cover : FormalCoproduct.{wι} (Over V),
          cover ∈ covering_system hV ∧
            Nonempty (cover ⟶ FormalCoproduct.mk ι family)
  /-- Every member of every selected covering of a basis object `V` has vanishing cohomology in
  degrees strictly larger than the chosen bound `d_V` for all modules belonging to `A`. -/
  higher_cohomology_isZero :
    ∀ ⦃V : C⦄ (hV : V ∈ basis) ⦃cover : FormalCoproduct.{wι} (Over V)⦄,
      cover ∈ covering_system hV →
        ∀ i : cover.I, ∀ p : ℕ, cohomology_bound hV < p →
          ∀ ⦃ℱ : SheafOfModules 𝒪⦄, A ℱ →
            IsZero (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p (cover.obj i).left)

/-- A bounded-cohomology basis can be used as its underlying subset of site objects. -/
instance bounded_cohomology_basis_coeSet
    (𝒪 : Sheaf J RingCat.{w}) (A : ObjectProperty (SheafOfModules 𝒪)) :
    CoeOut (bounded_cohomology_basis 𝒪 A) (Set C) where
  coe h := h.basis

end CategoryTheory.GrothendieckTopology
