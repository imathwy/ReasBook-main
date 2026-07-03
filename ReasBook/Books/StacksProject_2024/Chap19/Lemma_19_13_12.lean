import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 19.13.12:
- primary domain: filtered complexes in a Grothendieck abelian category and their realization in
  the derived category;
- sampled owner declarations:
  `Cocone`,
  `FilteredComplex`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.stageInclusion`,
  `FilteredComplex.stageMapOfLE`,
  `DerivedCategory.Q`,
  `Cocone.precompose`;
- best owner abstraction: `FilteredComplex A`;
- primitive data: a filtered complex `K : FilteredComplex A`;
- derived API: the stage tower `K.stageTower : ℤᵒᵖ ⥤ DerivedCategory A`, its canonical cocone
  `K.stageTowerCocone`, and the comparison to a given cocone `c : Cocone system` via
  `Cocone.precompose`;
- source/core/bridge triage:
  `source-facing`: `FilteredComplex.RealizesInverseSystem` and the existence theorem below;
  `core/canonical`: the owner object `FilteredComplex A`;
  `bridge/view`: the derived-category functor `stageTower`, the cocone `stageTowerCocone`, and
    cocone isomorphisms against a prescribed inverse-system cocone.

The previous version still unpacked realization as objectwise isomorphisms plus manually stated
compatibility squares. This file keeps the owner public and records the compatible target family at
the canonical functor/cocone layer. -/

namespace FilteredComplex

/-- The inverse-system tower in `D(A)` attached to the filtration stages of `K`. -/
noncomputable def stageTower (K : FilteredComplex A) : ℤᵒᵖ ⥤ DerivedCategory A where
  obj i := DerivedCategory.Q.obj (K.stage i.unop)
  map {i j} f := DerivedCategory.Q.map (K.stageMapOfLE f.unop.le)
  map_id i := by
    simp [FilteredComplex.stageMapOfLE_refl]
  map_comp f g := by
    rw [← DerivedCategory.Q.map_comp, FilteredComplex.stageMapOfLE_comp]

/-- The canonical cocone from the stage tower of `K` to the derived object represented by its
underlying complex. -/
noncomputable def stageTowerCocone (K : FilteredComplex A) : Cocone K.stageTower where
  pt := DerivedCategory.Q.obj K.underlying
  ι :=
    { app := fun i ↦ DerivedCategory.Q.map (K.stageInclusion i.unop)
      naturality := by
        intro i j f
        change
          DerivedCategory.Q.map (K.stageMapOfLE f.unop.le) ≫
              DerivedCategory.Q.map (K.stageInclusion j.unop) =
            DerivedCategory.Q.map (K.stageInclusion i.unop)
        rw [← DerivedCategory.Q.map_comp, FilteredComplex.stageMapOfLE_comp_stageInclusion] }

/-- A filtered complex realizes an inverse system in the derived category if its stage tower is
naturally isomorphic to the system and its canonical cocone identifies with the prescribed cocone
after transport along that natural isomorphism. -/
def RealizesInverseSystem
    (K : FilteredComplex A) {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system) : Prop :=
  ∃ stageIso : K.stageTower ≅ system,
    ∃ coconeHom : K.stageTowerCocone ⟶ (Cocone.precompose stageIso.hom).obj c,
      IsIso coconeHom

end FilteredComplex

variable [IsGrothendieckAbelian.{w} A]

-- Proof sketch: choose a K-injective complex representing `c.pt`, realize the inverse system by a
-- compatible tower of complexes mapping to that representative, and then build a filtered
-- cochain complex whose `i`-th stage is the chosen complex for `E^i`. The compatibility of the
-- tower maps with the cocone legs into `c.pt` gives the stated stagewise identifications in the derived
-- category.
/-- Lemma 19.13.12: for a compatible inverse system
`... ⟶ E^{i + 1} ⟶ E^i ⟶ E^{i - 1} ⟶ ... ⟶ E` in the derived category of a Grothendieck abelian
category, encoded by a cocone `c : Cocone system`, there exists a filtered complex whose
underlying complex represents `c.pt` and whose
filtration stages `F^i K^•` represent the objects `E^i` compatibly with the given cocone legs. -/
theorem exists_filteredCochainComplexRealization_of_inverseSystem
    (system : ℤᵒᵖ ⥤ DerivedCategory A) (c : Cocone system) :
    ∃ K : FilteredComplex A, K.RealizesInverseSystem c := sorry

end

end CategoryTheory
