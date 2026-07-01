import stacks_project.Chap12.Lemma_12_19_4
import stacks_project.Chap12.Lemma_12_19_7
import stacks_project.Chap12.Lemma_12_19_8
import stacks_project.Chap12.Aux_12_20_2_1

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem subobjectSubquotientProjection_condition {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY = 0 := by
  simp [subobjectQuotientMap, Category.assoc]

namespace FilteredObject

variable (A : FilteredObject C)
variable {X Y : Subobject A.obj}

/-
Source/core/bridge triage for Lemma 12.19.9:
- source-facing: the filtered subquotient `Y / X` for `X ≤ Y ≤ A` and the canonical filtered map
  `Y ⟶ Y / X`
- core/canonical owners: `subobjectFilteredObject`, `quotientFilteredObject`,
  `FilteredObject.Hom.Strict`, `strict_iff_induced_filtration_of_mono`,
  `strict_iff_quotient_filtration_of_epi`, `strict_comp_of_mono`, `strict_comp_of_epi`
- bridge/view: the induced filtered map `X ⟶ Y`; the maps `Y ⟶ A / X` and `Y / X ⟶ A / X`
  are expressed directly by the ambient owner maps `subobjectInclusion` and `toQuotient`
- primitive data: the inclusion `hXY : X ≤ Y` and the canonical subobject
  `subobjectSubquotientSubobject hXY ⊆ A / X`
- derived API: the strictness lemmas for the canonical maps in this subquotient square
-/

/-- The canonical map of filtered subobjects induced by an inclusion `X ≤ Y` inside `A`. -/
def subobjectInclusionOfLE (hXY : X ≤ Y) :
    A.subobjectFilteredObject X ⟶ A.subobjectFilteredObject Y where
  hom := Subobject.ofLE X Y hXY
  preserves := by
    intro p
    sorry

/-- The canonical filtered object on the subquotient `Y / X = subobjectSubquotient hXY`, viewed
as the canonical subobject `subobjectSubquotientSubobject hXY` of `A / X` with the induced
filtration from the quotient filtration on `A / X`. -/
abbrev subobjectSubquotientFilteredObject (hXY : X ≤ Y) :
    FilteredObject C :=
  (A.quotientFilteredObject X).subobjectFilteredObject (subobjectSubquotientSubobject hXY)

/-- The canonical filtered projection `Y ⟶ Y / X`. -/
def subobjectToSubquotient (hXY : X ≤ Y) :
    A.subobjectFilteredObject Y ⟶ A.subobjectSubquotientFilteredObject hXY where
  hom :=
    factorThruKernelSubobject (subobjectQuotientMap hXY) (Y.arrow ≫ cokernel.π X.arrow)
      (subobjectSubquotientProjection_condition hXY)
  preserves := by
    intro p
    sorry

-- Proof sketch: on each stage, the quotient filtration from `Y` computes
-- `(Y ∩ F^p A) / (X ∩ F^p A)`, while the induced filtration from `A / X` computes the kernel of
-- `(F^p A / (X ∩ F^p A)) ⟶ (F^p A / (Y ∩ F^p A))`; these are the same subobject of `Y / X`.
/-- Lemma 12.19.9: on the canonical subquotient `Y / X`, the quotient filtration from the induced
filtration on `Y` agrees stagewise with the filtration induced from the quotient filtration on
`A / X`. -/
theorem subquotient_quotient_filtration_eq_induced_filtration (hXY : X ≤ Y) :
    (A.filtration.induced Y).quotient (A.subobjectToSubquotient hXY).hom =
      (A.subobjectSubquotientFilteredObject hXY).filtration := by
  sorry

end FilteredObject

namespace FilteredObject.Hom

open FilteredObject

variable (A : FilteredObject C)
variable {X Y : Subobject A.obj}

/-- Lemma 12.19.9: the canonical map `X ⟶ Y` between induced filtered subobjects is strict. -/
theorem strict_subobjectInclusionOfLE (hXY : X ≤ Y) :
    Strict (A.subobjectInclusionOfLE hXY) := by
  sorry

/-- Lemma 12.19.9: the canonical projection `Y ⟶ Y / X` is strict for the induced and subquotient
filtrations. -/
theorem strict_subobjectToSubquotient (hXY : X ≤ Y) :
    Strict (A.subobjectToSubquotient hXY) := by
  sorry

/-- Lemma 12.19.9: the canonical inclusion `Y / X ⟶ A / X` is strict for the induced
filtrations. -/
theorem strict_subobjectSubquotientInclusion (hXY : X ≤ Y) :
    Strict
      ((A.quotientFilteredObject X).subobjectInclusion (subobjectSubquotientSubobject hXY)) := by
  sorry

/-- Lemma 12.19.9: when `X ≤ Y`, the canonical map `Y ⟶ A / X` is strict for the induced and
quotient filtrations. -/
theorem strict_subobjectToQuotient (hXY : X ≤ Y) :
    Strict (A.subobjectInclusion Y ≫ A.toQuotient X) := by
  sorry

end FilteredObject.Hom

end CategoryTheory
