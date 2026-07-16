import StacksProject_2024.stacks_project.Chap13.Definition_13_37_1
import StacksProject_2024.stacks_project.Chap22.ModuleCatHasDerivedCategory
import StacksProject_2024.stacks_project.Chap22.Lemma_22_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : DGMod ⥤ DMod)

/-- A derived object is a finite-cell retract when it is a retract of an object represented by a
differential graded module carrying a finite cell filtration. This is the source-facing existence
predicate appearing in Proposition 22.36.4. -/
class IsRetractOfFiniteCellDGModule (E : DMod) : Prop where
  exists_retract :
    ∃ P : DGMod, Nonempty (FiniteCellFiltration P) ∧ Nonempty (Retract E (Q.obj P))

@[simp]
theorem isRetractOfFiniteCellDGModule_iff (E : DMod) :
    IsRetractOfFiniteCellDGModule E ↔
      ∃ P : DGMod, Nonempty (FiniteCellFiltration P) ∧ Nonempty (Retract E (Q.obj P)) :=
  ⟨fun hE ↦ hE.exists_retract, fun hE ↦ ⟨hE⟩⟩

-- Semantic recall: `lean_leansearch` found only broad triangulated and differential-object
-- owners for this item. The checked statement below follows the local Chapter 22 convention that
-- differential graded `A`-modules are represented by cochain complexes of `A`-modules, and
-- Lemma 22.36.3 already owns the finite-cell filtration specialization of the source filtration.

/-- Proposition 22.36.4: for a differential graded algebra `(A, d)` and
`E : D(A, d)`, compactness of `E` is equivalent to `E` being a direct summand of an object
represented by a differential graded module with a finite filtration whose successive quotients
are finite direct sums of shifts of `A`. -/
@[stacks 09R3]
theorem isCompactObject_iff_retract_finiteCellDGModule
    (E : DMod) :
    IsCompactObject E ↔ IsRetractOfFiniteCellDGModule E := sorry

/-- Chapter 22 compactness alias form of Proposition 22.36.4. -/
theorem derivedCompactObject_iff_retract_finiteCellDGModule
    (E : DMod) :
    derivedCompactObject E ↔ IsRetractOfFiniteCellDGModule E := by
  simpa [derivedCompactObject, CategoryTheory.isCompactObject_iff] using
    isCompactObject_iff_retract_finiteCellDGModule E

theorem isRetractOfFiniteCellDGModule_of_derivedCompactObject
    {E : DMod} (hE : derivedCompactObject E) :
    IsRetractOfFiniteCellDGModule E :=
  (derivedCompactObject_iff_retract_finiteCellDGModule E).1 hE

theorem derivedCompactObject_of_isRetractOfFiniteCellDGModule
    {E : DMod} (hE : IsRetractOfFiniteCellDGModule E) :
    derivedCompactObject E :=
  (derivedCompactObject_iff_retract_finiteCellDGModule E).2 hE

theorem isRetractOfFiniteCellDGModule_of_isCompactObject
    {E : DMod} (hE : IsCompactObject E) :
    IsRetractOfFiniteCellDGModule E :=
  (isCompactObject_iff_retract_finiteCellDGModule E).1 hE

instance instIsCompactObjectOfIsRetractOfFiniteCellDGModule
    {E : DMod} [hE : IsRetractOfFiniteCellDGModule E] :
    IsCompactObject E :=
  (isCompactObject_iff_retract_finiteCellDGModule E).2 hE

end CochainComplex
