import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Proposition_15_79_3
import StacksProject_2024.stacks_project.Chap22.CompactDGModule
import StacksProject_2024.stacks_project.Chap22.ModuleCatHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory
open scoped DirectSum

noncomputable section

universe u

namespace CochainComplex

-- Semantic recall note: Chapter 15 already provides the canonical perfect/compact bridge in the
-- derived category, so this file keeps the source-facing finite graded projective hypothesis and
-- exposes the bounded finite-projective and perfect-object companions needed for reuse.

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : DGMod ⥤ DMod)

/-- A differential graded `A`-module in the canonical cochain-complex model is finite when the
graded direct sum of its homogeneous pieces is a finitely generated `A`-module. -/
abbrev finiteDGModule (P : DGMod) : Prop :=
  Module.Finite A (⨁ n : ℤ, P.X n)

/-- The finiteness predicate unfolds to finite generation of the graded direct sum of the terms.
-/
theorem finiteDGModule_iff (P : DGMod) :
    finiteDGModule P ↔ Module.Finite A (⨁ n : ℤ, P.X n) :=
  Iff.rfl

/-- A differential graded `A`-module in the canonical cochain-complex model is finite graded
projective when it is finite and every graded piece is projective as an `A`-module. -/
abbrev finiteGradedProjective (P : DGMod) : Prop :=
  finiteDGModule P ∧ ∀ n : ℤ, Projective (P.X n)

/-- The finite graded projective predicate is the conjunction of finiteness and termwise
projectivity. -/
theorem finiteGradedProjective_iff (P : DGMod) :
    finiteGradedProjective P ↔
      finiteDGModule P ∧ ∀ n : ℤ, Projective (P.X n) :=
  Iff.rfl

/-- A finite graded projective differential graded module is finite as a graded module. -/
theorem finiteGradedProjective.finiteDGModule {P : DGMod}
    (hP : finiteGradedProjective P) :
    finiteDGModule P :=
  hP.1

/-- A finite graded projective differential graded module is a bounded finite-projective complex in
the Chapter 15 canonical owner. -/
instance finiteGradedProjective.instIsBoundedFiniteProjective {P : DGMod}
    (hP : finiteGradedProjective P) :
    CochainComplex.IsBoundedFiniteProjective P := by
  sorry

/-- A finite graded projective differential graded module represents a perfect object of the
derived category. -/
theorem finiteGradedProjective.isPerfect {P : DGMod}
    (hP : finiteGradedProjective P) :
    (Q.obj P).IsPerfect := by
  exact ⟨P, Iso.refl _, finiteGradedProjective.instIsBoundedFiniteProjective hP⟩

/-- Companion to Remark 22.36.2 in the canonical compact-object owner
`CategoryTheory.IsCompactObject`. -/
instance isCompactObject_q_obj_of_finiteGradedProjective
    (P : DGMod) (hP : finiteGradedProjective P) :
    IsCompactObject (Q.obj P) := by
  exact (CategoryTheory.isPerfect_iff_isCompactObject (Q.obj P)).1 hP.isPerfect

/-- Remark 22.36.2: in the canonical cochain-complex model for differential graded `A`-modules, a
finite graded projective object gives a compact object of the derived category `D(A, d)`. -/
@[stacks 09R1]
theorem derivedCompact_of_finiteGradedProjective
    (P : DGMod) (hP : finiteGradedProjective P) :
    derivedCompactObject (Q.obj P) := by
  simpa [derivedCompactObject, CategoryTheory.isCompactObject_iff] using
    (isCompactObject_q_obj_of_finiteGradedProjective P hP)

end

end CochainComplex
