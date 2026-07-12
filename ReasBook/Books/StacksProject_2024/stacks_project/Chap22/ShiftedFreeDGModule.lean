import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.Single

open CategoryTheory

noncomputable section

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

/-- The shifted free differential graded module `A[k]` in the canonical cochain-complex model. -/
abbrev shiftedFreeDGModule (A : Type u) [Ring A] (k : ℤ) :
    CochainComplex (ModuleCat.{u, u} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u, u} A) (ComplexShape.up ℤ) (-k)).obj
    (ModuleCat.of.{u, u} A A)

/-- The shifted free differential graded module is the single complex on `A` in degree `-k`. -/
@[simp] theorem shiftedFreeDGModule_def (A : Type u) [Ring A] (k : ℤ) :
    shiftedFreeDGModule A k =
      (HomologicalComplex.single (ModuleCat.{u, u} A) (ComplexShape.up ℤ) (-k)).obj
        (ModuleCat.of.{u, u} A A) :=
  rfl

end

end CochainComplex
