import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import StacksProject_2024.Chap22.PropertyPDGModule

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomotopyCategory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat A) (up ℤ)

/-- A differential graded `A`-module is K-projective exactly when every morphism from it to an
acyclic differential graded `A`-module vanishes in the homotopy category `K(Mod_(A,d))`. -/
theorem isKProjective_iff_homotopyCategory_to_acyclic_eq_zero
    (P : DGMod) :
    P.IsKProjective ↔
      ∀ (N : DGMod) (_ : N.Acyclic) (f : (KQ).obj P ⟶ (KQ).obj N), f = 0 := by
  rw [isKProjective_iff_leftOrthogonal]
  constructor
  · intro h N hN f
    exact h f ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)
  · intro h X f hX
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    exact h N ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).1 hX) f

/-- Lemma 22.20.2: let `(A, d)` be a differential graded algebra and let `P` be a differential
graded `A`-module with property `(P)`. Then every morphism from `P` to an acyclic differential
graded `A`-module is zero in the homotopy category `K(Mod_(A,d))`. -/
@[stacks 09KM]
theorem homotopyCategory_hom_from_propertyP_to_acyclic_eq_zero
    (P N : DGMod) (hP : HasPropertyP P) (hN : N.Acyclic)
    (f : (KQ).obj P ⟶ (KQ).obj N) :
    f = 0 := sorry

/-- Companion instance: a differential graded `A`-module with property `(P)` is K-projective. -/
instance instIsKProjectiveOfHasPropertyP
    (P : DGMod) [hP : Fact (HasPropertyP P)] :
    P.IsKProjective := by
  exact (isKProjective_iff_homotopyCategory_to_acyclic_eq_zero P).2
    (fun N hN f ↦
      homotopyCategory_hom_from_propertyP_to_acyclic_eq_zero P N hP.1 hN f)

/-- Companion bridge to the canonical K-projective null-homotopy theorem: any morphism from a
property `(P)` differential graded `A`-module to an acyclic one is homotopic to zero. -/
theorem homotopic_to_zero_of_hasPropertyP_to_acyclic
    (P N : DGMod) (hP : HasPropertyP P) (hN : N.Acyclic) (f : P ⟶ N) :
    Nonempty (Homotopy f 0) := by
  let _ : Fact (HasPropertyP P) := ⟨hP⟩
  exact IsKProjective.nonempty_homotopy_zero f hN

end CochainComplex
