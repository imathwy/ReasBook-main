import Mathlib.Tactic.Recall
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations

universe v u

open CategoryTheory
open HomotopicalAlgebra

-- Semantic recall: `HomotopicalAlgebra.Cofibration` is the canonical mathlib owner for the
-- cofibration half of the framework, and the same module exposes the dual fibration surface.

/- Orientation 6.1.1

Exact sequences in homotopy, homology, and cohomology are organized through fiber and cofiber
sequences. For this section, the canonical mathlib surface begins with categories equipped with
cofibrations and the class `HomotopicalAlgebra.Cofibration` of cofibration morphisms; the dual
fibration API lives in the same module.
-/
recall CategoryWithCofibrations (C : Type u) [Category.{v} C] :
    Type (max u v)
recall CategoryWithFibrations (C : Type u) [Category.{v} C] :
    Type (max u v)

section

variable {C : Type u} [Category.{v} C] {X Y : C}

recall Cofibration (f : X ⟶ Y) [CategoryWithCofibrations C] : Prop
recall Fibration (f : X ⟶ Y) [CategoryWithFibrations C] : Prop

end

section

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] {X Y : C} (f : X ⟶ Y)

#check cofibration_iff f
#check fibration_op_iff f

end

section

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C] {X Y : C} (f : X ⟶ Y)

#check cofibration_op_iff f

end
