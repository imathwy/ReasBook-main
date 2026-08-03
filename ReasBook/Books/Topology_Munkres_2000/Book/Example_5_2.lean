module

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Prod

universe u

/- Example 5.2 (1): A three-coordinate Cartesian product is canonically
equivalent to the right-associated product `A × (B × C)`, preserving the
coordinate order. -/
#check fun (A B C : Type u) ↦
  ((Fin.consEquiv ![A, B, C]).symm.trans
    (Equiv.prodCongr (Equiv.refl A) (piFinTwoEquiv ![B, C])) :
      ((i : Fin 3) → ![A, B, C] i) ≃ A × (B × C))

/- Example 5.2 (2): A three-coordinate Cartesian product is canonically
equivalent to the left-associated product `(A × B) × C`, preserving the
coordinate order. -/
#check fun (A B C : Type u) ↦
  (((Fin.consEquiv ![A, B, C]).symm.trans
    (Equiv.prodCongr (Equiv.refl A) (piFinTwoEquiv ![B, C]))).trans
      (Equiv.prodAssoc A B C).symm :
        ((i : Fin 3) → ![A, B, C] i) ≃ (A × B) × C)
