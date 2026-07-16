import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.Definition_22_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open HomologicalComplex

noncomputable section

universe u

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]
variable (A B : CochainDGAlgebra R)
variable [HasTensor A.toCochainComplex B.toCochainComplex]

/- Lemma 22.3.5: the tensor-product differential graded algebra from Definition 22.3.4 has
underlying cochain complex `HomologicalComplex.tensorObj A.toCochainComplex B.toCochainComplex`.
This is exactly the canonical owner theorem `tensorProduct_toCochainComplex`. -/
recall tensorProduct_toCochainComplex

end CochainDGAlgebra
