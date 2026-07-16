import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import StacksProject_2024.stacks_project.Chap22.DGModuleModel

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

variable (A : Type u) [Ring A]

/- Proposition 22.10.3: for a differential graded algebra `(A, d)`, the homotopy category
`K(Mod_{(A,d)})` of differential graded `A`-modules, with its natural translation functors and
distinguished triangles, is a triangulated category. In the current canonical Lean model for this
section this is the triangulated structure on `ModuleCat.KDGMod A`. -/
#check (inferInstance : IsTriangulated (ModuleCat.KDGMod A))

end
