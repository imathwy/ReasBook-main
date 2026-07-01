import Mathlib
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : Type u} [TopologicalSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
variable {U V : Opens X} (hUV : U ≤ V)

/- 20.7.1.1: for open subsets `U ⊆ V`, the degree-`n` restriction map in sheaf cohomology sends
a class on `V` to its restriction to `U`. This is exactly the morphism induced by the canonical
cohomology presheaf along the inclusion `U ⟶ V`. -/
#check (((F.cohomologyPresheaf n).map (homOfLE hUV).op) : F.H' n V ⟶ F.H' n U)

end Sheaf
end CategoryTheory
