import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u

namespace CategoryTheory
namespace Sheaf

/-
Domain-style sampling for 20.7.1.1:
- primary domain: restriction morphisms in sheaf cohomology on opens of a topological space;
- sampled owner declarations:
  `CategoryTheory.Sheaf.cohomologyPresheaf`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `CategoryTheory.Sheaf.H'`,
  `Functor.map`;
- best owner abstraction: the canonical owner is `Sheaf.cohomologyPresheaf`; the textbook
  restriction map is its functorial image on the inclusion `U ⟶ V`;
- primitive data: a sheaf `F`, a degree `n`, and an inclusion `hUV : U ≤ V` of opens;
- derived API: the induced morphism `F.H' n V ⟶ F.H' n U`.

Source/core/bridge triage:
- `source-facing`: the degree-`n` restriction morphism in cohomology attached to `U ⊆ V`;
- `core/canonical`: `Sheaf.cohomologyPresheaf`;
- `bridge/view`: evaluation of the owner functor on the arrow `(homOfLE hUV).op`, written using
  the notation `F.H' n U` for objectwise cohomology.

This item adds no new owner-level mathematics, so the refined file should recall the canonical
owner and expose only the source-facing specialization.
-/

variable {X : Type u} [TopologicalSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
variable {U V : Opens X} (hUV : U ≤ V)

/- 20.7.1.1 is the direct source-facing use of the canonical cohomology-presheaf owner on the
inclusion `U ⟶ V`. -/
recall cohomologyPresheaf

/- 20.7.1.1: for open subsets `U ⊆ V`, the degree-`n` restriction map in sheaf cohomology sends
a class on `V` to its restriction to `U`. This is exactly the morphism induced by the canonical
cohomology presheaf along the inclusion `U ⟶ V`. -/
#check (((F.cohomologyPresheaf n).map (homOfLE hUV).op) : F.H' n V ⟶ F.H' n U)

end Sheaf
end CategoryTheory
