import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

namespace CategoryTheory
namespace Sheaf

/-
Domain-style sampling for 21.7.2.1:
- primary domain: restriction morphisms in the sheaf-cohomology presheaf on a site;
- sampled owner declarations:
  `Sheaf.cohomologyPresheafFunctor`,
  `Sheaf.cohomologyPresheaf`,
  `Sheaf.H'`;
- best owner abstraction: the restriction map is already canonically owned by the presheaf
  `F.cohomologyPresheaf n`, so the source-facing map `H^n(V, 𝓕) ⟶ H^n(U, 𝓕)`
  along `i : U ⟶ V` should be stated directly as `(F.cohomologyPresheaf n).map i.op`;
- primitive data: the abelian sheaf `F`, the degree `n`, and the morphism `i : U ⟶ V`;
- derived API: the objectwise cohomology objects `F.H' n U` and the induced restriction maps.

Source/core/bridge triage:
- `source-facing`: the restriction map `H^n(V, 𝓕) ⟶ H^n(U, 𝓕)`;
- `core/canonical`: `Sheaf.cohomologyPresheafFunctor` and `Sheaf.cohomologyPresheaf`;
- `bridge/view`: the notation `F.H' n X = (F.cohomologyPresheaf n).obj (op X)`.
-/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat] [HasExt (Sheaf J AddCommGrpCat)]
variable (F : Sheaf J AddCommGrpCat) (n : ℕ) {U V : C} (i : U ⟶ V)

/- 21.7.2.1 is the direct source-facing use of the canonical cohomology-presheaf owner on the
morphism `i : U ⟶ V`. -/
recall cohomologyPresheaf

/- 21.7.2.1: for a morphism `i : U ⟶ V` in the site, the restriction map
`H^n(V, 𝓕) ⟶ H^n(U, 𝓕)`, sending a class `ξ` to its restriction `ξ |_ U`,
is the morphism induced by the cohomology presheaf on `i.op`. -/
#check (((F.cohomologyPresheaf n).map i.op) : F.H' n V ⟶ F.H' n U)

end Sheaf
end CategoryTheory
