import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}

variable [IrreducibleSpace X]

/-- On an irreducible topological space, the constant abelian sheaf is flasque. -/
-- Proof sketch: by Definition `6.7.4`, sections of the constant sheaf over an open `U` are the
-- locally constant maps `U → A`. Every nonempty open subset of an irreducible space is again
-- irreducible, hence connected, so such a section is determined by any one of its values and is
-- therefore constant. Restriction maps are then surjective, which is exactly flasqueness.
theorem constantAbelianSheaf_isFlasque_of_irreducible
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) := sorry

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

-- Proof sketch: the previous theorem makes the constant abelian sheaf `\underline A` flasque on
-- an irreducible space. Flasque sheaves are acyclic for global sections by Lemma `20.12.3`, so
-- the positive-degree global cohomology objects `H^p(X, \underline A)` vanish.
/-- Lemma 20.20.2: if `X` is irreducible, then the higher cohomology of the constant abelian
sheaf `\underline A` vanishes in every positive degree. -/
theorem isZero_higherCohomology_constantAbelianSheaf_of_irreducible
    (A : AddCommGrpCat.{u}) {p : ℕ} (hp : 0 < p) :
    IsZero (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).H' p
      (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory
