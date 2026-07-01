import stacks_project.Chap20.«20_15_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}
variable [CompactSpace X] [T2Space X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

-- Proof sketch: Lemma `20.16.1` gives the comparison isomorphism in degrees `0` and `1`. Usual
-- sheaf cohomology is a universal `δ`-functor, while on compact Hausdorff spaces the Čech
-- cohomology groups admit compatible connecting morphisms and vanish in positive degree on
-- injective sheaves, so they also form a universal `δ`-functor. Uniqueness of universal
-- `δ`-functors then upgrades the comparison to an isomorphism in every degree.
/-- Lemma 20.16.2: if `X` is Hausdorff and quasi-compact and `ℱ` is an abelian sheaf on `X`, then
for every `n` the global Čech cohomology object `\check H^n(X, \mathcal F)` is canonically
isomorphic to the sheaf cohomology group `H^n(X, \mathcal F)`. -/
theorem globalCechCohomology_isomorphic_sheafCohomology_of_compact_t2
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (n : ℕ)
    [HasColimit (indexedOpenCoverCechCohomologyFunctor ℱ n)] :
    IsIsomorphic (globalCechCohomology ℱ n) (ℱ.H' n (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory
