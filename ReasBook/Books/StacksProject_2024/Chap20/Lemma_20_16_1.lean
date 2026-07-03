import StacksProject_2024.Chap20.«20_15_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

-- Proof sketch: for each indexed open cover `𝒰`, Lemma `20.11.5` gives the exact row
-- `0 → \check H^1(\mathcal U, \mathcal F) → H^1(X, \mathcal F) →
-- \check H^0(\mathcal U, \underline{H}^1(\mathcal F))`, so the coverwise comparison maps are
-- injective. Lemma `20.7.2` says the cohomology presheaf `\underline{H}^1(\mathcal F)` is locally
-- zero, hence its degree-zero Čech classes die after refinement. Passing to the colimit over all
-- indexed open covers makes the global comparison map surjective as well.
/-- Lemma 20.16.1: for an abelian sheaf `\mathcal F` on a topological space `X`, the global
Čech cohomology object `\check H^1(X, \mathcal F)` is canonically isomorphic to the first sheaf
cohomology group `H^1(X, \mathcal F)`. -/
theorem globalCechH1_isomorphic_sheafCohomology
    (ℱ : X.Sheaf AddCommGrpCat.{u})
    [HasColimit (indexedOpenCoverCechCohomologyFunctor ℱ 1)] :
    IsIsomorphic (globalCechCohomology ℱ 1) (ℱ.H' 1 (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory
