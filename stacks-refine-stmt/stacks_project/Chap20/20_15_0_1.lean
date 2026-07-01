import Mathlib
import stacks_project.Chap20.«20_9_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits
open CategoryTheory.Limits.FormalCoproduct

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

local instance (X : TopCat.{u}) : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for 20.15.0.1:
- primary domain: Čech cohomology of sheaves on `TopCat`, organized over the refinement category
  of indexed open covers;
- sampled owner declarations:
  `indexedOpenCoverProperty.ι`,
  `FormalCoproduct.cechFunctor`,
  `cechComplexFunctor`,
  `HomologicalComplex.homologyFunctor`;
- best owner abstraction: the coverwise owner lives first on
  `(FormalCoproduct (Opens X))ᵒᵖ`, where a formal coproduct of opens determines its Čech complex
  functorially via `FormalCoproduct.cechFunctor` and `cechComplexFunctor`; the indexed-open-cover
  diagram is then the restriction of this ambient owner along the full-subcategory inclusion
  `(indexedOpenCoverProperty X).ι.op`.

Source/core/bridge triage:
- `source-facing`: `indexedOpenCoverProperty`, `IndexedOpenCoverCat`,
  `indexedOpenCoverCechCohomologyFunctor`, `globalCechCohomology`;
- `core/canonical`: `opensHasFiniteProducts`, `cechComplexFunctor`, `K.homology p`;
- `bridge/view`: the refinement diagram of Čech complexes inducing the public cohomology diagram.

Primitive data versus derived API:
- primitive data: a topological space `X`, a sheaf `ℱ`, and a formal coproduct of opens;
- derived API: the Čech complex, its degree-`p` homology, the restriction to indexed open covers,
  and the global colimit object. -/

/-- The object property on formal coproducts of opens consisting of indexed open covers of `X`. -/
def indexedOpenCoverProperty (X : TopCat.{u}) :
    ObjectProperty (FormalCoproduct (Opens X)) :=
  fun U ↦ TopologicalSpace.IsOpenCover U.obj

/-- The refinement category of indexed open covers of `X`, oriented so that a morphism induces the
usual forward map on Čech cohomology under refinement. -/
abbrev IndexedOpenCoverCat (X : TopCat.{u}) :=
  (indexedOpenCoverProperty X).FullSubcategoryᵒᵖ

private noncomputable def formalCoproductCechComplexFunctor
    {X : TopCat.{u}} (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (FormalCoproduct (Opens X))ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℕ where
  obj U := (cechComplexFunctor U.unop.obj).obj ℱ.presheaf
  map {𝒰 𝒱} f :=
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).map
      ((((Functor.whiskeringLeft SimplexCategory
            ((FormalCoproduct (Opens X))ᵒᵖ) AddCommGrpCat.{u}).map
          ((cechFunctor.map f.unop).rightOp)).app
        ((evalOp (Opens X) AddCommGrpCat.{u}).obj ℱ.presheaf)))
  map_id 𝒰 := by
    ext n i
    simp
  map_comp f g := by
    ext n i
    simp

private noncomputable def formalCoproductCechCohomologyFunctor
    {X : TopCat.{u}} (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (FormalCoproduct (Opens X))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  formalCoproductCechComplexFunctor ℱ ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p

/-- The refinement diagram of degree-`p` Čech cohomology groups of a sheaf on `X`. -/
noncomputable def indexedOpenCoverCechCohomologyFunctor
    {X : TopCat.{u}} (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IndexedOpenCoverCat X ⥤ AddCommGrpCat.{u} :=
  (indexedOpenCoverProperty X).ι.op ⋙ formalCoproductCechCohomologyFunctor ℱ p

variable {X : TopCat.{u}}

/-- 20.15.0.1: the global Čech cohomology `\check H^p(X, \mathcal F)` of a sheaf `\mathcal F` on
`X` is the colimit of the degree-`p` Čech cohomology groups over all indexed open covers of `X`;
the textbook display also includes the canonical comparison map from this colimit to the sheaf
cohomology group `H^p(X, \mathcal F)`. -/
abbrev globalCechCohomology (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    [HasColimit (indexedOpenCoverCechCohomologyFunctor ℱ p)] :=
  colimit (indexedOpenCoverCechCohomologyFunctor ℱ p)

end Sheaf
end CategoryTheory
