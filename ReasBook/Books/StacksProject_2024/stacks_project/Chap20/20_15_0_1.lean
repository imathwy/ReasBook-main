import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksProject_2024.stacks_project.Chap20.Definition_20_9_1
import StacksProject_2024.stacks_project.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits
open CategoryTheory.Limits.FormalCoproduct

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

section

variable {X : TopCat.{u + 1}}

/- Domain-style sampling for 20.15.0.1:
- primary domain: Čech cohomology of sheaves on `TopCat`, organized over the refinement category
  of indexed open covers;
- sampled owner declarations:
  `TopCat.Presheaf.cechCohomology`,
  `FormalCoproduct.cochainComplexFunctor`,
  `FormalCoproduct.cechFunctor`,
  `HomologicalComplex.homologyFunctor`;
- best owner abstraction: the coverwise owner lives first on
  `TopCat.Presheaf.cechCohomology`, applied to the family of opens underlying an indexed open
  cover; the refinement morphisms are induced functorially from the ambient formal-coproduct Čech
  complex along the full-subcategory inclusion `(indexedOpenCoverProperty X).ι.op`.

Source/core/bridge triage:
- `source-facing`: `indexedOpenCoverProperty`, `IndexedOpenCoverCat`,
  `indexedOpenCoverFamily`, `indexedOpenCoverCechCohomologyFunctor`, `globalCechCohomology`;
- `core/canonical`: `TopCat.Presheaf.cechCohomology`, the canonical finite-product instance on
  `Opens X`, `FormalCoproduct.cochainComplexFunctor`, `HomologicalComplex.homologyFunctor`;
- `bridge/view`: the refinement diagram inducing the public cohomology diagram and the canonical
  objectwise bridge from that diagram to `TopCat.Presheaf.cechCohomology`.

Primitive data versus derived API:
- primitive data: a topological space `X`, a sheaf `ℱ`, and a degree `p`;
- derived API: the Čech complex, its degree-`p` homology, the restriction to indexed open covers,
  and the global colimit object. Source-facing comparison results are stated later as
  isomorphism-valued theorems rather than as a separate chosen morphism. -/

/-- The object property on formal coproducts of opens consisting of indexed open covers of `X`. -/
def indexedOpenCoverProperty (X : TopCat.{u + 1}) :
    ObjectProperty (FormalCoproduct.{u} (Opens X)) :=
  fun U ↦ TopologicalSpace.IsOpenCover U.obj

/-- The refinement category of indexed open covers of `X`, oriented so that a morphism induces the
usual forward map on Čech cohomology under refinement. -/
abbrev IndexedOpenCoverCat (X : TopCat.{u + 1}) :=
  (indexedOpenCoverProperty X).FullSubcategoryᵒᵖ

/-- The indexed family of opens underlying an object of `IndexedOpenCoverCat X`. -/
abbrev indexedOpenCoverFamily {X : TopCat.{u + 1}} (A : IndexedOpenCoverCat X) :
    let U := A.unop.obj
    U.I → Opens X :=
  let U := A.unop.obj
  U.obj

/-- Helper for 20.15.0.1: a morphism of formal coproduct covers induces the corresponding map of
their Čech cochain complexes on `ℱ.presheaf`. -/
private noncomputable def formalCoproductCechComplexMap
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1})
    {𝒰 𝒱 : (FormalCoproduct.{u} (Opens X))ᵒᵖ} (f : 𝒰 ⟶ 𝒱) :
    (FormalCoproduct.cochainComplexFunctor 𝒰.unop.cech).obj ℱ.presheaf ⟶
      (FormalCoproduct.cochainComplexFunctor 𝒱.unop.cech).obj ℱ.presheaf :=
  (Functor.whiskerRight
    (((Functor.whiskeringLeft SimplexCategory
          ((FormalCoproduct.{u} (Opens X))ᵒᵖ) AddCommGrpCat.{u + 1}).map
        ((FormalCoproduct.cechFunctor.map f.unop).rightOp)))
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1})).app
    ((evalOp (Opens X) AddCommGrpCat.{u + 1}).obj ℱ.presheaf)

/-- Helper for 20.15.0.1: the Čech-complex map attached to the identity cover refinement is the
identity morphism. -/
@[simp] private theorem formalCoproductCechComplexMap_id
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1})
    (𝒰 : (FormalCoproduct.{u} (Opens X))ᵒᵖ) :
    formalCoproductCechComplexMap ℱ (𝟙 𝒰) = 𝟙 _ := by
  -- The induced cochain map is determined degreewise, where the identity refinement acts by
  -- identity on each component.
  ext n x
  have h :
      (AddCommGrpCat.Hom.hom
          (𝟙
            ((AlgebraicTopology.AlternatingCofaceMapComplex.obj
                  (Functor.rightOp 𝒰.unop.cech ⋙
                    (evalOp (Opens X) AddCommGrpCat.{u + 1}).obj ℱ.presheaf)).X n))) x =
        (AddMonoidHom.id _) x := by
    change (AddMonoidHom.id _) x = (AddMonoidHom.id _) x
    rfl
  simpa [formalCoproductCechComplexMap] using h

/-- Helper for 20.15.0.1: the Čech-complex map attached to a composite refinement is the
composite of the induced Čech-complex maps. -/
@[simp] private theorem formalCoproductCechComplexMap_comp
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1})
    {𝒳 𝒴 𝒵 : (FormalCoproduct.{u} (Opens X))ᵒᵖ}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    formalCoproductCechComplexMap ℱ (f ≫ g) =
      formalCoproductCechComplexMap ℱ f ≫ formalCoproductCechComplexMap ℱ g := by
  -- The Čech-complex map is functorial degreewise, so it suffices to compare components.
  ext n x
  simp [formalCoproductCechComplexMap, HomologicalComplex.comp_f]
  rfl

private noncomputable def formalCoproductCechComplexFunctor
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) :
    (FormalCoproduct.{u} (Opens X))ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  { obj := fun U ↦ (FormalCoproduct.cochainComplexFunctor U.unop.cech).obj ℱ.presheaf
    map := fun f ↦ formalCoproductCechComplexMap ℱ f
    map_id := fun 𝒰 ↦ formalCoproductCechComplexMap_id ℱ 𝒰
    map_comp := fun f g ↦ formalCoproductCechComplexMap_comp ℱ f g }

/-- Bridge/view: the indexed-open-cover Čech-cohomology diagram induced from the
formal-coproduct Čech complex and the homology functor. The public owner below is stated
objectwise using `TopCat.Presheaf.cechCohomology`, and its bridge back to that owner is exported
separately. -/
noncomputable def indexedOpenCoverCechCohomologyBridgeFunctor
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ) :
    IndexedOpenCoverCat X ⥤ AddCommGrpCat.{u + 1} :=
  (indexedOpenCoverProperty X).ι.op ⋙ formalCoproductCechComplexFunctor ℱ ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p

/-- On an indexed open cover `A`, the bridge functor computes the canonical coverwise owner
`TopCat.Presheaf.cechCohomology` of the underlying family of opens. -/
@[simp] theorem indexedOpenCoverCechCohomologyBridgeFunctor_obj
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ)
    (A : IndexedOpenCoverCat X) :
    (indexedOpenCoverCechCohomologyBridgeFunctor ℱ p).obj A =
      TopCat.Presheaf.cechCohomology (indexedOpenCoverFamily A) ℱ.presheaf p := by
  cases A with
  | op A =>
      rcases A with ⟨A, hA⟩
      rfl

/-- The bridge functor and the canonical coverwise owner agree on each indexed open cover. -/
abbrev indexedOpenCoverCechCohomologyBridgeObjIso
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ)
    (A : IndexedOpenCoverCat X) :
    (indexedOpenCoverCechCohomologyBridgeFunctor ℱ p).obj A ≅
      TopCat.Presheaf.cechCohomology (indexedOpenCoverFamily A) ℱ.presheaf p :=
  eqToIso (indexedOpenCoverCechCohomologyBridgeFunctor_obj ℱ p A)

/-- The refinement diagram of degree-`p` Čech cohomology groups of a sheaf on `X`, stated
objectwise using the Chapter 20 owner `TopCat.Presheaf.cechCohomology`. -/
abbrev indexedOpenCoverCechCohomologyFunctor
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ) :
    IndexedOpenCoverCat X ⥤ AddCommGrpCat.{u + 1} :=
  indexedOpenCoverCechCohomologyBridgeFunctor ℱ p

/-- On an indexed open cover `A`, the refinement Čech-cohomology diagram evaluates to the canonical
owner `TopCat.Presheaf.cechCohomology` of the underlying family of opens. -/
@[simp] theorem indexedOpenCoverCechCohomologyFunctor_obj
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ)
    (A : IndexedOpenCoverCat X) :
    (indexedOpenCoverCechCohomologyFunctor ℱ p).obj A =
      TopCat.Presheaf.cechCohomology (indexedOpenCoverFamily A) ℱ.presheaf p :=
  indexedOpenCoverCechCohomologyBridgeFunctor_obj ℱ p A

/-- The public objectwise identification between the indexed-open-cover Čech-cohomology diagram
and the canonical coverwise owner. This is the transport-stable companion for evaluating natural
transformations out of `indexedOpenCoverCechCohomologyFunctor`. -/
abbrev indexedOpenCoverCechCohomologyFunctorObjIso
    {X : TopCat.{u + 1}} (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ)
    (A : IndexedOpenCoverCat X) :
    (indexedOpenCoverCechCohomologyFunctor ℱ p).obj A ≅
      TopCat.Presheaf.cechCohomology (indexedOpenCoverFamily A) ℱ.presheaf p :=
  indexedOpenCoverCechCohomologyBridgeObjIso ℱ p A

/-- Evaluate a natural transformation out of the indexed-open-cover Čech-cohomology diagram as a
map from the canonical coverwise owner `TopCat.Presheaf.cechCohomology`. -/
abbrev indexedOpenCoverCechCohomologyFunctorApp
    {X : TopCat.{u + 1}}
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ)
    {F : IndexedOpenCoverCat X ⥤ AddCommGrpCat.{u + 1}}
    (ι : indexedOpenCoverCechCohomologyFunctor ℱ p ⟶ F) (B : IndexedOpenCoverCat X) :
    TopCat.Presheaf.cechCohomology (indexedOpenCoverFamily B) ℱ.presheaf p ⟶ F.obj B :=
  (indexedOpenCoverCechCohomologyFunctorObjIso ℱ p B).inv ≫ ι.app B

variable {X : TopCat.{u + 1}}

/-- 20.15.0.1: the global Čech cohomology `Čech H^p(X, ℱ)` of a sheaf `ℱ` on `X` is the colimit of
the degree-`p` Čech cohomology groups over all indexed open covers of `X`. This file keeps the
canonical colimit object itself as the public owner. -/
@[stacks 09UZ]
abbrev globalCechCohomology (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ) :=
  colimit (indexedOpenCoverCechCohomologyFunctor ℱ p)

/-- The canonical cocone leg from an indexed open cover into `Čech H^p(X, ℱ)`. -/
abbrev globalCechCohomologyι
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ) (A : IndexedOpenCoverCat X) :
    (indexedOpenCoverCechCohomologyFunctor ℱ p).obj A ⟶ globalCechCohomology ℱ p :=
  colimit.ι (indexedOpenCoverCechCohomologyFunctor ℱ p) A

/-- The canonical morphism out of `Čech H^p(X, ℱ)` induced by a cocone over the indexed-open-cover
diagram. -/
abbrev globalCechCohomologyDesc
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ) {A : AddCommGrpCat.{u + 1}}
    (η : indexedOpenCoverCechCohomologyFunctor ℱ p ⟶ (Functor.const (IndexedOpenCoverCat X)).obj A) :
    globalCechCohomology ℱ p ⟶ A :=
  colimit.desc (indexedOpenCoverCechCohomologyFunctor ℱ p) (Cocone.mk A η)

@[simp, reassoc] theorem globalCechCohomology_ι_desc
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (p : ℕ) {A : AddCommGrpCat.{u + 1}}
    (η : indexedOpenCoverCechCohomologyFunctor ℱ p ⟶ (Functor.const (IndexedOpenCoverCat X)).obj A)
    (B : IndexedOpenCoverCat X) :
    globalCechCohomologyι ℱ p B ≫ globalCechCohomologyDesc ℱ p η = η.app B := by
  simpa [globalCechCohomologyι, globalCechCohomologyDesc] using
    colimit.ι_desc (Cocone.mk A η) B

end

end Sheaf
end CategoryTheory
