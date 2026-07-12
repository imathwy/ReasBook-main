import Mathlib
import StacksProject_2024.Chap10.Definition_10_78_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.pullback` and the affine
-- `pullbackSpecIso` API. Local Chapter 30 precedent states global cohomology as
-- `((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X)`, so the base-change
-- statement below keeps the source conclusion on that cohomology surface.

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {X Y : Scheme.{u}}

/-- Lemma 30.5.3 (Finite locally free base change): for a cartesian square
`Y -> X` over `Spec B -> Spec A`, a quasi-coherent module `\mathcal F` on `X`, and
`h^* \mathcal F` on `Y`, finite local freeness of `B` over `A` identifies
`H^i(X, \mathcal F) \otimes_A B` with `H^i(Y, h^* \mathcal F)`. The displayed tensor product is
written as `B ⊗[A] H^i(X, \mathcal F)`, using the canonical symmetry of tensor products over a
commutative base. The module structures in the statement are the source-induced `A`- and
`B`-linear cohomology structures. -/
@[stacks 0CKW]
theorem cohomology_tensor_isomorphic_of_finiteLocallyFree_baseChange
    (f : X ⟶ Spec (CommRingCat.of A))
    (g : Y ⟶ Spec (CommRingCat.of B))
    (h : Y ⟶ X)
    (sq : IsPullback h g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [Module.FiniteLocallyFree A B]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ)
    [Module A (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))]
    [Module B
      (((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback h).obj ℱ)).H' i
        (⊤ : Opens Y))] :
    IsIsomorphic
      (ModuleCat.of B
        (B ⊗[A] (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))))
      (ModuleCat.of B
        (((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback h).obj ℱ)).H' i
          (⊤ : Opens Y))) := sorry

end AlgebraicGeometry.Scheme
