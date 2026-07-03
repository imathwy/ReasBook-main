import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import stacks_project.Chap17.Lemma_17_18_2
import stacks_project.Chap18.Lemma_18_28_7
import stacks_project.Chap20.«20_9_0_1»
import stacks_project.Chap20.«20_10_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace HomologicalComplex
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/- Domain-style sampling for Lemma 20.10.3:
- primary domain: Čech complexes of presheaf `\mathcal O_X`-modules and the canonical cover chain
  complex built from free Yoneda summands;
- sampled owner declarations:
  `CategoryTheory.cechComplexFunctor`,
  `PresheafOfModules.localizedStructureModuleExtensionByZero`,
  `preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`;
- best owner abstraction: the source-facing owner in this file is the cover chain complex
  `openCoverChainComplex 𝒰`, while the canonical `Hom(K_\bullet,-)` cochain functor is obtained by
  applying `preadditiveCoyoneda` to `K.op` and then viewing the resulting complex of functors via
  `HomologicalComplex.asFunctor`; the Čech target remains the canonical owner
  `CategoryTheory.cechComplexFunctor 𝒰`.

Primitive data is only the ringed space `X` and the indexed open family `𝒰`. The formal-coproduct
realization of the cover is derived bridge data, and the `Hom(K_\bullet,-)` cochain construction
should be reused from the owner-level homological-complex API rather than rebuilt degreewise in
this file.

Source/core/bridge triage:
- `source-facing`: `openCoverChainComplex 𝒰` and the comparison theorem with the Čech complex;
- `core/canonical`: `CategoryTheory.cechComplexFunctor 𝒰`,
  `PresheafOfModules.localizedStructureModuleExtensionByZero`,
  `preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`;
- `bridge/view`: the formal-coproduct module functor realizing the cover. -/

private noncomputable abbrev openSubsetFreeModuleFunctor (X : RingedSpace.{u}) :
    Opens X.carrier ⥤ ringedSpacePresheafModules X :=
  yoneda ⋙ PresheafOfModules.free ((RingedSpace.ringCatSheaf X)).obj

/-- The extension of the open-subset module functor to formal coproducts of open subsets. -/
private noncomputable def coverFormalCoproductModuleFunctor (X : RingedSpace.{u}) :
    CategoryTheory.Limits.FormalCoproduct.{u} (Opens X.carrier) ⥤ ringedSpacePresheafModules X where
  obj U := ∐ fun i : U.I ↦ (openSubsetFreeModuleFunctor X).obj (U.obj i)
  map {U V} f :=
    Sigma.desc fun i ↦
      (openSubsetFreeModuleFunctor X).map (f.φ i) ≫
        Sigma.ι (fun j : V.I ↦ (openSubsetFreeModuleFunctor X).obj (V.obj j)) (f.f i)
  map_id U := by
    apply Sigma.hom_ext
    intro i
    simpa using
      (Sigma.ι_desc
        (p := fun j : U.I ↦
          Sigma.ι (fun k : U.I ↦ (openSubsetFreeModuleFunctor X).obj (U.obj k)) j)
        i)
  map_comp f g := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc]
    dsimp
    rw [Category.assoc, Sigma.ι_desc]
    have hmap :
        (openSubsetFreeModuleFunctor X).map (f.φ i ≫ g.φ (f.f i)) =
          (openSubsetFreeModuleFunctor X).map (f.φ i) ≫
            (openSubsetFreeModuleFunctor X).map (g.φ (f.f i)) :=
      Functor.map_comp (openSubsetFreeModuleFunctor X) (f.φ i) (g.φ (f.f i))
    simpa [Category.assoc] using
      congrArg
        (fun h ↦ h ≫ Sigma.ι _ (g.f (f.f i)))
        hmap

/-- The simplicial presheaf-module object attached to an indexed open covering. -/
private noncomputable abbrev openCoverSimplicialObject (𝒰 : ι → Opens X.carrier) :
    SimplicialObject (ringedSpacePresheafModules X) :=
  letI : OrderTop (Opens X.carrier) := opensOrderTop X.carrier
  letI : HasFiniteLimits (Opens X.carrier) :=
    hasFiniteLimits_of_semilatticeInf_orderTop
  letI : HasFiniteProducts (Opens X.carrier) := opensHasFiniteProducts X.carrier
  (FormalCoproduct.mk _ 𝒰).cech ⋙ coverFormalCoproductModuleFunctor X

/-- The chain complex of presheaf modules associated with an indexed open covering. -/
noncomputable abbrev openCoverChainComplex (𝒰 : ι → Opens X.carrier) :
    ChainComplex (ringedSpacePresheafModules X) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ringedSpacePresheafModules X)).obj
    (openCoverSimplicialObject 𝒰)

-- Proof sketch: realize the cover as the formal coproduct `∐ i, U_i` in `Opens X`, apply the Čech
-- simplicial formal-coproduct construction, and then evaluate it in presheaf modules via the
-- Yoneda-free module functor `U ↦ (free \circ yoneda)(U)`. Morphisms from the resulting degree-`p`
-- term to a presheaf module `ℱ` identify with sections of `ℱ` on the corresponding
-- `(p + 1)`-fold intersections, and the alternating face differential becomes the usual Čech
-- differential. These identifications are natural in `ℱ`, yielding the desired natural
-- isomorphism of functors.
/-- Lemma 20.10.3: for a ringed space `X` and an indexed open covering `𝒰`, the functor
`Hom_{\mathcal O_X}(K(\mathcal U)_\bullet,-)` associated with the canonical cover chain complex is
isomorphic to the canonical Čech complex functor of the cover. -/
theorem openCoverChainComplex_homFunctor_iso_cechComplexFunctor
    (𝒰 : ι → Opens X.carrier) :
    IsIsomorphic
      (((preadditiveCoyoneda.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (openCoverChainComplex 𝒰).op).asFunctor)
      (PresheafOfModules.toPresheaf ((RingedSpace.ringCatSheaf X)).obj ⋙
        cechComplexFunctor 𝒰) := sorry

end AlgebraicGeometry.RingedSpace
