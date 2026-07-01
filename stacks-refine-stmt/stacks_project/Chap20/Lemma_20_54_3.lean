import Mathlib
import stacks_project.Chap20.Definition_20_49_1
import stacks_project.Chap20.Lemma_20_32_4
import stacks_project.Chap20.Lemma_20_47_3
import stacks_project.Chap20.«20_54_2_1»
import stacks_project.Chap21.Lemma_21_47_2
import stacks_project.Chap21.Lemma_21_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.54.3:
- primary domain: projection-formula morphisms for derived pullback and derived pushforward of
  module sheaves, with the intrinsic owner living on ringed sites and the ringed-space statement
  as its opens-site specialization;
- sampled owner declarations:
  `RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect`,
  `RingedSite.Hom.projectionFormulaMorphism`,
  `CategoryTheory.projectionFormulaMorphism`,
  `modulePullbackDerived`,
  `modulePushforwardDerived`;
- best owner abstraction:
  `source-facing`: the ringed-space specialization for a morphism `f : X ⟶ Y`;
  `core/canonical`: `RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect`;
  `bridge/view`: the morphism of ringed sites on the opens topologies induced by `f`, whose
  projection-formula morphism specializes definitionally to the Chapter 20 ringed-space one.
- primitive data: the ringed-space morphism `f`, the chosen derived adjunction for `f`, the
  pullback-tensor comparison for `f`, and the perfectness hypothesis on `K`;
- derived API: the `IsIso` conclusion for the canonical ringed-space projection-formula morphism,
  obtained by specialization from the ringed-site owner theorem. -/

section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

private abbrev opensRingedSite (X : RingedSpace.{u}) :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

private noncomputable abbrev opensRingedSiteHom (f : X ⟶ Y) :
    opensRingedSite X ⟶ opensRingedSite Y where
  base := Opens.map f.hom.base
  structureSheafMap :=
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
      (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
        ⟨f.hom.c⟩)

private instance opensRingedSiteLocalizedRestrictionPreservesZeroMorphisms
    (U : opensRingedSite Y) :
    (RingedSite.Hom.localizedRestriction U).PreservesZeroMorphisms where
  map_zero _ _ := by
    rfl

private theorem siteIsPerfect_of_ringedSpaceIsPerfect
    (K : DModY) (hK : AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect K) :
    _root_.RingedSite.DerivedCategory.IsPerfect
      (show RingedSite.Hom.ModuleDerived (opensRingedSite Y) from K) := by
  sorry

variable (f : X ⟶ Y)

variable [CategoryWithHomology X.Modules] [CategoryWithHomology Y.Modules]
variable [(modulePullback f).Additive]
variable [(RingedSpace.Hom.pushforward f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived f) (ModuleQis X)]
variable [MonoidalCategory (DerivedCategory X.Modules)]
variable [MonoidalCategory (DerivedCategory Y.Modules)]
variable
  (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
  (tensorIso :
    ∀ (A B : DModY),
      (modulePullbackDerived f).obj (A ⊗ B) ≅
        ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))

-- Proof sketch: this is exactly the projection-formula argument from the Stacks Project. Work
-- locally on `Y` and represent the perfect object `K` by a strictly perfect complex. The claim is
-- stable under finite direct sums, shifts, and direct summands, so stupid truncations reduce to
-- the case `K = \mathcal O_Y[n]`, where the projection-formula morphism is immediate.
/-- Lemma 20.54.3: for a morphism of ringed spaces `f : X ⟶ Y`, an object `E ∈ D(\mathcal O_X)`,
and a perfect object `K ∈ D(\mathcal O_Y)`, the projection-formula morphism
`K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* E ⟶
Rf_*(Lf^* K \otimes_{\mathcal O_X}^{\mathbf L} E)` is an isomorphism in `D(\mathcal O_Y)`. -/
theorem projectionFormulaMorphism_isIso_of_isPerfect
    (E : DModX) (K : DModY)
    (hK : AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect K) :
    IsIso (projectionFormulaMorphism
      (modulePullbackDerived f)
      (modulePushforwardDerived f)
      adj
      tensorIso
      E
      K) := by
  have siteTensorIso :
      ∀ (A B : RingedSite.Hom.ModuleDerived (opensRingedSite Y)),
        (RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj
            (((curriedTensor (RingedSite.Hom.ModuleDerived (opensRingedSite Y))).obj B).obj A) ≅
          (((curriedTensor (RingedSite.Hom.ModuleDerived (opensRingedSite X))).obj
                ((RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj B)).obj
            ((RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj A)) := by
    intro A B
    sorry
  simpa only [opensRingedSite, opensRingedSiteHom, modulePushforwardDerived, modulePullbackDerived,
    modulePullbackToDerived, modulePushforwardToDerived, ModuleQis,
    RingedSite.Hom.modulePushforwardDerived, RingedSite.Hom.modulePullbackDerived,
    RingedSite.Hom.modulePullbackToDerived, RingedSite.Hom.modulePushforwardToDerived,
    RingedSite.Hom.ModuleQis, RingedSite.Hom.projectionFormulaMorphism,
    RingedSite.Hom.ModuleDerived, RingedSite.Hom.ModuleCat] using
    RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect
      (opensRingedSiteHom f) adj siteTensorIso E K
      (siteIsPerfect_of_ringedSpaceIsPerfect K hK)

end

end AlgebraicGeometry.RingedSpace
