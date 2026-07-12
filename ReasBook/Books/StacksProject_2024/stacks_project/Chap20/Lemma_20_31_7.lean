import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.RingedSpaceModuleHasDerivedCategory
import StacksProject_2024.Chap21.Lemma_21_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y Z : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (Modules X)
local notation "DModY" => DerivedCategory (Modules Y)
local notation "DModZ" => DerivedCategory (Modules Z)

variable
  (leftDerivedPullback_f : DModY ⥤ DModX)
  (rightDerivedPushforward_f : DModX ⥤ DModY)
  (pullPushAdj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
  (leftDerivedPullback_g : DModZ ⥤ DModY)
  (rightDerivedPushforward_g : DModY ⥤ DModZ)
  (pullPushAdj_g : leftDerivedPullback_g ⊣ rightDerivedPushforward_g)
  (leftDerivedPullback_comp : DModZ ⥤ DModX)
  (rightDerivedPushforward_comp : DModX ⥤ DModZ)
  (pullPushAdj_comp : leftDerivedPullback_comp ⊣ rightDerivedPushforward_comp)
  (pullbackCompIso : leftDerivedPullback_g ⋙ leftDerivedPullback_f ≅ leftDerivedPullback_comp)
  (pushforwardCompIso :
    rightDerivedPushforward_f ⋙ rightDerivedPushforward_g ≅ rightDerivedPushforward_comp)
  (pushforwardCompIso_hom_counit :
    Functor.whiskerRight pushforwardCompIso.hom leftDerivedPullback_comp ≫
        pullPushAdj_comp.counit =
      ((pullPushAdj_g.comp pullPushAdj_f).ofNatIsoLeft pullbackCompIso).counit)

variable
  (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
  (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
  (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)

variable
  (pullbackTensorIso_f :
    ∀ (A B : DModY),
      leftDerivedPullback_f.obj ((derivedTensorY.obj B).obj A) ≅
        ((derivedTensorX.obj (leftDerivedPullback_f.obj B)).obj
          (leftDerivedPullback_f.obj A)))
  (pullbackTensorIso_g :
    ∀ (A B : DModZ),
      leftDerivedPullback_g.obj ((derivedTensorZ.obj B).obj A) ≅
        ((derivedTensorY.obj (leftDerivedPullback_g.obj B)).obj
          (leftDerivedPullback_g.obj A)))
  (pullbackTensorIso_comp :
    ∀ (A B : DModZ),
      leftDerivedPullback_comp.obj ((derivedTensorZ.obj B).obj A) ≅
        ((derivedTensorX.obj (leftDerivedPullback_comp.obj B)).obj
          (leftDerivedPullback_comp.obj A)))

/- Domain-style sampling for Lemma 20.31.7:
- primary domain: compatibility of the relative derived cup product with composition of derived
  pushforwards;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProduct_comp_commSq`,
  `CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated`,
  `Adjunction.ofNatIsoLeft`;
- best owner abstraction:
  `source-facing`: the composition law for relative cup products on derived categories of
    `𝒪_X`-modules;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_comp_commSq` together with its
    equality-form companion `CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated`;
  `bridge/view`: this Chapter 20 item is just the ringed-space specialization of those owner
    theorems.

Primitive data are the two adjunctions, the composite adjunction, the pullback and pushforward
comparison isomorphisms, the induced counit-compatibility law, and the three pullback-tensor
comparison isomorphisms. The relative cup product and its composition-compatibility square are
derived API from the categorical owner, so this file should not keep a second local construction
of the cup-product morphisms or a parallel ringed-space theorem with the same content. -/

/- Lemma 20.31.7 is exactly the categorical owner theorem
  `CategoryTheory.relativeDerivedCupProduct_comp_commSq`, specialized to derived categories of
`𝒪_X`-modules on ringed spaces. -/
recall CategoryTheory.relativeDerivedCupProduct_comp_commSq

/- Equality-form companion to the previous square-form recall, in the same ringed-space derived
context. -/
recall CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated

end

end AlgebraicGeometry.RingedSpace
