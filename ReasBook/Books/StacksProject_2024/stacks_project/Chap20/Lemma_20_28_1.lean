import Mathlib.Topology.Category.TopCat.Opens
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap20.«20_14_1_1»
import StacksProject_2024.Chap20.Lemma_20_27_1
import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Lemma_21_19_1

open AlgebraicGeometry
open ComplexShape
open CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 20.28.1:
- primary domain: derived adjunctions for pullback and pushforward on module sheaves over ringed
  spaces;
- sampled owner declarations:
  `Adjunction.derived`,
  `modulePullbackToDerived`,
  `modulePushforwardToDerived`;
- best owner abstraction:
  `source-facing`: the derived adjunction `L(f)^* ⊣ R(f)_*`;
  `core/canonical`: the canonical derived-adjunction constructor `Adjunction.derived`;
  `bridge/view`: the ringed-space total left and right derived functor owners
    `modulePullbackToDerived` and `modulePushforwardToDerived`, whose canonical derived
    adjunction is best exposed through the source-facing adjointness theorem and its
    adjointness typeclass companions rather than a duplicate concrete `Adjunction` value.
- primitive data: the morphism `f`;
- derived API: the source-facing theorem asserting that `L(f)^*` is left adjoint and `R(f)_*`
  is right adjoint, together with the instance-driven concrete adjunction
  `Adjunction.ofIsLeftAdjoint (L(f)^*)`.
-/

variable (f : X ⟶ Y)
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(f _*).Additive]
variable [(f^*).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Lemma 20.28.1: the derived pullback `L(f)^*` is left adjoint to the derived pushforward
`R(f)_*`. -/
@[stacks 079W]
theorem modulePullbackDerived_isLeftAdjoint_and_modulePushforwardDerived_isRightAdjoint :
    Functor.IsLeftAdjoint (L(f)^*) ∧ Functor.IsRightAdjoint (R(f)_*) := by
  let adjD := RingedSite.Hom.modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f)
  constructor
  · exact adjD.isLeftAdjoint
  · exact adjD.isRightAdjoint

/-- Lemma 20.28.1, automation-facing form: derived pullback along a morphism of ringed spaces is a
left adjoint. The associated concrete adjunction is `Adjunction.ofIsLeftAdjoint (L(f)^*)`, whose
right adjoint is definitionally `R(f)_*`. -/
@[stacks 079W]
instance modulePullbackDerived_isLeftAdjoint :
    (L(f)^*).IsLeftAdjoint := by
  exact
    (modulePullbackDerived_isLeftAdjoint_and_modulePushforwardDerived_isRightAdjoint f).1

/-- Companion to Lemma 20.28.1: derived pushforward along a morphism of ringed spaces is a right
adjoint. -/
instance modulePushforwardDerived_isRightAdjoint :
    (R(f)_*).IsRightAdjoint := by
  exact
    (modulePullbackDerived_isLeftAdjoint_and_modulePushforwardDerived_isRightAdjoint f).2

end

end AlgebraicGeometry.RingedSpace
