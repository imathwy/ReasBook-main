import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap21.Lemma_21_19_1
import StacksProject_2024.Chap21.Lemma_21_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(f^*).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

local notation "LfStar" => modulePullbackDerived f
local notation "RfStar" => modulePushforwardDerived f
local notation "P" => counitIsomorphismProperty LfStar RfStar adj

/- Domain-style sampling for Lemma 21.28.2:
- primary domain: object properties on derived categories cut out by the counit of an adjunction,
  together with the induced full subcategory and restricted right adjoint;
- sampled owner declarations:
  `counitIsomorphismProperty`,
  `counitIsomorphismProperty_isClosedUnderIsomorphisms`,
  `counitIsomorphismProperty_isTriangulated`,
  `restrictedRightAdjoint_fullyFaithful`;
- best owner abstraction: the Chapter 21 owner object property
  `P`;
- primitive data: only a derived adjunction `adj : Lf^* ⊣ Rf_*`;
- derived API: strict-fullness, retract-stability, triangulatedity under the exactness hypotheses,
  the induced triangulated full subcategory, and the restricted-right-adjoint Hom bijection;
- source/core/bridge triage:
  `source-facing`: the ringed-site specialization of Lemma 21.28.2;
  `core/canonical`: the generic adjunction owners from [Lemma_21_28_1](/volume/math/users/zcwang/m2f-distributed-workspace/repos/stacks-refine-stmt/stacks_project/Chap21/Lemma_21_28_1.lean);
  `bridge/view`: the full subcategory `D'` and the restricted right adjoint.

This file is therefore a source-facing specialization of the generic Chapter 21 adjunction API.
The canonical owners already exist upstream, so the correct refinement is to reuse them directly
and only add the triangulated instance that packages the exactness hypotheses in the form
downstream files can infer.
-/

/- Lemma 21.28.2 (1): the full subcategory of `ModuleDerived X` cut out by the condition that
`Lf^* Rf_* K ⟶ K` is an isomorphism is strictly full. This is the canonical ringed-site
specialization of `CategoryTheory.counitIsomorphismProperty_isClosedUnderIsomorphisms`. -/
#check (inferInstance : ObjectProperty.IsClosedUnderIsomorphisms P)

/- Lemma 21.28.2 (2): the same counit-isomorphism condition is saturated, i.e. stable under
retracts. This is the canonical ringed-site specialization of
`CategoryTheory.counitIsomorphismProperty_isStableUnderRetracts`. -/
#check
  (CategoryTheory.counitIsomorphismProperty_isStableUnderRetracts LfStar RfStar adj :
    ObjectProperty.IsStableUnderRetracts P)

section Triangulated

variable [(modulePullbackDerived f).CommShift ℤ]
variable [(modulePullbackDerived f).IsTriangulated]

-- Proof sketch: the canonical adjunction `Lf^* ⊣ Rf_*` inherits the right-adjoint shift and
-- triangulated structures from the exactness of `Lf^*`, so the generic owner theorem from
-- Lemma `21.28.1` applies directly.
/-- Lemma 21.28.2 (3): once `Lf^*` is exact, the counit-isomorphism condition defines a
triangulated object property, hence a triangulated full subcategory. -/
@[stacks 0D7R]
instance counitIsomorphismProperty_isTriangulated :
    ObjectProperty.IsTriangulated P := by
  letI : (modulePushforwardDerived f).CommShift ℤ := adj.rightAdjointCommShift ℤ
  letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  letI : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  exact CategoryTheory.counitIsomorphismProperty_isTriangulated LfStar RfStar adj

end Triangulated

/- Lemma 21.28.2 (4): the restriction of `Rf_*` to the full subcategory of `ModuleDerived X`
cut out by the counit-isomorphism condition is the canonical restricted right adjoint from
Lemma 21.28.1, and it is fully faithful. This is the canonical ringed-site specialization of the
instance `CategoryTheory.restrictedRightAdjoint_fullyFaithful`. -/
#check (CategoryTheory.restrictedRightAdjoint_fullyFaithful LfStar RfStar adj :
  (CategoryTheory.restrictedRightAdjoint LfStar RfStar adj).FullyFaithful)

end

end RingedSite.Hom
