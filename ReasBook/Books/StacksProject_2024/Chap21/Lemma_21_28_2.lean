import Mathlib
import StacksProject_2024.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

/-- The object property on `D(\mathcal O_X)` cut out by the counit-isomorphism condition
`Lf^* Rf_* K ⟶ K`. -/
abbrev modulePullbackPushforwardCounitIsoProperty
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f) :
    ObjectProperty (ModuleDerived X) :=
  fun K ↦ IsIso (adj.counit.app K)

-- Proof sketch: the counit is a natural transformation, so for any isomorphism `K ≅ L` the two
-- counit components are conjugate. Hence invertibility of `Lf^* Rf_* K ⟶ K` is invariant under
-- isomorphism.
/-- Lemma 21.28.2 (1): the full subcategory of `D(\mathcal O_\mathcal C)` defined by the condition
that `Lf^* Rf_* K ⟶ K` is an isomorphism is strictly full. -/
instance modulePullbackPushforwardCounitIsoProperty_isClosedUnderIsomorphisms :
    (modulePullbackPushforwardCounitIsoProperty f adj).IsClosedUnderIsomorphisms := sorry

-- Proof sketch: if `K` is a retract of `L`, then naturality of the counit makes
-- `Lf^* Rf_* K ⟶ K` a retract of `Lf^* Rf_* L ⟶ L`. Retracts of isomorphisms are isomorphisms, so
-- the defining property is stable under retracts/direct summands.
/-- Lemma 21.28.2 (2): the full subcategory of `D(\mathcal O_\mathcal C)` defined by the counit
isomorphism condition is saturated, i.e. stable under retracts. -/
instance modulePullbackPushforwardCounitIsoProperty_isStableUnderRetracts :
    (modulePullbackPushforwardCounitIsoProperty f adj).IsStableUnderRetracts := sorry

/-- The counit-isomorphism condition defines a triangulated object property on
`D(\mathcal O_X)`. -/
instance modulePullbackPushforwardCounitIsoProperty_isTriangulated :
    (modulePullbackPushforwardCounitIsoProperty f adj).IsTriangulated := sorry

-- Proof sketch: the counit `Lf^* Rf_* ⟶ 𝟭` is a natural transformation between exact functors on
-- the derived category. The full subcategory where this natural transformation is an isomorphism
-- is therefore closed under shifts and distinguished triangles, and the previous two clauses give
-- strict fullness and saturation.
/-- Lemma 21.28.2 (3): the full subcategory of `D(\mathcal O_\mathcal C)` on objects `K` for which
`Lf^* Rf_* K ⟶ K` is an isomorphism is a triangulated subcategory. -/
theorem modulePullbackPushforwardCounitSubcategory_isTriangulated :
    CategoryTheory.IsTriangulated
      (modulePullbackPushforwardCounitIsoProperty f adj).FullSubcategory := sorry

-- Proof sketch: restrict the adjunction `Lf^* ⊣ Rf_*` along the full subcategory cut out by the
-- counit-isomorphism condition. On that restricted domain, every counit component is an
-- isomorphism by definition, so the standard adjunction criterion implies that the restricted
-- right adjoint `Rf_*` is fully faithful.
/-- Lemma 21.28.2 (4): the restriction of `Rf_*` to the full subcategory where
`Lf^* Rf_* K ⟶ K` is an isomorphism is fully faithful. -/
theorem modulePushforwardDerived_restriction_full_faithful :
    (((modulePullbackPushforwardCounitIsoProperty f adj).ι) ⋙
      modulePushforwardDerived f).Full ∧
      (((modulePullbackPushforwardCounitIsoProperty f adj).ι) ⋙
        modulePushforwardDerived f).Faithful :=
  sorry

end

end RingedSite.Hom
