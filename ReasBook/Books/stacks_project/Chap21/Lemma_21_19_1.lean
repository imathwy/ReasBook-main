import Mathlib
import stacks_project.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

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

/-- Lemma 21.19.1: for a morphism of ringed topoi formalized by the ringed-site morphism `f`,
the unbounded derived pullback `Lf^*` is left adjoint to the unbounded derived pushforward
`Rf_*`. -/
abbrev modulePullbackDerived_pushforward_adjunction : Prop :=
  Nonempty (modulePullbackDerived f ⊣ modulePushforwardDerived f)

-- Proof sketch: start from the underived adjunction `f^* ⊣ f_*` on module sheaves from
-- Lemma `18.13.2`. Lemma `21.18.2` supplies the total left derived functor `Lf^*`, and the
-- construction of `Rf_*` gives the total right derived functor. Then apply the generic derived
-- adjunction result of Lemma `13.30.3`, and evaluate the resulting adjunction at `(𝒢, ℱ)`.
/-- The Hom-set formulation of the derived pullback-pushforward adjunction. -/
theorem modulePullbackDerived_pushforward_homEquiv
    (h : modulePullbackDerived_pushforward_adjunction f)
    (ℱ : ModuleDerived X) (𝒢 : ModuleDerived Y) :
    Nonempty
      (((modulePullbackDerived f).obj 𝒢 ⟶ ℱ) ≃
        (𝒢 ⟶ (modulePushforwardDerived f).obj ℱ)) := sorry

end

end RingedSite.Hom
