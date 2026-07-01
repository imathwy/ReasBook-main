import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import stacks_project.Chap18.Definition_18_31_1
import stacks_project.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.IsFlat]
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The exact-functor package on module sheaves attached to pullback along a flat morphism of
ringed sites. -/
noncomputable abbrev modulePullbackExactFunctor : ModuleCat Y ⥤ₑ ModuleCat X :=
  let _ : PreservesFiniteLimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).1
  let _ : PreservesFiniteColimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).2
  ExactFunctor.of f.modulePullback

/-- The pullback functor on derived categories induced by the exact pullback on module sheaves for
a flat morphism of ringed sites. -/
noncomputable abbrev modulePullbackDerivedOfFlat : ModuleDerived Y ⥤ ModuleDerived X :=
  let _ : (modulePullbackExactFunctor f).obj.Additive :=
    (inferInstance : f.modulePullback.Additive)
  (modulePullbackExactFunctor f).obj.mapDerivedCategory

local notation "fStarDerived" => modulePullbackDerivedOfFlat f

-- Proof sketch: let `D'` be the full triangulated subcategory of `D(\mathcal O_Y)` on objects for
-- which the adjunction unit is an isomorphism. Each cohomology sheaf `H^q(K)[0]` lies in `D'` by
-- hypothesis, and bounded-below truncation induction then shows that the bounded-below object `K`
-- itself lies in `D'`.
/-- Lemma 21.28.4: for a flat morphism of ringed topoi formalized by a flat morphism of ringed
sites `f`, if a derived `\mathcal O_\mathcal D`-module `K` is bounded below and the adjunction
unit is an isomorphism on every cohomology sheaf `H^q(K)[0]`, then the unit
`K ⟶ Rf_* f^* K` is an isomorphism. In this library-facing formulation, `f^*` is the exact
pullback functor on the derived category induced by flatness. -/
theorem unit_isIso_of_boundedBelow_of_cohomologySheaf_unit_isIso
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (K : ModuleDerived Y)
    (hbounded : ∃ n : ℤ, K.IsGE n)
    (hcohom : ∀ q : ℤ,
      IsIso
        (adj.unit.app
          ((DerivedCategory.singleFunctor (ModuleCat Y) (0 : ℤ)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat Y) q).obj K)))) :
    IsIso (adj.unit.app K) := sorry

end

end RingedSite.Hom
