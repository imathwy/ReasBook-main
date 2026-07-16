import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RingedSite.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.19.6:
- primary domain: compatibility of the derived adjunction counit with the canonical comparison
  morphisms `L(f)^* ⟶ f^*` and `f_* ⟶ R(f)_*`;
- sampled owner declarations:
  `modulePullbackDerived_isLeftAdjoint`,
  `Adjunction.ofIsLeftAdjoint`,
  `CategoryTheory.Adjunction.derivedε`,
  `CategoryTheory.Adjunction.derivedε_fac_app`,
  `modulePullbackDerived`,
  `modulePushforwardDerived`;
- best owner abstraction:
  `source-facing`: the ringed-site compatibility square for the derived adjunction
    `L(f)^* ⊣ R(f)_*`;
  `core/canonical`: `CategoryTheory.Adjunction.derivedε_fac_app`;
  `bridge/view`: the ringed-site left-adjoint instance `modulePullbackDerived_isLeftAdjoint`,
    from which the concrete adjunction is recovered as `Adjunction.ofIsLeftAdjoint (L(f)^*)`
    without introducing a parallel local wrapper.
- primitive data: the canonical ringed-site derived adjunction and the comparison morphisms used
  in `derivedε_fac_app`;
- derived API: the Chapter 21 ringed-site specialization of that generic square.

Source/core/bridge triage:
- `source-facing`: the ringed-site reading of the square for `L(f)^*`, `R(f)_*`, and a complex
  of `𝒪_Y`-modules;
- `core/canonical`: `CategoryTheory.Adjunction.derivedε_fac_app`;
- `bridge/view`: the derived adjunction owner `Adjunction.ofIsLeftAdjoint (L(f)^*)`, recovered
  from `modulePullbackDerived_isLeftAdjoint` to read the generic theorem in Chapter 21 notation.

This item adds no new owner-level mathematics beyond that canonical derived-adjunction theorem, so
the refined file records the Chapter 21 specialization point and then recalls the generic owner
directly instead of keeping a parallel local copy.
-/

/- Lemma 21.19.6 is specialized to ringed sites through the canonical Chapter 21 left-adjoint
instance
`modulePullbackDerived_isLeftAdjoint`, which yields
`Adjunction.ofIsLeftAdjoint (L(f)^*) : L(f)^* ⊣ R(f)_*`. -/
#check modulePullbackDerived_isLeftAdjoint

/- Lemma 21.19.6: for a morphism of ringed topoi formalized by a morphism of ringed sites and a
complex `K^•`, the square in the derived category built from the comparison `L(f)^* ⟶ f^*` on
complexes, the comparison `f_* ⟶ R(f)_*` on complexes, the underived counit
`f^* f_* K^• ⟶ K^•`, and the derived counit `L(f)^* R(f)_* K^• ⟶ K^•` commutes. In canonical
mathlib form this is the generic derived-adjunction counit compatibility
`CategoryTheory.Adjunction.derivedε_fac_app`, read using the Chapter 21 adjunction owner above. -/
recall CategoryTheory.Adjunction.derivedε_fac_app

end RingedSite.Hom
