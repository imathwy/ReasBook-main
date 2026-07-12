import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Lemma_20_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.28.6:
- primary domain: compatibility of the derived adjunction counit with the canonical comparison
  maps `Lf^* ⟶ f^*` and `f_* ⟶ Rf_*`;
- sampled owner declarations:
  `modulePullbackDerived_isLeftAdjoint`,
  `Adjunction.ofIsLeftAdjoint`,
  `Adjunction.derivedε`,
  `Adjunction.derivedε_fac_app`,
  `modulePullbackDerived`,
  `modulePushforwardDerived`;
- best owner abstraction:
  `source-facing`: the ringed-space compatibility square for the derived adjunction
    `L(f)^* ⊣ R(f)_*`;
  `core/canonical`: `Adjunction.derivedε_fac_app`;
  `bridge/view`: the ringed-space left-adjoint instance `modulePullbackDerived_isLeftAdjoint`,
    from which the concrete adjunction is recovered as `Adjunction.ofIsLeftAdjoint (L(f)^*)`
    without introducing a parallel local wrapper.
- primitive data: the canonical ringed-space derived adjunction and the comparison morphisms used
  in `derivedε_fac_app`;
- derived API: the Chapter 20 ringed-space specialization of that generic square, read through the
  induced adjunction `Adjunction.ofIsLeftAdjoint (L(f)^*)`.

Source/core/bridge triage:
- `source-facing`: the ringed-space reading of the square for `L(f)^*`, `R(f)_*`, and a complex
  of `𝒪_X`-modules;
- `core/canonical`: `Adjunction.derivedε_fac_app`;
- `bridge/view`: the derived adjunction owner
  `Adjunction.ofIsLeftAdjoint (L(f)^*)`, recovered from `modulePullbackDerived_isLeftAdjoint`
  to read the generic theorem in Chapter 20 notation.

This item adds no new owner-level mathematics beyond that canonical derived-adjunction theorem, so
the refined file records the Chapter 20 specialization point and then recalls the generic owner
directly instead of keeping a parallel local copy.
-/

/- Lemma 20.28.6 is specialized to ringed spaces through the canonical ringed-space derived
adjunction recovered from the automation-facing instance
`modulePullbackDerived_isLeftAdjoint` as
`Adjunction.ofIsLeftAdjoint (L(f)^*) : L(f)^* ⊣ R(f)_*`. -/
#check modulePullbackDerived_isLeftAdjoint

/- Lemma 20.28.6: for a morphism of ringed spaces and a complex `K^•`, the square in the
derived category obtained from the comparison `Lf^* ⟶ f^*` on complexes, the comparison
`f_* ⟶ Rf_*` on complexes, the underived counit `f^* f_* K^• ⟶ K^•`, and the derived counit
`Lf^* Rf_* K^• ⟶ K^•` commutes. In canonical mathlib form this is the generic
derived-adjunction counit compatibility `Adjunction.derivedε_fac_app`, read using
the Chapter 20 adjunction owner above. -/
recall Adjunction.derivedε_fac_app

end AlgebraicGeometry.RingedSpace
