import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Remark_21_35_10

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Remark 20.42.11:
- primary domain: pushforward/internal-Hom comparison morphisms in braided closed monoidal
  derived categories of module sheaves on ringed spaces, viewed through the opens ringed site;
- sampled owner declarations:
  `RingedSite.Hom.derivedPushforwardInternalHomComparison`,
  `RingedSite.Hom.derivedPushforwardInternalHomComparison_spec`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.MonoidalClosed.braidedHomEquiv`;
- best owner abstraction:
  `source-facing`: the canonical morphism
    `Rf_* Rℋom(L, K) ⟶ Rℋom(Rf_* L, Rf_* K)`;
  `core/canonical`: `RingedSite.Hom.derivedPushforwardInternalHomComparison` together with its
    specification theorem;
  `bridge/view`: this file, which only recalls that Chapter 21 owner for the ringed-space chapter.
- primitive data: the morphism `f`, the canonical adjunction `Lf^* ⊣ Rf_*`, the pullback-tensor
  comparison, and the objects `L`, `K`;
- derived API: the comparison morphism itself and the tensor-side specification theorem.

Source/core/bridge triage:
- `source-facing`: Remark 20.42.11 as the ringed-space chapter’s canonical pushforward/internal-Hom
  comparison;
- `core/canonical`: `RingedSite.Hom.derivedPushforwardInternalHomComparison`;
- `bridge/view`: this file is recall-only and should not keep a second parallel ringed-space owner.
-/

/- Remark 20.42.11: the canonical morphism
`Rf_* Rℋom(L, K) ⟶ Rℋom(Rf_* L, Rf_* K)`
is already owned by the Chapter 21 declaration
`RingedSite.Hom.derivedPushforwardInternalHomComparison`. -/
recall RingedSite.Hom.derivedPushforwardInternalHomComparison

/- The adjunction-side description of Remark 20.42.11 is already owned by the companion theorem
`RingedSite.Hom.derivedPushforwardInternalHomComparison_spec`. -/
recall RingedSite.Hom.derivedPushforwardInternalHomComparison_spec

end AlgebraicGeometry.RingedSpace
