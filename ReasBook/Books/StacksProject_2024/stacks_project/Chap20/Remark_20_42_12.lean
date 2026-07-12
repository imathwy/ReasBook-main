import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Remark_21_35_10

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Remark 20.42.12:
- primary domain: compatibility between the pushforward/internal-Hom comparison of Remark
  `20.42.11` and the canonical evaluation pairing in braided closed monoidal derived categories of
  module sheaves on ringed spaces;
- sampled owner declarations:
  `RingedSite.Hom.derivedPushforwardInternalHomComparison`,
  `RingedSite.Hom.derivedPushforwardInternalHomComparison_spec`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.ihom.ev`;
- best owner abstraction:
  `source-facing`: the evaluation-compatibility statement for the comparison morphism of Remark
    `20.42.11`;
  `core/canonical`: `RingedSite.Hom.derivedPushforwardInternalHomComparison_spec`;
  `bridge/view`: this file, which only recalls the Chapter 21 owner in the ringed-space chapter.
- primitive data: the morphism `f`, the canonical adjunction/tensor-comparison package defining
  the comparison map, and the objects `L`, `K`;
- derived API: the evaluation-compatibility statement, already encoded by the owner theorem
  `RingedSite.Hom.derivedPushforwardInternalHomComparison_spec`.

Source/core/bridge triage:
- `source-facing`: Remark 20.42.12 as the ringed-space chapter's evaluation-compatibility reading
  of the pushforward/internal-Hom comparison;
- `core/canonical`: `RingedSite.Hom.derivedPushforwardInternalHomComparison_spec`;
- `bridge/view`: this file is recall-only and should not keep a second ringed-space theorem whose
  content is just the owner theorem rewritten as a local `CommSq`.
-/

/- Remark 20.42.12: the compatibility of
`Rf_* Rℋom(L, K) ⟶ Rℋom(Rf_* L, Rf_* K)`
with the canonical evaluation morphisms is already owned by the Chapter 21 specification theorem
`RingedSite.Hom.derivedPushforwardInternalHomComparison_spec`. The commutative-square reading in
the ringed-space chapter is exactly this owner theorem specialized to the opens ringed site. -/
recall RingedSite.Hom.derivedPushforwardInternalHomComparison_spec

end AlgebraicGeometry.RingedSpace
