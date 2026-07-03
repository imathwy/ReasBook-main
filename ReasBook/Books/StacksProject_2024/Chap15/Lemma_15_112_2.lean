import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Lemma_15_124_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Ideal IsLocalRing

/- Domain-style sampling for Lemma 15.112.2:
- primary domain: ramification and inertia for extensions of discrete valuation rings with finite
  fraction-field extension;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings.residueDegree`,
  `IsExtensionOfDiscreteValuationRings.residueDegree_eq_finrank`,
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension`,
  `ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension`;
- best owner abstraction: the source-facing DVR extension owner is
  `IsExtensionOfDiscreteValuationRings`, while the core numerical statements are the valuation-ring
  extension theorems from `Lemma_15_124_2`;
- primitive-vs-derived split: the primitive data for the source-facing lemma are the DVR extension
  together with the finite-dimensional fraction-field hypothesis, while the owner-level comparison
  `valuationRing_ramificationIndex_eq` is derived directly from the two ramification-index owners
  and does not use finiteness; the chapter names `ramificationIndex` and `residueDegree` are the
  source-facing DVR owners reused directly in the bridge statements below.

Source/core/bridge triage:
- `source-facing`: the textbook statements in terms of `ramificationIndex A B` and
  `residueDegree A B`;
- `core/canonical`: the valuation-ring extension theorems
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension` and
  `ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension`;
- `bridge/view`: the specialization of those valuation-ring theorems to the chapter-local DVR
  owner.
-/

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/- Lemma 15.112.2 (1): for an extension of discrete valuation rings `A ⊂ B`, if the induced
fraction-field extension `FractionRing B / FractionRing A` is finite, then the induced residue
field extension is finite. This is the exact valuation-ring owner theorem recalled in the
discrete-valuation-ring setting via the canonical instance
`discreteValuationRingExtension_toIsExtensionOfValuationRings`. -/
recall finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

attribute [local instance]
  finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

namespace IsExtensionOfDiscreteValuationRings

/-- The valuation-ring ramification index agrees with the source-facing DVR ramification index. -/
theorem valuationRing_ramificationIndex_eq
    : IsExtensionOfValuationRings.ramificationIndex A B = ramificationIndex A B := by
  sorry

-- Proof sketch: first rewrite the valuation-ring ramification index through
-- `valuationRing_ramificationIndex_eq`; the valuation-ring residue degree is definitionally the
-- same as the chapter-local DVR residue degree. Then specialize the canonical valuation-ring
-- inequality from `Lemma_15_124_2` to the DVR extension `A ⊂ B` and convert the resulting `ℕ∞`
-- inequality back to `ℕ`.
/-- Lemma 15.112.2 (2): for an extension of discrete valuation rings `A ⊂ B`, if the induced
fraction-field extension `FractionRing B / FractionRing A` is finite, then the ramification index
times the residue degree is bounded by `[FractionRing B : FractionRing A]`. This is the
source-facing DVR restatement of the canonical valuation-ring inequality from `Lemma_15_124_2`. -/
theorem ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    ramificationIndex A B * residueDegree A B ≤
      Module.finrank (FractionRing A) (FractionRing B) := by
  sorry

end IsExtensionOfDiscreteValuationRings

end
