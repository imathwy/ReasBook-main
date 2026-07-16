import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1_core

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Remark 20.28.7:
- primary domain: relative cup products for the derived pullback/pushforward adjunction on
  ringed spaces;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProductAdjointMap`,
  `CategoryTheory.relativeDerivedCupProduct_spec`;
- source/core/bridge triage:
  `source-facing`: the relative cup-product morphism attached to the Chapter 20 adjunction
    `Lf^* ⊣ Rf_*`;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct`;
  `bridge/view`: this ringed-space recall surface.

The primitive data are already those of the canonical categorical owner: the derived adjunction and
the pullback-tensor comparison. This remark therefore contributes a source-facing recall surface,
not a second ringed-space-specific cup-product owner.
-/

/- Remark 20.28.7: given the Chapter 20 adjunction `Lf^* ⊣ Rf_*` and the pullback-tensor
comparison from Lemma 20.27.3, the resulting relative cup product is the canonical owner
`CategoryTheory.relativeDerivedCupProduct`. -/
recall CategoryTheory.relativeDerivedCupProduct

end AlgebraicGeometry.RingedSpace
