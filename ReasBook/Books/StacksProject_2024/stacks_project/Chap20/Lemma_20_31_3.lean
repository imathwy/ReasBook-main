import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_33_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Lemma 20.31.3:
- primary domain: relative derived cup products and the tensor/naive-cup-product comparison
  square in derived categories;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.derivedPushforward_tensor_naiveCupProduct_commSq`,
  `CategoryTheory.CommSq`,
  `Adjunction.homEquiv`;
- owner abstraction:
  `source-facing`: the ringed-space specialization of the tensor/naive-cup-product square;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct` together with
    `CategoryTheory.derivedPushforward_tensor_naiveCupProduct_commSq`;
  `bridge/view`: the present specialization to chosen source/target complex representatives.

Primitive data are the adjunction, the pullback-tensor comparison, the chosen source/target
representatives, and the four comparison maps on those representatives. The relative cup product
and the commuting-square statement are already canonical owner API upstream, so this file should
reuse them directly rather than rebuilding a parallel local owner. -/

/- Lemma 20.31.3, in canonical `CommSq` form, is exactly the categorical owner theorem
`CategoryTheory.derivedPushforward_tensor_naiveCupProduct_commSq` specialized to derived
categories of `𝒪_X`-modules on ringed spaces. -/
recall CategoryTheory.derivedPushforward_tensor_naiveCupProduct_commSq

end

end AlgebraicGeometry.RingedSpace
